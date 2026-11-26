import LeanDeny.Graph.Query
import LeanDeny.Policy.Resolve
import LeanDeny.Rules.Common

/-!
# `[[deny]]` rules

A deny rule says no module of `from` may import a module of `to`. Pure.

- **Direct** (the default): every import from a module of `from` to a module
  of `to` is a violation, one per (importer, imported) pair, with the first
  such directive in source order as its witness. Every import counts: plain,
  `meta`, and Lean's implicit `Init` imports.
- **Transitive** (`transitive = true`): every module of `from` that reaches
  `to` through one or more imports is a violation, one per `from` module,
  with a shortest chain as its witness (`Graph.shortestPath?`'s tie-break).
  The graph's external modules import nothing, so a chain ends at the first
  one.
- **Wrappers** excuse importers. A `from` module that is a wrapper is
  excused, in both modes. A transitive search never walks out of a wrapper,
  so a chain through one is allowed; reaching a wrapper that is itself in
  `to` is still a violation, since a chain stops at the first `to` module.

A rule's selectors are resolved against the graph first. A selector that
matches nothing, a `from` selector that matches only external modules, `from`
and `to` sharing modules, and a wrapper selector that excuses nothing are
errors, each naming the rule and, for a selector, the field. A rule with an
error is not evaluated, and any error anywhere means no violation is
reported: a policy known to be wrong gives no result to trust.

A wrapper module is *used* when it is the first wrapper on a chain from a
`from` module into `to`: for a direct rule, a `from` module with an import
into `to`; for a transitive rule, a module reached from `from` (or in it)
without passing a wrapper or a `to` module, from which some `to` module is
reachable. A wrapper in `to` is never used, in either mode: no `to` module
is in `from`, and a chain stops at it before walking out of it. A wrapper
selector none of whose modules is used excuses nothing; when every module it
matches is in `to`, the error says so and points at the importer instead.
-/

open Lean LeanDeny.Graph

namespace LeanDeny

/-- A deny rule with its selectors resolved. -/
structure DenyResolved where
  rule : DenyRule
  /-- The union of `from`, sorted. -/
  sources : Array NodeId
  /-- The union of `to`, sorted. -/
  targets : Array NodeId
  /-- Each wrapper selector with what it matches, in source order. -/
  wrappers : Array (SelectorRef × Array NodeId)
  deriving Inhabited

/-- The violation of rule `r` that `chain` witnesses: a chain of imports
from a module in `from` to a module in `to`. -/
def DenyRule.violation (r : DenyRule) (chain : Array Edge) : Violation :=
  { rule := r.ref, pos? := r.pos?, reason? := some r.reason, chain }

/-- Resolve rule `r`'s selectors in `g`, with the policy's sets resolved in
`sets`. The errors, in order: each selector that matches nothing (source
order), each `from` selector that matches only external modules, then, only
if there was neither, `from` and `to` sharing modules. -/
def resolveDeny (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId)) (r : DenyRule) :
    Except (Array String) DenyResolved :=
  Id.run do
    let loc := Policy.locate p.path
    let mut errs := #[]
    let mut sources := #[]
    let mut targets := #[]
    let mut wrappers := #[]
    let mut externalOnly := #[]
    for ref in r.refs do
      match matchRef g sets ref with
      | .ok ns =>
        match ref.use with
        | .rule _ _ "from" =>
          sources := sortedUnion sources ns
          if !ns.isEmpty && ns.all (isExternalId g) then
            externalOnly := externalOnly.push ref
        | .rule _ _ "to" =>
          targets := sortedUnion targets ns
        | _ =>
          wrappers := wrappers.push (ref, ns)
      | m =>
        errs := errs.push (loc ref.pos? ((matchError? ref m).getD ""))
    for ref in externalOnly do
      let msg :=
        s!"{ref.describe} matches only modules outside the workspace, which import nothing \
          in the graph"
      errs := errs.push (loc ref.pos? msg)
    if errs.isEmpty then
      let inTo := memberMask g targets
      let shared := sources.filter (inTo[·]?.getD false)
      if !shared.isEmpty then
        let names := ", ".intercalate ((displayOrder g shared).map (nodeName g)).toList
        let msg :=
          s!"{r.label}: 'from' and 'to' share modules: {names} (take them out of one side \
            with a set's 'except')"
        errs := errs.push (loc r.pos? msg)
    if errs.isEmpty then
      return .ok { rule := r, sources, targets, wrappers }
    return .error errs

/-- Evaluate a resolved rule: its violations, in report order (each `from`
module in `displayOrder`, then, for a direct rule, its imports in source
order), and, per wrapper selector, whether it excuses anything. -/
def evalDeny (g : Graph) (d : DenyResolved) : Array Violation × Array Bool :=
  Id.run do
    let inTo := memberMask g d.targets
    let inFrom := memberMask g d.sources
    let inW := memberMask g (d.wrappers.foldl (fun acc (_, ns) => sortedUnion acc ns) #[])
    let isTo (n : NodeId) : Bool := inTo[n]?.getD false
    let isW (n : NodeId) : Bool := inW[n]?.getD false
    let mut vs := #[]
    for f in displayOrder g d.sources do
      if isW f then
        continue
      if d.rule.transitive then
        if let some chain := g.shortestPath? #[f] isTo (follow := fun e => !isW e.src) then
          vs := vs.push (d.rule.violation chain)
      else
        -- One violation per imported module: the first directive is the witness.
        let mut seen : Array NodeId := #[]
        for e in g.imports f do
          if isTo e.dst && !seen.contains e.dst then
            seen := seen.push e.dst
            vs := vs.push (d.rule.violation #[e])
    -- Modules reached from `from` without walking out of a wrapper or a `to`
    -- module: a wrapper among them, or in `from`, is a first wrapper.
    let reached :=
      if d.rule.transitive then
        memberMask g <| g.reachable d.sources (follow := fun e => !isW e.src && !isTo e.src)
      else #[]
    let used (w : NodeId) : Bool :=
      let inFromW := inFrom[w]?.getD false
      !isTo w &&
        if d.rule.transitive then
          (inFromW || reached[w]?.getD false) && (g.shortestPath? #[w] isTo).isSome
        else inFromW && (g.imports w).any (isTo ·.dst)
    return (vs, d.wrappers.map fun (_, ns) => ns.any used)

/-- The message for wrapper selector `ref` of rule `r` that excuses nothing,
`allInTo` when every module it matches is in `to`. -/
private def unusedWrapper (r : DenyRule) (ref : SelectorRef) (allInTo : Bool) : String :=
  let why :=
    match allInTo, r.transitive with
    | true, _ =>
      "it matches only modules in 'to', and a wrapper is a module allowed to import 'to', \
        so list the module that imports it instead"
    | false, true =>
      "none of its modules is the first wrapper on an import chain from 'from' to 'to'"
    | false, false => "none of its modules is in 'from' and imports a module in 'to'"
  s!"{ref.describe} excuses nothing: {why}"

/-- Every deny rule of `p`, with the policy's sets resolved in `sets`: the
violations in rule order, or every error of every rule (rule order; per rule,
resolution errors, then unused wrappers in source order). -/
def checkDeny (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId)) :
    Except (Array String) (Array Violation) :=
  Id.run do
    let mut errs := #[]
    let mut vs := #[]
    for r in p.deny do
      match resolveDeny g p sets r with
      | .error es =>
        errs := errs ++ es
      | .ok d =>
        let (rvs, used) := evalDeny g d
        for ((ref, ns), u) in d.wrappers.zip used do
          unless u do
            let allInTo := ns.all d.targets.contains
            errs := errs.push (Policy.locate p.path ref.pos? (unusedWrapper r ref allInTo))
        vs := vs ++ rvs
    if errs.isEmpty then
      return .ok vs
    return .error errs

end LeanDeny
