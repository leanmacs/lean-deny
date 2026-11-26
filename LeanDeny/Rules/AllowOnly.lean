import LeanDeny.Graph.Query
import LeanDeny.Policy.Resolve
import LeanDeny.Rules.Common

/-!
# `[[allow-only]]` rules

An allow-only rule says what a module may import from outside its own
package: every such import must land in `allow`. Pure.

- A rule **covers** the workspace modules of `from` minus `except`.
- A module is **governed** by the most specific rule covering it: the one
  rule whose covered modules are a subset of every other covering rule's.
  Nested rules are tiers (a library, its tests, a linked test), and only the
  governing rule's `allow` applies; it is not combined with the outer
  tiers'. A module no rule covers is not checked.
- Every import of a governed module whose target is external or in another
  package must be in `allow`: plain, `meta` and Lean's implicit `Init`
  imports alike. Imports within the module's own package are never checked.
  One violation per (importer, imported) pair, the first directive in source
  order as its witness.

Errors, each naming the rule and, for a selector, the field: a selector that
matches nothing, a `from` selector that matches only external modules, an
`except` selector that removes nothing from `from`, a rule its `except`
empties; then, across rules, two rules covering the same modules, and rules
that overlap without one nesting in the other (no rule is the most specific
for the modules they share); then, per rule, a rule that governs no module
and an `allow` selector that allows nothing. Any error means no violation is
reported.
-/

open Lean LeanDeny.Graph

namespace LeanDeny

/-- An allow-only rule with its selectors resolved. -/
structure AllowOnlyResolved where
  rule : AllowOnlyRule
  /-- What the rule covers: the workspace modules of `from` minus `except`,
  sorted; non-empty. -/
  covered : Array NodeId
  /-- Each `allow` selector with what it matches, in source order. -/
  allow : Array (SelectorRef × Array NodeId)
  deriving Inhabited

/-- The violation of rule `r` that import `e` witnesses. -/
def AllowOnlyRule.violation (r : AllowOnlyRule) (e : Edge) : Violation :=
  { rule := r.ref, pos? := r.pos?, reason? := some r.reason, chain := #[e] }

/-- "allow-only rule 3", or "allow-only rules 3 and 4". -/
private def rulesText (ns : Array Nat) : String :=
  s!"allow-only rule{if ns.size == 1 then "" else "s"} {proseList (ns.map toString)}"

/-- Resolve rule `r`'s selectors in `g`, with the policy's sets resolved in
`sets`. The errors, in order: each selector that matches nothing (source
order), each `from` selector that matches only external modules, then, if no
`from` selector matched nothing, each `except` selector that removes no
module of `from`, then, only if there was no error so far, a rule `except`
leaves covering no workspace module. -/
def resolveAllowOnly (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId))
    (r : AllowOnlyRule) : Except (Array String) AllowOnlyResolved :=
  Id.run do
    let loc := Policy.locate p.path
    let mut errs := #[]
    let mut sources := #[]
    let mut excepts := #[]
    let mut allow := #[]
    let mut externalOnly := #[]
    let mut fromFailed := false
    for ref in r.refs do
      match matchRef g sets ref with
      | .ok ns =>
        match ref.use with
        | .rule _ _ "from" =>
          sources := sortedUnion sources ns
          if !ns.isEmpty && ns.all (isExternalId g) then
            externalOnly := externalOnly.push ref
        | .rule _ _ "except" =>
          excepts := excepts.push (ref, ns)
        | _ =>
          allow := allow.push (ref, ns)
      | m =>
        if let .rule _ _ "from" := ref.use then
          fromFailed := true
        errs := errs.push (loc ref.pos? ((matchError? ref m).getD ""))
    for ref in externalOnly do
      let msg :=
        s!"{ref.describe} matches only modules outside the workspace, which import nothing \
          in the graph"
      errs := errs.push (loc ref.pos? msg)
    if !fromFailed then
      for (ref, ns) in excepts do
        if !ns.isEmpty && (sortedDiff ns sources).size == ns.size then
          errs := errs.push (loc ref.pos? s!"{ref.describe} removes no module from 'from'")
    let removed := excepts.foldl (fun acc (_, ns) => sortedUnion acc ns) #[]
    let covered := (sortedDiff sources removed).filter (!isExternalId g ·)
    if errs.isEmpty && covered.isEmpty then
      let msg := s!"{r.label} covers no module: 'except' removes every workspace module of 'from'"
      errs := errs.push (loc r.pos? msg)
    if errs.isEmpty then
      return .ok { rule := r, covered, allow }
    return .error errs

/-- The message for modules `names` that rules `rules` (two or more) all
cover, none being the most specific for them. -/
private def overlapMessage (rules : Array Nat) (names : Array String) : String :=
  let two := rules.size == 2
  let mods := ", ".intercalate names.toList
  s!"{rulesText rules} overlap without nesting: {if two then "both" else "all"} cover {mods}, \
    but each also covers a module {if two then "the other" else "another"} does not, so \
    {if two then "neither" else "none"} is the most specific for \
    {if names.size == 1 then "it" else "them"} (nest one rule's modules inside \
    {if two then "the other's" else "another's"}, or take the shared modules out of one with \
    'except')"

/-- Per node, the index into `rs` of the rule that governs it (the most
specific rule covering it), `none` when no rule covers it; or the errors:
rules covering the same modules, else groups of modules with no most specific
rule (in `displayOrder`, one message per group of rules). Every message is
rendered with the policy path `path`. -/
def governing (g : Graph) (path : String) (rs : Array AllowOnlyResolved) :
    Except (Array String) (Array (Option Nat)) :=
  Id.run do
    let loc := Policy.locate path
    let mut errs := #[]
    for j in [0:rs.size] do
      let some rj := rs[j]? | continue
      if let some i :=
          (Array.range j).find? fun i => (rs[i]?.map (·.covered)) == some rj.covered then
        let ri := rs[i]!.rule
        let msg :=
          s!"{rj.rule.label} covers exactly the modules {ri.label} covers, so neither is the \
            most specific (merge the two rules, or narrow one with 'except')"
        errs := errs.push (loc rj.rule.pos? msg)
    if !errs.isEmpty then
      return .error errs
    let masks := rs.map (memberMask g ·.covered)
    let covers (k : Nat) (n : NodeId) : Bool := (masks[k]?.bind (·[n]?)).getD false
    -- `strict[a][b]`: rule a covers a proper subset of what rule b covers.
    -- No two rules cover the same modules here, so a subset is proper.
    let strict :=
      rs.map fun a =>
        (Array.range rs.size).map fun b =>
          (rs[b]?.any fun rb => rb.covered.size > a.covered.size) && a.covered.all (covers b)
    let mut gov := Array.replicate g.nodes.size none
    -- Per group of minimal rules (indices into `rs`): its modules.
    let mut groups : Array (Array Nat × Array NodeId) := #[]
    for n in displayOrder g (Array.range g.nodes.size) do
      let cs := (Array.range rs.size).filter (covers · n)
      let minimal := cs.filter fun a => !cs.any fun b => (strict[b]?.bind (·[a]?)).getD false
      match minimal.toList with
      | [] =>
        pure ()
      | [k] =>
        gov := gov.set! n (some k)
      | _ =>
        match groups.findIdx? (·.1 == minimal) with
        | some gi =>
          groups := groups.modify gi fun (ks, ns) => (ks, ns.push n)
        | none =>
          groups := groups.push (minimal, #[n])
    for (ks, ns) in groups do
      let rules := ks.filterMap fun k => rs[k]?.map (·.rule)
      let some last := rules.back? | continue
      errs := errs.push (loc last.pos? (overlapMessage (rules.map (·.index)) (ns.map (nodeName g))))
    if !errs.isEmpty then
      return .error errs
    return .ok gov

/-- Evaluate a resolved rule over the modules it governs (`governed`, in
`displayOrder`): its violations, in report order (each governed module, then
its imports in source order), and, per allow selector, whether it allows any
import. -/
def evalAllowOnly (g : Graph) (d : AllowOnlyResolved) (governed : Array NodeId) :
    Array Violation × Array Bool :=
  Id.run do
    let inAllow := memberMask g (d.allow.foldl (fun acc (_, ns) => sortedUnion acc ns) #[])
    let masks := d.allow.map fun (_, ns) => memberMask g ns
    let mut used := Array.replicate d.allow.size false
    let mut vs := #[]
    for f in governed do
      -- One violation per imported module: the first directive is the witness.
      let mut seen : Array NodeId := #[]
      for e in g.imports f do
        unless leavesPackage g e do
          continue
        for h : k in [0:masks.size] do
          if masks[k][e.dst]?.getD false then
            used := used.set! k true
        if !(inAllow[e.dst]?.getD false) && !seen.contains e.dst then
          seen := seen.push e.dst
          vs := vs.push (d.rule.violation e)
    return (vs, used)

/-- Every allow-only rule of `p`, with the policy's sets resolved in `sets`:
the violations in rule order, or every error. The errors: each rule's
resolution errors (rule order); else, only when every rule resolved,
`governing`'s; else, per rule, a rule that governs no module, or its allow
selectors that allow nothing (source order). -/
def checkAllowOnly (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId)) :
    Except (Array String) (Array Violation) :=
  Id.run do
    let mut errs := #[]
    let mut rs := #[]
    for r in p.allowOnly do
      match resolveAllowOnly g p sets r with
      | .error es =>
        errs := errs ++ es
      | .ok d =>
        rs := rs.push d
    if !errs.isEmpty then
      return .error errs
    let gov ←
      match governing g p.path rs with
      | .ok gov =>
        pure gov
      | .error es =>
        return .error es
    let mut vs := #[]
    for (d, i) in rs.zipIdx do
      let governedBy (n : NodeId) : Option Nat := gov[n]?.join
      let governed := displayOrder g (d.covered.filter (governedBy · == some i))
      if governed.isEmpty then
        let others :=
          (d.covered.filterMap fun n =>
              (governedBy n).bind fun k =>
                rs[k]?.map (·.rule.index)) |>.toList.eraseDups.toArray.qsort
            (· < ·)
        let msg :=
          s!"{d.rule.label} governs no module: a more specific rule governs each module it \
            covers ({rulesText others})"
        errs := errs.push (Policy.locate p.path d.rule.pos? msg)
        continue
      let (rvs, used) := evalAllowOnly g d governed
      for ((ref, _), u) in d.allow.zip used do
        unless u do
          let msg :=
            s!"{ref.describe} allows nothing: no module the rule governs imports a module it \
              matches from outside its own package"
          errs := errs.push (Policy.locate p.path ref.pos? msg)
      vs := vs ++ rvs
    if errs.isEmpty then
      return .ok vs
    return .error errs

end LeanDeny
