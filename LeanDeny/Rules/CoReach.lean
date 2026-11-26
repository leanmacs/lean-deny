import LeanDeny.Graph.Query
import LeanDeny.Graph.View
import LeanDeny.Policy.Resolve
import LeanDeny.Rules.Common

/-!
# `[[co-reach]]` rules

A co-reach rule says every module of `roots` that reaches a module of
`if-reaches` also reaches every module of `must-reach`. Pure.

- The **closure** of a root is the root and every module it imports,
  directly or not. It is reflexive: a root that is itself an `if-reaches`
  module triggers the rule, and a root that is itself a `must-reach` module
  reaches it. Every import counts: plain, `meta`, and Lean's implicit `Init`
  imports.
- A root is **triggered** when its closure holds any module of
  `if-reaches`. Its witness is the shortest import chain from the root to
  the nearest one (`Graph.shortestPath?`), empty when the root is itself one.
- A triggered root whose closure misses any module of `must-reach` is one
  violation, naming every missing module in `displayOrder`. Violations come
  in the roots' `displayOrder`. The modules checked are the loaded graph's
  workspace modules and declared roots; an external module a selector
  matches is dropped, as it has no file and imports nothing in the graph.

A rule's selectors are resolved against the graph first. The errors, in
order: each selector that matches nothing, each `roots` selector, then each
`if-reaches` selector, then each `must-reach` selector, that matches only
external modules, then, only if there was none of those, a rule none of
whose roots reaches an `if-reaches` module, so it holds of nothing. A rule
with an error is not evaluated, and any error anywhere means no violation is
reported.
-/

open Lean LeanDeny.Graph

namespace LeanDeny

/-- A co-reach rule with its selectors resolved. -/
structure CoReachResolved where
  rule : CoReachRule
  /-- The workspace modules of `roots`, sorted. -/
  roots : Array NodeId
  /-- The workspace modules of `if-reaches`, sorted. -/
  ifReaches : Array NodeId
  /-- The workspace modules of `must-reach`, sorted. -/
  mustReach : Array NodeId
  /-- Each triggered root, in `displayOrder`: the root, the `if-reaches`
  module it reaches nearest, and the chain from one to the other (empty when
  they are the same module). Non-empty. -/
  triggered : Array (NodeId × NodeId × Array Edge)
  deriving Inhabited

/-- Each root of `roots`, in `displayOrder`, that reaches a module of
`ifMask`: the root, the nearest such module, and the chain to it. -/
def coReachTriggers (g : Graph) (roots : Array NodeId) (ifMask : Array Bool) :
    Array (NodeId × NodeId × Array Edge) :=
  (displayOrder g roots).filterMap fun r =>
    if ifMask[r]?.getD false then some (r, r, #[])
    else
      (g.shortestPath? #[r] (ifMask[·]?.getD false)).bind fun path =>
        path.back?.map fun e => (r, e.dst, path)

/-- The violation of rule `r` for root `root`, which reaches `trigger`
through `chain` but not the modules `missing`. -/
def CoReachRule.violation (g : Graph) (r : CoReachRule) (root trigger : NodeId) (chain : Array Edge)
    (missing : Array NodeId) : Violation :=
  let missingText := proseList (missing.map (nodeName g))
  let detail :=
    if root == trigger then
      s!"{nodeName g root} is in 'if-reaches' but does not reach {missingText}"
    else s!"{nodeName g root} reaches {nodeName g trigger} but not {missingText}"
  { rule := r.ref, pos? := r.pos?, reason? := some r.reason, detail? := some detail, chain,
    module? := some root, missing }

/-- Resolve rule `r`'s selectors in `g`, with the policy's sets resolved in
`sets`. The errors, in order: each selector that matches nothing (source
order), each `roots`, then `if-reaches`, then `must-reach` selector that
matches only external modules, then, only if there was none of those, a
rule none of whose roots reaches an `if-reaches` module. -/
def resolveCoReach (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId))
    (r : CoReachRule) : Except (Array String) CoReachResolved :=
  Id.run do
    let loc := Policy.locate p.path
    let mut errs := #[]
    let mut roots := #[]
    let mut ifReaches := #[]
    let mut mustReach := #[]
    let mut rootsExternal := #[]
    let mut ifExternal := #[]
    let mut mustExternal := #[]
    for ref in r.refs do
      match matchRef g sets ref with
      | .ok ns =>
        let external := !ns.isEmpty && ns.all (isExternalId g)
        match ref.use with
        | .rule _ _ "roots" =>
          roots := sortedUnion roots ns
          if external then
            rootsExternal := rootsExternal.push ref
        | .rule _ _ "if-reaches" =>
          ifReaches := sortedUnion ifReaches ns
          if external then
            ifExternal := ifExternal.push ref
        | _ =>
          mustReach := sortedUnion mustReach ns
          if external then
            mustExternal := mustExternal.push ref
      | m =>
        errs := errs.push (loc ref.pos? ((matchError? ref m).getD ""))
    for ref in rootsExternal do
      let msg :=
        s!"{ref.describe} matches only modules outside the workspace, which import nothing \
          in the graph"
      errs := errs.push (loc ref.pos? msg)
    for ref in ifExternal ++ mustExternal do
      let msg :=
        s!"{ref.describe} matches only modules outside the workspace, which a rule about \
          reach does not check"
      errs := errs.push (loc ref.pos? msg)
    roots := roots.filter (!isExternalId g ·)
    ifReaches := ifReaches.filter (!isExternalId g ·)
    mustReach := mustReach.filter (!isExternalId g ·)
    if !errs.isEmpty then
      return .error errs
    let triggered := coReachTriggers g roots (memberMask g ifReaches)
    if triggered.isEmpty then
      let msg :=
        s!"{r.label}: no module of 'roots' reaches a module of 'if-reaches', so the rule \
          holds of nothing"
      return .error #[loc r.pos? msg]
    return .ok { rule := r, roots, ifReaches, mustReach, triggered }

/-- Evaluate a resolved rule: one violation per triggered root whose closure
misses a `must-reach` module, in the roots' `displayOrder`. -/
def evalCoReach (g : Graph) (d : CoReachResolved) : Array Violation :=
  let must := displayOrder g d.mustReach
  d.triggered.filterMap fun (root, trigger, chain) =>
    let reached := memberMask g (sortedUnion #[root] (g.reachable #[root]))
    let missing := must.filter fun m => !(reached[m]?.getD false)
    if missing.isEmpty then none else some (d.rule.violation g root trigger chain missing)

/-- Every co-reach rule of `p`, with the policy's sets resolved in `sets`:
the violations in rule order, or every rule's errors in rule order. -/
def checkCoReach (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId)) :
    Except (Array String) (Array Violation) :=
  Id.run do
    let mut errs := #[]
    let mut vs := #[]
    for r in p.coReach do
      match resolveCoReach g p sets r with
      | .error es =>
        errs := errs ++ es
      | .ok d =>
        vs := vs ++ evalCoReach g d
    if errs.isEmpty then
      return .ok vs
    return .error errs

end LeanDeny
