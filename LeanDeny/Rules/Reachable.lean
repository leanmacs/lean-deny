import LeanDeny.Graph.Query
import LeanDeny.Policy.Resolve
import LeanDeny.Rules.Common

/-!
# `[[reachable]]` rules

A reachable rule says every module of `must-cover` is reached from `from`.
Pure.

- The **closure** of a rule is the modules of `from` and every module they
  import, directly or not. It is reflexive: a `from` module counts as
  covered. Every import counts: plain, `meta`, and Lean's implicit `Init`
  imports.
- Every module of `must-cover` outside the closure is one violation, in
  `displayOrder`. The modules checked are the loaded graph's workspace
  modules and declared roots; an external module `must-cover` matches is
  ignored, as it has no file and is not the build's to cover.

A rule's selectors are resolved against the graph first. The errors, in
order: each selector that matches nothing, each `from` selector that matches
only external modules, each `must-cover` selector that matches only external
modules, then, only if there was none of those, a rule every module of whose
`must-cover` is in `from`, so it checks nothing. A rule with an error is not
evaluated, and any error anywhere means no violation is reported.
-/

open Lean LeanDeny.Graph

namespace LeanDeny

/-- A reachable rule with its selectors resolved. -/
structure ReachableResolved where
  rule : ReachableRule
  /-- The union of `from`, sorted. -/
  sources : Array NodeId
  /-- The workspace modules of `must-cover`, sorted; non-empty. -/
  mustCover : Array NodeId
  deriving Inhabited

/-- The violation of rule `r` for module `m`, outside the closure of `from`,
whose module names are `froms`: listed when there are at most three,
otherwise counted. -/
def ReachableRule.violation (g : Graph) (r : ReachableRule) (froms : Array NodeId) (m : NodeId) :
    Violation :=
  let fromText :=
    if froms.size ≤ 3 then proseList (froms.map (nodeName g)) else s!"'from' ({froms.size} modules)"
  { rule := r.ref, pos? := r.pos?, reason? := some r.reason,
    detail? := some s!"{nodeName g m} is outside the import closure of {fromText}", chain := #[],
    module? := some m }

/-- Resolve rule `r`'s selectors in `g`, with the policy's sets resolved in
`sets`. The errors, in order: each selector that matches nothing (source
order), each `from` selector that matches only external modules, each
`must-cover` selector that matches only external modules, then, only if
there was none of those, a rule whose workspace `must-cover` modules all lie
in `from`. -/
def resolveReachable (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId))
    (r : ReachableRule) : Except (Array String) ReachableResolved :=
  Id.run do
    let loc := Policy.locate p.path
    let mut errs := #[]
    let mut sources := #[]
    let mut mustCover := #[]
    let mut fromExternal := #[]
    let mut coverExternal := #[]
    for ref in r.refs do
      match matchRef g sets ref with
      | .ok ns =>
        let external := !ns.isEmpty && ns.all (isExternalId g)
        match ref.use with
        | .rule _ _ "from" =>
          sources := sortedUnion sources ns
          if external then
            fromExternal := fromExternal.push ref
        | _ =>
          mustCover := sortedUnion mustCover ns
          if external then
            coverExternal := coverExternal.push ref
      | m =>
        errs := errs.push (loc ref.pos? ((matchError? ref m).getD ""))
    for ref in fromExternal do
      let msg :=
        s!"{ref.describe} matches only modules outside the workspace, which import nothing \
          in the graph"
      errs := errs.push (loc ref.pos? msg)
    for ref in coverExternal do
      let msg :=
        s!"{ref.describe} matches only modules outside the workspace, which a rule about \
          reach does not check"
      errs := errs.push (loc ref.pos? msg)
    mustCover := mustCover.filter (!isExternalId g ·)
    if errs.isEmpty && (sortedDiff mustCover sources).isEmpty then
      let msg := s!"{r.label}: every module of 'must-cover' is in 'from', so it checks nothing"
      errs := errs.push (loc r.pos? msg)
    if errs.isEmpty then
      return .ok { rule := r, sources, mustCover }
    return .error errs

/-- Evaluate a resolved rule: one violation per `must-cover` module outside
the closure of `from`, in `displayOrder`. -/
def evalReachable (g : Graph) (d : ReachableResolved) : Array Violation :=
  let covered := memberMask g (sortedUnion d.sources (g.reachable d.sources))
  let froms := displayOrder g d.sources
  (displayOrder g d.mustCover).filterMap fun m =>
    if covered[m]?.getD false then none else some (d.rule.violation g froms m)

/-- Every reachable rule of `p`, with the policy's sets resolved in `sets`:
the violations in rule order, or every rule's errors in rule order. -/
def checkReachable (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId)) :
    Except (Array String) (Array Violation) :=
  Id.run do
    let mut errs := #[]
    let mut vs := #[]
    for r in p.reachable do
      match resolveReachable g p sets r with
      | .error es =>
        errs := errs ++ es
      | .ok d =>
        vs := vs ++ evalReachable g d
    if errs.isEmpty then
      return .ok vs
    return .error errs

end LeanDeny
