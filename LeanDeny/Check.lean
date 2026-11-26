import LeanDeny.Cli
import LeanDeny.Exit
import LeanDeny.Load
import LeanDeny.Policy
import LeanDeny.Policy.Resolve
import LeanDeny.Rules.AllowOnly
import LeanDeny.Rules.Deny
import LeanDeny.Rules.Layers
import LeanDeny.Rules.Reachable

/-!
# `lean-deny check`

Resolve the workspace, load the policy, load the workspace's module graph
with the policy's declared roots (`[[root]]`),
resolve every set of the policy against it (each selector must match), then
check the policy's rules: deny rules (`LeanDeny.Rules.Deny`), then
allow-only rules (`LeanDeny.Rules.AllowOnly`), then `[layers]`
(`LeanDeny.Rules.Layers`), then reachable rules
(`LeanDeny.Rules.Reachable`). Cheap failures come first: a bad workspace path
or policy is reported before Lake runs.

The report goes to stdout in the format `--format` names
(`LeanDeny.Report`): for text, `lean-deny: ok (N rules)` when every rule
holds (exit 0), or one block per violation and a summary line (exit 1).
Errors go to stderr in every format (exit 2), and a policy with any error
reports no violation. The exit code is the same in every format.
-/

open System

namespace LeanDeny

/-- Every rule of `p`, with the policy's sets resolved in `sets`: deny rules,
then allow-only rules, then `[layers]`, then reachable rules. Every error of
every kind (in that order), or, when there is none, every violation (in that
order). -/
def checkRules (g : Graph.Graph) (p : Policy) (sets : Std.HashMap String (Array Graph.NodeId)) :
    Except (Array String) (Array Violation) :=
  let rs :=
    #[checkDeny g p sets, checkAllowOnly g p sets, checkLayers g p sets, checkReachable g p sets]
  let errs :=
    rs.flatMap fun
      | .error es => es
      | .ok _ => #[]
  if errs.isEmpty then
    .ok
      (rs.flatMap fun
        | .ok vs => vs
        | .error _ => #[])
  else .error errs

/-- Run `check`. Diagnostics go to stderr, one line each, in every format;
the report in `opts.format` to stdout (`LeanDeny.Report`). -/
def runCheck (opts : CheckOpts) : IO Outcome := do
  let ws := opts.workspace
  let policyPath := opts.config?.getD (defaultPolicyPath ws)
  let cwd := (← IO.FS.realPath (← IO.currentDir)).toString
  let ctx : ReportCtx := { policyPath := policyPath.toString, cwd }
  let finish (r : CheckResult) : IO Outcome := do
    if let .failed _ msgs := r then
      msgs.forM printError
    IO.print (renderCheck opts.format ctx r)
    return r.outcome
  if let .error msgs← checkWorkspaceDir ws then
    return ← finish (.failed none msgs)
  let policy ←
    match ← loadPolicy policyPath with
    | .ok p =>
      pure p
    | .error msgs =>
      return ← finish (.failed none msgs)
  let rules := some policy.ruleCount
  let g ←
    match ← loadGraph ws (rootDecls policy.path policy.roots) with
    | .ok g =>
      pure g
    | .error msgs =>
      return ← finish (.failed rules msgs)
  -- Every set is resolved, used by a rule or not, so a renamed module is
  -- caught.
  let sets ←
    match resolveSets g policy with
    | .ok sets =>
      pure sets
    | .error msgs =>
      return ← finish (.failed rules msgs)
  match checkRules g policy sets with
  | .error msgs =>
    finish (.failed rules msgs)
  | .ok vs =>
    finish (.checked g policy vs)

end LeanDeny
