import LeanDeny.Cli
import LeanDeny.Exit
import LeanDeny.Load
import LeanDeny.Policy
import LeanDeny.Policy.Resolve

/-!
# `lean-deny check`

Resolve the workspace, load the policy, load the workspace's module graph,
resolve every set of the policy against it (each selector must match), then
check the policy's rules. Cheap failures come first: a bad workspace path or
policy is reported before Lake runs.
-/

open System

namespace LeanDeny

/-- Run `check`. Diagnostics go to stderr; the success line to stdout. -/
def runCheck (opts : CheckOpts) : IO Outcome := do
  let fail (msgs : Array String) : IO Outcome := do
    msgs.forM printError
    return .error
  let ws := opts.workspace
  if let .error msgs← checkWorkspaceDir ws then
    return ← fail msgs
  let policyPath := opts.config?.getD (defaultPolicyPath ws)
  let policy ←
    match ← loadPolicy policyPath with
    | .ok p =>
      pure p
    | .error msgs =>
      return ← fail msgs
  let g ←
    match ← loadGraph ws with
    | .ok g =>
      pure g
    | .error msgs =>
      return ← fail msgs
  -- Every set is resolved, used by a rule or not, so a renamed module is
  -- caught. No rule kinds exist yet.
  if let .error msgs := resolveSets g policy then
    return ← fail msgs
  IO.println "lean-deny: ok (0 rules)"
  return .holds

end LeanDeny
