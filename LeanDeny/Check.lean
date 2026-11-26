import LeanDeny.Cli
import LeanDeny.Exit
import LeanDeny.Policy
import LeanDeny.Load

/-!
# `lean-deny check`

Resolve the workspace, load the policy, load the workspace's module graph,
then check the policy's rules against it. Cheap failures come first: a bad
workspace path or policy is reported before Lake runs.
-/

open System

namespace LeanDeny

/-- Run `check`. Diagnostics go to stderr; the success line to stdout. -/
def runCheck (opts : CheckOpts) : IO Outcome := do
  let fail (msgs : Array String) : IO Outcome := do
    msgs.forM printError
    return .error
  let ws := opts.workspace
  if let .error msgs ← checkWorkspaceDir ws then return ← fail msgs
  let policyPath := opts.config?.getD (defaultPolicyPath ws)
  let _policy ← match ← loadPolicy policyPath with
    | .ok p => pure p
    | .error msgs => return ← fail msgs
  -- Load the graph for real, so a workspace that cannot be loaded fails now.
  -- No rule kinds exist yet, so the graph is not used.
  if let .error msgs ← loadGraph ws then return ← fail msgs
  IO.println "lean-deny: ok (0 rules)"
  return .holds

end LeanDeny
