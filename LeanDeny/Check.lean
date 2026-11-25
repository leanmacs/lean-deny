import LeanDeny.Cli
import LeanDeny.Exit
import LeanDeny.Policy
import LeanDeny.Graph.LakeApi

/-!
# `lean-deny check`

Resolve the workspace, load the policy, load the workspace's module graph,
then check the policy's rules against it. Cheap failures come first: a bad
workspace path or policy is reported before Lake runs.
-/

open System

namespace LeanDeny

/-- Print one diagnostic to stderr. -/
def printError (msg : String) : IO Unit :=
  IO.eprintln s!"lean-deny: error: {msg}"

/-- Run `check`. Diagnostics go to stderr; the success line to stdout. -/
def runCheck (opts : CheckOpts) : IO Outcome := do
  let fail (msgs : Array String) : IO Outcome := do
    msgs.forM printError
    return .error
  let ws := opts.workspace
  unless ← ws.pathExists do
    return ← fail #[s!"workspace '{ws}' does not exist"]
  unless ← ws.isDir do
    return ← fail #[s!"workspace '{ws}' is not a directory"]
  let policyPath := opts.config?.getD (defaultPolicyPath ws)
  let _policy ← match ← loadPolicy policyPath with
    | .ok p => pure p
    | .error msgs => return ← fail msgs
  -- Load the graph for real, so an unloadable workspace fails now. No rule
  -- kinds exist yet, so the snapshot is not used. A load error may carry
  -- several of Lake's messages, one per line; each is its own diagnostic.
  try
    let _snap ← Graph.LakeApi.snapshot ws
  catch e =>
    return ← fail ((toString e).splitOn "\n").toArray
  IO.println "lean-deny: ok (0 rules)"
  return .holds

end LeanDeny
