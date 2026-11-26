import LeanDeny.Cli
import LeanDeny.Exit
import LeanDeny.Load
import LeanDeny.Policy
import LeanDeny.Policy.Resolve
import LeanDeny.Rules.Deny

/-!
# `lean-deny check`

Resolve the workspace, load the policy, load the workspace's module graph,
resolve every set of the policy against it (each selector must match), then
check the policy's rules. Cheap failures come first: a bad workspace path or
policy is reported before Lake runs.

The report goes to stdout: `lean-deny: ok (N rules)` when every rule holds
(exit 0), or one block per violation and a summary line (exit 1). Errors go
to stderr (exit 2), and a policy with any error reports no violation.
-/

open System

namespace LeanDeny

/-- The line `check` prints when every rule holds: "lean-deny: ok (2 rules)". -/
def okLine (rules : Nat) : String :=
  s!"lean-deny: ok ({Graph.plural rules "rule"})"

/-- The last line of a report with violations:
"lean-deny: 3 violations in 1 of 2 rules". -/
def summaryLine (violations broken rules : Nat) : String :=
  s!"lean-deny: {Graph.plural violations "violation"} in {broken} of {Graph.plural rules "rule"}"

/-- What `check` prints on stdout for the rules' result `vs`: the ok line, or
every violation's block followed by the summary line. -/
def checkReport (g : Graph.Graph) (p : Policy) (vs : Array DenyViolation) : Array String :=
  if vs.isEmpty then #[okLine p.ruleCount]
  else
    let broken := (vs.map (·.rule.index)).toList.eraseDups.length
    vs.flatMap (·.render g p.path) |>.push (summaryLine vs.size broken p.ruleCount)

/-- Run `check`. Diagnostics go to stderr; the report to stdout. -/
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
  -- caught.
  let sets ←
    match resolveSets g policy with
    | .ok sets =>
      pure sets
    | .error msgs =>
      return ← fail msgs
  match checkDeny g policy sets with
  | .error msgs =>
    fail msgs
  | .ok vs =>
    (checkReport g policy vs).forM IO.println
    return if vs.isEmpty then .holds else .violation

end LeanDeny
