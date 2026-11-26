import LeanDeny.Cli
import LeanDeny.Exit
import LeanDeny.Load
import LeanDeny.Policy
import LeanDeny.Policy.Resolve
import LeanDeny.Rules.AllowOnly
import LeanDeny.Rules.Deny

/-!
# `lean-deny check`

Resolve the workspace, load the policy, load the workspace's module graph,
resolve every set of the policy against it (each selector must match), then
check the policy's rules: deny rules (`LeanDeny.Rules.Deny`), then
allow-only rules (`LeanDeny.Rules.AllowOnly`). Cheap failures come first: a bad workspace path or
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

/-- Every rule of `p`, with the policy's sets resolved in `sets`: deny rules,
then allow-only rules. Every error of both kinds (deny's first), or, when
there is none, every violation (deny's first). -/
def checkRules (g : Graph.Graph) (p : Policy) (sets : Std.HashMap String (Array Graph.NodeId)) :
    Except (Array String) (Array Violation) :=
  match checkDeny g p sets, checkAllowOnly g p sets with
  | .ok dvs, .ok avs => .ok (dvs ++ avs)
  | .error des, .error aes => .error (des ++ aes)
  | .error des, .ok _ => .error des
  | .ok _, .error aes => .error aes

/-- What `check` prints on stdout for the rules' result `vs`: the ok line, or
every violation's block followed by the summary line. -/
def checkReport (g : Graph.Graph) (p : Policy) (vs : Array Violation) : Array String :=
  if vs.isEmpty then #[okLine p.ruleCount]
  else
    let broken := (vs.map (·.label)).toList.eraseDups.length
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
  match checkRules g policy sets with
  | .error msgs =>
    fail msgs
  | .ok vs =>
    (checkReport g policy vs).forM IO.println
    return if vs.isEmpty then .holds else .violation

end LeanDeny
