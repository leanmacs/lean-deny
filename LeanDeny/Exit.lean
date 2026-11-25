/-!
# Outcomes and exit codes

Every command ends in an `Outcome`; only `Outcome.toExitCode` turns it into a
process exit code.
-/

namespace LeanDeny

/-- How a run of lean-deny ended. -/
inductive Outcome where
  /-- Every rule holds (exit 0). -/
  | holds
  /-- At least one rule is broken (exit 1). -/
  | violation
  /-- The command line, the policy or the workspace is bad, or lean-deny
  itself failed (exit 2). -/
  | error
  deriving BEq, Repr, Inhabited

/-- The process exit code of an outcome. -/
def Outcome.toExitCode : Outcome → UInt32
  | .holds => 0
  | .violation => 1
  | .error => 2

end LeanDeny
