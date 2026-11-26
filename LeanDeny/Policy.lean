import LeanDeny.Lake.Toml

/-!
# Policy file

`lean-deny.toml`. No rule kinds exist yet, so the only valid policy is an
empty one: an empty file, or one with only comments and whitespace. Any key is
rejected rather than ignored, so a policy full of rules cannot pass while
checking nothing.
-/

open System

namespace LeanDeny

/-- A parsed policy. Empty until rule kinds exist (roadmap `policy-rules`). -/
structure Policy where
  deriving Repr, Inhabited

/-- The default policy file of a workspace. -/
def defaultPolicyPath (workspace : FilePath) : FilePath :=
  if workspace.toString == "." then "lean-deny.toml" else workspace / "lean-deny.toml"

/-- Load the policy at `path`, or the error messages (without any prefix). -/
def loadPolicy (path : FilePath) : IO (Except (Array String) Policy) := do
  unless ← path.pathExists do
    return .error #[s!"no policy file '{path}'"]
  if ← path.isDir then
    return .error #[s!"policy file '{path}' is a directory"]
  let input ←
    try
      IO.FS.readFile path
    catch e =>
      return .error #[s!"cannot read policy file '{path}': {e}"]
  match ← Toml.parse path.toString input with
  | .error msgs =>
    return .error msgs
  | .ok entries =>
    if entries.isEmpty then
      return .ok {}
    return .error <|
        entries.map fun (k, _) => s!"{path}: unknown key '{k}' (this version supports no rules yet)"

end LeanDeny
