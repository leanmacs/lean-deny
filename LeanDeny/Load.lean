import LeanDeny.Graph

/-!
# Loading a workspace

What every command that reads a workspace shares: the cheap checks on its
path, loading its module graph, and printing diagnostics. Each failure is a
list of diagnostics, one `lean-deny: error:` line each.
-/

open System

namespace LeanDeny

/-- Print one diagnostic to stderr. -/
def printError (msg : String) : IO Unit :=
  IO.eprintln s!"lean-deny: error: {msg}"

/-- Fail unless `ws` exists and is a directory. -/
def checkWorkspaceDir (ws : FilePath) : IO (Except (Array String) Unit) := do
  unless ← ws.pathExists do
    return .error #[s!"workspace '{ws}' does not exist"]
  unless ← ws.isDir do
    return .error #[s!"workspace '{ws}' is not a directory"]
  return .ok ()

/-- Load the module graph of the workspace at `ws` (already checked by
`checkWorkspaceDir`). A load error may carry several of Lake's messages, one
per line; each is its own diagnostic. -/
def loadGraph (ws : FilePath) : IO (Except (Array String) Graph.Graph) := do
  try
    let (g, _) ← Graph.load ws
    return .ok g
  catch e =>
    return .error ((toString e).splitOn "\n").toArray

end LeanDeny
