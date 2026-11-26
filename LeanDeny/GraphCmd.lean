import LeanDeny.Cli
import LeanDeny.Exit
import LeanDeny.Load
import LeanDeny.Graph.View
import LeanDeny.Graph.Render

/-!
# `lean-deny graph`

Load the workspace's module graph, group it at the requested level and
print it. The policy is not read, so a bad `lean-deny.toml` cannot stop
anyone from looking at the graph.
-/

namespace LeanDeny

/-- Run `graph`. Diagnostics go to stderr; the rendering to stdout. -/
def runGraph (opts : GraphOpts) : IO Outcome := do
  let fail (msgs : Array String) : IO Outcome := do
    msgs.forM printError
    return .error
  if let .error msgs ← checkWorkspaceDir opts.workspace then return ← fail msgs
  match ← loadGraph opts.workspace with
  | .error msgs => fail msgs
  | .ok g =>
    IO.print (Graph.render g (Graph.collapse g opts.level) opts.format)
    return .holds

end LeanDeny
