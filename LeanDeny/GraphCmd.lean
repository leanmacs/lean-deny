import LeanDeny.Cli
import LeanDeny.Exit
import LeanDeny.Graph.Render
import LeanDeny.Graph.View
import LeanDeny.Load

/-!
# `lean-deny graph`

Load the workspace's module graph, with the policy's declared roots, group
it at the requested level and print it. Only the policy's `[[root]]` tables
are read (`loadDeclaredRoots`), so a policy whose rules are broken cannot stop
anyone from looking at the graph, and one that is not valid TOML only warns
(the graph is then printed without declared roots).
-/

namespace LeanDeny

/-- Run `graph`. Diagnostics go to stderr; the rendering to stdout. -/
def runGraph (opts : GraphOpts) : IO Outcome := do
  let fail (msgs : Array String) : IO Outcome := do
    msgs.forM printError
    return .error
  if let .error msgs← checkWorkspaceDir opts.workspace then
    return ← fail msgs
  let roots ←
    match ← loadDeclaredRoots opts.workspace opts.config? with
    | .ok roots =>
      pure roots
    | .error msgs =>
      return ← fail msgs
  match ← loadGraph opts.workspace roots with
  | .error msgs =>
    fail msgs
  | .ok g =>
    IO.print (Graph.render g (Graph.collapse g opts.level) opts.format)
    return .holds

end LeanDeny
