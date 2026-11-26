import LeanDeny.Graph.Build
import LeanDeny.Graph.Header
import LeanDeny.Graph.LakeApi
import LeanDeny.Graph.Query

/-!
# Loading the module graph

`load` is the one entry point: Lake's snapshot (`LakeApi.snapshot`), then
each module's and each declared root's header parsed for import lines
(`HeaderParser`), then the graph built (`build`). Every failure is an `IO.userError` whose lines are
one diagnostic each.
-/

open Lean System

namespace LeanDeny.Graph

/-- Load the module graph of the workspace at `dir`, with the declared roots
`roots`, building nothing, with stage timings. -/
def load (dir : FilePath) (roots : Array RootDecl := #[]) : IO (Graph × LakeApi.Timings) := do
  let (snap, t) ← LakeApi.snapshot dir roots
  let (headers, tHeaders) ←
    LakeApi.timed do
        let p ← HeaderParser.new
        let mut hs : Std.HashMap Name (Array HeaderImport) := {}
        -- One parse per module, however many targets list it.
        let files :=
          snap.modules.map (fun m => (m.name, m.file)) ++
            snap.roots.map fun r => (r.decl.module, r.file)
        for (name, file) in files do
          if hs.contains name then
            continue
          match p.parse file.toString (← IO.FS.readFile file) with
          | .ok imps =>
            hs := hs.insert name imps
          | .error e =>
            throw <| IO.userError e
        return hs
  let (g?, tBuild) ← LakeApi.timed (IO.lazyPure fun _ => build snap headers)
  match g? with
  | .ok g =>
    return (g,
        { t with
          headers := tHeaders, build := tBuild })
  | .error e =>
    throw <| IO.userError e

end LeanDeny.Graph
