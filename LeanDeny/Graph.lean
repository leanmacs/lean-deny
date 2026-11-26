import LeanDeny.Graph.LakeApi
import LeanDeny.Graph.Header
import LeanDeny.Graph.Build
import LeanDeny.Graph.Query

/-!
# Loading the module graph

`load` is the one entry point: Lake's snapshot (`LakeApi.snapshot`), then
each module's header parsed for import lines (`HeaderParser`), then the
graph built (`build`). Every failure is an `IO.userError` whose lines are
one diagnostic each.
-/

open Lean System

namespace LeanDeny.Graph

/-- Load the module graph of the workspace at `dir`, building nothing, with
stage timings. -/
def load (dir : FilePath) : IO (Graph × LakeApi.Timings) := do
  let (snap, t) ← LakeApi.snapshot dir
  let (headers, tHeaders) ←
    LakeApi.timed do
        let p ← HeaderParser.new
        let mut hs : Std.HashMap Name (Array HeaderImport) := {}
        -- One parse per module, however many targets list it.
        for m in snap.modules do
          if hs.contains m.name then
            continue
          match p.parse m.file.toString (← IO.FS.readFile m.file) with
          | .ok imps =>
            hs := hs.insert m.name imps
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
