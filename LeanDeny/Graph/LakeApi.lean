import Lake
import Lake.Load.Workspace
import LeanDeny.Graph.Raw

/-!
# The workspace snapshot, from the in-process Lake API

Load a Lake workspace in-process with `Lake.loadWorkspace`, then fetch each
library's `modules` facet, and each module's and each executable root's
`input` facet (its parsed header plus resolved imports), through
`Workspace.runBuild` with `noBuild := true`. Nothing is built; the only files
Lake may write are the cached configuration oleans under
`<workspace>/.lake/config/` for packages configured with `lakefile.lean`.

This file is lean-deny's only use of Lake's build API
(`docs/decisions/graph-source.md`). It hands over a plain
`LeanDeny.Graph.Snapshot`; everything after it is Lake-free.
-/

open Lake Lean System

namespace LeanDeny.Graph.LakeApi

/-- Stage timings in milliseconds. `headers` and `build` are filled by
`LeanDeny.Graph.load`, after the snapshot. -/
structure Timings where
  env : Nat := 0
  load : Nat := 0
  fetch : Nat := 0
  headers : Nat := 0
  build : Nat := 0
  deriving Inhabited, Repr

/-- Elapsed milliseconds of `x`, alongside its result. -/
def timed (x : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let a ← x
  return (a, (← IO.monoMsNow) - t0)

/-! Errors are thrown as `IO.userError` with bare messages; the CLI adds the
single `lean-deny: error: ` prefix when it prints them. -/

/-- Compute the Lake environment from the installs Lake itself would find.

`findInstall?` locates Lake from the running executable's path or `LAKE_HOME`;
a standalone binary has neither (only `lake exe`/`lake test` set `LAKE_HOME`),
so fall back to the Lake that ships co-located with the detected Lean. -/
def computeEnv : IO Lake.Env := do
  let (elan?, lean?, lake?) ← findInstall?
  let some lean := lean?
    | throw <| IO.userError "no Lean installation found (is `lean` on PATH or LEAN_SYSROOT set?)"
  let lake := lake?.getD (LakeInstall.ofLean lean)
  match ← (Env.compute lake lean elan?).toBaseIO with
  | .ok env => return env
  | .error msg => throw <| IO.userError s!"cannot compute the Lake environment: {msg}"

/-- Load the workspace rooted at `dir` without updating or fetching anything.

Refuses any workspace without a `lake-manifest.json`: with no manifest,
`loadWorkspace` falls back to `updateAndMaterialize`, which may clone, fetch,
and write a manifest. -/
def loadWs (env : Lake.Env) (dir : FilePath) : IO Workspace := do
  let dir ← IO.FS.realPath dir
  unless ← (dir / defaultManifestFile).pathExists do
    throw <| IO.userError s!"{dir} has no {defaultManifestFile}; \
      run `lake update` there first (lean-deny never resolves dependencies itself)"
  let cfg : LoadConfig := {
    lakeEnv := env
    wsDir := dir
    updateDeps := false
    reconfigure := false
    updateToolchain := false
  }
  -- Capture Lake's log rather than let `toBaseIO` print it, so its messages
  -- come out as lean-deny diagnostics.
  let (ws?, log) ← (loadWorkspace cfg).captureLog
  match ws? with
  | some ws =>
    for e in log.entries do
      if e.level ≥ .warning then
        IO.eprintln s!"lean-deny: warning: {e.message.trimAsciiEnd}"
    return ws
  | none =>
    let msgs := log.entries.filter (·.level ≥ .error) |>.map (·.message.trimAsciiEnd.toString)
    throw <| IO.userError <| "\n".intercalate <|
      (msgs.push s!"failed to load the Lake workspace at {dir}").toList

/-- A job that never fails: its failure becomes `.error log`, the failing
job's log. A failed job a fetch does not register with Lake's build monitor
is never reported by it, so its messages would be lost; capturing them lets
`snapshot` report them itself. -/
def capture (job : Job α) : Job (Except Log α) :=
  job.mapResult (sync := true) fun
    | .ok a s => .ok (.ok a) s
    | .error _ s => .ok (.error s.log) { s with log := {} }

/-- Copy a module's fetched input out of Lake. -/
def rawModule (owner : Owner) (mod : Lake.Module) (input : ModuleInput) : RawModule := {
  name := mod.name
  owner
  file := input.path
  isModule := input.header.isModule
  imports := input.imports.map fun imp => {
    module := imp.module
    isExported := imp.isExported
    isMeta := imp.isMeta
    importAll := imp.importAll
    resolved? := imp.module?.map fun m => (m.pkg.baseName, m.lib.name)
  }
}

/-- Every module of every library, and the root module of every executable,
of every package of `ws`, with its direct imports, as one job that never
fails. Reads headers only. -/
def collect (ws : Workspace) : FetchM (Job (Array (Except Log RawModule))) := do
  let mut jobs : Array (Job (Array (Except Log RawModule))) := #[]
  for pkg in ws.packages do
    for lib in pkg.leanLibs do
      let owner := { pkg := pkg.baseName, kind := .lib, target := lib.name : Owner }
      let job ← (capture (← lib.modules.fetch)).bindM (sync := true) fun
        | .error log => return Job.pure #[.error log]
        | .ok mods => do
          let rows ← mods.mapM fun mod => do
            return (capture (← mod.input.fetch)).map (sync := true) (·.map (rawModule owner mod))
          return Job.collectArray rows
      jobs := jobs.push job
    for exe in pkg.leanExes do
      let owner := { pkg := pkg.baseName, kind := .exe, target := exe.name : Owner }
      let mod := exe.root
      jobs := jobs.push <|
        (capture (← mod.input.fetch)).map (sync := true) fun r => #[r.map (rawModule owner mod)]
  return (Job.collectArray jobs).map (sync := true) (·.flatten)

/-- The build configuration of every fetch: `noBuild` makes any accidental
real build fail instead of run. -/
def fetchCfg : BuildConfig := { noBuild := true, verbosity := .quiet }

/-- A package's metadata. -/
def packageInfo (ws : Workspace) (pkg : Package) : PackageInfo := {
  name := pkg.baseName
  dir := pkg.dir
  configFile := pkg.configFile
  keywords := pkg.keywords
  remoteUrl? := pkg.remoteUrl?
  requires := pkg.depConfigs.map (·.name)
  libs := pkg.leanLibs.map fun lib =>
    { name := lib.name, roots := lib.roots, globs := lib.config.globs.map toString }
  exes := pkg.leanExes.map fun exe => { name := exe.name, root := exe.config.root }
  isRoot := pkg.baseName == ws.root.baseName
}

/-- Load `dir` and copy out everything the graph needs, with stage timings.

A module whose header Lake cannot read, or a library whose module list it
cannot compute, fails the whole load with Lake's error messages, one per
line, in module order. -/
def snapshot (dir : FilePath) : IO (Snapshot × Timings) := do
  let (env, tEnv) ← timed computeEnv
  let (ws, tLoad) ← timed (loadWs env dir)
  let (results, tFetch) ← timed (ws.runBuild (collect ws) fetchCfg)
  let mut errs : Array String := #[]
  let mut modules : Array RawModule := #[]
  for r in results do
    match r with
    | .ok m => modules := modules.push m
    | .error log =>
      -- A failure must never be dropped: with no error-level entry, report
      -- whatever Lake logged, or that it logged nothing.
      let es := log.entries.filter (·.level ≥ .error)
      let es := if es.isEmpty then log.entries else es
      let msgs := if es.isEmpty then #["a Lake fetch failed without a message"]
        else es.map (·.message.trimAsciiEnd.toString)
      for msg in msgs do
        unless errs.contains msg do errs := errs.push msg
  unless errs.isEmpty do
    throw <| IO.userError <| "\n".intercalate errs.toList
  let snap := { root := ws.root.dir, packages := ws.packages.map (packageInfo ws), modules }
  return (snap, { env := tEnv, load := tLoad, fetch := tFetch })

end LeanDeny.Graph.LakeApi
