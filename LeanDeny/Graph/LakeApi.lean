import Lake
import Lake.Load.Workspace

/-!
# Module graph from the in-process Lake API (graph-source spike)

Source 1 of the graph-source spike: load a Lake workspace in-process with
`Lake.loadWorkspace`, then fetch each library's `modules` facet and each
module's `input` facet (its parsed header plus resolved imports) through
`Workspace.runBuild` with `noBuild := true`. Nothing is built; the only files
Lake may write are the cached configuration oleans under
`<workspace>/.lake/config/` for packages configured with `lakefile.lean`.

Source 1 was chosen (`docs/decisions/graph-source.md`), and this prototype is
kept as the starting point for phase 3. The record says what phase 3 reuses
from it and what it still lacks: `lean_exe` roots and import positions.
-/

open Lake Lean System

namespace LeanDeny.Graph.LakeApi

/-- One direct import of a module, as Lake resolved it. -/
structure Edge where
  /-- The imported module's name, as written in the header. -/
  target : Name
  /-- The workspace package holding the imported module; `none` for a module
  of the toolchain (or one no workspace library holds). -/
  targetPkg? : Option Name
  /-- The workspace library holding the imported module, if any. -/
  targetLib? : Option Name
  /-- `public import` (always `true` outside the module system). -/
  isExported : Bool
  /-- `meta import`. -/
  isMeta : Bool
  /-- `import all`. -/
  importAll : Bool
  deriving Inhabited, Repr

/-- One module of a workspace library with its direct imports. -/
structure Row where
  pkg : Name
  lib : Name
  module : Name
  /-- The header starts with `module` (the module system is on). -/
  isModule : Bool
  /-- Whether `Init` is imported; `false` exactly when the header says `prelude`. -/
  importsInit : Bool
  edges : Array Edge
  deriving Inhabited, Repr

/-- Package metadata a policy could key on. -/
structure PkgMeta where
  name : Name
  dir : FilePath
  configFile : FilePath
  keywords : Array String
  remoteUrl : String
  requires : Array Name
  libs : Array (Name × Array Name × Array String)
  deriving Inhabited

/-- Stage timings in milliseconds. -/
structure Timings where
  env : Nat := 0
  load : Nat := 0
  fetch : Nat := 0
  deriving Inhabited

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
  match ← (loadWorkspace cfg).toBaseIO with
  | some ws => return ws
  | none => throw <| IO.userError s!"failed to load the Lake workspace at {dir}"

/-- Build a `Row` from a module's fetched input. -/
def mkRow (pkg : Package) (lib : LeanLib) (mod : Lake.Module) (input : ModuleInput) : Row :=
  let edges := input.imports.map fun imp => {
    target := imp.module
    targetPkg? := imp.module?.map (·.pkg.baseName)
    targetLib? := imp.module?.map (·.lib.name)
    isExported := imp.isExported
    isMeta := imp.isMeta
    importAll := imp.importAll
    : Edge }
  { pkg := pkg.baseName, lib := lib.name, module := mod.name
    isModule := input.header.isModule
    importsInit := input.imports.any (·.module == `Init)
    edges }

/-- Every module of every library of every package of `ws`, with its direct
imports, as one job. Reads headers only. -/
def collect (ws : Workspace) : FetchM (Job (Array Row)) := do
  let mut jobs : Array (Job (Array Row)) := #[]
  for pkg in ws.packages do
    for lib in pkg.leanLibs do
      let job ← (← lib.modules.fetch).bindM fun mods => do
        let rows ← mods.mapM fun mod => do
          (← mod.input.fetch).mapM (sync := true) fun input =>
            return mkRow pkg lib mod input
        return Job.collectArray rows
      jobs := jobs.push job
  return (Job.collectArray jobs).map (sync := true) (·.flatten)

/-- The build configuration of every fetch: `noBuild` makes any accidental
real build fail instead of run. -/
def fetchCfg : BuildConfig := { noBuild := true, verbosity := .quiet }

/-- The module graph of a loaded workspace. -/
def graphOf (ws : Workspace) : IO (Array Row) :=
  ws.runBuild (collect ws) fetchCfg

/-- Each library's module list (no headers read). -/
def modulesOf (ws : Workspace) : IO (Array (Package × LeanLib × Array Lake.Module)) :=
  ws.runBuild (cfg := fetchCfg) do
    let mut jobs : Array (Job (Package × LeanLib × Array Lake.Module)) := #[]
    for pkg in ws.packages do
      for lib in pkg.leanLibs do
        jobs := jobs.push <| (← lib.modules.fetch).map (sync := true) fun mods => (pkg, lib, mods)
    return Job.collectArray jobs

/-- Load `dir` and compute its module graph, with stage timings. -/
def graph (dir : FilePath) : IO (Workspace × Array Row × Timings) := do
  let (env, tEnv) ← timed computeEnv
  let (ws, tLoad) ← timed (loadWs env dir)
  let (rows, tFetch) ← timed (graphOf ws)
  return (ws, rows, { env := tEnv, load := tLoad, fetch := tFetch })

/-- Package metadata for every package of the workspace. -/
def pkgMeta (ws : Workspace) : Array PkgMeta :=
  ws.packages.map fun pkg => {
    name := pkg.baseName
    dir := pkg.dir
    configFile := pkg.configFile
    keywords := pkg.keywords
    remoteUrl := pkg.remoteUrl
    requires := pkg.depConfigs.map (·.name)
    libs := pkg.leanLibs.map fun lib =>
      (lib.name, lib.roots, lib.config.globs.map toString)
  }

end LeanDeny.Graph.LakeApi
