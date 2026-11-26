import Lake
import Lake.Load.Workspace
import LeanDeny.Graph.Raw

/-!
# The workspace snapshot, from the in-process Lake API

Load a Lake workspace in-process with `Lake.loadWorkspace`, then fetch each
library's `modules` facet, and each module's and each executable root's
`input` facet (its parsed header plus resolved imports), through
`Workspace.runBuild` with `noBuild := true`. A module no `modules` facet
lists, but that a fetched module imports and that Lake resolves to a
workspace library with an existing file, is fetched too, owned by that
library (`ws.findModule?`, as Lake's `module?`), repeated until no new module
appears (`collectAll`). Nothing is built; the only files
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
  | .ok env =>
    return env
  | .error msg =>
    throw <| IO.userError s!"cannot compute the Lake environment: {msg}"

/-- Load the workspace rooted at `dir` without updating or fetching anything.

Refuses any workspace without a `lake-manifest.json`: with no manifest,
`loadWorkspace` falls back to `updateAndMaterialize`, which may clone, fetch,
and write a manifest. -/
def loadWs (env : Lake.Env) (dir : FilePath) : IO Workspace := do
  let dir ← IO.FS.realPath dir
  unless ← (dir / defaultManifestFile).pathExists do
    throw <|
        IO.userError
          s!"{dir} has no {defaultManifestFile}; \
      run `lake update` there first (lean-deny never resolves dependencies itself)"
  let cfg : LoadConfig :=
    { lakeEnv := env
      wsDir := dir
      updateDeps := false
      reconfigure := false
      updateToolchain := false }
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
    throw <|
        IO.userError <|
        "\n".intercalate <| (msgs.push s!"failed to load the Lake workspace at {dir}").toList

/-- A job that never fails: its failure becomes `.error log`, the failing
job's log. A failed job a fetch does not register with Lake's build monitor
is never reported by it, so its messages would be lost; capturing them lets
`snapshot` report them itself. -/
def capture (job : Job α) : Job (Except Log α) :=
  job.mapResult (sync := true) fun
    | .ok a s => .ok (.ok a) s
    | .error _ s => .ok (.error s.log) { s with log := {} }

/-- Copy a module's fetched input out of Lake. -/
def rawModule (owner : Owner) (mod : Lake.Module) (input : ModuleInput) : RawModule :=
  { name := mod.name
    owner
    file := input.path
    isModule := input.header.isModule
    imports :=
      input.imports.map fun imp =>
        { module := imp.module
          isExported := imp.isExported
          isMeta := imp.isMeta
          importAll := imp.importAll
          resolved? := imp.module?.map fun m => (m.pkg.baseName, m.lib.name) } }

/-- The library Lake's `module?` resolves `mod` to, as an owner. -/
def libOwner (mod : Lake.Module) : Owner :=
  { pkg := mod.pkg.baseName, kind := .lib, target := mod.lib.name }

/-- Fetch the `input` of each of `mods`, each owned by `owner mod`, as one job
that never fails. -/
def fetchRows (owner : Lake.Module → Owner) (mods : Array Lake.Module) :
    FetchM (Job (Array (Except Log RawModule))) := do
  let rows ←
    mods.mapM fun mod => do
        return (capture (← mod.input.fetch)).map (sync := true) (·.map (rawModule (owner mod) mod))
  return Job.collectArray rows

/-- Every module of every library, and the root module of every executable,
of every package of `ws`, with its direct imports, as one job that never
fails. Reads headers only. -/
def collect (ws : Workspace) : FetchM (Job (Array (Except Log RawModule))) := do
  let mut jobs : Array (Job (Array (Except Log RawModule))) := #[]
  for pkg in ws.packages do
    for lib in pkg.leanLibs do
      let owner := { pkg := pkg.baseName, kind := .lib, target := lib.name : Owner }
      let job ←
        (capture (← lib.modules.fetch)).bindM (sync := true) fun
            | .error log => return Job.pure #[.error log]
            | .ok mods => fetchRows (fun _ => owner) mods
      jobs := jobs.push job
    for exe in pkg.leanExes do
      let owner := { pkg := pkg.baseName, kind := .exe, target := exe.name : Owner }
      let mod := exe.root
      jobs :=
        jobs.push <|
          (capture (← mod.input.fetch)).map (sync := true) fun r => #[r.map (rawModule owner mod)]
  return (Job.collectArray jobs).map (sync := true) (·.flatten)

/-- The build configuration of every fetch: `noBuild` makes any accidental
real build fail instead of run. -/
def fetchCfg : BuildConfig :=
  { noBuild := true, verbosity := .quiet }

/-- The modules `rows` import that Lake resolves to a workspace library, that
are not yet in `seen`, and whose file exists, in first-occurrence order, with
`seen` extended by them. Each is `ws.findModule?`'s, the module Lake's
`module?` names. A resolved import with no file is left out, so the graph
builder reports it with its file and line. -/
def unreached (ws : Workspace) (seen : Std.HashSet Name) (rows : Array (Except Log RawModule)) :
    IO (Array Lake.Module × Std.HashSet Name) := do
  let mut seen := seen
  let mut found : Array Lake.Module := #[]
  for r in rows do
    let .ok m := r
      | continue
    for imp in m.imports do
      if imp.resolved?.isNone || seen.contains imp.module then
        continue
      let some mod := ws.findModule? imp.module
        | continue
      unless ← mod.leanFile.pathExists do
        continue
      seen := seen.insert imp.module
      found := found.push mod
  return (found, seen)

/-- `collect`'s rows, plus every module the `modules` facets do not list but
some fetched module imports and Lake resolves to a workspace library with an
existing file, owned by that library, repeated until no new module appears.
It terminates: `seen` only grows, within the workspace's finitely many
modules. -/
def collectAll (ws : Workspace) : IO (Array (Except Log RawModule)) := do
  let mut rows ← ws.runBuild (collect ws) fetchCfg
  let mut seen : Std.HashSet Name := {}
  for r in rows do
    if let .ok m := r then
      seen := seen.insert m.name
  let mut frontier := rows
  repeat
    let (extra, seen') ← unreached ws seen frontier
    seen := seen'
    if extra.isEmpty then
      break
    let new ← ws.runBuild (fetchRows libOwner extra) fetchCfg
    rows := rows ++ new
    frontier := new
  return rows

/-- A package's metadata. -/
def packageInfo (ws : Workspace) (pkg : Package) : PackageInfo :=
  { name := pkg.baseName
    dir := pkg.dir
    configFile := pkg.configFile
    keywords := pkg.keywords
    remoteUrl? := pkg.remoteUrl?
    requires := pkg.depConfigs.map (·.name)
    libs :=
      pkg.leanLibs.map fun lib =>
        { name := lib.name, roots := lib.roots, globs := lib.config.globs.map toString }
    exes := pkg.leanExes.map fun exe => { name := exe.name, root := exe.config.root }
    isRoot := pkg.baseName == ws.root.baseName }

/-- The messages to report for failed fetches, each failure given as its
log's entries, `(isError, message)`, in fetch order.

A failure must never be dropped: each contributes its error-level messages,
or with none whatever it logged, or with an empty log a placeholder. Each
distinct message is kept once, at its first place: a module listed by two
targets is fetched for both, and fails twice with the same log. -/
def failureMessages (failures : Array (Array (Bool × String))) : Array String :=
  Id.run do
    let mut errs : Array String := #[]
    for entries in failures do
      let es := entries.filter (·.1)
      let es := if es.isEmpty then entries else es
      let msgs := if es.isEmpty then #["a Lake fetch failed without a message"] else es.map (·.2)
      for msg in msgs do
        unless errs.contains msg do
          errs := errs.push msg
    return errs

/-- Load `dir` and copy out everything the graph needs, with stage timings.

A module whose header Lake cannot read, or a library whose module list it
cannot compute, fails the whole load with Lake's error messages, one per
line, in module order (`failureMessages`). -/
def snapshot (dir : FilePath) : IO (Snapshot × Timings) := do
  let (env, tEnv) ← timed computeEnv
  let (ws, tLoad) ← timed (loadWs env dir)
  let (results, tFetch) ← timed (collectAll ws)
  let mut failures : Array (Array (Bool × String)) := #[]
  let mut modules : Array RawModule := #[]
  for r in results do
    match r with
    | .ok m =>
      modules := modules.push m
    | .error log =>
      failures :=
        failures.push <|
          log.entries.map fun e => (e.level ≥ .error, e.message.trimAsciiEnd.toString)
  let errs := failureMessages failures
  unless errs.isEmpty do
    throw <| IO.userError <| "\n".intercalate errs.toList
  let snap := { root := ws.root.dir, packages := ws.packages.map (packageInfo ws), modules }
  return (snap, { env := tEnv, load := tLoad, fetch := tFetch })

end LeanDeny.Graph.LakeApi
