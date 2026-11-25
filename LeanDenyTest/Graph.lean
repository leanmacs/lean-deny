import LeanDeny

/-!
Graph checks (formerly the spike's `SpikeTest`): load `tests/fixtures/spike-ws`
through the in-process Lake API and check the graph it resolves, including the
module-system import flags and `prelude`, and the no-manifest guard.
-/

open Lean LeanDeny.Graph.LakeApi

namespace LeanDenyTest.Graph

/-- The failures of the fixture's graph against what is expected. -/
def failures (rows : Array Row) : Array String := Id.run do
  let mut fs : Array String := #[]
  let fixRows := rows.filter fun r => r.pkg == `«spike-ws» && r.lib == `Fix
  unless fixRows.size == 4 && rows.size == 4 do
    fs := fs.push s!"expected 4 modules in lib Fix of package spike-ws, got {rows.map (·.module)}"
  let row? (m : Name) : Option Row := rows.find? (·.module == m)
  let edge? (src dst : Name) : Option Edge :=
    (row? src).bind fun r => r.edges.find? (·.target == dst)
  let expectEdge (src dst : Name) (ok : Edge → Bool) (what : String) : Option String :=
    match edge? src dst with
    | some e => if ok e then none else some s!"{src}→{dst} should be {what}: {repr e}"
    | none => some s!"missing edge {src}→{dst}"
  let expectRow (m : Name) (ok : Row → Bool) (what : String) : Option String :=
    match row? m with
    | some r => if ok r then none else some s!"{m} {what}: {repr r}"
    | none => some s!"missing module {m}"
  let inWs (e : Edge) := e.targetPkg? == some `«spike-ws» && e.targetLib? == some `Fix
  let checks := #[
    expectEdge `Fix.A `Fix.B (fun e => inWs e && e.isExported && !e.isMeta && !e.importAll)
      "a resolved public import",
    expectEdge `Fix.A `Fix.C (fun e => inWs e && e.isMeta && !e.isExported && !e.importAll)
      "a resolved (private) meta import",
    expectEdge `Fix.A `Fix.D (fun e => inWs e && e.importAll && !e.isMeta)
      "a resolved import all",
    expectEdge `Fix.B `Fix.C inWs "a resolved import",
    expectEdge `Fix.B `Init (·.targetPkg?.isNone) "a toolchain import (no workspace package)",
    expectRow `Fix.C (fun r => !r.importsInit && r.edges.isEmpty) "(prelude) should import nothing, not even Init",
    expectRow `Fix.A (·.isModule) "should have isModule = true",
    expectRow `Fix.D (fun r => r.importsInit && !r.isModule) "should import Init and not be a module"
  ]
  for c in checks do
    if let some f := c then fs := fs.push f
  return fs

/-- Whether `s` contains `sub`. -/
def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- The failures of the no-manifest guard in `loadWs`: a copy of the fixture
without its `lake-manifest.json` must be refused before Lake runs, so Lake's
`updateAndMaterialize` fallback never writes a manifest or `.lake/` into it. -/
def noManifestFailures (fixture : System.FilePath) : IO (Array String) :=
  IO.FS.withTempDir fun tmp => do
    IO.FS.createDirAll (tmp / "Fix")
    IO.FS.writeFile (tmp / "lakefile.toml") (← IO.FS.readFile (fixture / "lakefile.toml"))
    for m in ["A", "B", "C", "D"] do
      let f := s!"{m}.lean"
      IO.FS.writeFile (tmp / "Fix" / f) (← IO.FS.readFile (fixture / "Fix" / f))
    let mut fs : Array String := #[]
    match ← (graph tmp).toBaseIO with
    | .ok (_, rows, _) =>
      fs := fs.push s!"loading a workspace without {Lake.defaultManifestFile} should fail, \
        but resolved {rows.size} modules"
    | .error e =>
      let msg := toString e
      unless hasSubstr msg s!"has no {Lake.defaultManifestFile}" do
        fs := fs.push s!"expected the no-manifest guard's error, got: {msg}"
    if ← (tmp / Lake.defaultManifestFile).pathExists then
      fs := fs.push s!"{Lake.defaultManifestFile} was written into the manifest-less workspace"
    if ← (tmp / ".lake").pathExists then
      fs := fs.push ".lake/ was created in the manifest-less workspace"
    return fs

/-- Run the graph checks against `<root>/tests/fixtures/spike-ws`. -/
def run (root : System.FilePath) : IO (Array String) := do
  let dir := root / "tests" / "fixtures" / "spike-ws"
  match ← (graph dir).toBaseIO with
  | .ok (_, rows, _) => return failures rows ++ (← noManifestFailures dir)
  | .error e => return #[s!"loading spike-ws failed: {e}"]

end LeanDenyTest.Graph
