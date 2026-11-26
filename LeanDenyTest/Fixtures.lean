import LeanDeny

/-!
# Fixture runner

Each subdirectory of `tests/fixtures/` is one fixture, described by its
`fixture.toml`:

```toml
run  = "direct"   # or "lake"
args = ["check"]  # direct: lean-deny's argv; lake: lake's argv, e.g. ["lint"]
exit = 0
```

`expected.stdout` and `expected.stderr` sit next to it; a missing file means
"expected empty". The command runs with the fixture directory as its working
directory and the inherited environment:

- `direct` runs the real `lean-deny` binary, which sits next to the test
  driver (the driver's `needs` builds it first);
- `lake` runs `$LAKE` (set by `lake test`, so the same toolchain), else `lake`.

The exit code and stdout must match exactly. stderr must match exactly in
`direct` mode; in `lake` mode the expected text need only occur in it, since
Lake's own build progress also goes there. Before comparing, the fixture's
real path becomes `<fixture>`, the repository's becomes `<repo>`, and CRLF
becomes LF.

A `lake` fixture must carry a `lean-toolchain` equal to the root's, so a
toolchain bump cannot leave it on another Lean.
-/

open System LeanDeny

namespace LeanDenyTest.Fixtures

inductive Mode where
  | direct
  | lake
  deriving BEq, Repr

structure Fixture where
  name : String
  /-- The fixture directory (a real path). -/
  dir : FilePath
  mode : Mode
  args : Array String
  exit : UInt32

/-- Parse `fixture.toml`'s entries. -/
def parseSpec (name : String) (dir : FilePath) (entries : Array (String × Toml.Value)) :
    Except String Fixture := do
  let mut mode? := none
  let mut args? := none
  let mut exit? := none
  for (k, v) in entries do
    match k, v with
    | "run", .string "direct" =>
      mode? := some Mode.direct
    | "run", .string "lake" =>
      mode? := some Mode.lake
    | "run", _ =>
      throw "`run` must be \"direct\" or \"lake\""
    | "args", .array xs =>
      let ss ←
        xs.mapM fun
            | .string s => pure s
            | _ => throw "`args` must be an array of strings"
      args? := some ss
    | "args", _ =>
      throw "`args` must be an array of strings"
    | "exit", .integer n =>
      unless 0 ≤ n && n < 256 do
        throw "`exit` must be in 0..255"
      exit? := some n.toNat.toUInt32
    | "exit", _ =>
      throw "`exit` must be an integer"
    | k, _ =>
      throw s!"unknown key `{k}`"
  let some mode := mode? | throw "missing `run`"
  let some args := args? | throw "missing `args`"
  let some exit := exit? | throw "missing `exit`"
  return { name, dir, mode, args, exit }

/-- Read a fixture directory's `fixture.toml`. -/
def load (name : String) (dir : FilePath) : IO (Except String Fixture) := do
  let spec := dir / "fixture.toml"
  unless ← spec.pathExists do
    return .error "no fixture.toml"
  match ← Toml.parse "fixture.toml" (← IO.FS.readFile spec) with
  | .error msgs =>
    return .error ("; ".intercalate msgs.toList)
  | .ok entries =>
    return parseSpec name dir entries

/-- Every fixture directory name under `fixturesDir`, sorted. -/
def discover (fixturesDir : FilePath) : IO (Array String) := do
  let mut names := #[]
  for e in ← fixturesDir.readDir do
    if ← e.path.isDir then
      names := names.push e.fileName
  return names.qsort (· < ·)

/-- Read `path`, or `""` if it does not exist. -/
def readOrEmpty (path : FilePath) : IO String := do
  if ← path.pathExists then
    IO.FS.readFile path
  else
    return ""

def normalise (root dir : FilePath) (s : String) : String :=
  ((s.replace dir.toString "<fixture>").replace root.toString "<repo>").replace "\r\n" "\n"

def hasSubstr (s sub : String) : Bool :=
  sub.isEmpty || (s.splitOn sub).length > 1

/-- Show a stream's text for a mismatch report. -/
def block (s : String) : String :=
  if s.isEmpty then "    (empty)"
  else "\n".intercalate ((s.trimAsciiEnd.toString.splitOn "\n").map ("    | " ++ ·))

/-- Run one fixture; the failures, described. -/
def runOne (root : FilePath) (fx : Fixture) : IO (Array String) := do
  let (cmd, mode) ←
    match fx.mode with
    | .direct =>
      pure (((← IO.appPath).parent.getD "." / "lean-deny").toString, "direct")
    | .lake =>
      pure (((← IO.getEnv "LAKE").getD "lake"), "lake")
  let mut fs := #[]
  if fx.mode == .lake then
    let tc := fx.dir / "lean-toolchain"
    let want := (← IO.FS.readFile (root / "lean-toolchain")).trimAscii.toString
    if !(← tc.pathExists) then
      return #["a lake-mode fixture needs a lean-toolchain"]
    let got := (← IO.FS.readFile tc).trimAscii.toString
    unless got == want do
      return #[s!"lean-toolchain is '{got}', the root's is '{want}'"]
  let out ← IO.Process.output { cmd, args := fx.args, cwd := some fx.dir }
  let stdout := normalise root fx.dir out.stdout
  let stderr := normalise root fx.dir out.stderr
  let wantOut := normalise root fx.dir (← readOrEmpty (fx.dir / "expected.stdout"))
  let wantErr := normalise root fx.dir (← readOrEmpty (fx.dir / "expected.stderr"))
  if out.exitCode != fx.exit then
    fs := fs.push s!"exit code: expected {fx.exit}, got {out.exitCode} ({mode} {fx.args})"
  if stdout != wantOut then
    fs := fs.push s!"stdout differs\n  expected:\n{block wantOut}\n  actual:\n{block stdout}"
  let errOk :=
    match fx.mode with
    | .direct => stderr == wantErr
    | .lake => hasSubstr stderr wantErr
  unless errOk do
    let how := if fx.mode == .direct then "differs" else "does not contain the expected text"
    fs := fs.push s!"stderr {how}\n  expected:\n{block wantErr}\n  actual:\n{block stderr}"
  return fs

/-- Run the fixtures under `<root>/tests/fixtures`, or only those named.
Prints each failure; returns `(fixtures run, fixtures failed)`. -/
def run (root : FilePath) (only : List String) : IO (Nat × Nat) := do
  let fixturesDir := root / "tests" / "fixtures"
  let all ← discover fixturesDir
  let mut failed := 0
  for n in only do
    unless all.contains n do
      IO.eprintln s!"FAIL fixture {n}: no such fixture under tests/fixtures"
      failed := failed + 1
  let names := if only.isEmpty then all else all.filter only.contains
  for name in names do
    let dir ← IO.FS.realPath (fixturesDir / name)
    let fs ←
      match ← load name dir with
      | .error e =>
        pure #[s!"fixture.toml: {e}"]
      | .ok fx =>
        runOne root fx
    if fs.isEmpty then
      IO.println s!"ok   fixture {name}"
    else
      failed := failed + 1
      IO.eprintln s!"FAIL fixture {name}"
      for f in fs do
        IO.eprintln s!"  {f}"
  return (names.size + (only.filter (!all.contains ·)).length, failed)

end LeanDenyTest.Fixtures
