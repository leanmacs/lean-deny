import LeanDenyTest.Fixtures

/-!
Tests of the fixture runner's own checks (`LeanDenyTest.Fixtures`): spec
parsing, the text helpers, and the failures `load` and `runOne` must report.
Every committed fixture takes the passing path, so without these a runner
that always passed would go unnoticed.
-/

open System LeanDeny LeanDenyTest.Fixtures

namespace LeanDenyTest.Harness

/-- What a `parseSpec` case expects: the parsed fields, or this error. -/
abbrev Expect :=
  Except String (Mode × Array String × UInt32)

def good : Array (String × Toml.Value) :=
  #[("run", .string "direct"), ("args", .array #[.string "check"]), ("exit", .integer 0)]

def specCases : Array (Array (String × Toml.Value) × Expect) :=
  #[(good, .ok (.direct, #["check"], 0)),
    (#[("run", .string "lake"), ("args", .array #[]), ("exit", .integer 255)],
      .ok (.lake, #[], 255)),
    (good.filter (·.1 != "run"), .error "missing `run`"),
    (good.filter (·.1 != "args"), .error "missing `args`"),
    (good.filter (·.1 != "exit"), .error "missing `exit`"),
    (good.push ("frob", .boolean true), .error "unknown key `frob`"),
    (#[("run", .string "shell")], .error "`run` must be \"direct\" or \"lake\""),
    (#[("run", .integer 1)], .error "`run` must be \"direct\" or \"lake\""),
    (#[("args", .string "check")], .error "`args` must be an array of strings"),
    (#[("args", .array #[.integer 1])], .error "`args` must be an array of strings"),
    (#[("exit", .string "0")], .error "`exit` must be an integer"),
    (#[("exit", .integer 256)], .error "`exit` must be in 0..255"),
    (#[("exit", .integer (-1))], .error "`exit` must be in 0..255")]

def renderSpec : Except String Fixture → String
  | .ok fx => s!"ok {repr fx.mode} {fx.args} {fx.exit}"
  | .error e => s!"error {repr e}"

def renderExpect : Expect → String
  | .ok (m, a, e) => s!"ok {repr m} {a} {e}"
  | .error e => s!"error {repr e}"

def specFailures : Array String :=
  Id.run do
    let mut fs := #[]
    for (entries, want) in specCases do
      let got := parseSpec "t" "." entries
      let same :=
        match got, want with
        | .ok fx, .ok (m, a, e) => fx.mode == m && fx.args == a && fx.exit == e
        | .error e, .error m => e == m
        | _, _ => false
      unless same do
        let keys := entries.map (·.1)
        fs := fs.push s!"parseSpec {keys}: expected {renderExpect want}, got {renderSpec got}"
    return fs

def substrCases : Array (String × String × Bool) :=
  #[("abc", "", true), ("", "", true), ("abc", "b", true), ("abc", "abc", true),
    ("abc", "x", false), ("", "x", false), ("ab", "abc", false)]

/-- `(root, dir, input, expected)`; the fixture lies inside the repository,
so its path must be replaced before the repository's. -/
def normaliseCases : Array (String × String × String × String) :=
  #[("/r/repo", "/r/repo/tests/fixtures/x", "/r/repo/tests/fixtures/x/a and /r/repo/b",
      "<fixture>/a and <repo>/b"),
    ("/r/repo", "/r/repo/tests/fixtures/x", "one\r\ntwo\r\n", "one\ntwo\n"),
    ("/r/repo", "/r/repo/tests/fixtures/x", "plain\n", "plain\n")]

def pureFailures : Array String :=
  Id.run do
    let mut fs := specFailures
    for (s, sub, want) in substrCases do
      let got := hasSubstr s sub
      unless got == want do
        fs := fs.push s!"hasSubstr {repr s} {repr sub}: expected {want}, got {got}"
    for (root, dir, s, want) in normaliseCases do
      let got := normalise root dir s
      unless got == want do
        fs := fs.push s!"normalise {repr s}: expected {repr want}, got {repr got}"
    return fs

/-- A lake-mode fixture in `dir`, never actually run: each case below must
fail before `runOne` starts a process. -/
def lakeFixture (dir : FilePath) : Fixture :=
  { name := "t", dir, mode := .lake, args := #["--version"], exit := 0 }

/-- `load` and `runOne` on temporary fixtures; the failures, described. -/
def ioFailures (root : FilePath) : IO (Array String) := do
  let want := (← IO.FS.readFile (root / "lean-toolchain")).trimAscii.toString
  IO.FS.withTempDir fun tmp => do
      let mut fs := #[]
      -- No fixture.toml.
      match ← load "t" tmp with
      | .error "no fixture.toml" =>
        pure ()
      | .error e =>
        fs := fs.push s!"load without fixture.toml: wrong error {repr e}"
      | .ok _ =>
        fs := fs.push "load without fixture.toml: succeeded"
      -- A lake fixture with no lean-toolchain.
      let got ← runOne root (lakeFixture tmp)
      unless got == #["a lake-mode fixture needs a lean-toolchain"] do
        fs := fs.push s!"runOne without lean-toolchain: got {got}"
      -- A lake fixture on another toolchain.
      IO.FS.writeFile (tmp / "lean-toolchain") "leanprover/lean4:v0.0.0\n"
      let got ← runOne root (lakeFixture tmp)
      unless got == #[s!"lean-toolchain is 'leanprover/lean4:v0.0.0', the root's is '{want}'"] do
        fs := fs.push s!"runOne with a mismatched lean-toolchain: got {got}"
      return fs

/-- Every harness check; the failures, described. -/
def run (root : FilePath) : IO (Array String) :=
  return pureFailures ++ (← ioFailures root)

end LeanDenyTest.Harness
