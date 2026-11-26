import LeanDeny

/-!
Tests of `LeanDeny.Graph.HeaderParser.parse` on strings: each directive's
module, keywords and line, and the headers it must reject.
-/

open Lean LeanDeny.Graph

namespace LeanDenyTest.Header

/-- A directive as `Name [kw,…] line`. -/
def render (i : HeaderImport) : String :=
  let kws :=
    (if i.kind.isPublic then #["public"] else #[]) ++ (if i.kind.isMeta then #["meta"] else #[]) ++
      (if i.kind.isAll then #["all"] else #[])
  s!"{i.module} [{",".intercalate kws.toList}] {i.line}"

/-- `(case, source, expected)`: the rendered directives, or `none` for a
header that must be rejected. -/
def cases : Array (String × String × Option (Array String)) :=
  #[("no header", "def x : Nat := 1\n", some #[]), ("empty file", "", some #[]),
    ("prelude only", "prelude\n", some #[]),
    ("prelude and an import", "prelude\nimport Init.Core\n", some #["Init.Core [] 2"]),
    ("module and every kind",
      "module\n\nimport A\npublic import B\nmeta import C\nimport all D\npublic meta import E\nmeta import all F\n",
      some
        #["A [] 3", "B [public] 4", "C [meta] 5", "D [all] 6", "E [public,meta] 7",
          "F [meta,all] 8"]),
    ("plain file", "import A\nimport B.C\n", some #["A [] 1", "B.C [] 2"]),
    ("two directives on one line", "import A import B\nimport C\n",
      some #["A [] 1", "B [] 1", "C [] 2"]),
    ("a directive split across lines", "module\n  meta\n  import C\nimport\n  D\n",
      some #["C [meta] 2", "D [] 4"]),
    ("comments, one holding an import",
      "/- a block comment\nimport Bogus -/\nmodule -- the header\n-- a line comment\n\
     public import Fix.B import all Fix.D\n  meta\n  import Fix.C\n-- import Nope\n",
      some #["Fix.B [public] 5", "Fix.D [all] 5", "Fix.C [meta] 6"]),
    ("nested block comment", "/- a /- nested -/ import X -/\nimport A\n", some #["A [] 2"]),
    ("CRLF line endings", "module\r\n\r\npublic import A\r\nimport B\r\n\r\ndef x := 1\r\n",
      some #["A [public] 3", "B [] 4"]),
    ("quoted names", "import «my-pkg».«A B»\nimport C.«d»\n",
      some #["«my-pkg».«A B» [] 1", "C.d [] 2"]),
    ("the header followed by declarations",
      "import A\n\n/-- doc -/\ndef x : Nat := 1\n\nimport B\n", some #["A [] 1"]),
    ("no trailing newline", "import A", some #["A [] 1"]),
    ("a malformed header", "import A\nimport 42\n", none),
    ("public outside the module system", "public import A\n", none)]

def failures (p : HeaderParser) : Array String :=
  Id.run do
    let mut fs := #[]
    for (name, src, want) in cases do
      match p.parse "T.lean" src, want with
      | .ok got, some want =>
        let got := got.map render
        unless got == want do
          fs := fs.push s!"{name}: expected {want}, got {got}"
      | .ok got, none =>
        fs := fs.push s!"{name}: expected an error, got {got.map render}"
      | .error e, some want =>
        fs := fs.push s!"{name}: expected {want}, got error {e}"
      | .error e, none =>
        unless e.startsWith "T.lean:" do
          fs := fs.push s!"{name}: the error should start with the file name: {e}"
    return fs

/-- The error message carries the position. -/
def positionFailures (p : HeaderParser) : Array String :=
  match p.parse "T.lean" "import A\nimport 42\n" with
  | .error e =>
    if e == "T.lean:2:7: expected identifier" then #[]
    else #[s!"malformed header: unexpected message {repr e}"]
  | .ok _ => #["malformed header: expected an error"]

def run : IO (Array String) := do
  let p ← HeaderParser.new
  return failures p ++ positionFailures p

end LeanDenyTest.Header
