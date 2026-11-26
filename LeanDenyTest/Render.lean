import LeanDeny

/-!
Tests of the graph renderings (`LeanDeny.Graph.Render`): DOT quoting, import
directives in Lean syntax, and the format names. The renderings of a real
workspace are covered by the `graph-*` fixtures.
-/

open Lean LeanDeny.Graph

namespace LeanDenyTest.Render

def expect (what got want : String) : Array String :=
  if got == want then #[] else #[s!"{what}: expected {repr want}, got {repr got}"]

def dotFailures : Array String :=
  expect "plain id" (dotQuote "graph-ws/lib/App") "\"graph-ws/lib/App\"" ++
  expect "quote and backslash" (dotQuote "a\"b\\c") "\"a\\\"b\\\\c\"" ++
  expect "guillemets" (dotQuote (Name.mkStr (Name.mkSimple "x-y") "Z").toString) "\"«x-y».Z\"" ++
  expect "empty" (dotQuote "") "\"\""

/-- Every combination of `public`, `meta` and `all`. -/
def directiveFailures : Array String := Id.run do
  let mut fs := #[]
  for p in [false, true] do
    for m in [false, true] do
      for a in [false, true] do
        let want := (if p then "public " else "") ++ (if m then "meta " else "") ++
          "import " ++ (if a then "all " else "") ++ "A.B"
        fs := fs ++ expect s!"directive public={p} meta={m} all={a}"
          (ImportKind.directive { isPublic := p, isMeta := m, isAll := a } `A.B) want
  return fs ++ expect "escaped module" (ImportKind.directive {} (Name.mkSimple "my-mod"))
    "import «my-mod»"

def formatFailures : Array String :=
  (#[LeanDeny.Graph.Format.text, .json, .dot].filterMap fun f =>
    if LeanDeny.Graph.Format.parse? (toString f) == some f then none else some s!"Format {f} does not round-trip") ++
  (#["", "xml", "JSON", "svg"].filterMap fun s =>
    if (LeanDeny.Graph.Format.parse? s).isNone then none else some s!"Format.parse? accepts {repr s}")

def run (_root : System.FilePath) : IO (Array String) :=
  return dotFailures ++ directiveFailures ++ formatFailures

end LeanDenyTest.Render
