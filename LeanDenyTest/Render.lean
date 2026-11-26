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
def directiveFailures : Array String :=
  Id.run do
    let mut fs := #[]
    for p in [false, true] do
      for m in [false, true] do
        for a in [false, true] do
          let want :=
            (if p then "public " else "") ++ (if m then "meta " else "") ++ "import " ++
              (if a then "all " else "") ++
              "A.B"
          fs :=
            fs ++
              expect s!"directive public={p} meta={m} all={a}"
                (ImportKind.directive { isPublic := p, isMeta := m, isAll := a } `A.B) want
    return fs ++
        expect "escaped module" (ImportKind.directive {} (Name.mkSimple "my-mod")) "import «my-mod»"

/-- Package `name`, requiring `reqs`. -/
def pkg (name : Name) (reqs : Array Name) : PackageInfo :=
  { name, dir := "/ws", configFile := "/ws/lakefile.toml", keywords := #[], remoteUrl? := none,
    requires := reqs, libs := #[], exes := #[], isRoot := false }

/-- The text rendering's `packages` section: several requires join with
`, ` in lakefile order, one require stands alone, none is `nothing`. -/
def packagesFailures : Array String :=
  let g : Graph :=
    { (default : Graph) with
      packages :=
        #[pkg `app #[`core, Name.mkSimple "my-lib", `base], pkg `core #[`base], pkg `base #[]] }
  expect "requiresText: two" (requiresText #[`a, `b]) "requires a, b" ++
    expect "requiresText: none" (requiresText #[]) "requires nothing" ++
    expect "text: packages with several requires"
      (render g { level := .module, nodes := #[], edges := #[] } .text)
      "packages (3):\n  app: requires core, my-lib, base\n  core: requires base\n  \
        base: requires nothing\n\nnodes (0):\n\nedges (0):\n"

def formatFailures : Array String :=
  (#[LeanDeny.Graph.Format.text, .json, .dot].filterMap fun f =>
      if LeanDeny.Graph.Format.parse? (toString f) == some f then none
      else some s!"Format {f} does not round-trip") ++
    (#["", "xml", "JSON", "svg"].filterMap fun s =>
      if (LeanDeny.Graph.Format.parse? s).isNone then none
      else some s!"Format.parse? accepts {repr s}")

/-- The failures of the golden JSON (`tests/fixtures/graph-json-module`,
graph-ws at module level), whose bytes the fixture checks against the
binary: it is canonical `Json.pretty` output of schema version 1, every edge
joins two of its nodes and counts its imports, and the imports add up to
graph-ws's 31 (`LeanDenyTest.Graph.graphWsEdges`). -/
def goldenFailures (golden : String) : Array String :=
  Id.run do
    let j ←
      match Json.parse golden with
      | .ok j =>
        pure j
      | .error e =>
        return #[s!"golden JSON does not parse: {e}"]
    let mut fs := #[]
    unless j.pretty ++ "\n" == golden do
      fs := fs.push "golden JSON is not in Json.pretty's layout"
    unless
      (j.getObjValAs? Nat "schemaVersion").toOption == some jsonSchemaVersion &&
        jsonSchemaVersion == 1 do
      fs := fs.push "golden JSON: schemaVersion is not 1"
    let arr (x : Json) (k : String) : Array Json :=
      ((x.getObjVal? k).bind (·.getArr?)).toOption.getD #[]
    let ids := (arr j "nodes").filterMap fun n => (n.getObjValAs? String "id").toOption
    let mut total := 0
    for e in arr j "edges" do
      let ends := ["from", "to"].map fun k => (e.getObjValAs? String k).toOption
      unless ends.all fun x? => x?.any ids.contains do
        fs := fs.push s!"golden JSON: an edge with an unknown end: {e.compress}"
      let count := (e.getObjValAs? Nat "count").toOption.getD 0
      unless count == (arr e "imports").size do
        fs := fs.push s!"golden JSON: count {count} disagrees with the imports of {e.compress}"
      total := total + count
    unless total == 31 do
      fs := fs.push s!"golden JSON: {total} imports in all, expected 31"
    unless ids.size == 13 && (arr j "edges").size == 22 do
      fs :=
        fs.push
          s!"golden JSON: {ids.size} nodes and {(arr j "edges").size} edges, expected 13 and 22"
    return fs

def run (root : System.FilePath) : IO (Array String) := do
  let golden := root / "tests" / "fixtures" / "graph-json-module" / "expected.stdout"
  let goldenFs ←
    match ← (IO.FS.readFile golden).toBaseIO with
    | .ok s =>
      pure (goldenFailures s)
    | .error e =>
      pure #[s!"reading {golden}: {e}"]
  return dotFailures ++ directiveFailures ++ packagesFailures ++ formatFailures ++ goldenFs

end LeanDenyTest.Render
