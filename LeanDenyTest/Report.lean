import LeanDenyTest.Deny

/-!
Tests of the check report's renderings (`LeanDeny.Report`) on hand-made
values: GitHub workflow-command escaping, relative paths, splitting a
diagnostic into its location and message, the format names, rule labels and
violation messages, the GitHub and JSON renderings of every kind of result,
and the golden JSON of `tests/fixtures/check-json-deny`.
-/

open Lean LeanDeny LeanDeny.Graph LeanDenyTest.Query

namespace LeanDenyTest.Report

def expect (what got want : String) : Array String :=
  if got == want then #[] else #[s!"{what}: expected {repr want}, got {repr got}"]

def check (what : String) (ok : Bool) : Array String :=
  if ok then #[] else #[what]

/-- `(input, escapeData, escapeProperty)`. -/
def escapeCases : Array (String × String × String) :=
  #[("plain", "plain", "plain"), ("a%b", "a%25b", "a%25b"), ("a\nb", "a%0Ab", "a%0Ab"),
    ("a\rb", "a%0Db", "a%0Db"), ("a:b,c", "a:b,c", "a%3Ab%2Cc"), ("%0A", "%250A", "%250A"),
    ("", "", "")]

def escapeFailures : Array String :=
  escapeCases.flatMap fun (i, d, p) =>
    expect s!"escapeData {repr i}" (escapeData i) d ++
      expect s!"escapeProperty {repr i}" (escapeProperty i) p

def commandFailures : Array String :=
  expect "githubCommand with properties"
      (githubCommand "error" [("file", "a,b.lean"), ("line", "3"), ("title", "x: y")] "m%\n")
      "::error file=a%2Cb.lean,line=3,title=x%3A y::m%25%0A" ++
    expect "githubCommand without properties" (githubCommand "error" [] "m") "::error::m"

def pathFailures : Array String :=
  (#[("/a/b", "/a/b/c.lean", "c.lean"), ("/a/b", "/a/x/y.lean", "../x/y.lean"),
          ("/a/b", "/a/b", "."), ("/a/b", "/q", "../../q"), ("/", "/a/b", "a/b"),
          ("/a/b/", "/a/b//c", "c"), ("/a/b", "rel/x.lean", "rel/x.lean"),
          ("/a/bc", "/a/b/x", "../b/x")].flatMap
      fun (b, p, w) => expect s!"relativePath {repr b} {repr p}" (relativePath b p) w) ++
    (#[("/ws", "./lean-deny.toml", "lean-deny.toml"), ("/ws", "/ws/sub/p.toml", "sub/p.toml"),
          ("/ws", "p.toml", "p.toml")].flatMap
      fun (c, p, w) => expect s!"githubFile {repr c} {repr p}" (githubFile c p) w)

def renderDiagnostic (d : Diagnostic) : String :=
  s!"{d.file?}|{d.pos?.map fun p => (p.line, p.column)}|{d.message}"

def diagnosticFailures : Array String :=
  let unloc (m : String) : Diagnostic := { message := m }
  let cases : Array (String × String × Diagnostic) :=
    #[("p.toml", "p.toml:4:7: m: n",
        { file? := some "p.toml", pos? := some ⟨4, 7⟩, message := "m: n" }),
      ("p.toml", "p.toml: m", { file? := some "p.toml", message := "m" }),
      ("p.toml", "workspace 'x' does not exist", unloc "workspace 'x' does not exist"),
      ("p.toml", "other.toml:1:2: m", unloc "other.toml:1:2: m"),
      ("p.toml", "p.toml:4:x: m", unloc "p.toml:4:x: m"),
      ("p.toml", "p.toml.bak:1:2: m", unloc "p.toml.bak:1:2: m"),
      ("../d/p.toml", "../d/p.toml:21:11: m",
        { file? := some "../d/p.toml", pos? := some ⟨21, 11⟩, message := "m" })]
  cases.flatMap fun (path, msg, want) =>
    expect s!"Diagnostic.ofMessage {repr path} {repr msg}"
      (renderDiagnostic (Diagnostic.ofMessage path msg)) (renderDiagnostic want)

def formatFailures : Array String :=
  (#[CheckFormat.text, .json, .github].filterMap fun f =>
      if CheckFormat.parse? (toString f) == some f then none
      else some s!"CheckFormat {f} does not round-trip") ++
    (#["", "JSON", "dot", "Github"].filterMap fun s =>
      if (CheckFormat.parse? s).isNone then none else some s!"CheckFormat.parse? accepts {repr s}")

def labelFailures : Array String :=
  let v (r? d? : Option String) : Violation :=
    { rule := ⟨.deny, 1⟩, pos? := none, reason? := r?, detail? := d?, chain := #[] }
  expect "message of a reason" (v (some "r") none).message "r" ++
    expect "message of a detail" (v none (some "d")).message "d" ++
    expect "message of both" (v (some "r") (some "d")).message "r: d" ++
    (#[(RuleRef.mk .deny 2, "deny rule 2"), (⟨.allowOnly, 1⟩, "allow-only rule 1"),
          (⟨.layers, 1⟩, "layers")].flatMap
      fun (r, w) => expect s!"label of {repr r}" r.label w) ++
    expect "RuleKind.toString .allowOnly" (RuleKind.toString .allowOnly) "allow-only"

def ctx : ReportCtx :=
  { policyPath := "p.toml", cwd := "/ws" }

/-- The hand-made results: the transitive deny violation `A > Y > Z`, a
violation on an implicit import, one without a position, one of `[layers]`,
one of a target-config rule, one of a require-backed rule; and the policy
they are checked against. -/
structure Fixture where
  g : Graph
  p : Policy
  vs : Array Violation
  implicitV : Violation
  noPos : Violation
  layersV : Violation
  targetV : Violation
  requireV : Violation

def fixture : IO (Except String Fixture) := do
  let ms := #[Deny.m `A #[`X, `Y], Deny.m `X, Deny.m `Y #[`Z], Deny.m `Z]
  let some g := (mkGraph ms).toOption | return .error "graph does not build"
  let .ok p ←
    LeanDenyTest.Policy.load
        (Deny.trule "\"mod:A!\"" "\"mod:Z!\"") | return .error "policy does not load"
  let .ok sets := resolveSets g p | return .error "sets do not resolve"
  let .ok vs := checkRules g p sets | return .error "rules give errors"
  let some implicitE :=
    g.edges.find? fun e =>
      e.implicit && nodeName g e.src == "A" | return .error "no implicit import of A"
  let some v0 := vs[0]? | return .error "no violation"
  return .ok
      { g, p, vs, implicitV := { v0 with chain := #[implicitE] }, noPos := { v0 with pos? := none },
        layersV :=
          { rule := ⟨.layers, 1⟩, pos? := v0.pos?, reason? := some "why",
            detail? := some "a (x) may not import b (y)", chain := v0.chain.extract 0 1 }
        targetV :=
          { rule := ⟨.targetConfig, 1⟩, pos? := v0.pos?, reason? := some "why"
            detail? := some "lean_lib p/L does not load t", chain := #[]
            target? :=
              some
                { pkg := `p, kind := .lib, name := `L, configFile := "/ws/p/lakefile.toml"
                  plugins := #[{ text := "@x/y" }] } }
        requireV :=
          { rule := ⟨.requireBacked, 1⟩, pos? := v0.pos?, reason? := some "why"
            detail? := some "A (package p) imports package q, which p does not require directly"
            chain := v0.chain.extract 0 1
            require? :=
              some
                { pkg := `p, imported := `q, configFile := "/ws/lakefile.toml",
                  requires := #[`r] } } }

def githubFailures (f : Fixture) : Array String :=
  let gh (vs : Array Violation) := renderGithub ctx (.checked f.g f.p vs)
  expect "github: transitive deny" (gh f.vs)
      "::error file=A.lean,line=2,title=lean-deny%3A deny rule 1::deny rule 1 (p.toml:1:0): r%0A  \
          A.lean:2: A imports Y%0A  Y.lean:1: Y imports Z\nlean-deny: 1 violation in 1 of 1 rule\n" ++
    expect "github: implicit step" (gh #[f.implicitV])
      "::error file=A.lean,title=lean-deny%3A deny rule 1::deny rule 1 (p.toml:1:0): r%0A  \
                  A.lean: A imports Init (implicit)\nlean-deny: 1 violation in 1 of 1 rule\n" ++
    check "github: no position"
      ((gh #[f.noPos]).startsWith
        "::error file=A.lean,line=2,title=lean-deny%3A deny rule 1::deny rule 1 (p.toml): r%0A") ++
    check s!"github: layers {repr (gh #[f.layersV])}"
      ((gh #[f.layersV]).startsWith
        "::error file=A.lean,line=2,title=lean-deny%3A layers::layers (p.toml:1:0): why: a (x) \
                may not import b (y)%0A") ++
    expect "github: target-config, on the lakefile with no line" (gh #[f.targetV])
      "::error file=p/lakefile.toml,title=lean-deny%3A target-config rule 1::target-config rule 1 \
          (p.toml:1:0): why: lean_lib p/L does not load t%0A  p/lakefile.toml: lean_lib L\n\
          lean-deny: 1 violation in 1 of 1 rule\n" ++
    expect "text: target-config" ("\n".intercalate (f.targetV.render f.g f.p.path).toList)
      "target-config rule 1 (p.toml:1:0): why: lean_lib p/L does not load t\n  \
          p/lakefile.toml: lean_lib L" ++
    expect "github: require-backed, on the import, the requires line last" (gh #[f.requireV])
      "::error file=A.lean,line=2,title=lean-deny%3A require-backed rule 1::require-backed rule 1 \
          (p.toml:1:0): why: A (package p) imports package q, which p does not require \
          directly%0A  A.lean:2: A imports Y%0A  lakefile.toml: p requires r\n\
          lean-deny: 1 violation in 1 of 1 rule\n" ++
    expect "text: require-backed" ("\n".intercalate (f.requireV.render f.g f.p.path).toList)
      "require-backed rule 1 (p.toml:1:0): why: A (package p) imports package q, which p does not \
          require directly\n  A.lean:2: A imports Y\n  lakefile.toml: p requires r" ++
    expect "text: require-backed, requiring nothing"
      ("\n".intercalate
        ({ f.requireV with
                require? :=
                  f.requireV.require?.map fun (r : RequireGap) =>
                    { r with requires := #[] } }.render
            f.g f.p.path).toList)
      "require-backed rule 1 (p.toml:1:0): why: A (package p) imports package q, which p does not \
          require directly\n  A.lean:2: A imports Y\n  lakefile.toml: p requires nothing" ++
    expect "text: require-backed, several requires joined in order"
      ("\n".intercalate
        ({ f.requireV with
                require? :=
                  f.requireV.require?.map fun (r : RequireGap) =>
                    { r with requires := #[`r, Name.mkSimple "my-lib", `s] } }.render
            f.g f.p.path).toList)
      "require-backed rule 1 (p.toml:1:0): why: A (package p) imports package q, which p does not \
          require directly\n  A.lean:2: A imports Y\n  lakefile.toml: p requires r, my-lib, s" ++
    expect "github: holds" (gh #[]) "lean-deny: ok (1 rule)\n" ++
    expect "github: failed" (renderGithub ctx (.failed (some 2) #["p.toml:4:7: bad", "lake: boom"]))
      "::error file=p.toml,line=4,col=8,title=lean-deny%3A error::bad\n::error \
          title=lean-deny%3A error::lake: boom\nlean-deny: 2 errors\n"

/-- Parse `renderCheck .json ctx r`, checking it round-trips. -/
def parseJson (what : String) (r : CheckResult) : Except String Json := do
  let s := renderCheck .json ctx r
  let j ← (Json.parse s).mapError (s!"{what}: does not parse: " ++ ·)
  unless j.pretty ++ "\n" == s do
    throw s!"{what}: not in Json.pretty's layout"
  return j

def jsonFailures (f : Fixture) : Array String :=
  Id.run do
    let results : Array (String × CheckResult × Bool × String × Json) :=
      #[("holds", .checked f.g f.p #[], true, "holds", toJson (1 : Nat)),
        ("violation", .checked f.g f.p (f.vs ++ #[f.implicitV, f.layersV, f.targetV, f.requireV]),
          false, "violation", toJson (1 : Nat)),
        ("failed", .failed none #["p.toml:4:7: bad", "lake: boom"], false, "error", .null)]
    let mut fs := #[]
    for (what, r, ok, outcome, rules) in results do
      match parseJson what r with
      | .error e =>
        fs := fs.push e
      | .ok j =>
        let get (k : String) : Json := (j.getObjVal? k).toOption.getD .null
        fs :=
          fs ++
            check s!"{what}: schemaVersion"
              (get "schemaVersion" == toJson checkJsonSchemaVersion &&
                checkJsonSchemaVersion == 1) ++
            check s!"{what}: ok" (get "ok" == toJson ok) ++
            check s!"{what}: outcome" (get "outcome" == Json.str outcome) ++
            check s!"{what}: rules" (get "rules" == rules) ++
            check s!"{what}: summary"
              (some (get "summary") ==
                ((renderGithub ctx r).splitOn "\n").dropLast.getLast?.map Json.str) ++
            check s!"{what}: policy" (get "policy" == Json.str "p.toml")
        if what == "violation" then
          let vs := (get "violations").getArr?.toOption.getD #[]
          let field (v : Json) (path : List String) : Json :=
            path.foldl (fun x k => (x.getObjVal? k).toOption.getD .null) v
          let step0 (v : Json) : Json := (((field v ["chain"]).getArrVal? 0).toOption).getD .null
          fs :=
            fs ++ check "violation: five violations" (vs.size == 5) ++
              check "violation: a deny violation's target is null"
                (field vs[0]! ["target"] == .null) ++
              check "violation: a deny or target-config violation's require is null"
                (field vs[0]! ["require"] == .null && field vs[3]! ["require"] == .null) ++
              check "violation: the require-backed require"
                (field vs[4]! ["require"] ==
                  Json.mkObj
                    [("package", Json.str "p"), ("imported", Json.str "q"),
                      ("file", Json.str "lakefile.toml"),
                      ("requires", Json.arr #[Json.str "r"])]) ++
              check "violation: a require-backed chain is the one import, its kind and label"
                ((field vs[4]! ["chain"]).getArr?.toOption.map (·.size) == some 1 &&
                  field vs[4]! ["rule", "kind"] == Json.str "require-backed" &&
                  field vs[4]! ["rule", "label"] == Json.str "require-backed rule 1" &&
                  field vs[4]! ["target"] == .null) ++
              check "violation: the target-config target"
                (field vs[3]! ["target"] ==
                  Json.mkObj
                    [("package", Json.str "p"), ("kind", Json.str "lib"), ("name", Json.str "L"),
                      ("file", Json.str "p/lakefile.toml"),
                      ("plugins", Json.arr #[Json.str "@x/y"])]) ++
              check "violation: a target-config chain is empty and module null"
                (field vs[3]! ["chain"] == Json.arr #[] && field vs[3]! ["module"] == .null) ++
              check "violation: a deny violation's detail is null"
                (field vs[0]! ["detail"] == .null) ++
              check "violation: the implicit step's line is null"
                (field (step0 vs[1]!) ["line"] == .null) ++
              check "violation: the implicit step is implicit"
                (field (step0 vs[1]!) ["implicit"] == toJson true) ++
              check "violation: layers reason"
                (field vs[2]! ["rule", "reason"] == Json.str "why") ++
              check "violation: layers detail"
                (field vs[2]! ["detail"] == Json.str "a (x) may not import b (y)") ++
              check "violation: layers message"
                (field vs[2]! ["message"] == Json.str "why: a (x) may not import b (y)")
        if what == "failed" then
          let want :=
            Json.arr
              #[Json.mkObj
                  [("file", Json.str "p.toml"), ("line", toJson (4 : Nat)),
                    ("column", toJson (7 : Nat)), ("message", Json.str "bad")],
                Json.mkObj
                  [("file", .null), ("line", .null), ("column", .null),
                    ("message", Json.str "lake: boom")]]
          fs := fs ++ check "failed: errors" (get "errors" == want)
    return fs ++
        check "text of a failed result is empty" (renderCheck .text ctx (.failed none #["x"]) == "")

/-- The keys of a JSON object. -/
def keys (j : Json) : Array String :=
  match j with
  | .obj kvs => kvs.foldl (fun acc k _ => acc.push k) #[]
  | _ => #[]

/-- The failures of the golden JSON (`tests/fixtures/check-json-deny`), whose
bytes the fixture checks against the binary; `importKeys` is the key set of
a graph JSON Import object (from `graph-json-module`). -/
def goldenFailures (golden : String) (importKeys : Array String) : Array String :=
  Id.run do
    let j ←
      match Json.parse golden with
      | .ok j =>
        pure j
      | .error e =>
        return #[s!"golden check JSON does not parse: {e}"]
    let get (x : Json) (k : String) : Json := (x.getObjVal? k).toOption.getD .null
    let arr (x : Json) (k : String) : Array Json := (get x k).getArr?.toOption.getD #[]
    let mut fs := #[]
    unless j.pretty ++ "\n" == golden do
      fs := fs.push "golden check JSON is not in Json.pretty's layout"
    unless get j "schemaVersion" == toJson (1 : Nat) do
      fs := fs.push "golden check JSON: schemaVersion is not 1"
    unless get j "outcome" == Json.str "violation" do
      fs := fs.push "golden check JSON: outcome is not violation"
    unless (arr j "violations").size == 2 && get j "brokenRules" == toJson (2 : Nat) do
      fs := fs.push "golden check JSON: expected 2 violations of 2 rules"
    unless get j "summary" == Json.str (summaryLine 2 2 2) do
      fs := fs.push "golden check JSON: summary"
    if importKeys.isEmpty then
      fs := fs.push "graph JSON golden: no import object"
    for v in arr j "violations" do
      let chain := arr v "chain"
      if chain.isEmpty then
        fs := fs.push s!"golden check JSON: an empty chain in {v.compress}"
      for i in [0:chain.size - 1] do
        unless get chain[i]! "imported" == get chain[i + 1]! "importer" do
          fs := fs.push s!"golden check JSON: a chain that is not consecutive: {v.compress}"
      unless
        [Json.str "deny", .str "allow-only", .str "layers"].contains (get (get v "rule") "kind") do
        fs := fs.push s!"golden check JSON: an unknown rule kind in {v.compress}"
      for s in chain do
        unless (keys s).qsort (· < ·) == importKeys.qsort (· < ·) do
          fs :=
            fs.push
              s!"golden check JSON: a chain step without graph JSON's Import keys: {s.compress}"
    return fs

/-- The keys of the first import object in the graph JSON `src`. -/
def importKeysOf (src : String) : Array String :=
  match Json.parse src with
  | .ok j =>
    let edges := ((j.getObjVal? "edges").bind (·.getArr?)).toOption.getD #[]
    let imp? := edges[0]? >>= fun e => (((e.getObjVal? "imports").bind (·.getArrVal? 0)).toOption)
    (imp?.map keys).getD #[]
  | .error _ => #[]

def run (root : System.FilePath) : IO (Array String) := do
  let fixtures := root / "tests" / "fixtures"
  let read (p : System.FilePath) : IO (Except String String) := do
    match ← (IO.FS.readFile p).toBaseIO with
    | .ok s =>
      return .ok s
    | .error e =>
      return .error s!"reading {p}: {e}"
  let goldenFs ←
    match ← read (fixtures / "check-json-deny" / "expected.stdout"),
      ← read (fixtures / "graph-json-module" / "expected.stdout") with
    | .ok golden, .ok graph =>
      pure (goldenFailures golden (importKeysOf graph))
    | .error e, _ | _, .error e =>
      pure #[e]
  let fixtureFs ←
    match ← fixture with
    | .ok f =>
      pure (githubFailures f ++ jsonFailures f)
    | .error e =>
      pure #[s!"fixture: {e}"]
  return escapeFailures ++ commandFailures ++ pathFailures ++ diagnosticFailures ++
      formatFailures ++
      labelFailures ++
      fixtureFs ++
      goldenFs

end LeanDenyTest.Report
