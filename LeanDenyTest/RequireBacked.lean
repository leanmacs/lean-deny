import LeanDenyTest.Deny

/-!
Tests of `[[require-backed]]` rules (`LeanDeny.Rules.RequireBacked`) on
hand-written graphs and package metadata, from the policy's TOML text to
what `check` prints: a direct require backs an import, a transitive one does
not; imports within a package, of external modules and to or from declared
roots are not judged, nor are an unmatched package's; one violation per
(importer, imported) pair, in display order; `meta` and `public` imports
count; a package Lake did not load requires nothing; the errors a rule can
give and their order; and loading.
-/

open Lean LeanDeny LeanDeny.Graph LeanDenyTest.Query

namespace LeanDenyTest.RequireBacked

open LeanDenyTest.Deny (outcome)

/-- Module `n` of package `pkg` (library `L`), with plain imports
`imports`. -/
def m (n pkg : Name) (imports : Array Name := #[]) : M :=
  { name := n, pkg, imports := imports.map plain }

/-- Package `name`, requiring `requires`, its lakefile at
`/ws/<name>/lakefile.toml`. -/
def pkg (name : Name) (reqs : Array Name := #[]) : PackageInfo :=
  { name, dir := s!"/ws/{name}", configFile := s!"/ws/{name}/lakefile.toml", keywords := #[]
    remoteUrl? := none, requires := reqs, libs := #[], exes := #[], isRoot := false }

/-- The packages: `a` requires `p` directly, `p` requires `b`, `b` and `x`
require nothing. -/
def packages : Array PackageInfo :=
  #[pkg `a #[`p], pkg `p #[`b], pkg `b, pkg `x]

/-- A require-backed table (lines: header, `packages`, `reason = "r"`),
`packages` given as a TOML value. -/
def rule (packagesV : String) : String :=
  s!"[[require-backed]]\npackages = {packagesV}\nreason = \"r\"\n"

def header (line : Nat) (index : Nat := 1) : String :=
  s!"require-backed rule {index} (p.toml:{line}:0): r"

def ok1 : Array String :=
  #["lean-deny: ok (1 rule)"]

/-- The detail of a violation: `imp` (package `pa`) imports package `pb`. -/
def detail (imp pa pb : String) : String :=
  s!"{imp} (package {pa}) imports package {pb}, which {pa} does not require directly"

/-- `(case, modules, declared roots, packages, policy, expected lines)`. -/
def cases :
    Array
      (String × Array M × Array (Name × Array Name) × Array PackageInfo × String × Array String) :=
  #[ -- Holding.
    ("a direct require backs the import", #[m `A `a #[`P], m `P `p], #[], packages,
      rule "\"pkg:a\"", ok1),
    ("imports within a package are not judged", #[m `A `a #[`A2], m `A2 `a], #[], packages,
      rule "\"pkg:a\"", ok1),
    ("imports of external modules are not judged", #[m `A `a #[`Lean.Data.Json]], #[], packages,
      rule "\"pkg:a\"", ok1),
    ("a declared root's imports are not judged", #[m `A `a, m `B `b], #[(`R, #[`B])], packages,
      rule "\"pkg:a\"", ok1),
    ("an unmatched package's unbacked import is ignored", #[m `A `a #[`B], m `P `p, m `B `b], #[],
      packages, rule "\"pkg:p\"", ok1),
    -- Violations.
    ("a transitive-only require does not back the import",
      #[m `A `a #[`P, `B], m `P `p #[`B], m `B `b], #[], packages, rule "\"pkg:a\"",
      #[s!"{header 1}: {detail "A" "a" "b"}", "  A.lean:2: A imports B",
        "  a/lakefile.toml: a requires p", "lean-deny: 1 violation in 1 of 1 rule"]),
    ("a package that requires nothing", #[m `B `b #[`A], m `A `a], #[], packages, rule "\"pkg:b\"",
      #[s!"{header 1}: {detail "B" "b" "a"}", "  B.lean:1: B imports A",
        "  b/lakefile.toml: b requires nothing", "lean-deny: 1 violation in 1 of 1 rule"]),
    ("a module imported twice is one violation, the first directive the witness",
      #[{ name := `A, pkg := `a, imports := #[(`B, {}), (`B, { isMeta := true })] }, m `B `b], #[],
      packages, rule "\"pkg:a\"",
      #[s!"{header 1}: {detail "A" "a" "b"}", "  A.lean:1: A imports B",
        "  a/lakefile.toml: a requires p", "lean-deny: 1 violation in 1 of 1 rule"]),
    ("one per (importer, imported) pair, in display order",
      #[m `A2 `a #[`B], m `A `a #[`X, `B], m `B `b, m `X `x], #[], packages, rule "\"pkg:a\"",
      #[s!"{header 1}: {detail "A" "a" "x"}", "  A.lean:1: A imports X",
        "  a/lakefile.toml: a requires p", s!"{header 1}: {detail "A" "a" "b"}",
        "  A.lean:2: A imports B", "  a/lakefile.toml: a requires p",
        s!"{header 1}: {detail "A2" "a" "b"}", "  A2.lean:1: A2 imports B",
        "  a/lakefile.toml: a requires p", "lean-deny: 3 violations in 1 of 1 rule"]),
    ("meta and public imports count",
      #[{ name := `A, pkg := `a, isModule := true,
          imports := #[(`B, { isMeta := true }), (`X, { isPublic := true })] },
        m `B `b, m `X `x],
      #[], packages, rule "\"pkg:a\"",
      #[s!"{header 1}: {detail "A" "a" "b"}", "  A.lean:1: A imports B",
        "  a/lakefile.toml: a requires p", s!"{header 1}: {detail "A" "a" "x"}",
        "  A.lean:2: A imports X", "  a/lakefile.toml: a requires p",
        "lean-deny: 2 violations in 1 of 1 rule"]),
    ("a package Lake did not load requires nothing", #[m `A `a #[`P], m `P `p], #[], #[pkg `p],
      rule "\"mod:A!\"",
      #[s!"{header 1}: {detail "A" "a" "p"}", "  A.lean:1: A imports P", "  .: a requires nothing",
        "lean-deny: 1 violation in 1 of 1 rule"]),
    ("several packages and rules, after the other kinds", #[m `A `a #[`B], m `B `b #[`X], m `X `x],
      #[], packages,
      rule "[\"pkg:b\", \"pkg:a\"]" ++ rule "\"pkg:a\"" ++
        "[[reachable]]\nfrom = \"mod:A!\"\nmust-cover = \"mod:X!\"\nreason = \"c\"\n",
      #[s!"{header 1}: {detail "A" "a" "b"}", "  A.lean:1: A imports B",
        "  a/lakefile.toml: a requires p", s!"{header 1}: {detail "B" "b" "x"}",
        "  B.lean:1: B imports X", "  b/lakefile.toml: b requires nothing",
        s!"{header 4 2}: {detail "A" "a" "b"}", "  A.lean:1: A imports B",
        "  a/lakefile.toml: a requires p", "lean-deny: 3 violations in 2 of 3 rules"]),
    -- Errors.
    ("a selector that matches nothing", #[m `A `a], #[], packages, rule "\"mod:Nope!\"",
      #["p.toml:2:11: selector 'mod:Nope!' in require-backed rule 1 ('packages') matches no \
          module: no workspace module named 'Nope'"]),
    ("a selector that matches only external modules", #[m `A `a], #[], packages,
      rule "\"external:Init\"",
      #["p.toml:2:11: selector 'external:Init' in require-backed rule 1 ('packages') matches \
          only modules outside the workspace, which are in no package"]),
    ("a selector that matches only declared roots", #[m `A `a], #[(`R, #[`A])], packages,
      rule "\"mod:R!\"",
      #["p.toml:2:11: selector 'mod:R!' in require-backed rule 1 ('packages') matches only \
          declared roots or modules outside the workspace, which are in no package"]),
    ("a rule that splits a package", #[m `A `a #[`B], m `A2 `a, m `B `b], #[], packages,
      rule "\"mod:A!\"",
      #["p.toml:1:0: require-backed rule 1 splits package 'a': it matches A but not A2; the \
          rule judges whole packages, so select them with pkg:, keyword:, or a set of them"]),
    ("selector errors first, in source order; a split only without them", #[m `A `a, m `A2 `a], #[],
      packages, rule "[\"mod:A!\", \"external:Init\", \"mod:Nope!\"]",
      #["p.toml:2:39: selector 'mod:Nope!' in require-backed rule 1 ('packages') matches no \
          module: no workspace module named 'Nope'",
        "p.toml:2:22: selector 'external:Init' in require-backed rule 1 ('packages') matches \
          only modules outside the workspace, which are in no package"]),
    ("an error in one rule hides another's violations", #[m `A `a #[`B], m `B `b], #[], packages,
      rule "\"pkg:a\"" ++ rule "\"mod:Nope!\"",
      #["p.toml:5:11: selector 'mod:Nope!' in require-backed rule 2 ('packages') matches no \
          module: no workspace module named 'Nope'"])]

/-- `(case, policy, expected lines)`: what loading reports, over a graph of
one module `A`. -/
def loadCases : Array (String × String × Array String) :=
  #[("require-backed = 1", "require-backed = 1\n",
      #["load: p.toml:1:17: 'require-backed' must be an array of tables, such as \
          [[require-backed]]"]),
    ("require-backed = []", "require-backed = []\n",
      #["load: p.toml:1:17: 'require-backed' is empty (omit it)"]),
    ("require-backed = [1]", "require-backed = [1]\n",
      #["load: p.toml:1:18: require-backed rule 1 must be a table, found an integer"]),
    ("missing keys", "[[require-backed]]\n",
      #["load: p.toml:1:0: require-backed rule 1 has no 'packages'",
        "load: p.toml:1:0: require-backed rule 1 has no 'reason'"]),
    ("wrong types and an unknown key",
      "[[require-backed]]\npackages = 1\nreason = true\nfrom = \"pkg:x\"\n",
      #["load: p.toml:2:11: require-backed rule 1: 'packages' must be a selector or an array of \
          selectors, found an integer",
        "load: p.toml:3:9: require-backed rule 1: 'reason' must be a string, found a boolean",
        "load: p.toml:4:7: require-backed rule 1: unknown key 'from' (expected packages, reason)"]),
    ("an empty packages and a blank reason", "[[require-backed]]\npackages = []\nreason = \" \"\n",
      #["load: p.toml:2:11: require-backed rule 1: 'packages' is empty",
        "load: p.toml:3:9: require-backed rule 1: 'reason' is empty"]),
    ("a bad selector", "[[require-backed]]\npackages = [\"crate:x\", 2]\nreason = \"r\"\n",
      #["load: p.toml:2:12: invalid selector 'crate:x': unknown kind 'crate' (expected pkg, lib, \
          mod, keyword, external, set or imports)",
        "load: p.toml:2:23: require-backed rule 1 ('packages'): expected a selector string, found \
          an integer"]),
    ("an unknown set", rule "\"set:nope\"",
      #["load: p.toml:2:11: selector 'set:nope' in require-backed rule 1 ('packages') names an \
          unknown set (the policy defines no sets)"])]

/-- The rule's label, kind and count. -/
def labelFailures : IO (Array String) := do
  let r : RequireBackedRule := { index := 2, pos? := none }
  let mut fs := #[]
  unless r.label == "require-backed rule 2" && r.ref.kind.toString == "require-backed" do
    fs := fs.push s!"label: got {r.label}, kind {r.ref.kind}"
  match ← LeanDenyTest.Policy.load (rule "\"pkg:a\"" ++ rule "[\"pkg:a\", \"keyword:k\"]") with
  | .ok p =>
    unless
      p.ruleCount == 2 && p.requireBacked.map (·.index) == #[1, 2] &&
        p.requireBacked.map (·.packages.size) == #[1, 2] do
      fs := fs.push s!"ruleCount: got {p.ruleCount}"
  | .error es =>
    fs := fs.push s!"ruleCount: load failed: {es}"
  return fs

def run : IO (Array String) := do
  let mut fs ← labelFailures
  for (name, ms, roots, pkgs, src, want) in cases do
    let got ← outcome ms src pkgs roots
    unless got == want do
      fs := fs.push s!"{name}: expected {repr want}, got {repr got}"
  for (name, src, want) in loadCases do
    let got ← outcome #[m `A `a] src
    unless got == want do
      fs := fs.push s!"{name}: expected {repr want}, got {repr got}"
  return fs

end LeanDenyTest.RequireBacked
