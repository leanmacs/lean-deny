import LeanDenyTest.Deny

/-!
Tests of `[[target-config]]` rules (`LeanDeny.Rules.TargetConfig`) on
hand-written graphs and package metadata, from the policy's TOML text to
what `check` prints: which targets `pkg:` and `lib:` select, `except` and
de-duplication, matching `load-plugin` by full and bare name (a facet key
and another package never match), `or-imports` direct and transitive, an
executable's root alone, the closure not being reflexive, the order, the
errors a rule can give and their order, loading, and `PluginName.parse?`.
-/

open Lean LeanDeny LeanDeny.Graph LeanDenyTest.Query

namespace LeanDenyTest.TargetConfig

open LeanDenyTest.Deny (outcome)

/-- Module `n` of target `target` (of kind `kind`) of package `pkg`, with
plain imports `imports`. -/
def m (n pkg : Name) (kind : TargetKind) (target : Name) (imports : Array Name := #[]) : M :=
  { name := n, pkg, kind, target, imports := imports.map plain }

/-- A plugin `@pkg/target` (`pkg = .anonymous`: the bare `target`). -/
def pl (pkg target : Name) : PluginRef :=
  let t := target.toString (escape := false)
  if pkg.isAnonymous then { target? := some target, text := t }
  else
    { pkg? := some pkg, target? := some target, text := s!"@{pkg.toString (escape := false)}/{t}" }

def lib (name : Name) (plugins : Array PluginRef := #[]) : LibInfo :=
  { name, roots := #[name], globs := #[], plugins }

def exe (name root : Name) (plugins : Array PluginRef := #[]) : ExeInfo :=
  { name, root, plugins }

def pkg (name : Name) (libs : Array LibInfo) (exes : Array ExeInfo) : PackageInfo :=
  { name, dir := s!"/ws/{name}", configFile := s!"/ws/{name}/lakefile.toml", keywords := #[]
    remoteUrl? := none, requires := #[], libs, exes, isRoot := false }

/-- The modules: package `lint` (Lint imports Lint.Wait, LintTest.Wait
imports Lint.Wait, the lint-test root imports LintTest.Wait), package `a`
(A, and the a-tool root importing it), package `b` (B, BX, BF, BUses
importing Lint, and the b-tool root importing B). -/
def ms : Array M :=
  #[m `Lint `lint .lib `Lint #[`Lint.Wait], m `Lint.Wait `lint .lib `Lint,
    m `LintTest.Wait `lint .lib `LintTests #[`Lint.Wait],
    m `LintTest `lint .exe `«lint-test» #[`LintTest.Wait], m `A `a .lib `A,
    m `ATool `a .exe `«a-tool» #[`A], m `B `b .lib `B, m `BX `b .lib `BX, m `BF `b .lib `BF,
    m `BUses `b .lib `BUses #[`Lint], m `BRoot `b .exe `«b-tool» #[`B]]

/-- The packages, in this order: lint (no plugins), a (A and a-tool load
`@lint/lintShared`, AEmpty has no modules and loads nothing), b (B loads the
bare `lintShared`, BX `@other/lintShared`, BF a facet key, BUses and b-tool
nothing), empty (no target). -/
def packages : Array PackageInfo :=
  #[pkg `lint #[lib `Lint, lib `LintTests] #[exe `«lint-test» `LintTest],
    pkg `a #[lib `A #[pl `lint `lintShared], lib `AEmpty]
      #[exe `«a-tool» `ATool #[pl `lint `lintShared]],
    pkg `b
      #[lib `B #[pl .anonymous `lintShared], lib `BX #[pl `other `lintShared],
        lib `BF #[{ text := "@lint/lintShared:shared" }], lib `BUses]
      #[exe `«b-tool» `BRoot],
    pkg `empty #[] #[]]

/-- A target-config table (lines: header, `targets`, `load-plugin`, then
`extra`, then `reason = "r"`), `targets` given as a TOML value. -/
def rule (targetsV plugin : String) (extra : String := "") : String :=
  s!"[[target-config]]\ntargets = {targetsV}\nload-plugin = \"{plugin}\"\n{extra}reason = \"r\"\n"

def header (line : Nat) (index : Nat := 1) : String :=
  s!"target-config rule {index} (p.toml:{line}:0): r"

def ok1 : Array String :=
  #["lean-deny: ok (1 rule)"]

/-- `(case, packages, policy, expected lines)`. -/
def cases : Array (String × Array PackageInfo × String × Array String) :=
  #[ -- Selection and matching.
    ("pkg: picks every lib and exe; a library with no modules is a target", packages,
      rule "\"pkg:a\"" "@lint/lintShared",
      #[s!"{header 1}: lean_lib a/AEmpty does not load @lint/lintShared",
        "  a/lakefile.toml: lean_lib AEmpty", "lean-deny: 1 violation in 1 of 1 rule"]),
    ("a bare name matches any package's target; a facet key never matches", packages,
      rule "\"pkg:b\"" "lintShared",
      #[s!"{header 1}: lean_lib b/BF does not load lintShared", "  b/lakefile.toml: lean_lib BF",
        s!"{header 1}: lean_lib b/BUses does not load lintShared",
        "  b/lakefile.toml: lean_lib BUses",
        s!"{header 1}: lean_exe b/b-tool does not load lintShared",
        "  b/lakefile.toml: lean_exe b-tool", "lean-deny: 3 violations in 1 of 1 rule"]),
    ("a given package must match", packages, rule "[\"lib:b/B\", \"lib:BX\"]" "lint/lintShared",
      #[s!"{header 1}: lean_lib b/B does not load lint/lintShared", "  b/lakefile.toml: lean_lib B",
        s!"{header 1}: lean_lib b/BX does not load lint/lintShared",
        "  b/lakefile.toml: lean_lib BX", "lean-deny: 2 violations in 1 of 1 rule"]),
    ("except and duplicates", packages,
      rule "[\"pkg:a\", \"lib:a/A\", \"lib:AEmpty\"]" "@lint/lintShared"
        "except = \"lib:a/AEmpty\"\n",
      ok1),
    -- or-imports.
    ("or-imports, direct and transitive; an exe's root alone counts", packages,
      rule "[\"pkg:b\", \"pkg:lint\"]" "@lint/lintShared" "or-imports = \"lib:lint/Lint\"\n",
      #[s!"{header 1}: lean_lib b/B does not load @lint/lintShared and imports no module of \
          lib:lint/Lint",
        "  b/lakefile.toml: lean_lib B",
        s!"{header 1}: lean_lib b/BX does not load @lint/lintShared and imports no module of \
          lib:lint/Lint",
        "  b/lakefile.toml: lean_lib BX",
        s!"{header 1}: lean_lib b/BF does not load @lint/lintShared and imports no module of \
          lib:lint/Lint",
        "  b/lakefile.toml: lean_lib BF",
        s!"{header 1}: lean_exe b/b-tool does not load @lint/lintShared and imports no module of \
          lib:lint/Lint",
        "  b/lakefile.toml: lean_exe b-tool", "lean-deny: 4 violations in 1 of 1 rule"]),
    ("the closure is not reflexive; several or-imports are named", packages,
      rule "\"lib:lint/Lint\"" "@lint/lintShared" "or-imports = [\"mod:Lint!\", \"mod:B!\"]\n",
      #[s!"{header 1}: lean_lib lint/Lint does not load @lint/lintShared and imports no module of \
          mod:Lint! or mod:B!",
        "  lint/lakefile.toml: lean_lib Lint", "lean-deny: 1 violation in 1 of 1 rule"]),
    ("in rule order, after the other kinds", packages,
      rule "\"lib:b/BF\"" "@lint/lintShared" ++
        "[[reachable]]\nfrom = \"mod:A!\"\n\
        must-cover = \"mod:B!\"\nreason = \"q\"\n" ++
        rule "\"lib:a/AEmpty\"" "@lint/lintShared",
      #[s!"reachable rule 1 (p.toml:5:0): q: B is outside the import closure of A", "  B.lean: B",
        s!"{header 1}: lean_lib b/BF does not load @lint/lintShared",
        "  b/lakefile.toml: lean_lib BF",
        s!"{header 9 2}: lean_lib a/AEmpty does not load @lint/lintShared",
        "  a/lakefile.toml: lean_lib AEmpty", "lean-deny: 3 violations in 3 of 3 rules"]),
    -- Errors.
    ("every target selector error, in order", packages,
      rule "[\"pkg:nope\", \"pkg:empty\", \"lib:Nope\", \"lib:a/Nope\", \"lib:b/nope\", \"pkg:a\"]"
        "t" "except = \"pkg:b\"\n",
      #["p.toml:2:11: selector 'pkg:nope' in target-config rule 1 ('targets') matches no target: \
          no package named 'nope' (packages: lint, a, b, empty)",
        "p.toml:2:23: selector 'pkg:empty' in target-config rule 1 ('targets') matches no target: \
          package 'empty' declares no lean_lib or lean_exe",
        "p.toml:2:36: selector 'lib:Nope' in target-config rule 1 ('targets') matches no target: \
          no package has a lean_lib named 'Nope'",
        "p.toml:2:48: selector 'lib:a/Nope' in target-config rule 1 ('targets') matches no \
          target: package 'a' has no lean_lib named 'Nope'",
        "p.toml:2:62: selector 'lib:b/nope' in target-config rule 1 ('targets') matches no \
          target: package 'b' has no lean_lib named 'nope'"]),
    ("an ambiguous lib:", packages.push (pkg `c #[lib `B] #[]), rule "\"lib:B\"" "t",
      #["p.toml:2:10: selector 'lib:B' in target-config rule 1 ('targets') is ambiguous: \
          lean_lib 'B' is in packages b, c; write 'lib:<package>/B'"]),
    ("or-imports errors, then an except that removes nothing", packages,
      rule "\"pkg:a\"" "t"
        "except = \"lib:b/B\"\nor-imports = [\"mod:Nope!\", \"external:Init\"]\n",
      #["p.toml:5:14: selector 'mod:Nope!' in target-config rule 1 ('or-imports') matches no \
          module: no workspace module named 'Nope'",
        "p.toml:5:27: selector 'external:Init' in target-config rule 1 ('or-imports') matches \
          only modules outside the workspace, which a rule about reach does not check",
        "p.toml:4:9: selector 'lib:b/B' in target-config rule 1 ('except') removes no target the \
          rule selects"]),
    ("an except that empties the rule", packages, rule "\"lib:a/A\"" "t" "except = \"pkg:a\"\n",
      #["p.toml:1:0: target-config rule 1: 'except' removes every target it selects, so it checks \
          nothing"]),
    ("an error in one rule hides another's violations", packages,
      rule "\"lib:b/BF\"" "t" ++ rule "\"lib:Nope\"" "t",
      #["p.toml:6:10: selector 'lib:Nope' in target-config rule 2 ('targets') matches no target: \
          no package has a lean_lib named 'Nope'"])]

/-- `(case, policy, expected lines)`: what loading reports. -/
def loadCases : Array (String × String × Array String) :=
  #[("target-config = 1", "target-config = 1\n",
      #["load: p.toml:1:16: 'target-config' must be an array of tables, such as \
          [[target-config]]"]),
    ("target-config = []", "target-config = []\n",
      #["load: p.toml:1:16: 'target-config' is empty (omit it)"]),
    ("target-config = [1]", "target-config = [1]\n",
      #["load: p.toml:1:17: target-config rule 1 must be a table, found an integer"]),
    ("missing keys", "[[target-config]]\nexcept = \"pkg:a\"\n",
      #["load: p.toml:1:0: target-config rule 1 has no 'targets'",
        "load: p.toml:1:0: target-config rule 1 has no 'load-plugin'",
        "load: p.toml:1:0: target-config rule 1 has no 'reason'"]),
    ("not target selectors",
      rule "[\"mod:X\", \"set:s\", \"keyword:k\", \"external:E\", \"imports:pkg:a\"]" "t"
        "except = \"mod:Y!\"\n",
      #["load: p.toml:2:11: target-config rule 1 ('targets'): 'mod:X' is not a target selector \
          (expected pkg:<package>, lib:<lib> or lib:<package>/<lib>)",
        "load: p.toml:2:20: target-config rule 1 ('targets'): 'set:s' is not a target selector \
          (expected pkg:<package>, lib:<lib> or lib:<package>/<lib>)",
        "load: p.toml:2:29: target-config rule 1 ('targets'): 'keyword:k' is not a target \
          selector (expected pkg:<package>, lib:<lib> or lib:<package>/<lib>)",
        "load: p.toml:2:42: target-config rule 1 ('targets'): 'external:E' is not a target \
          selector (expected pkg:<package>, lib:<lib> or lib:<package>/<lib>)",
        "load: p.toml:2:56: target-config rule 1 ('targets'): 'imports:pkg:a' is not a target \
          selector (expected pkg:<package>, lib:<lib> or lib:<package>/<lib>)",
        "load: p.toml:4:9: target-config rule 1 ('except'): 'mod:Y!' is not a target selector \
          (expected pkg:<package>, lib:<lib> or lib:<package>/<lib>)"]),
    ("wrong types, empty lists and an unknown key",
      "[[target-config]]\ntargets = 1\nexcept = []\nload-plugin = 1\nor-imports = []\n\
        reason = true\ntransitive = true\n",
      #["load: p.toml:2:10: target-config rule 1: 'targets' must be a selector or an array of \
          selectors, found an integer",
        "load: p.toml:3:9: target-config rule 1: 'except' is empty (omit it)",
        "load: p.toml:4:14: target-config rule 1: 'load-plugin' must be a string, found an \
          integer",
        "load: p.toml:5:13: target-config rule 1: 'or-imports' is empty (omit it)",
        "load: p.toml:6:9: target-config rule 1: 'reason' must be a string, found a boolean",
        "load: p.toml:7:13: target-config rule 1: unknown key 'transitive' (expected targets, \
          except, load-plugin, or-imports, reason)"]),
    ("a bad load-plugin", rule "\"pkg:a\"" "@lint/Lint:shared",
      #["load: p.toml:3:14: target-config rule 1: 'load-plugin' must be a Lake target name, \
          '<target>' or '@<package>/<target>', found '@lint/Lint:shared'"]),
    ("a blank reason",
      "[[target-config]]\ntargets = \"pkg:a\"\nload-plugin = \"t\"\nreason = \" \"\n",
      #["load: p.toml:4:9: target-config rule 1: 'reason' is empty"]),
    ("an unknown set in or-imports", rule "\"pkg:a\"" "t" "or-imports = \"set:nope\"\n",
      #["load: p.toml:4:13: selector 'set:nope' in target-config rule 1 ('or-imports') names an \
          unknown set (the policy defines no sets)"])]

/-- `PluginName.parse?`'s cases: the text and what it parses to, as
`pkg/target` (`-` for no package), or `none`. -/
def pluginCases : Array (String × Option String) :=
  #[("t", some "-/t"), ("p/t", some "p/t"), ("@p/t", some "p/t"),
    ("editor-core/lintShared", some "editor-core/lintShared"), ("", none), ("@p", none),
    ("p/", none), ("/t", none), ("@/t", none), ("a/b/c", none), ("p/t:f", none), ("t:f", none),
    ("+M", none), ("p/+M", none), ("a b", none), ("@@p/t", none)]

/-- The rule's label, kind and count, and `PluginName.parse?`. -/
def unitFailures : IO (Array String) := do
  let r : TargetConfigRule := { index := 2, pos? := none }
  let mut fs := #[]
  unless r.label == "target-config rule 2" && r.ref.kind.toString == "target-config" do
    fs := fs.push s!"label: got {r.label}, kind {r.ref.kind}"
  match ← LeanDenyTest.Policy.load (rule "\"pkg:a\"" "t" ++ rule "\"lib:b/B\"" "@b/t") with
  | .ok p =>
    unless
      p.ruleCount == 2 && p.targetConfig.map (·.index) == #[1, 2] &&
        p.targetConfig.map (·.loadPlugin?.map (·.text)) == #[some "t", some "@b/t"] do
      fs := fs.push s!"ruleCount: got {p.ruleCount}"
  | .error es =>
    fs := fs.push s!"ruleCount: load failed: {es}"
  for (s, want) in pluginCases do
    let got := (PluginName.parse? s).map fun n => s!"{n.pkg?.getD "-"}/{n.target}"
    unless got == want do
      fs := fs.push s!"PluginName.parse? {repr s}: expected {repr want}, got {repr got}"
  return fs

def run : IO (Array String) := do
  let mut fs ← unitFailures
  for (name, pkgs, src, want) in cases do
    let got ← outcome ms src (packages := pkgs)
    unless got == want do
      fs := fs.push s!"{name}: expected {repr want}, got {repr got}"
  for (name, src, want) in loadCases do
    let got ← outcome ms src (packages := packages)
    unless got == want do
      fs := fs.push s!"{name}: expected {repr want}, got {repr got}"
  return fs

end LeanDenyTest.TargetConfig
