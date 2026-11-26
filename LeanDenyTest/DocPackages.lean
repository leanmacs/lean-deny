import LeanDenyTest.RequireBacked

/-!
Tests of `[[doc-packages]]` rules (`LeanDeny.Rules.DocPackages`) on
hand-written graphs, package metadata and table texts, from the policy's
TOML text to what `check` prints: an agreeing table holds whatever its row
order, duplicates and other columns; missing packages by name, extra rows,
layer and requires differences, each one violation, in report order;
`requires-except`; which table is read; the errors a rule can give and their
order; `[layers]` errors giving none of the rule's; loading; and the rule's
label and count.
-/

open Lean LeanDeny LeanDeny.Graph LeanDenyTest.Query

namespace LeanDenyTest.DocPackages

open LeanDenyTest.RequireBacked (m pkg)

/-- The modules: one per package, `Impl2` in `impl` too; nothing imports
anything, so `[layers]` allows nothing and judges nothing. -/
def mods : Array M :=
  #[m `Core `core, m `Api `api, m `Impl `impl, m `Impl2 `impl, m `X `x]

/-- The packages: `impl` requires `core` and `api`, `api` requires `core`,
`core` and `x` nothing. -/
def packages : Array PackageInfo :=
  #[pkg `core, pkg `api #[`core], pkg `impl #[`core, `api], pkg `x]

/-- `[layers]` (lines 1 to 3): `core` in core, `api` in interface, the rest
in implementation. -/
def layers : String :=
  "[layers]\nclassify = [{ layer = \"core\", select = \"pkg:core\" }, \
    { layer = \"interface\", select = \"pkg:api\" }]\ndefault = \"implementation\"\n"

/-- A doc-packages table (lines: header, `file`, `section`, the three
columns, `packages`, then `extra`, then `reason = "r"`), `packages` given as
a TOML value. -/
def rule (packagesV : String := "[\"pkg:api\", \"pkg:impl\"]")
    (extra : String := "requires-except = \"core\"\n") : String :=
  s!"[[doc-packages]]\nfile = \"docs/p.md\"\nsection = \"Pkgs\"\npackage-column = \"Package\"\n\
    layer-column = \"Layer\"\nrequires-column = \"Requires\"\npackages = {packagesV}\n{extra}\
    reason = \"r\"\n"

/-- `layers`, then `rule` (header on line 4). -/
def policy (packagesV : String := "[\"pkg:api\", \"pkg:impl\"]")
    (extra : String := "requires-except = \"core\"\n") : String :=
  layers ++ rule packagesV extra

/-- What `check` prints for policy `src` over `mods` and `packages`, every
doc-packages rule's file given by `contents`: the errors, or the report. -/
def outcome (src : String) (contents : Option (Except String String)) : IO (Array String) := do
  let g ←
    match mkGraph mods with
    | .ok g =>
      pure { g with packages }
    | .error e =>
      return #[s!"graph: {e}"]
  match ← LeanDenyTest.Policy.load src with
  | .error es =>
    return es.map ("load: " ++ ·)
  | .ok p =>
    match resolveSets g p with
    | .error es =>
      return es.map ("sets: " ++ ·)
    | .ok sets =>
      let tables := p.docPackages.map (·.readResult p contents)
      match checkRules g p sets #[] tables with
      | .error es =>
        return es
      | .ok vs =>
        return checkReport g p vs

def text (t : String) : Option (Except String String) :=
  some (.ok t)

/-- Section `Pkgs` (line 1) holding one package table (header on line 2,
rows from line 4) with the rows `rows`. -/
def tbl (rows : String) : Option (Except String String) :=
  text s!"## Pkgs\n| Package | Layer | Requires |\n|---|---|---|\n{rows}"

/-- The rows that agree: `impl`, then `api`. -/
def agree : String :=
  "| `impl` | implementation | `api` |\n| `api` | interface | none |\n"

def ok2 : Array String :=
  #["lean-deny: ok (2 rules)"]

def header : String :=
  "doc-packages rule 1 (p.toml:4:0): r"

/-- `n` violations of the one doc-packages rule. -/
def summary (n : Nat) : String :=
  s!"lean-deny: {n} violation{if n == 1 then "" else "s"} in 1 of 2 rules"

def sect : String :=
  "section 'Pkgs' of docs/p.md"

def missingRow (p : String) : Array String :=
  #[s!"{header}: package {p} has no row in {sect}", "  docs/p.md:1: section 'Pkgs'"]

def extraRow (p : String) (line : Nat) : Array String :=
  #[s!"{header}: {sect} has a row for {p}, which 'packages' does not match",
    s!"  docs/p.md:{line}: {p}"]

def layerRow (p doc lay : String) (line : Nat) : Array String :=
  #[s!"{header}: {sect} gives {p} layer {doc}, but [layers] puts it in {lay}",
    s!"  docs/p.md:{line}: {p}"]

def requiresRow (p cell direct diff : String) (line : Nat) : Array String :=
  #[s!"{header}: {sect} gives {p} requires {cell}, but {p} requires {direct} directly: {diff}",
    s!"  docs/p.md:{line}: {p}"]

/-- `(case, policy, contents, expected lines)`. -/
def cases : Array (String × String × Option (Except String String) × Array String) :=
  #[ -- Holding.
    ("an agreeing table holds", policy, tbl agree, ok2),
    ("row order, a duplicate agreeing row and other columns do not matter", policy,
      text
        "## Pkgs\n| Notes | Requires | Package | Layer |\n|---|---|---|---|\n\
        | n | none | `api` | `interface` |\n| n | `api` | `impl` | implementation |\n\
        | n | none | `api` | interface |\n",
      ok2),
    ("a nested table before the package table is not read", policy,
      text
        s!"## Pkgs\n- item:\n\n  | Package | Layer | Requires |\n  |---|---|---|\n  | `x` | y | z |\n\n\
        | Package | Layer | Requires |\n|---|---|---|\n{agree}",
      ok2),
    ("the first table with every column is read", policy,
      text
        s!"## Pkgs\n| Package | Layer |\n|---|---|\n| `x` | y |\n\n| Package | Layer | Requires |\n\
        |---|---|---|\n{agree}\n| Package | Layer | Requires |\n|---|---|---|\n| `x` | y | none |\n",
      ok2),
    ("without requires-except the core is a require", policy (extra := ""),
      tbl "| `impl` | implementation | `core`, `api` |\n| `api` | interface | `core` |\n", ok2),
    -- Violations.
    ("each missing package, by name", policy, tbl "",
      missingRow "api" ++ missingRow "impl" ++ #[summary 2]),
    ("an extra row for an unselected workspace package and an unknown name", policy,
      tbl (agree ++ "| `x` | implementation | none |\n| `gone` | interface | none |\n"),
      extraRow "x" 6 ++ extraRow "gone" 7 ++ #[summary 2]),
    ("a layer that differs", policy,
      tbl "| `impl` | interface | `api` |\n| `api` | interface | none |\n",
      layerRow "impl" "interface" "implementation" 4 ++ #[summary 1]),
    ("a missing require", policy,
      tbl "| `impl` | implementation | none |\n| `api` | interface | none |\n",
      requiresRow "impl" "none" "api" "missing api" 4 ++ #[summary 1]),
    ("an extra require", policy,
      tbl "| `impl` | implementation | `api` |\n| `api` | interface | `impl` |\n",
      requiresRow "api" "impl" "nothing" "extra impl" 5 ++ #[summary 1]),
    ("missing and extra requires are one violation", policy,
      tbl "| `impl` | implementation | `x`, `x` |\n| `api` | interface | none |\n",
      requiresRow "impl" "x" "api" "missing api; extra x" 4 ++ #[summary 1]),
    ("requires-except makes the core extra in a cell", policy,
      tbl "| `impl` | implementation | `api` `core` |\n| `api` | interface | none |\n",
      requiresRow "impl" "api, core" "api" "extra core" 4 ++ #[summary 1]),
    ("missing first, then rows in document order, layer before requires", policy,
      tbl "| `gone` | x | none |\n| `api` | implementation | `impl` |\n",
      missingRow "impl" ++ extraRow "gone" 4 ++ layerRow "api" "implementation" "interface" 5 ++
        requiresRow "api" "impl" "nothing" "extra impl" 5 ++
        #[summary 4]),
    -- Errors.
    ("a selector that matches nothing", policy "\"mod:Nope!\"", tbl agree,
      #["p.toml:10:11: selector 'mod:Nope!' in doc-packages rule 1 ('packages') matches no \
          module: no workspace module named 'Nope'"]),
    ("a rule that splits a package", policy "\"mod:Impl!\"", tbl agree,
      #["p.toml:4:0: doc-packages rule 1 splits package 'impl': it matches Impl but not Impl2; the \
          rule judges whole packages, so select them with pkg:, keyword:, or a set of them"]),
    ("a requires-except package the workspace does not have",
      policy (extra := "requires-except = [\"core\", \"kernel\", \"k2\"]\n"), tbl agree,
      #["p.toml:11:27: doc-packages rule 1: 'requires-except' names package 'kernel', which the \
          workspace does not have",
        "p.toml:11:37: doc-packages rule 1: 'requires-except' names package 'k2', which the \
          workspace does not have"]),
    ("no file", policy, none,
      #["p.toml:4:0: doc-packages rule 1: no file 'docs/p.md' in the workspace (looking for \
          heading 'Pkgs')"]),
    ("a read failure", policy, some (.error "boom"),
      #["p.toml:4:0: doc-packages rule 1: cannot read 'docs/p.md' (looking for heading 'Pkgs'): \
          boom"]),
    ("no heading", policy, text "## Other\n",
      #["p.toml:4:0: doc-packages rule 1: no heading 'Pkgs' in 'docs/p.md'"]),
    ("a heading appearing twice", policy, text "## Pkgs\n## Pkgs\n",
      #["p.toml:4:0: doc-packages rule 1: heading 'Pkgs' appears 2 times in 'docs/p.md' (lines 1 \
          and 2)"]),
    ("no top-level table", policy,
      text "## Pkgs\n- `api`\n\n  | Package | Layer | Requires |\n  |---|---|---|\n",
      #["p.toml:4:0: doc-packages rule 1: section 'Pkgs' of 'docs/p.md' has no top-level table"]),
    ("no table with every column", policy,
      text "## Pkgs\n| Package |\n|---|\n\n| Package | Layer |\n|---|---|\n",
      #["p.toml:4:0: doc-packages rule 1: no top-level table in section 'Pkgs' of 'docs/p.md' has \
          the columns 'Package', 'Layer' and 'Requires' (the first, at line 2, has no 'Layer' and \
          'Requires')"]),
    ("a package cell with no backticks", policy, tbl "| impl | implementation | none |\n",
      #["p.toml:4:0: doc-packages rule 1: 'docs/p.md':4: the 'Package' cell names no package in \
          backticks"]),
    ("an empty layer cell", policy, tbl (agree ++ "| `impl` |  | none |\n"),
      #["p.toml:4:0: doc-packages rule 1: 'docs/p.md':6: the 'Layer' cell is empty"]),
    ("a requires cell neither none nor names", policy,
      tbl "| `impl` | implementation | nothing |\n",
      #["p.toml:4:0: doc-packages rule 1: 'docs/p.md':4: the 'Requires' cell is neither 'none' \
          nor package names in backticks"]),
    ("a selector error, then the file's", policy "\"mod:Nope!\"", none,
      #["p.toml:10:11: selector 'mod:Nope!' in doc-packages rule 1 ('packages') matches no \
          module: no workspace module named 'Nope'",
        "p.toml:4:0: doc-packages rule 1: no file 'docs/p.md' in the workspace (looking for \
          heading 'Pkgs')"]),
    ("[layers] errors are [layers]'s alone",
      "[layers]\nclassify = [{ layer = \"core\", select = \"pkg:nope\" }]\ndefault = \"implementation\"\n" ++
        rule,
      tbl agree,
      #["p.toml:2:39: selector 'pkg:nope' in layers classify entry 1 matches no module: no \
          package named 'nope' (packages: core, api, impl, x)"]),
    -- Loading.
    ("an unknown key", policy (extra := "heading = \"Pkgs\"\n"), tbl agree,
      #["load: p.toml:11:10: doc-packages rule 1: unknown key 'heading' (expected file, section, \
          package-column, layer-column, requires-column, packages, requires-except, reason)"]),
    ("no [layers]", rule, tbl agree,
      #["load: p.toml:1:0: doc-packages rule 1: the policy has no [layers], which gives each \
          package's layer"])]

/-- The rule's label, kind and count, and a missing `docs` entry. -/
def labelFailures : IO (Array String) := do
  let r : DocPackagesRule := { index := 2, pos? := none }
  let mut fs := #[]
  unless r.label == "doc-packages rule 2" && r.ref.kind.toString == "doc-packages" do
    fs := fs.push s!"label: got {r.label}, kind {r.ref.kind}"
  match ← LeanDenyTest.Policy.load (policy ++ rule "\"pkg:api\"") with
  | .ok p =>
    unless
      p.ruleCount == 3 && p.docPackages.map (·.index) == #[1, 2] &&
        p.docPackages.map (·.packages.size) == #[2, 1] do
      fs := fs.push s!"ruleCount: got {p.ruleCount}"
    match mkGraph mods with
    | .ok g =>
      let g := { g with packages }
      match resolveSets g p with
      | .ok sets =>
        let want :=
          #["p.toml:4:0: doc-packages rule 1: internal error: its file was not read",
            "p.toml:13:0: doc-packages rule 2: internal error: its file was not read"]
        match checkDocPackages g p sets #[] with
        | .error es =>
          unless es == want do
            fs := fs.push s!"a missing docs entry: got {es}"
        | .ok _ =>
          fs := fs.push "a missing docs entry is not an error"
      | .error es =>
        fs := fs.push s!"sets: {es}"
    | .error e =>
      fs := fs.push s!"graph: {e}"
  | .error es =>
    fs := fs.push s!"ruleCount: load failed: {es}"
  return fs

def run : IO (Array String) := do
  let mut fs ← labelFailures
  for (name, src, contents, want) in cases do
    let got ← outcome src contents
    unless got == want do
      fs := fs.push s!"{name}: expected {repr want}, got {repr got}"
  return fs

end LeanDenyTest.DocPackages
