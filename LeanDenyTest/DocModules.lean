import LeanDenyTest.Deny

/-!
Tests of `[[doc-modules]]` rules (`LeanDeny.Rules.DocModules`) on
hand-written graphs and section texts, from the policy's TOML text to what
`check` prints: equal sets hold whatever the order and duplicates; names
without the prefix are ignored; missing modules, then extra names, each in
order; a declared root counts and an external in a mixed match is ignored;
the errors a rule can give and their order; and the rule's label and count.
-/

open Lean LeanDeny LeanDeny.Graph LeanDenyTest.Query

namespace LeanDenyTest.DocModules

open LeanDenyTest.Deny (m)

/-- A doc-modules table (lines: header, `file`, `section`, `prefix`,
`modules`, `reason = "r"`), `modules` given as a TOML value. -/
def rule (modulesV : String) (sect : String := "Mods") (pfx : String := "A.") : String :=
  s!"[[doc-modules]]\nfile = \"docs/m.md\"\nsection = \"{sect}\"\nprefix = \"{pfx}\"\n\
    modules = {modulesV}\nreason = \"r\"\n"

/-- The modules A.X, A.Y and A (the root). -/
def mods : Array M :=
  #[m `A #[`A.X, `A.Y], m `A.X, m `A.Y]

/-- `{select = ["mod:A"], except = ["mod:A!"]}` as a set `xs`. -/
def setXs : String :=
  "[sets]\nxs = { select = [\"mod:A\"], except = [\"mod:A!\"] }\n"

/-- What `check` prints for policy `src` over the graph of `ms` with the
declared roots `roots`, every doc-modules rule's file given by `contents`:
the errors, or the report. -/
def outcome (ms : Array M) (src : String) (contents : Option (Except String String))
    (roots : Array (Name × Array Name) := #[]) : IO (Array String) := do
  let resolve (n : Name) : Option (Name × Name) :=
    (ms.find? fun m => m.name == n && m.kind == .lib).map fun m => (m.pkg, m.target)
  let (s, h) :=
    roots.foldl (init := mkInput ms) fun acc (r, imps) =>
      addRoot acc r (imps.map fun n => (n, resolve n))
  let g ←
    match build s h with
    | .ok g =>
      pure g
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
      let docs := p.docModules.map (·.readResult p contents)
      match checkRules g p sets docs with
      | .error es =>
        return es
      | .ok vs =>
        return checkReport g p vs

def text (t : String) : Option (Except String String) :=
  some (.ok t)

def ok1 : Array String :=
  #["lean-deny: ok (1 rule)"]

def header (line : Nat) (index : Nat := 1) : String :=
  s!"doc-modules rule {index} (p.toml:{line}:0): r"

/-- A missing violation's lines, the rule's table on line 3 (after
`setXs`). -/
def missing (name : String) (line : Nat) : Array String :=
  #[s!"{header 3}: {name} is not listed in section 'Mods' of docs/m.md", s!"  {name}.lean: {name}",
    s!"  docs/m.md:{line}: section 'Mods'"]

/-- An extra violation's lines, the rule's table on line 3 (after
`setXs`). -/
def extra (name : String) (line : Nat) : Array String :=
  #[s!"{header 3}: section 'Mods' of docs/m.md lists {name}, which 'modules' does not match",
    s!"  docs/m.md:{line}: {name}"]

/-- `(case, modules, declared roots, policy, contents, expected lines)`. -/
def cases :
    Array
      (String ×
        Array M ×
        Array (Name × Array Name) × String × Option (Except String String) × Array String) :=
  #[ -- Holding.
    ("equal sets hold", mods, #[], rule "[\"mod:A.X!\", \"mod:A.Y!\"]",
      text "## Mods\n`A.X` `A.Y`\n", ok1),
    ("order and duplicates do not matter", mods, #[], setXs ++ rule "\"set:xs\"",
      text "## Mods\n- `A.Y`\n- `A.X`, `A.Y`\n### More\n`A.X`\n", ok1),
    ("names without the prefix are ignored", mods, #[], setXs ++ rule "\"set:xs\"",
      text "## Mods\n`A.X` `A.Y` `Nat.succ` `A` `B.A.X` `a/b`\n", ok1),
    ("a declared root counts", mods, #[(`A.R, #[`A.X])], setXs ++ rule "[\"set:xs\", \"mod:A.R!\"]",
      text "## Mods\n`A.X` `A.Y` `A.R`\n", ok1),
    ("an external in a mixed match is ignored", mods, #[],
      "[sets]\nmix = [\"mod:A.X!\", \"mod:A.Y!\", \"external:Init\"]\n" ++ rule "\"set:mix\"",
      text "## Mods\n`A.X` `A.Y`\n", ok1),
    -- Violations.
    ("a missing module", mods, #[], setXs ++ rule "\"set:xs\"", text "# T\n## Mods\n`A.X`\n",
      missing "A.Y" 2 ++ #["lean-deny: 1 violation in 1 of 1 rule"]),
    ("an extra name, at its first listing", mods, #[], setXs ++ rule "\"set:xs\"",
      text "## Mods\n`A.X` `A.Y`\n\n`A.Gone`\n`A.Gone`\n",
      extra "A.Gone" 4 ++ #["lean-deny: 1 violation in 1 of 1 rule"]),
    ("missing in display order, then extra in document order", mods, #[],
      setXs ++ rule "\"set:xs\"", text "## Mods\n`A.Z`\n`A.W` `A.Z`\n",
      missing "A.X" 1 ++ missing "A.Y" 1 ++ extra "A.Z" 2 ++ extra "A.W" 3 ++
        #["lean-deny: 4 violations in 1 of 1 rule"]),
    -- Errors.
    ("a selector that matches nothing", mods, #[], rule "\"mod:Nope!\"", text "## Mods\n",
      #["p.toml:5:10: selector 'mod:Nope!' in doc-modules rule 1 ('modules') matches no module: \
          no workspace module named 'Nope'"]),
    ("a selector that matches only external modules", mods, #[],
      rule "[\"mod:A.X!\", \"external:Init\"]", text "## Mods\n",
      #["p.toml:5:23: selector 'external:Init' in doc-modules rule 1 ('modules') matches only \
          modules outside the workspace, which a doc-modules rule does not compare"]),
    ("a module without the prefix", mods, #[], rule "\"mod:A\"", text "## Mods\n",
      #["p.toml:1:0: doc-modules rule 1: 'modules' matches A, which does not start with the \
          prefix 'A.', so the section cannot list it"]),
    ("several without the prefix", mods, #[], rule "\"mod:A\"" "Mods" "B.", text "## Mods\n",
      #["p.toml:1:0: doc-modules rule 1: 'modules' matches A (and 2 more), which does not start \
          with the prefix 'B.', so the section cannot list it"]),
    ("selector errors in source order, and no prefix error with them", mods, #[],
      rule "[\"mod:A\", \"external:Init\", \"mod:Nope!\"]", text "## Mods\n",
      #["p.toml:5:37: selector 'mod:Nope!' in doc-modules rule 1 ('modules') matches no \
          module: no workspace module named 'Nope'",
        "p.toml:5:20: selector 'external:Init' in doc-modules rule 1 ('modules') matches only \
          modules outside the workspace, which a doc-modules rule does not compare"]),
    ("no file", mods, #[], rule "\"mod:A.X!\"", none,
      #["p.toml:1:0: doc-modules rule 1: no file 'docs/m.md' in the workspace (looking for \
          heading 'Mods')"]),
    ("a read failure", mods, #[], rule "\"mod:A.X!\"", some (.error "boom"),
      #["p.toml:1:0: doc-modules rule 1: cannot read 'docs/m.md' (looking for heading 'Mods'): \
          boom"]),
    ("no heading", mods, #[], rule "\"mod:A.X!\"", text "## Other\n`A.X`\n",
      #["p.toml:1:0: doc-modules rule 1: no heading 'Mods' in 'docs/m.md'"]),
    ("a heading appearing twice", mods, #[], rule "\"mod:A.X!\"", text "## Mods\n# Mods\n",
      #["p.toml:1:0: doc-modules rule 1: heading 'Mods' appears 2 times in 'docs/m.md' (lines 1 \
          and 2)"]),
    ("a selector error and a file error are both reported", mods, #[], rule "\"mod:Nope!\"", none,
      #["p.toml:5:10: selector 'mod:Nope!' in doc-modules rule 1 ('modules') matches no module: \
          no workspace module named 'Nope'",
        "p.toml:1:0: doc-modules rule 1: no file 'docs/m.md' in the workspace (looking for \
          heading 'Mods')"]),
    ("an error in one rule hides another's violations", mods, #[],
      rule "\"mod:A.X!\"" ++ rule "\"mod:Nope!\"", text "## Mods\n",
      #["p.toml:11:10: selector 'mod:Nope!' in doc-modules rule 2 ('modules') matches no module: \
          no workspace module named 'Nope'"])]

/-- The rule's label, kind and count, and a missing `docs` entry. -/
def labelFailures : IO (Array String) := do
  let r : DocModulesRule := { index := 2, pos? := none }
  let mut fs := #[]
  unless r.label == "doc-modules rule 2" && r.ref.kind.toString == "doc-modules" do
    fs := fs.push s!"label: got {r.label}, kind {r.ref.kind}"
  match ← LeanDenyTest.Policy.load (rule "\"mod:A.X!\"" ++ rule "[\"mod:A.X!\", \"mod:A.Y!\"]") with
  | .ok p =>
    unless
      p.ruleCount == 2 && p.docModules.map (·.index) == #[1, 2] &&
        p.docModules.map (·.modules.size) == #[1, 2] do
      fs := fs.push s!"ruleCount: got {p.ruleCount}"
    match mkGraph mods with
    | .ok g =>
      match resolveSets g p with
      | .ok sets =>
        let want :=
          #["p.toml:1:0: doc-modules rule 1: internal error: its file was not read",
            "p.toml:7:0: doc-modules rule 2: internal error: its file was not read"]
        match checkDocModules g p sets #[] with
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
  for (name, ms, roots, src, contents, want) in cases do
    let got ← outcome ms src contents roots
    unless got == want do
      fs := fs.push s!"{name}: expected {repr want}, got {repr got}"
  return fs

end LeanDenyTest.DocModules
