import LeanDenyTest.Deny

/-!
Tests of `[[reachable]]` rules (`LeanDeny.Rules.Reachable`) on hand-written
graphs, from the policy's TOML text to what `check` prints: the closure (reflexive,
transitive, through `meta` imports), one violation per uncovered module and
their order, external `must-cover` modules ignored, declared roots, the
errors a rule can give and their order, and loading.
-/

open Lean LeanDeny LeanDeny.Graph LeanDenyTest.Query

namespace LeanDenyTest.Reachable

open LeanDenyTest.Deny (m outcome)

/-- A reachable table (lines: header, `from`, `must-cover`,
`reason = "r"`), `from` and `must-cover` given as TOML values. -/
def rule (fromV coverV : String) : String :=
  s!"[[reachable]]\nfrom = {fromV}\nmust-cover = {coverV}\nreason = \"r\"\n"

def header (line : Nat) (index : Nat := 1) : String :=
  s!"reachable rule {index} (p.toml:{line}:0): r"

def ok1 : Array String :=
  #["lean-deny: ok (1 rule)"]

/-- `(case, modules, declared roots, policy, expected lines)`. -/
def cases : Array (String × Array M × Array (Name × Array Name) × String × Array String) :=
  #[ -- The closure.
    ("holds, reflexive and transitive", #[m `R #[`R.A], m `R.A #[`R.B], m `R.B], #[],
      rule "\"mod:R!\"" "\"mod:R\"", ok1),
    ("a from module covers itself", #[m `A #[`C], m `B, m `C], #[],
      rule "[\"mod:A!\", \"mod:B!\"]" "[\"mod:B!\", \"mod:C!\"]", ok1),
    ("several hops", #[m `A #[`B], m `B #[`C], m `C #[`D], m `D], #[],
      rule "\"mod:A!\"" "\"mod:D!\"", ok1),
    ("a meta import counts", #[{ name := `A, imports := #[(`B, { isMeta := true })] }, m `B], #[],
      rule "\"mod:A!\"" "\"mod:B!\"", ok1),
    ("an import all counts", #[{ name := `A, imports := #[(`B, { isAll := true })] }, m `B], #[],
      rule "\"mod:A!\"" "\"mod:B!\"", ok1),
    ("an import does not cover its importer", #[m `A, m `B #[`A]], #[],
      rule "\"mod:A!\"" "\"mod:B!\"",
      #[s!"{header 1}: B is outside the import closure of A", "  B.lean: B",
        "lean-deny: 1 violation in 1 of 1 rule"]),
    -- Violations.
    ("one per uncovered module, in display order",
      #[m `A #[`Z.B], m `Z, m `Z.B, m `Z.A, { m `Z.C with file? := some "/ws/sub/Z/C.lean" }], #[],
      rule "\"mod:A!\"" "\"mod:Z\"",
      #[s!"{header 1}: Z is outside the import closure of A", "  Z.lean: Z",
        s!"{header 1}: Z.A is outside the import closure of A", "  Z.A.lean: Z.A",
        s!"{header 1}: Z.C is outside the import closure of A", "  sub/Z/C.lean: Z.C",
        "lean-deny: 3 violations in 1 of 1 rule"]),
    ("two from modules are named", #[m `A, m `B, m `C], #[],
      rule "[\"mod:B!\", \"mod:A!\"]" "\"mod:C!\"",
      #[s!"{header 1}: C is outside the import closure of A and B", "  C.lean: C",
        "lean-deny: 1 violation in 1 of 1 rule"]),
    ("four from modules are counted", #[m `A, m `B, m `C, m `D, m `E], #[],
      rule "[\"mod:A!\", \"mod:B!\", \"mod:C!\", \"mod:D!\"]" "\"mod:E!\"",
      #[s!"{header 1}: E is outside the import closure of 'from' (4 modules)", "  E.lean: E",
        "lean-deny: 1 violation in 1 of 1 rule"]),
    -- A prelude module does not reach Init, which must-cover matches but is ignored.
    ("external modules of must-cover are ignored", #[{ name := `A, isPrelude := true }, m `B], #[],
      "[sets]\ns = [\"mod:B!\", \"external:Init\"]\n\n" ++ rule "\"mod:A!\"" "\"set:s\"",
      #[s!"{header 4}: B is outside the import closure of A", "  B.lean: B",
        "lean-deny: 1 violation in 1 of 1 rule"]),
    ("a declared root counts, with its file", #[m `A, m `B], #[(`R, #[`A]), (`S, #[`A])],
      rule "\"mod:R!\"" "[\"mod:A!\", \"mod:B!\", \"mod:S!\"]",
      #[s!"{header 1}: B is outside the import closure of R", "  B.lean: B",
        s!"{header 1}: S is outside the import closure of R", "  gen/S.lean: S",
        "lean-deny: 2 violations in 1 of 1 rule"]),
    ("after the other kinds, in rule order", #[m `A #[`T], m `T, m `X], #[],
      rule "\"mod:A!\"" "\"mod:X!\"" ++
        "[[deny]]\nfrom = \"mod:A!\"\nto = \"mod:T!\"\nreason = \"d\"\n" ++
        rule "\"mod:T!\"" "\"mod:A!\"",
      #["deny rule 1 (p.toml:5:0): d", "  A.lean:1: A imports T",
        s!"{header 1}: X is outside the import closure of A", "  X.lean: X",
        s!"{header 9 2}: A is outside the import closure of T", "  A.lean: A",
        "lean-deny: 3 violations in 3 of 3 rules"]),
    -- Errors.
    ("every selector error, in order", #[m `A #[`Lean.Data.Json], m `B], #[],
      rule "[\"external:Lean\", \"mod:Nope!\"]" "[\"external:Init\", \"mod:Gone!\"]",
      #["p.toml:2:25: selector 'mod:Nope!' in reachable rule 1 ('from') matches no module: no \
          workspace module named 'Nope'",
        "p.toml:3:31: selector 'mod:Gone!' in reachable rule 1 ('must-cover') matches no module: \
          no workspace module named 'Gone'",
        "p.toml:2:8: selector 'external:Lean' in reachable rule 1 ('from') matches only modules \
          outside the workspace, which import nothing in the graph",
        "p.toml:3:14: selector 'external:Init' in reachable rule 1 ('must-cover') matches only \
          modules outside the workspace, which a rule about reach does not check"]),
    ("must-cover inside from checks nothing", #[m `A #[`B], m `B], #[],
      rule "[\"mod:A!\", \"mod:B!\"]" "\"mod:B!\"",
      #["p.toml:1:0: reachable rule 1: every module of 'must-cover' is in 'from', so it checks \
          nothing"]),
    ("checks nothing is not reported beside another error", #[m `A], #[],
      rule "[\"mod:A!\", \"mod:Nope!\"]" "\"mod:A!\"",
      #["p.toml:2:18: selector 'mod:Nope!' in reachable rule 1 ('from') matches no module: no \
          workspace module named 'Nope'"]),
    ("an error in one rule hides another's violations", #[m `A, m `B], #[],
      rule "\"mod:A!\"" "\"mod:B!\"" ++ rule "\"mod:A!\"" "\"lib:Nope\"",
      #["p.toml:7:13: selector 'lib:Nope' in reachable rule 2 ('must-cover') matches no module: \
          no package has a lean_lib named 'Nope'"])]

/-- `(case, policy, expected lines)`: what loading reports, over a graph of
one module `A`. -/
def loadCases : Array (String × String × Array String) :=
  #[("reachable = 1", "reachable = 1\n",
      #["load: p.toml:1:12: 'reachable' must be an array of tables, such as [[reachable]]"]),
    ("reachable = []", "reachable = []\n", #["load: p.toml:1:12: 'reachable' is empty (omit it)"]),
    ("reachable = [1]", "reachable = [1]\n",
      #["load: p.toml:1:13: reachable rule 1 must be a table, found an integer"]),
    ("missing keys", "[[reachable]]\n",
      #["load: p.toml:1:0: reachable rule 1 has no 'from'",
        "load: p.toml:1:0: reachable rule 1 has no 'must-cover'",
        "load: p.toml:1:0: reachable rule 1 has no 'reason'"]),
    ("wrong types and an unknown key",
      "[[reachable]]\nfrom = 1\nmust-cover = []\nreason = true\ntransitive = true\n",
      #["load: p.toml:2:7: reachable rule 1: 'from' must be a selector or an array of selectors, \
          found an integer",
        "load: p.toml:3:13: reachable rule 1: 'must-cover' is empty",
        "load: p.toml:4:9: reachable rule 1: 'reason' must be a string, found a boolean",
        "load: p.toml:5:13: reachable rule 1: unknown key 'transitive' (expected from, must-cover, \
          reason)"]),
    ("a blank reason", "[[reachable]]\nfrom = \"mod:A!\"\nmust-cover = \"mod:A\"\nreason = \" \"\n",
      #["load: p.toml:4:9: reachable rule 1: 'reason' is empty"]),
    ("an unknown set", rule "\"set:nope\"" "\"mod:A\"",
      #["load: p.toml:2:7: selector 'set:nope' in reachable rule 1 ('from') names an unknown set \
          (the policy defines no sets)"])]

/-- The rule's label, kind and count. -/
def labelFailures : IO (Array String) := do
  let r : ReachableRule := { index := 2, pos? := none }
  let mut fs := #[]
  unless r.label == "reachable rule 2" && r.ref.kind.toString == "reachable" do
    fs := fs.push s!"label: got {r.label}, kind {r.ref.kind}"
  match
    ← LeanDenyTest.Policy.load (rule "\"mod:A!\"" "\"mod:B\"" ++ rule "\"mod:A!\"" "\"mod:C\"") with
  | .ok p =>
    unless p.ruleCount == 2 && p.reachable.map (·.index) == #[1, 2] do
      fs := fs.push s!"ruleCount: got {p.ruleCount}"
  | .error es =>
    fs := fs.push s!"ruleCount: load failed: {es}"
  return fs

def run : IO (Array String) := do
  let mut fs ← labelFailures
  for (name, ms, roots, src, want) in cases do
    let got ← outcome ms src (roots := roots)
    unless got == want do
      fs := fs.push s!"{name}: expected {repr want}, got {repr got}"
  for (name, src, want) in loadCases do
    let got ← outcome #[m `A] src
    unless got == want do
      fs := fs.push s!"{name}: expected {repr want}, got {repr got}"
  return fs

end LeanDenyTest.Reachable
