import LeanDenyTest.Deny

/-!
Tests of `[[co-reach]]` rules (`LeanDeny.Rules.CoReach`) on hand-written
graphs, from the policy's TOML text to what `check` prints: the closure
(reflexive for both `if-reaches` and `must-reach`, transitive, through `meta`
imports), the nearest-trigger witness, one violation per root naming every
missing module, untriggered roots skipped, external modules dropped, declared
roots, the errors a rule can give and their order, and loading.
-/

open Lean LeanDeny LeanDeny.Graph LeanDenyTest.Query

namespace LeanDenyTest.CoReach

open LeanDenyTest.Deny (m outcome)

/-- A co-reach table (lines: header, `roots`, `if-reaches`, `must-reach`,
`reason = "r"`), each selector field given as a TOML value. -/
def rule (rootsV ifV mustV : String) : String :=
  s!"[[co-reach]]\nroots = {rootsV}\nif-reaches = {ifV}\nmust-reach = {mustV}\nreason = \"r\"\n"

def header (line : Nat) (index : Nat := 1) : String :=
  s!"co-reach rule {index} (p.toml:{line}:0): r"

def ok1 : Array String :=
  #["lean-deny: ok (1 rule)"]

/-- `(case, modules, declared roots, policy, expected lines)`. -/
def cases : Array (String × Array M × Array (Name × Array Name) × String × Array String) :=
  #[ -- Holding.
    ("holds, transitive", #[m `R #[`A, `B], m `A #[`T], m `B #[`M], m `T, m `M], #[],
      rule "\"mod:R!\"" "\"mod:T!\"" "\"mod:M!\"", ok1),
    ("a root that is a must-reach module reaches itself", #[m `A #[`T], m `T], #[],
      rule "\"mod:A!\"" "\"mod:T!\"" "\"mod:A!\"", ok1),
    ("a meta import counts",
      #[{ name := `A, imports := #[(`T, { isMeta := true }), (`M, {})] }, m `T, m `M], #[],
      rule "\"mod:A!\"" "\"mod:T!\"" "\"mod:M!\"", ok1),
    ("an untriggered root is skipped", #[m `A #[`T, `M], m `C, m `T, m `M], #[],
      rule "[\"mod:A!\", \"mod:C!\"]" "\"mod:T!\"" "\"mod:M!\"", ok1),
    -- Violations.
    ("a root that is an if-reaches module triggers itself", #[m `A, m `B], #[],
      rule "\"mod:A!\"" "\"mod:A!\"" "\"mod:B!\"",
      #[s!"{header 1}: A is in 'if-reaches' but does not reach B", "  A.lean: A",
        "lean-deny: 1 violation in 1 of 1 rule"]),
    ("every missing module, one violation, nearest trigger",
      #[m `A #[`X, `T1], m `X #[`T2], m `T1, m `T2, m `M1, m `M2, m `M3], #[],
      rule "\"mod:A!\"" "[\"mod:T2!\", \"mod:T1!\"]" "[\"mod:M3!\", \"mod:M1!\", \"mod:M2!\"]",
      #[s!"{header 1}: A reaches T1 but not M1, M2 and M3", "  A.lean:2: A imports T1",
        "lean-deny: 1 violation in 1 of 1 rule"]),
    ("only the missing modules are named", #[m `A #[`B], m `B #[`T, `M1], m `T, m `M1, m `M2], #[],
      rule "\"mod:A!\"" "\"mod:T!\"" "[\"mod:M1!\", \"mod:M2!\"]",
      #[s!"{header 1}: A reaches T but not M2", "  A.lean:1: A imports B",
        "  B.lean:1: B imports T", "lean-deny: 1 violation in 1 of 1 rule"]),
    ("one per root, in display order", #[m `B #[`T], m `A #[`T], m `C #[`T, `M], m `T, m `M], #[],
      rule "[\"mod:C!\", \"mod:B!\", \"mod:A!\"]" "\"mod:T!\"" "\"mod:M!\"",
      #[s!"{header 1}: A reaches T but not M", "  A.lean:1: A imports T",
        s!"{header 1}: B reaches T but not M", "  B.lean:1: B imports T",
        "lean-deny: 2 violations in 1 of 1 rule"]),
    ("external modules a selector matches are dropped",
      #[{ name := `A, isPrelude := true, imports := #[(`T, {})] }, m `T, m `M], #[],
      "[sets]\nr = [\"mod:A!\", \"external:Init\"]\nt = [\"mod:T!\", \"external:Init\"]\n" ++
        "s = [\"mod:M!\", \"external:Init\"]\n\n" ++
        rule "\"set:r\"" "\"set:t\"" "\"set:s\"",
      #[s!"{header 6}: A reaches T but not M", "  A.lean:1: A imports T",
        "lean-deny: 1 violation in 1 of 1 rule"]),
    ("a declared root counts", #[m `T, m `M], #[(`R, #[`T])],
      rule "\"mod:R!\"" "\"mod:T!\"" "\"mod:M!\"",
      #[s!"{header 1}: R reaches T but not M", "  gen/R.lean:1: R imports T",
        "lean-deny: 1 violation in 1 of 1 rule"]),
    ("after the other kinds, in rule order", #[m `A #[`T], m `T, m `X], #[],
      rule "\"mod:A!\"" "\"mod:T!\"" "\"mod:X!\"" ++
        "[[reachable]]\nfrom = \"mod:A!\"\nmust-cover = \"mod:X!\"\nreason = \"c\"\n",
      #["reachable rule 1 (p.toml:6:0): c: X is outside the import closure of A", "  X.lean: X",
        s!"{header 1}: A reaches T but not X", "  A.lean:1: A imports T",
        "lean-deny: 2 violations in 2 of 2 rules"]),
    -- Errors.
    ("every selector error, in order", #[m `A #[`Lean.Data.Json], m `B], #[],
      rule "[\"external:Lean\", \"mod:Nope!\"]" "[\"external:Lean\", \"mod:Gone!\"]"
        "[\"external:Init\", \"mod:B!\"]",
      #["p.toml:2:26: selector 'mod:Nope!' in co-reach rule 1 ('roots') matches no module: no \
          workspace module named 'Nope'",
        "p.toml:3:31: selector 'mod:Gone!' in co-reach rule 1 ('if-reaches') matches no module: \
          no workspace module named 'Gone'",
        "p.toml:2:9: selector 'external:Lean' in co-reach rule 1 ('roots') matches only modules \
          outside the workspace, which import nothing in the graph",
        "p.toml:3:14: selector 'external:Lean' in co-reach rule 1 ('if-reaches') matches only \
          modules outside the workspace, which a rule about reach does not check",
        "p.toml:4:14: selector 'external:Init' in co-reach rule 1 ('must-reach') matches only \
          modules outside the workspace, which a rule about reach does not check"]),
    ("no root reaches if-reaches: the rule holds of nothing", #[m `A, m `T #[`A], m `M], #[],
      rule "\"mod:A!\"" "\"mod:T!\"" "\"mod:M!\"",
      #["p.toml:1:0: co-reach rule 1: no module of 'roots' reaches a module of 'if-reaches', so \
          the rule holds of nothing"]),
    ("holds of nothing is not reported beside another error", #[m `A, m `T], #[],
      rule "[\"mod:A!\", \"mod:Nope!\"]" "\"mod:T!\"" "\"mod:A!\"",
      #["p.toml:2:19: selector 'mod:Nope!' in co-reach rule 1 ('roots') matches no module: no \
          workspace module named 'Nope'"]),
    ("an error in one rule hides another's violations", #[m `A, m `B], #[],
      rule "\"mod:A!\"" "\"mod:A!\"" "\"mod:B!\"" ++ rule "\"mod:A!\"" "\"mod:B!\"" "\"mod:A!\"",
      #["p.toml:6:0: co-reach rule 2: no module of 'roots' reaches a module of 'if-reaches', so \
          the rule holds of nothing"])]

/-- `(case, policy, expected lines)`: what loading reports, over a graph of
one module `A`. -/
def loadCases : Array (String × String × Array String) :=
  #[("co-reach = 1", "co-reach = 1\n",
      #["load: p.toml:1:11: 'co-reach' must be an array of tables, such as [[co-reach]]"]),
    ("co-reach = []", "co-reach = []\n", #["load: p.toml:1:11: 'co-reach' is empty (omit it)"]),
    ("co-reach = [1]", "co-reach = [1]\n",
      #["load: p.toml:1:12: co-reach rule 1 must be a table, found an integer"]),
    ("missing keys", "[[co-reach]]\n",
      #["load: p.toml:1:0: co-reach rule 1 has no 'roots'",
        "load: p.toml:1:0: co-reach rule 1 has no 'if-reaches'",
        "load: p.toml:1:0: co-reach rule 1 has no 'must-reach'",
        "load: p.toml:1:0: co-reach rule 1 has no 'reason'"]),
    ("wrong types and an unknown key",
      "[[co-reach]]\nroots = 1\nif-reaches = []\nmust-reach = [2]\nreason = true\n\
        transitive = true\n",
      #["load: p.toml:2:8: co-reach rule 1: 'roots' must be a selector or an array of selectors, \
          found an integer",
        "load: p.toml:3:13: co-reach rule 1: 'if-reaches' is empty",
        "load: p.toml:4:14: co-reach rule 1 ('must-reach'): expected a selector string, found an \
          integer",
        "load: p.toml:5:9: co-reach rule 1: 'reason' must be a string, found a boolean",
        "load: p.toml:6:13: co-reach rule 1: unknown key 'transitive' (expected roots, \
          if-reaches, must-reach, reason)"]),
    ("a blank reason",
      "[[co-reach]]\nroots = \"mod:A!\"\nif-reaches = \"mod:A\"\nmust-reach = \"mod:A\"\n\
        reason = \" \"\n",
      #["load: p.toml:5:9: co-reach rule 1: 'reason' is empty"]),
    ("an unknown set", rule "\"mod:A!\"" "\"mod:A!\"" "\"set:nope\"",
      #["load: p.toml:4:13: selector 'set:nope' in co-reach rule 1 ('must-reach') names an \
          unknown set (the policy defines no sets)"])]

/-- The rule's label, kind and count. -/
def labelFailures : IO (Array String) := do
  let r : CoReachRule := { index := 2, pos? := none }
  let mut fs := #[]
  unless r.label == "co-reach rule 2" && r.ref.kind.toString == "co-reach" do
    fs := fs.push s!"label: got {r.label}, kind {r.ref.kind}"
  match
    ←
      LeanDenyTest.Policy.load
          (rule "\"mod:A!\"" "\"mod:B\"" "\"mod:C\"" ++
            rule "\"mod:A!\"" "\"mod:C\"" "\"mod:B\"") with
  | .ok p =>
    unless p.ruleCount == 2 && p.coReach.map (·.index) == #[1, 2] do
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

end LeanDenyTest.CoReach
