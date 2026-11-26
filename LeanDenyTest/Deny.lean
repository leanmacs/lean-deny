import LeanDenyTest.Policy
import LeanDenyTest.Query

/-!
Tests of `[[deny]]` rules (`LeanDeny.Rules.Deny`) on hand-written graphs,
from the policy's TOML text to what `check` prints: direct and transitive
violations, their witnesses and order, wrappers and when one excuses
nothing, external and implicit targets, the errors a rule can give and their
order, and the report's lines.
-/

open Lean LeanDeny LeanDeny.Graph LeanDenyTest.Query

namespace LeanDenyTest.Deny

/-- Module `n` with plain imports `imports`, the `n`th on line `n`. -/
def m (n : Name) (imports : Array Name := #[]) : M :=
  { name := n, imports := imports.map plain }

/-- What `check` prints for policy `src` (as `p.toml`) over the graph of
`ms`, with package metadata `packages` when given: the errors, or the
report. -/
def outcome (ms : Array M) (src : String) (packages : Array PackageInfo := #[]) :
    IO (Array String) := do
  let g ←
    match mkGraph ms with
    | .ok g =>
      pure (if packages.isEmpty then g else { g with packages })
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
      match checkRules g p sets with
      | .error es =>
        return es
      | .ok vs =>
        return checkReport g p vs

/-- A deny table (lines: header, `from`, `to`, then `extra`, then
`reason = "r"`), `from` and `to` given as TOML values. -/
def rule (fromV toV : String) (extra : String := "") : String :=
  s!"[[deny]]\nfrom = {fromV}\nto = {toV}\n{extra}reason = \"r\"\n"

/-- `rule` with `transitive = true` (line 4). -/
def trule (fromV toV : String) (extra : String := "") : String :=
  rule fromV toV ("transitive = true\n" ++ extra)

def header (line : Nat) : String :=
  s!"deny rule 1 (p.toml:{line}:0): r"

def ok1 : Array String :=
  #["lean-deny: ok (1 rule)"]

def direct : String :=
  "none of its modules is in 'from' and imports a module in 'to'"

def transitive : String :=
  "none of its modules is the first wrapper on an import chain from 'from' to 'to'"

def inTo : String :=
  "it matches only modules in 'to', and a wrapper is a module allowed to import 'to', so list \
    the module that imports it instead"

/-- `(case, modules, policy, expected lines)`. -/
def cases : Array (String × Array M × String × Array String) :=
  #[ -- Direct rules.
    ("direct bites", #[m `A #[`T], m `T], rule "\"mod:A!\"" "\"mod:T!\"",
      #[header 1, "  A.lean:1: A imports T", "lean-deny: 1 violation in 1 of 1 rule"]),
    ("a file under the root is relative",
      #[{ m `A #[`T] with file? := some "/ws/sub/A.lean" }, m `T], rule "\"mod:A!\"" "\"mod:T!\"",
      #[header 1, "  sub/A.lean:1: A imports T", "lean-deny: 1 violation in 1 of 1 rule"]),
    ("one violation per pair",
      #[{ name := `A, imports := #[plain `T, (`T, { isMeta := true })] }, m `T],
      rule "\"mod:A!\"" "\"mod:T!\"",
      #[header 1, "  A.lean:1: A imports T", "lean-deny: 1 violation in 1 of 1 rule"]),
    ("direct ignores indirect; transitive does not", #[m `A #[`B], m `B #[`T], m `T],
      rule "\"mod:A!\"" "\"mod:T!\"" ++ trule "\"mod:A!\"" "\"mod:T!\"",
      #["deny rule 2 (p.toml:5:0): r", "  A.lean:1: A imports B", "  B.lean:1: B imports T",
        "lean-deny: 1 violation in 1 of 2 rules"]),
    ("direct order: importer by name, then source order",
      #[m `Z #[`T2, `T1], m `A #[`T2, `T1], m `T1, m `T2],
      rule "[\"mod:Z!\", \"mod:A!\"]" "[\"mod:T1!\", \"mod:T2!\"]",
      #[header 1, "  A.lean:1: A imports T2", header 1, "  A.lean:2: A imports T1", header 1,
        "  Z.lean:1: Z imports T2", header 1, "  Z.lean:2: Z imports T1",
        "lean-deny: 4 violations in 1 of 1 rule"]),
    -- Transitive rules.
    ("transitive, several steps", #[m `A #[`B], m `B #[`C], m `C #[`T], m `T],
      trule "\"mod:A!\"" "\"mod:T!\"",
      #[header 1, "  A.lean:1: A imports B", "  B.lean:1: B imports C", "  C.lean:1: C imports T",
        "lean-deny: 1 violation in 1 of 1 rule"]),
    ("the witness: fewest edges, then source order",
      #[m `A #[`B, `C], m `B #[`X, `T], m `C #[`T], m `X #[`T], m `T],
      trule "\"mod:A!\"" "\"mod:T!\"",
      #[header 1, "  A.lean:1: A imports B", "  B.lean:2: B imports T",
        "lean-deny: 1 violation in 1 of 1 rule"]),
    ("one violation per from module", #[m `A #[`B], m `B #[`T], m `T],
      trule "[\"mod:A!\", \"mod:B!\"]" "\"mod:T!\"",
      #[header 1, "  A.lean:1: A imports B", "  B.lean:1: B imports T", header 1,
        "  B.lean:1: B imports T", "lean-deny: 2 violations in 1 of 1 rule"]),
    ("a cycle that reaches the target", #[m `A #[`B], m `B #[`A, `T], m `T],
      trule "\"mod:A!\"" "\"mod:T!\"",
      #[header 1, "  A.lean:1: A imports B", "  B.lean:2: B imports T",
        "lean-deny: 1 violation in 1 of 1 rule"]),
    ("a cycle that does not", #[m `A #[`B], m `B #[`A], m `T], trule "\"mod:A!\"" "\"mod:T!\"",
      ok1),
    -- Wrappers.
    ("a direct wrapper in from excuses its imports", #[m `A #[`W], m `W #[`T], m `T],
      rule "[\"mod:A!\", \"mod:W!\"]" "\"mod:T!\"" "wrappers = \"mod:W!\"\n", ok1),
    ("a wrapper selector needs one module that excuses", #[m `A, m `W.One #[`T], m `W.Two, m `T],
      rule "[\"mod:A!\", \"mod:W\"]" "\"mod:T!\"" "wrappers = \"mod:W\"\n", ok1),
    ("direct: a wrapper outside from excuses nothing", #[m `A, m `W #[`T], m `T],
      rule "\"mod:A!\"" "\"mod:T!\"" "wrappers = \"mod:W!\"\n",
      #[s!"p.toml:4:11: selector 'mod:W!' in deny rule 1 ('wrappers') excuses nothing: {direct}"]),
    ("direct: a wrapper in from with no import into to excuses nothing", #[m `A, m `W #[`A], m `T],
      rule "[\"mod:A!\", \"mod:W!\"]" "\"mod:T!\"" "wrappers = \"mod:W!\"\n",
      #[s!"p.toml:4:11: selector 'mod:W!' in deny rule 1 ('wrappers') excuses nothing: {direct}"]),
    ("transitive: a wrapper outside from", #[m `A #[`W], m `W #[`T], m `T],
      trule "\"mod:A!\"" "\"mod:T!\"" "wrappers = \"mod:W!\"\n", ok1),
    ("transitive: a wrapper inside from", #[m `A #[`W], m `W #[`T], m `T],
      trule "[\"mod:A!\", \"mod:W!\"]" "\"mod:T!\"" "wrappers = \"mod:W!\"\n", ok1),
    ("transitive: a wrapper excuses only the chains through it",
      #[m `A #[`W, `Y], m `W #[`T], m `Y #[`T], m `T],
      trule "\"mod:A!\"" "\"mod:T!\"" "wrappers = \"mod:W!\"\n",
      #[header 1, "  A.lean:2: A imports Y", "  Y.lean:1: Y imports T",
        "lean-deny: 1 violation in 1 of 1 rule"]),
    ("transitive: a wrapper not reached excuses nothing", #[m `A, m `V #[`W], m `W #[`T], m `T],
      trule "\"mod:A!\"" "\"mod:T!\"" "wrappers = \"mod:W!\"\n",
      #[s!"p.toml:5:11: selector 'mod:W!' in deny rule 1 ('wrappers') excuses nothing: \
          {transitive}"]),
    ("transitive: a wrapper that reaches nothing in to excuses nothing",
      #[m `A #[`W, `T], m `W #[`X], m `X, m `T],
      trule "\"mod:A!\"" "\"mod:T!\"" "wrappers = \"mod:W!\"\n",
      #[s!"p.toml:5:11: selector 'mod:W!' in deny rule 1 ('wrappers') excuses nothing: \
          {transitive}"]),
    ("transitive: of two wrappers in series, only the first excuses",
      #[m `A #[`W1], m `W1 #[`W2], m `W2 #[`T], m `T],
      trule "\"mod:A!\"" "\"mod:T!\"" "wrappers = [\"mod:W1!\", \"mod:W2!\"]\n",
      #[s!"p.toml:5:23: selector 'mod:W2!' in deny rule 1 ('wrappers') excuses nothing: \
          {transitive}"]),
    ("transitive: a second wrapper in from is a first wrapper too",
      #[m `A #[`W1], m `W1 #[`W2], m `W2 #[`T], m `T],
      trule "[\"mod:A!\", \"mod:W2!\"]" "\"mod:T!\"" "wrappers = [\"mod:W1!\", \"mod:W2!\"]\n",
      ok1),
    ("transitive: a wrapper reached only through to excuses nothing, and errors hide violations",
      #[m `A #[`T], m `T #[`W], m `W #[`T2], m `T2],
      trule "\"mod:A!\"" "[\"mod:T!\", \"mod:T2!\"]" "wrappers = \"mod:W!\"\n",
      #[s!"p.toml:5:11: selector 'mod:W!' in deny rule 1 ('wrappers') excuses nothing: \
          {transitive}"]),
    ("a wrapper in to excuses nothing, in either mode", #[m `A #[`W], m `W #[`T], m `T],
      rule "\"mod:A!\"" "[\"mod:W!\", \"mod:T!\"]" "wrappers = \"mod:W!\"\n" ++
        trule "\"mod:A!\"" "[\"mod:W!\", \"mod:T!\"]" "wrappers = \"mod:W!\"\n",
      #[s!"p.toml:4:11: selector 'mod:W!' in deny rule 1 ('wrappers') excuses nothing: {inTo}",
        s!"p.toml:10:11: selector 'mod:W!' in deny rule 2 ('wrappers') excuses nothing: {inTo}"]),
    ("transitive: a wrapper in to that reaches no other to module excuses nothing",
      #[m `A #[`W], m `W, m `T],
      trule "\"mod:A!\"" "[\"mod:W!\", \"mod:T!\"]" "wrappers = \"mod:W!\"\n",
      #[s!"p.toml:5:11: selector 'mod:W!' in deny rule 1 ('wrappers') excuses nothing: {inTo}"]),
    -- `mod:W` matches W, in `to`, and W.Ok, outside it, which B reaches.
    ("transitive: reaching a wrapper in to is still a violation",
      #[m `A #[`W, `B], m `W #[`T], m `B #[`W.Ok], m `W.Ok #[`T], m `T],
      trule "\"mod:A!\"" "[\"mod:W!\", \"mod:T!\"]" "wrappers = \"mod:W\"\n",
      #[header 1, "  A.lean:1: A imports W", "lean-deny: 1 violation in 1 of 1 rule"]),
    ("transitive: a selector partly in to, its other modules unused, excuses nothing",
      #[m `A #[`W], m `W #[`T], m `W.Ok #[`T], m `T],
      trule "\"mod:A!\"" "[\"mod:W!\", \"mod:T!\"]" "wrappers = \"mod:W\"\n",
      #[s!"p.toml:5:11: selector 'mod:W' in deny rule 1 ('wrappers') excuses nothing: \
          {transitive}"]),
    -- External and implicit targets.
    ("direct: an external target", #[m `A #[`Lean.Elab.Command]],
      rule "\"mod:A!\"" "\"external:Lean.Elab\"",
      #[header 1, "  A.lean:1: A imports Lean.Elab.Command",
        "lean-deny: 1 violation in 1 of 1 rule"]),
    ("transitive: a chain ends at an external target", #[m `A #[`B], m `B #[`Lean.Elab.Command]],
      trule "\"mod:A!\"" "\"external:Lean.Elab\"",
      #[header 1, "  A.lean:1: A imports B", "  B.lean:1: B imports Lean.Elab.Command",
        "lean-deny: 1 violation in 1 of 1 rule"]),
    ("the implicit Init import counts", #[m `A], rule "\"mod:A!\"" "\"external:Init\"",
      #[header 1, "  A.lean: A imports Init (implicit)", "lean-deny: 1 violation in 1 of 1 rule"]),
    -- Errors.
    ("from matches nothing", #[m `A, m `T], rule "\"mod:Nope!\"" "\"mod:T!\"",
      #["p.toml:2:7: selector 'mod:Nope!' in deny rule 1 ('from') matches no module: no \
          workspace module named 'Nope'"]),
    ("to matches nothing", #[m `A, m `T], rule "\"mod:A!\"" "\"mod:Nope!\"",
      #["p.toml:3:5: selector 'mod:Nope!' in deny rule 1 ('to') matches no module: no \
          workspace module named 'Nope'"]),
    ("a wrapper matches nothing", #[m `A, m `T],
      rule "\"mod:A!\"" "\"mod:T!\"" "wrappers = \"mod:Nope!\"\n",
      #["p.toml:4:11: selector 'mod:Nope!' in deny rule 1 ('wrappers') matches no module: no \
          workspace module named 'Nope'"]),
    ("from matches only externals; matching nothing comes first", #[m `A #[`Lean.Data.Json], m `T],
      rule "[\"external:Lean\", \"mod:Nope!\"]" "\"mod:T!\"",
      #["p.toml:2:25: selector 'mod:Nope!' in deny rule 1 ('from') matches no module: no \
          workspace module named 'Nope'",
        "p.toml:2:8: selector 'external:Lean' in deny rule 1 ('from') matches only modules \
          outside the workspace, which import nothing in the graph"]),
    ("from and to overlap, listed in display order", #[m `App, m `App.Shared, m `AppTest, m `T],
      rule "[\"mod:App\", \"mod:AppTest!\"]" "[\"mod:AppTest!\", \"mod:App.Shared!\", \"mod:T!\"]",
      #["p.toml:1:0: deny rule 1: 'from' and 'to' share modules: App.Shared, AppTest (take them \
          out of one side with a set's 'except')"]),
    ("errors of two rules, in rule order", #[m `A #[`T], m `T],
      rule "\"mod:A!\"" "\"mod:Nope!\"" ++ rule "\"mod:Gone!\"" "\"mod:T!\"",
      #["p.toml:3:5: selector 'mod:Nope!' in deny rule 1 ('to') matches no module: no \
          workspace module named 'Nope'",
        "p.toml:6:7: selector 'mod:Gone!' in deny rule 2 ('from') matches no module: no \
          workspace module named 'Gone'"]),
    ("an error beside a broken rule is reported alone", #[m `A #[`T], m `T],
      rule "\"mod:A!\"" "\"mod:A!\"" ++ rule "\"mod:A!\"" "\"mod:T!\"",
      #["p.toml:1:0: deny rule 1: 'from' and 'to' share modules: A (take them out of one side \
          with a set's 'except')"]),
    ("a rule whose to fails reports no unused wrapper", #[m `A, m `W, m `T],
      rule "\"mod:A!\"" "\"mod:Nope!\"" "wrappers = \"mod:W!\"\n",
      #["p.toml:3:5: selector 'mod:Nope!' in deny rule 1 ('to') matches no module: no \
          workspace module named 'Nope'"]),
    -- Sets.
    ("a set in a rule, with an except", #[m `A #[`C.Inner, `C], m `C, m `C.Inner],
      "[sets]\ncore = { select = [\"mod:C\"], except = [\"mod:C.Inner!\"] }\n\n" ++
        rule "\"mod:A!\"" "\"set:core\"",
      #[header 4, "  A.lean:2: A imports C", "lean-deny: 1 violation in 1 of 1 rule"])]

/-- `okLine`, `summaryLine` and a violation's header without a position. -/
def renderingFailures : Array String :=
  let v : Violation := { label := "deny rule 1", pos? := none, reason := "r", chain := #[] }
  let want :=
    [(okLine 0, "lean-deny: ok (0 rules)"), (okLine 1, "lean-deny: ok (1 rule)"),
      (okLine 2, "lean-deny: ok (2 rules)"),
      (summaryLine 1 1 1, "lean-deny: 1 violation in 1 of 1 rule"),
      (summaryLine 3 2 4, "lean-deny: 3 violations in 2 of 4 rules"),
      (", ".intercalate (v.render default "p.toml").toList, "deny rule 1 (p.toml): r")]
  want.toArray.filterMap fun (got, w) =>
    if got == w then none else some s!"expected {repr w}, got {repr got}"

def run : IO (Array String) := do
  let mut fs := renderingFailures
  for (name, ms, src, want) in cases do
    let got ← outcome ms src
    unless got == want do
      fs := fs.push s!"{name}: expected {repr want}, got {repr got}"
  return fs

end LeanDenyTest.Deny
