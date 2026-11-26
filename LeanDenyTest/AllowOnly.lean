import LeanDenyTest.Deny

/-!
Tests of `[[allow-only]]` rules (`LeanDeny.Rules.AllowOnly`) on hand-written
graphs, from the policy's TOML text to what `check` prints: which imports
are checked (those leaving the importer's package, the implicit `Init`
included), the most specific rule governing a module, `except`, the errors a
rule or a group of rules can give and their order, and deny and allow-only
rules together.
-/

open Lean LeanDeny LeanDeny.Graph LeanDenyTest.Query

namespace LeanDenyTest.AllowOnly

/-- Module `n` of package `pkg` with plain imports `imports`, the `n`th on
line `n`. -/
def mp (pkg : Name) (n : Name) (imports : Array Name := #[]) : M :=
  { name := n, imports := imports.map plain, pkg }

/-- An allow-only table (lines: header, `from`, then `extra`, then `allow`,
then `reason = "r"`), `from` and `allow` given as TOML values. -/
def arule (fromV allowV : String) (extra : String := "") : String :=
  s!"[[allow-only]]\nfrom = {fromV}\n{extra}allow = {allowV}\nreason = \"r\"\n"

/-- The header of allow-only rule `i`, its table on line `line`. -/
def hdr (i line : Nat) : String :=
  s!"allow-only rule {i} (p.toml:{line}:0): r"

def ok1 : Array String :=
  #["lean-deny: ok (1 rule)"]

def init : String :=
  "\"external:Init\""

/-- The tail of an unused allow selector's message. -/
def allowsNothing : String :=
  "allows nothing: no module the rule governs imports a module it matches from outside its own \
    package"

def overlap2 (mods pronoun : String) : String :=
  s!"overlap without nesting: both cover {mods}, but each also covers a module the other does \
    not, so neither is the most specific for {pronoun} (nest one rule's modules inside the \
    other's, or take the shared modules out of one with 'except')"

/-- `(case, modules, policy, expected lines)`. -/
def cases : Array (String × Array M × String × Array String) :=
  #[ -- What is checked.
    ("bites", #[mp `a `A #[`X], mp `x `X], arule "\"mod:A!\"" init,
      #[hdr 1 1, "  A.lean:1: A imports X", "lean-deny: 1 violation in 1 of 1 rule"]),
    ("holds", #[mp `a `A #[`X], mp `x `X], arule "\"mod:A!\"" s!"[\"mod:X!\", {init}]", ok1),
    ("imports within the package are not checked", #[mp `a `A #[`B], mp `a `B],
      arule "\"mod:A!\"" init, ok1),
    ("an external module must be allowed", #[mp `a `A #[`Std.Data.HashMap]],
      arule "\"mod:A!\"" init,
      #[hdr 1 1, "  A.lean:1: A imports Std.Data.HashMap",
        "lean-deny: 1 violation in 1 of 1 rule"]),
    ("an allowed external module", #[mp `a `A #[`Std.Data.HashMap]],
      arule "\"mod:A!\"" s!"[\"external:Std\", {init}]", ok1),
    ("the implicit Init import counts, once per pair", #[mp `a `A #[`X], mp `x `X],
      arule "\"mod:A!\"" "\"mod:X!\"",
      #[hdr 1 1, "  A.lean: A imports Init (implicit)", "lean-deny: 1 violation in 1 of 1 rule"]),
    ("one violation per pair",
      #[{ mp `a `A with imports := #[plain `X, (`X, { isMeta := true })] }, mp `x `X],
      arule "\"mod:A!\"" init,
      #[hdr 1 1, "  A.lean:1: A imports X", "lean-deny: 1 violation in 1 of 1 rule"]),
    ("order: importer in display order, then source order",
      #[mp `a `Z #[`X2, `X1], mp `a `A #[`X2, `X1], mp `x `X1, mp `x `X2],
      arule "[\"mod:Z!\", \"mod:A!\"]" init,
      #[hdr 1 1, "  A.lean:1: A imports X2", hdr 1 1, "  A.lean:2: A imports X1", hdr 1 1,
        "  Z.lean:1: Z imports X2", hdr 1 1, "  Z.lean:2: Z imports X1",
        "lean-deny: 4 violations in 1 of 1 rule"]),
    ("a module no rule covers is not checked",
      #[mp `a `A #[`X, `Y], mp `b `B #[`Y], mp `x `X, mp `x `Y],
      arule "\"mod:A!\"" s!"[\"mod:X!\", {init}]",
      #[hdr 1 1, "  A.lean:2: A imports Y", "lean-deny: 1 violation in 1 of 1 rule"]),
    -- Tiers: the most specific rule governs, with its own allow alone.
    ("the most specific rule governs, and allows are not inherited",
      #[mp `a `A #[`X, `D], mp `a `A.T #[`D, `X], mp `x `X, mp `d `D],
      arule "\"mod:A\"" s!"[\"mod:X!\", {init}]" ++ arule "\"mod:A.T!\"" s!"[\"mod:D!\", {init}]",
      #[hdr 1 1, "  A.lean:2: A imports D", hdr 2 5, "  A.T.lean:2: A.T imports X",
        "lean-deny: 2 violations in 2 of 2 rules"]),
    ("three nested tiers",
      #[mp `a `A #[`X1, `X2], mp `a `A.T #[`X1, `X2, `X3], mp `a `A.T.L #[`X1, `X2, `X3], mp `x `X1,
        mp `x `X2, mp `x `X3],
      arule "\"mod:A\"" s!"[\"mod:X1!\", {init}]" ++
        arule "\"mod:A.T\"" s!"[\"mod:X1!\", \"mod:X2!\", {init}]" ++
        arule "\"mod:A.T.L!\"" s!"[\"mod:X1!\", \"mod:X2!\", \"mod:X3!\", {init}]",
      #[hdr 1 1, "  A.lean:2: A imports X2", hdr 2 5, "  A.T.lean:3: A.T imports X3",
        "lean-deny: 2 violations in 2 of 3 rules"]),
    ("except takes modules out of the rule",
      #[mp `a `A #[`X], mp `a `A.T #[`Y], mp `x `X, mp `x `Y],
      arule "\"mod:A\"" s!"[\"mod:X!\", {init}]" "except = \"mod:A.T!\"\n", ok1),
    ("an overlap settled by a more specific rule",
      #[mp `a `A, mp `a `B, mp `a `C, mp `a `D, mp `a `M #[`Y, `Z], mp `y `Y, mp `z `Z],
      arule "[\"mod:A!\", \"mod:B!\", \"mod:M!\"]" init ++
        arule "[\"mod:C!\", \"mod:D!\", \"mod:M!\"]" init ++
        arule "\"mod:M!\"" s!"[\"mod:Y!\", {init}]",
      #[hdr 3 9, "  M.lean:2: M imports Z", "lean-deny: 1 violation in 1 of 3 rules"]),
    -- Resolution errors.
    ("an except entry that removes nothing", #[mp `a `A #[`X], mp `x `X, mp `b `B],
      arule "\"mod:A!\"" s!"[\"mod:X!\", {init}]" "except = \"mod:B!\"\n",
      #["p.toml:3:9: selector 'mod:B!' in allow-only rule 1 ('except') removes no module from \
          'from'"]),
    ("an except list that empties from", #[mp `a `A, mp `a `A.T],
      arule "\"mod:A\"" init "except = [\"mod:A.T!\", \"mod:A!\"]\n",
      #["p.toml:1:0: allow-only rule 1 covers no module: 'except' removes every workspace module \
          of 'from'"]),
    ("from matches only externals; matching nothing comes first", #[mp `a `A #[`Std.Data.HashMap]],
      arule "[\"external:Std\", \"mod:Nope!\"]" init,
      #["p.toml:2:24: selector 'mod:Nope!' in allow-only rule 1 ('from') matches no module: no \
          workspace module named 'Nope'",
        "p.toml:2:8: selector 'external:Std' in allow-only rule 1 ('from') matches only modules \
          outside the workspace, which import nothing in the graph"]),
    ("allow matches nothing", #[mp `a `A], arule "\"mod:A!\"" s!"[\"mod:Nope!\", {init}]",
      #["p.toml:3:9: selector 'mod:Nope!' in allow-only rule 1 ('allow') matches no module: no \
          workspace module named 'Nope'"]),
    ("except matches nothing: no removes-nothing error", #[mp `a `A],
      arule "\"mod:A!\"" init "except = \"mod:Nope!\"\n",
      #["p.toml:3:9: selector 'mod:Nope!' in allow-only rule 1 ('except') matches no module: no \
          workspace module named 'Nope'"]),
    ("a from failure suppresses the except checks", #[mp `a `A, mp `b `B],
      arule "[\"mod:A!\", \"mod:Nope!\"]" init "except = \"mod:B!\"\n",
      #["p.toml:2:18: selector 'mod:Nope!' in allow-only rule 1 ('from') matches no module: no \
          workspace module named 'Nope'"]),
    ("a resolution error suppresses the checks across rules", #[mp `a `A, mp `a `B, mp `a `C],
      arule "\"mod:A!\"" s!"[\"mod:Nope!\", {init}]" ++ arule "[\"mod:A!\", \"mod:B!\"]" init ++
        arule "[\"mod:B!\", \"mod:C!\"]" init,
      #["p.toml:3:9: selector 'mod:Nope!' in allow-only rule 1 ('allow') matches no module: no \
          workspace module named 'Nope'"]),
    -- Errors across rules.
    ("two rules overlap without nesting, modules in display order",
      #[mp `a `App, mp `a `App.Shared, mp `a `AppTest, mp `a `Y, mp `a `Z],
      arule "[\"mod:App\", \"mod:AppTest!\", \"mod:Y!\"]" init ++
        arule "[\"mod:Z!\", \"mod:AppTest!\", \"mod:App\"]" init,
      #[s!"p.toml:5:0: allow-only rules 1 and 2 {overlap2 "App, App.Shared, AppTest" "them"}"]),
    ("two rules share one module", #[mp `a `A, mp `a `B, mp `a `M],
      arule "[\"mod:A!\", \"mod:M!\"]" init ++ arule "[\"mod:B!\", \"mod:M!\"]" init,
      #[s!"p.toml:5:0: allow-only rules 1 and 2 {overlap2 "M" "it"}"]),
    ("three rules overlap without nesting", #[mp `a `A, mp `a `X1, mp `a `X2, mp `a `X3],
      arule "[\"mod:A!\", \"mod:X1!\"]" init ++ arule "[\"mod:A!\", \"mod:X2!\"]" init ++
        arule "[\"mod:A!\", \"mod:X3!\"]" init,
      #["p.toml:9:0: allow-only rules 1, 2 and 3 overlap without nesting: all cover A, but each \
          also covers a module another does not, so none is the most specific for it (nest one \
          rule's modules inside another's, or take the shared modules out of one with 'except')"]),
    ("the same coverage, reported before any overlap", #[mp `a `A, mp `a `B, mp `a `C],
      arule "[\"mod:A!\", \"mod:B!\"]" init ++ arule "[\"mod:B!\", \"mod:A!\"]" init ++
        arule "[\"mod:B!\", \"mod:C!\"]" init,
      #["p.toml:5:0: allow-only rule 2 covers exactly the modules allow-only rule 1 covers, so \
          neither is the most specific (merge the two rules, or narrow one with 'except')"]),
    -- Errors per rule.
    ("a rule that governs no module; its allow is not checked", #[mp `a `A, mp `a `B, mp `x `X],
      arule "[\"mod:A!\", \"mod:B!\"]" s!"[\"mod:X!\", {init}]" ++ arule "\"mod:A!\"" init ++
        arule "\"mod:B!\"" init,
      #["p.toml:1:0: allow-only rule 1 governs no module: a more specific rule governs each \
          module it covers (allow-only rules 2 and 3)"]),
    ("a rule that governs no module, three more specific rules", #[mp `a `A, mp `a `B, mp `a `C],
      arule "[\"mod:A!\", \"mod:B!\", \"mod:C!\"]" init ++ arule "\"mod:A!\"" init ++
        arule "\"mod:B!\"" init ++
        arule "\"mod:C!\"" init,
      #["p.toml:1:0: allow-only rule 1 governs no module: a more specific rule governs each \
          module it covers (allow-only rules 2, 3 and 4)"]),
    ("an allow selector naming only the importer's own package",
      #[mp `a `A #[`B, `X], mp `a `B, mp `x `X],
      arule "\"mod:A!\"" s!"[\"mod:B!\", \"mod:X!\", {init}]",
      #[s!"p.toml:3:9: selector 'mod:B!' in allow-only rule 1 ('allow') {allowsNothing}"]),
    ("an allow selector only a more specific rule's module needs",
      #[mp `a `A #[`X], mp `a `A.T #[`Y], mp `x `X, mp `x `Y],
      arule "\"mod:A\"" s!"[\"mod:X!\", \"mod:Y!\", {init}]" ++
        arule "\"mod:A.T!\"" s!"[\"mod:Y!\", {init}]",
      #[s!"p.toml:3:19: selector 'mod:Y!' in allow-only rule 1 ('allow') {allowsNothing}"]),
    ("an allow selector needs one module that is used", #[mp `a `A #[`X], mp `x `X, mp `x `X.Other],
      arule "\"mod:A!\"" s!"[\"mod:X\", {init}]", ok1),
    ("errors hide violations", #[mp `a `A #[`B, `X], mp `a `B, mp `x `X],
      arule "\"mod:A!\"" s!"[\"mod:B!\", {init}]",
      #[s!"p.toml:3:9: selector 'mod:B!' in allow-only rule 1 ('allow') {allowsNothing}"]),
    -- Deny and allow-only rules together.
    ("errors of both kinds: deny's first", #[mp `a `A],
      arule "\"mod:A!\"" s!"[\"mod:Nope!\", {init}]" ++
        LeanDenyTest.Deny.rule "\"mod:A!\"" "\"mod:Gone!\"",
      #["p.toml:7:5: selector 'mod:Gone!' in deny rule 1 ('to') matches no module: no workspace \
          module named 'Gone'",
        "p.toml:3:9: selector 'mod:Nope!' in allow-only rule 1 ('allow') matches no module: no \
          workspace module named 'Nope'"]),
    ("violations of both kinds: deny's first", #[mp `a `A #[`X], mp `x `X],
      arule "\"mod:A!\"" init ++ LeanDenyTest.Deny.rule "\"mod:A!\"" "\"mod:X!\"",
      #["deny rule 1 (p.toml:5:0): r", "  A.lean:1: A imports X", hdr 1 1,
        "  A.lean:1: A imports X", "lean-deny: 2 violations in 2 of 2 rules"]),
    ("both kinds hold", #[mp `a `A #[`X], mp `x `X, mp `y `Y],
      arule "\"mod:A!\"" s!"[\"mod:X!\", {init}]" ++
        LeanDenyTest.Deny.rule "\"mod:A!\"" "\"mod:Y!\"",
      #["lean-deny: ok (2 rules)"]),
    -- Sets.
    ("sets in from, except and allow",
      #[mp `a `A #[`X, `Y], mp `a `A.T #[`Z], mp `x `X, mp `x `Y, mp `x `Z],
      "[sets]\nmine = [\"mod:A\"]\ntests = [\"mod:A.T!\"]\nout = [\"mod:X!\", \"external:Init\"]\n\n" ++
        arule "\"set:mine\"" "\"set:out\"" "except = \"set:tests\"\n",
      #[hdr 1 6, "  A.lean:2: A imports Y", "lean-deny: 1 violation in 1 of 1 rule"])]

/-- An allow-only violation's header without a position. -/
def renderingFailures : Array String :=
  let v : Violation := { rule := ⟨.allowOnly, 1⟩, pos? := none, reason? := some "r", chain := #[] }
  let got := ", ".intercalate (v.render default "p.toml").toList
  let want := "allow-only rule 1 (p.toml): r"
  if got == want then #[] else #[s!"expected {repr want}, got {repr got}"]

def run : IO (Array String) := do
  let mut fs := renderingFailures
  for (name, ms, src, want) in cases do
    let got ← LeanDenyTest.Deny.outcome ms src
    unless got == want do
      fs := fs.push s!"{name}: expected {repr want}, got {repr got}"
  return fs

end LeanDenyTest.AllowOnly
