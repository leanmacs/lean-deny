import LeanDenyTest.AllowOnly
import LeanDenyTest.Resolve

/-!
Tests of `[layers]` (`LeanDeny.Rules.Layers`) on hand-written graphs, from
the policy's TOML text to what `check` prints: which imports are judged
(between two packages, not within one, not of external modules), allowed
pairs, same-layer pairs, the default layer, one violation per pair and the
order, the errors classification and the allow pairs can give and their
order, and all three rule kinds together.
-/

open Lean LeanDeny LeanDeny.Graph LeanDenyTest.Query LeanDenyTest.AllowOnly

namespace LeanDenyTest.Layers

/-- A `[layers]` table: line 1 `[layers]`, line 2 `classify = [`, one entry
per line (`  { layer = "<l>", select = <s> },`, the select a TOML value),
then `]`; then `default = "<d>"` when given; then, when `allow` is
non-empty, `allow = [`, one pair per line (`  ["<a>", "<b>"],`), `]`; then
`extra`. -/
def lrule (classify : Array (String × String)) (default? : Option String := some "impl")
    (allow : Array (String × String) := #[]) (extra : String := "") : String :=
  let entries :=
    classify.foldl (init := "") fun acc (l, s) => acc ++ s!"  \{ layer = \"{l}\", select = {s} },\n"
  let dflt := (default?.map fun d => s!"default = \"{d}\"\n").getD ""
  let pairs :=
    if allow.isEmpty then ""
    else
      "allow = [\n" ++
        allow.foldl (init := "") (fun acc (a, b) => acc ++ s!"  [\"{a}\", \"{b}\"],\n") ++
        "]\n"
  s!"[layers]\nclassify = [\n{entries}]\n{dflt}{pairs}{extra}"

/-- A layers violation's header, the table on line 1. -/
def hdr (s : String) : String :=
  s!"layers (p.toml:1:0): {s}"

/-- Packages `c` (the core: `C`, `C.T`), `i` (an interface: `I`), `a` and
`b` (implementations: `A`, `B`). `I` imports the core, `A` imports `I` and
the core, `B` imports only an external module. -/
def base : Array M :=
  #[mp `c `C #[`C.T], mp `c `C.T, mp `i `I #[`C], mp `a `A #[`I, `C], mp `b `B #[`Std.Data.HashMap]]

/-- `ms` with the module named as `m` replaced by `m`, or `m` added. -/
def withM (ms : Array M) (m : M) : Array M :=
  if ms.any (·.name == m.name) then ms.map fun x => if x.name == m.name then m else x else ms.push m

def cls : Array (String × String) :=
  #[("core", "\"mod:C\""), ("iface", "\"mod:I\"")]

def std : Array (String × String) :=
  #[("iface", "core"), ("impl", "core"), ("impl", "iface")]

def ok1 : Array String :=
  #["lean-deny: ok (1 rule)"]

def summary1 : String :=
  "lean-deny: 1 violation in 1 of 1 rule"

/-- `base` where the core imports the implementation package `b`. -/
def coreImportsB : Array M :=
  withM base (mp `c `C #[`C.T, `B])

/-- `base` where `A` also imports the implementation package `b`. -/
def aImportsB : Array M :=
  withM base (mp `a `A #[`I, `C, `B])

def splitTail : String :=
  "a layer holds whole packages, so select them with pkg:, keyword:, or a set of them"

/-- `base` where `A` imports `B2` and `B` (twice) of package `b`, and `A.Z`
imports `B`. -/
def manyImports : Array M :=
  let a : M :=
    { mp `a `A with
      imports := #[plain `I, plain `C, plain `B2, plain `B, (`B, { isMeta := true })] }
  #[a, mp `a `A.Z #[`B], mp `b `B2].foldl withM base

/-- `(case, modules, packages, policy, expected lines)`. -/
def cases : Array (String × Array M × Array PackageInfo × String × Array String) :=
  #[ -- What is judged.
    ("holds", base, #[], lrule cls (allow := std), ok1),
    ("the core importing a package bites", coreImportsB, #[], lrule cls (allow := std),
      #[hdr "c (core) may not import b (impl)", "  C.lean:2: C imports B", summary1]),
    ("an implementation package importing one bites", aImportsB, #[], lrule cls (allow := std),
      #[hdr "a (impl) may not import b (impl)", "  A.lean:3: A imports B", summary1]),
    ("an interface package importing an implementation package bites",
      withM base (mp `i `I #[`C, `B]), #[], lrule cls (allow := std),
      #[hdr "i (iface) may not import b (impl)", "  I.lean:2: I imports B", summary1]),
    ("a listed same-layer pair", aImportsB, #[], lrule cls (allow := std.push ("impl", "impl")),
      ok1),
    ("imports within a package and of external modules are not judged", base, #[],
      lrule cls (allow := std) (extra := "same-package = \"allow\"\n"), ok1),
    ("one violation per pair, importers in display order, then source order", manyImports, #[],
      lrule cls (allow := std),
      #[hdr "a (impl) may not import b (impl)", "  A.lean:3: A imports B2",
        hdr "a (impl) may not import b (impl)", "  A.lean:4: A imports B",
        hdr "a (impl) may not import b (impl)", "  A.Z.lean:1: A.Z imports B",
        "lean-deny: 3 violations in 1 of 1 rule"]),
    ("a reason starts the header", coreImportsB, #[],
      lrule cls (allow := std) (extra := "reason = \"why\"\n"),
      #[hdr "why: c (core) may not import b (impl)", "  C.lean:2: C imports B", summary1]),
    -- The default layer.
    ("no default, every package classified", base, #[],
      lrule (cls ++ #[("impl", "\"mod:A\""), ("impl", "\"mod:B\"")]) none std, ok1),
    ("no default, unclassified packages", base, #[], lrule cls none #[("iface", "core")],
      #["p.toml:1:0: layers: packages 'a' and 'b' are in no layer: no classify entry selects \
          them, and there is no 'default'"]),
    ("no default, one unclassified package", base, #[],
      lrule (cls ++ #[("impl", "\"mod:A\"")]) none std,
      #["p.toml:1:0: layers: package 'b' is in no layer: no classify entry selects it, and there \
          is no 'default'"]),
    ("the default holds no package", base, #[],
      lrule (cls ++ #[("impl", "\"mod:A\""), ("impl", "\"mod:B\"")]) (some "spare") std,
      #["p.toml:8:10: layers: layer 'spare' (the default) holds no package: a classify entry \
          selects every package"]),
    ("a default that is also a classify layer", base, #[],
      lrule (cls ++ #[("impl", "\"mod:A\"")]) (some "impl") std, ok1),
    -- Classification errors.
    ("a selector that splits a package", base, #[],
      lrule #[("core", "\"mod:C!\""), ("iface", "\"mod:I\"")] (allow := std),
      #[s!"p.toml:3:2: layers classify entry 1 splits package 'c': it matches C but not C.T; \
          {splitTail}"]),
    ("a package in two entries", base, #[], lrule (cls ++ #[("other", "\"mod:C\"")]) (allow := std),
      #["p.toml:5:2: package 'c' is in layers classify entries 1 and 3; a package is in one layer"]),
    ("a package in three entries", base, #[],
      lrule (cls ++ #[("other", "\"mod:C\""), ("more", "\"mod:C\"")]) (allow := std),
      #["p.toml:6:2: package 'c' is in layers classify entries 1, 3 and 4; a package is in one \
          layer"]),
    ("matches nothing, then matches only externals", base, #[],
      lrule
        #[("core", "\"mod:C\""), ("iface", "[\"mod:I\", \"mod:Nope\"]"),
          ("ext", "\"external:Std\"")]
        (allow := std),
      #["p.toml:4:40: selector 'mod:Nope' in layers classify entry 2 matches no module: no \
          workspace module is or is under 'Nope'",
        "p.toml:5:28: selector 'external:Std' in layers classify entry 3 matches only modules \
          outside the workspace, which are in no package"]),
    ("resolution errors suppress classification errors", base, #[],
      lrule (cls ++ #[("x", "[\"mod:C\", \"mod:Nope!\"]")]) (allow := std),
      #["p.toml:5:36: selector 'mod:Nope!' in layers classify entry 3 matches no module: no \
          workspace module named 'Nope'"]),
    -- Allow pairs that allow nothing.
    ("an allow pair that allows nothing hides the violations", coreImportsB, #[],
      lrule cls (allow := std.push ("impl", "impl")),
      #["p.toml:11:2: layers: allow entry 4 ([\"impl\", \"impl\"]) allows nothing: no module of a \
          package in layer 'impl' imports a module of another package in layer 'impl'"]),
    ("a self pair needs two packages of the layer", base, #[],
      lrule cls (allow := std.push ("core", "core")),
      #["p.toml:11:2: layers: allow entry 4 ([\"core\", \"core\"]) allows nothing: no module of a \
          package in layer 'core' imports a module of another package in layer 'core'"]),
    -- Selectors over package metadata and sets.
    ("a misspelt keyword leaves a package in the default layer",
      withM (withM base (mp `a `A #[`I, `C, `T])) (mp `t `T),
      #[LeanDenyTest.Resolve.pkg `c #[] #[] #[], LeanDenyTest.Resolve.pkg `i #["iface"] #[] #[],
        LeanDenyTest.Resolve.pkg `a #[] #[] #[], LeanDenyTest.Resolve.pkg `b #[] #[] #[],
        LeanDenyTest.Resolve.pkg `t #["ifcae"] #[] #[]],
      lrule #[("core", "\"pkg:c\""), ("iface", "\"keyword:iface\"")] (allow := std),
      #[hdr "a (impl) may not import t (impl)", "  A.lean:3: A imports T", summary1]),
    ("set: in select", base, #[],
      "[sets]\ncore = [\"mod:C\"]\n\n" ++
        lrule #[("core", "\"set:core\""), ("iface", "\"mod:I\"")] (allow := std),
      ok1),
    -- All three kinds together.
    ("all three kinds: violations in kind order", coreImportsB, #[],
      lrule cls (allow := std) ++ LeanDenyTest.Deny.rule "\"mod:C!\"" "\"mod:B!\"" ++
        arule "\"mod:C!\"" init,
      #["deny rule 1 (p.toml:12:0): r", "  C.lean:2: C imports B",
        "allow-only rule 1 (p.toml:16:0): r", "  C.lean:2: C imports B",
        hdr "c (core) may not import b (impl)", "  C.lean:2: C imports B",
        "lean-deny: 3 violations in 3 of 3 rules"]),
    ("all three kinds: errors in kind order", base, #[],
      lrule #[("core", "\"mod:Gone\""), ("iface", "\"mod:I\"")] (allow := std) ++
        LeanDenyTest.Deny.rule "\"mod:C!\"" "\"mod:Nope!\"" ++
        arule "\"mod:C!\"" "[\"mod:Nada!\", \"external:Init\"]",
      #["p.toml:14:5: selector 'mod:Nope!' in deny rule 1 ('to') matches no module: no workspace \
          module named 'Nope'",
        "p.toml:18:9: selector 'mod:Nada!' in allow-only rule 1 ('allow') matches no module: no \
          workspace module named 'Nada'",
        "p.toml:3:29: selector 'mod:Gone' in layers classify entry 1 matches no module: no \
          workspace module is or is under 'Gone'"]),
    ("all three kinds hold", base, #[],
      lrule cls (allow := std) ++ LeanDenyTest.Deny.rule "\"mod:C!\"" "\"mod:B!\"" ++
        arule "\"mod:I!\"" s!"[\"mod:C!\", {init}]",
      #["lean-deny: ok (3 rules)"])]

/-- A layers violation's header without a position. -/
def renderingFailures : Array String :=
  let v : Violation := { label := "layers", pos? := none, reason := "r", chain := #[] }
  let got := ", ".intercalate (v.render default "p.toml").toList
  let want := "layers (p.toml): r"
  if got == want then #[] else #[s!"expected {repr want}, got {repr got}"]

def run : IO (Array String) := do
  let mut fs := renderingFailures
  for (name, ms, packages, src, want) in cases do
    let got ← LeanDenyTest.Deny.outcome ms src packages
    unless got == want do
      fs := fs.push s!"{name}: expected {repr want}, got {repr got}"
  return fs

end LeanDenyTest.Layers
