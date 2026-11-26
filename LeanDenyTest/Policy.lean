import LeanDeny

/-!
Tests of the policy loader (`LeanDeny.Policy.ofToml`) on TOML texts: the
three forms of a set, the positions of sets and selectors, every load-time
error with its exact rendering, `set:` references and cycles, and the
order sets are resolved in.
-/

open LeanDeny

namespace LeanDenyTest.Policy

/-- Parse `src` as the policy `p.toml`. -/
def load (src : String) : IO (Except (Array String) LeanDeny.Policy) := do
  match ← Toml.parseLocated "p.toml" src with
  | .error msgs =>
    return .error msgs
  | .ok entries =>
    return Policy.ofToml "p.toml" entries

def renderPos : Option Toml.Pos → String
  | some p => s!"{p.line}:{p.column}"
  | none => "-"

def renderUse : Use → String
  | .setSelect n => s!"select({n})"
  | .setExcept n => s!"except({n})"
  | .commandLine => "cli"

def renderRef (r : SelectorRef) : String :=
  s!"{r.text}@{renderPos r.pos?} {renderUse r.use}"

/-- A set as `name@pos [selectors] except [selectors]`. -/
def renderSet (d : SetDef) : String :=
  let sel := ", ".intercalate (d.select.map renderRef).toList
  let exc := ", ".intercalate (d.except.map renderRef).toList
  s!"{d.name}@{renderPos d.pos?} [{sel}]{if d.except.isEmpty then "" else s!" except [{exc}]"}"

/-- Every set, then the order by name. -/
def renderPolicy (p : LeanDeny.Policy) : Array String :=
  p.sets.map renderSet |>.push
    s!"order: {" ".intercalate (p.order.map fun i => (p.sets[i]?.map (·.name)).getD "?").toList}"

/-- `(case, source, expected)`: the rendered policy (`renderPolicy`) or
the exact error messages. -/
def cases : Array (String × String × Except (Array String) (Array String)) :=
  #[("empty file", "", .ok #["order: "]), ("only comments", "# nothing\n\n", .ok #["order: "]),
    ("empty [sets]", "[sets]\n", .ok #["order: "]), ("sets = {}", "sets = {}\n", .ok #["order: "]),
    ("bare array", "[sets]\ncore = [\"pkg:core\", \"mod:A!\"]\n",
      .ok #["core@2:7 [pkg:core@2:8 select(core), mod:A!@2:20 select(core)]", "order: core"]),
    ("inline table", "[sets]\ncore = { select = [\"pkg:core\"], except = [\"mod:A!\"] }\n",
      .ok
        #["core@2:7 [pkg:core@2:19 select(core)] except [mod:A!@2:42 except(core)]",
          "order: core"]),
    ("sub-table", "[sets.x]\nselect = [\"pkg:core\"]\nexcept = [\"mod:A!\"]\n",
      .ok #["x@1:0 [pkg:core@2:10 select(x)] except [mod:A!@3:10 except(x)]", "order: x"]),
    ("a multi-line array", "[sets]\ncore = [\n  \"pkg:core\",\n\n    \"mod:A!\",\n]\n",
      .ok #["core@2:7 [pkg:core@3:2 select(core), mod:A!@5:4 select(core)]", "order: core"]),
    ("sets = { ... } inline", "sets = { a = [\"pkg:a\"] }\n",
      .ok #["a@1:13 [pkg:a@1:14 select(a)]", "order: a"]),
    ("order puts every dependency first",
      "[sets]\na = [\"set:b\", \"set:c\"]\nb = [\"set:c\"]\nc = [\"pkg:c\"]\nd = [\"pkg:d\"]\n",
      .ok
        #["a@2:4 [set:b@2:5 select(a), set:c@2:14 select(a)]", "b@3:4 [set:c@3:5 select(b)]",
          "c@4:4 [pkg:c@4:5 select(c)]", "d@5:4 [pkg:d@5:5 select(d)]", "order: c b a d"]),
    ("a reference in except is an edge",
      "[sets]\na = { select = [\"pkg:a\"], except = [\"set:b\"] }\nb = [\"pkg:b\"]\n",
      .ok
        #["a@2:4 [pkg:a@2:16 select(a)] except [set:b@2:36 except(a)]",
          "b@3:4 [pkg:b@3:5 select(b)]", "order: b a"]),
    -- Unknown top-level keys.
    ("[[bans]]", "[[bans]]\nfrom = \"pkg:a\"\n",
      .error #["p.toml:1:0: unknown key 'bans' (known keys: sets)"]),
    ("foo = 1", "foo = 1\n", .error #["p.toml:1:6: unknown key 'foo' (known keys: sets)"]),
    ("sets = 1", "sets = 1\n", .error #["p.toml:1:7: 'sets' must be a table, such as [sets]"]),
    ("sets = []", "sets = []\n", .error #["p.toml:1:7: 'sets' must be a table, such as [sets]"]),
    -- Every load-time error of a set.
    ("invalid set name", "[sets]\n\"core api\" = [\"pkg:core\"]\n",
      .error #["p.toml:2:13: invalid set name 'core api' (use letters, digits, '-' and '_')"]),
    ("a string, not a list", "[sets]\nscalar = \"pkg:core\"\n",
      .error
        #["p.toml:2:9: set 'scalar' must be an array of selectors or a table with 'select' \
            and 'except', found a string"]),
    ("an integer, not a list", "[sets]\nn = 1\n",
      .error
        #["p.toml:2:4: set 'n' must be an array of selectors or a table with 'select' \
            and 'except', found an integer"]),
    ("empty bare array", "[sets]\nempty = []\n", .error #["p.toml:2:8: set 'empty' is empty"]),
    ("an element not a string", "[sets]\nmixed = [\"pkg:core\", 1, true]\n",
      .error
        #["p.toml:2:21: set 'mixed': expected a selector string, found an integer",
          "p.toml:2:24: set 'mixed': expected a selector string, found a boolean"]),
    ("table without select", "[sets]\nnosel = { except = [\"mod:A!\"] }\n",
      .error #["p.toml:2:8: set 'nosel' has no 'select' list"]),
    ("unknown table key", "[sets]\ntypo = { select = [\"pkg:core\"], exept = [\"mod:A!\"] }\n",
      .error #["p.toml:2:40: set 'typo': unknown key 'exept' (expected 'select' or 'except')"]),
    ("select not an array", "[sets]\nx = { select = \"pkg:core\" }\n",
      .error #["p.toml:2:15: set 'x': 'select' must be an array of selectors, found a string"]),
    ("except not an array", "[sets]\nx = { select = [\"pkg:a\"], except = { a = 1 } }\n",
      .error #["p.toml:2:35: set 'x': 'except' must be an array of selectors, found a table"]),
    ("select = []", "[sets]\nx = { select = [] }\n",
      .error #["p.toml:2:15: set 'x': 'select' is empty"]),
    ("except = []", "[sets]\nx = { select = [\"pkg:a\"], except = [] }\n",
      .error #["p.toml:2:35: set 'x': 'except' is empty (omit it)"]),
    ("a malformed selector", "[sets]\nx = [\"pkg:\", \"mod:A..B\"]\n",
      .error
        #["p.toml:2:5: invalid selector 'pkg:': nothing after 'pkg:'",
          "p.toml:2:13: invalid selector 'mod:A..B': 'A..B' is not a module name"]),
    -- References.
    ("an unknown set", "[sets]\ncore = [\"pkg:core\"]\napi = [\"set:cor\"]\n",
      .error
        #["p.toml:3:7: selector 'set:cor' in set 'api' names an unknown set (defined: core, api)"]),
    ("an unknown set in except",
      "[sets]\ncore = { select = [\"pkg:core\"], except = [\"set:nope\"] }\n",
      .error
        #["p.toml:2:42: selector 'set:nope' in the except list of set 'core' names an \
            unknown set (defined: core)"]),
    ("a self cycle", "[sets]\nc = [\"pkg:a\", \"set:c\"]\n",
      .error #["p.toml:2:14: set 'c' refers to itself: c -> c"]),
    ("a 2-cycle", "[sets]\na = [\"set:b\"]\nb = [\"mod:X\", \"set:a\"]\n",
      .error #["p.toml:2:5: set 'a' refers to itself: a -> b -> a"]),
    ("a 3-cycle is reported once", "[sets]\na = [\"set:b\"]\nb = [\"set:c\"]\nc = [\"set:a\"]\n",
      .error #["p.toml:2:5: set 'a' refers to itself: a -> b -> c -> a"]),
    ("a cycle entered from outside starts at its first set",
      "[sets]\nx = [\"set:a\"]\na = [\"set:b\"]\nb = [\"set:a\"]\n",
      .error #["p.toml:3:5: set 'a' refers to itself: a -> b -> a"]),
    ("two separate cycles", "[sets]\na = [\"set:b\"]\nb = [\"set:a\"]\nc = [\"set:c\"]\n",
      .error
        #["p.toml:2:5: set 'a' refers to itself: a -> b -> a",
          "p.toml:4:5: set 'c' refers to itself: c -> c"]),
    ("a cycle through except",
      "[sets]\na = { select = [\"pkg:a\"], except = [\"set:b\"] }\nb = [\"set:a\"]\n",
      .error #["p.toml:2:36: set 'a' refers to itself: a -> b -> a"]),
    -- Lake's own errors pass through.
    ("a duplicate key", "[sets]\ncore = [\"pkg:core\"]\ncore = [\"pkg:base\"]\n",
      .error #["p.toml:3:0: cannot redefine value key `sets.core`"]),
    -- Errors are collected, in source order: shape and syntax first, then references.
    ("several errors", "[sets]\na = [\"set:zz\"]\nb = []\nc = [\"crate:x\"]\n\n[[bans]]\nx = 1\n",
      .error
        #["p.toml:3:4: set 'b' is empty",
          "p.toml:4:5: invalid selector 'crate:x': unknown kind 'crate' (expected pkg, lib, \
            mod, keyword, external or set)",
          "p.toml:6:0: unknown key 'bans' (known keys: sets)",
          "p.toml:2:5: selector 'set:zz' in set 'a' names an unknown set (defined: a, b, c)"])]

def renderResult : Except (Array String) (Array String) → String
  | .ok xs => s!"ok {repr xs}"
  | .error es => s!"error {repr es}"

/-- The renderings of `Use` and `SelectorRef`. -/
def renderingFailures : Array String :=
  let r (use : Use) : SelectorRef := { text := "mod:X", sel := .mod `X false, pos? := none, use }
  let want :=
    [(r (.setSelect "core"), "selector 'mod:X' in set 'core'"),
      (r (.setExcept "core"), "selector 'mod:X' in the except list of set 'core'"),
      (r .commandLine, "selector 'mod:X'")]
  let fs :=
    want.toArray.filterMap fun (ref, w) =>
      if ref.describe == w then none
      else some s!"describe: expected {repr w}, got {repr ref.describe}"
  let locs :=
    [(Policy.locate "p.toml" (some { line := 3, column := 0 }) "m", "p.toml:3:0: m"),
      (Policy.locate "p.toml" none "m", "p.toml: m")]
  fs ++
    locs.toArray.filterMap fun (got, w) =>
      if got == w then none else some s!"locate: expected {repr w}, got {repr got}"

def run : IO (Array String) := do
  let mut fs := renderingFailures
  for (name, src, want) in cases do
    let got := (← load src).map renderPolicy
    let same :=
      match got, want with
      | .ok a, .ok b => a == b
      | .error a, .error b => a == b
      | _, _ => false
    unless same do
      fs := fs.push s!"{name}: expected {renderResult want}, got {renderResult got}"
  return fs

end LeanDenyTest.Policy
