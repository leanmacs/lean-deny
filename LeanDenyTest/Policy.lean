import LeanDeny

/-!
Tests of the policy loader (`LeanDeny.Policy.ofToml`) on TOML texts: the
three forms of a set, the two forms of `[[deny]]` and of `[[allow-only]]`,
the three forms of `[layers]`, the positions of sets, rules and selectors,
every load-time error with its exact rendering, `set:` references and
cycles, the order sets are resolved in, and that the README's sketched
policy loads.
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
  | .rule k i f => s!"{k}{i}.{f}"
  | .layer i => s!"layers{i}"
  | .commandLine => "cli"

def renderRef (r : SelectorRef) : String :=
  s!"{r.text}@{renderPos r.pos?} {renderUse r.use}"

/-- A set as `name@pos [selectors] except [selectors]`. -/
def renderSet (d : SetDef) : String :=
  let sel := ", ".intercalate (d.select.map renderRef).toList
  let exc := ", ".intercalate (d.except.map renderRef).toList
  s!"{d.name}@{renderPos d.pos?} [{sel}]{if d.except.isEmpty then "" else s!" except [{exc}]"}"

/-- A deny rule as `deny#1@pos from[…] to[…][ transitive][ wrappers[…]] reason="…"`. -/
def renderRule (r : DenyRule) : String :=
  let refs (rs : Array SelectorRef) := ", ".intercalate (rs.map renderRef).toList
  s!"deny#{r.index}@{renderPos r.pos?} from[{refs r.sources}] to[{refs r.targets}]\
    {if r.transitive then " transitive" else ""}\
    {if r.wrappers.isEmpty then "" else s!" wrappers[{refs r.wrappers}]"} reason={repr r.reason}"

/-- An allow-only rule as `allow-only#1@pos from[…][ except[…]] allow[…] reason="…"`. -/
def renderAllowOnly (r : AllowOnlyRule) : String :=
  let refs (rs : Array SelectorRef) := ", ".intercalate (rs.map renderRef).toList
  s!"allow-only#{r.index}@{renderPos r.pos?} from[{refs r.sources}]\
    {if r.except.isEmpty then "" else s!" except[{refs r.except}]"} allow[{refs r.allow}] \
    reason={repr r.reason}"

/-- `[layers]` as `layers@pos classify[layer@pos(selectors), …] default=d@pos
allow[importer>imported@pos, …] reason="…"`, `-` for an absent `default` or
`reason`. -/
def renderLayers (r : LayersRule) : String :=
  let refs (rs : Array SelectorRef) := ", ".intercalate (rs.map renderRef).toList
  let entry (c : LayerClass) := s!"{c.layer}@{renderPos c.pos?}({refs c.select})"
  let pair (q : LayerPair) := s!"{q.importer}>{q.imported}@{renderPos q.pos?}"
  let dflt :=
    match r.default? with
    | some d => s!"{d}@{renderPos r.defaultPos?}"
    | none => "-"
  let reason :=
    match r.reason? with
    | some s => toString (repr s)
    | none => "-"
  s!"layers@{renderPos r.pos?} classify[{", ".intercalate (r.classify.map entry).toList}] \
    default={dflt} allow[{", ".intercalate (r.allow.map pair).toList}] reason={reason}"

/-- A require-backed rule as `require-backed#1@pos packages[…] reason="…"`. -/
def renderRequireBacked (r : RequireBackedRule) : String :=
  let refs (rs : Array SelectorRef) := ", ".intercalate (rs.map renderRef).toList
  s!"require-backed#{r.index}@{renderPos r.pos?} packages[{refs r.packages}] \
    reason={repr r.reason}"

/-- A doc-modules rule as `doc-modules#1@pos file="…" section="…"
prefix="…" modules[…] reason="…"`. -/
def renderDocModules (r : DocModulesRule) : String :=
  let refs (rs : Array SelectorRef) := ", ".intercalate (rs.map renderRef).toList
  s!"doc-modules#{r.index}@{renderPos r.pos?} file={repr r.file} section={repr r.heading} \
    prefix={repr r.pfx} modules[{refs r.modules}] reason={repr r.reason}"

/-- A doc-packages rule as `doc-packages#1@pos file="…" section="…"
columns="…","…","…" packages[…] except[name@pos, …] reason="…"`. -/
def renderDocPackages (r : DocPackagesRule) : String :=
  let refs (rs : Array SelectorRef) := ", ".intercalate (rs.map renderRef).toList
  let names :=
    ", ".intercalate (r.requiresExcept.map fun (n, pos?) => s!"{n}@{renderPos pos?}").toList
  s!"doc-packages#{r.index}@{renderPos r.pos?} file={repr r.file} section={repr r.heading} \
    columns={repr r.packageColumn},{repr r.layerColumn},{repr r.requiresColumn} \
    packages[{refs r.packages}] except[{names}] reason={repr r.reason}"

/-- A declared root as `root#1@pos Module=path`. -/
def renderRoot (r : RootDef) : String :=
  s!"root#{r.index}@{renderPos r.pos?} {r.module}={r.path}"

/-- Every set, then the order by name, then every deny rule, then every
allow-only rule, then `[layers]`, then every require-backed rule, then
every doc-modules rule, then every doc-packages rule, then every declared
root. -/
def renderPolicy (p : LeanDeny.Policy) : Array String :=
  (p.sets.map renderSet |>.push
      s!"order: {" ".intercalate (p.order.map fun i => (p.sets[i]?.map (·.name)).getD "?").toList}") ++
    p.deny.map renderRule ++
    p.allowOnly.map renderAllowOnly ++
    (p.layers?.map fun r => #[renderLayers r]).getD #[] ++
    p.requireBacked.map renderRequireBacked ++
    p.docModules.map renderDocModules ++
    p.docPackages.map renderDocPackages ++
    p.roots.map renderRoot

/-- A deny table with `from`, `to` and `reason`, then `extra` lines. -/
def denyWith (extra : String) : String :=
  s!"[[deny]]\nfrom = \"mod:A\"\nto = \"mod:B\"\nreason = \"r\"\n{extra}"

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
      .error
        #["p.toml:1:0: unknown key 'bans' (known keys: sets, deny, allow-only, layers, reachable, \
            co-reach, target-config, require-backed, doc-modules, doc-packages, root)"]),
    ("foo = 1", "foo = 1\n",
      .error
        #["p.toml:1:6: unknown key 'foo' (known keys: sets, deny, allow-only, layers, reachable, \
            co-reach, target-config, require-backed, doc-modules, doc-packages, root)"]),
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
    ("a cycle through imports:", "[sets]\na = [\"imports:set:a\"]\n",
      .error #["p.toml:2:5: set 'a' refers to itself: a -> a"]),
    ("an unknown set inside imports:", "[sets]\nb = [\"imports:set:nope\"]\n",
      .error
        #["p.toml:2:5: selector 'imports:set:nope' in set 'b' names an unknown set (defined: b)"]),
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
            mod, keyword, external, set or imports)",
          "p.toml:6:0: unknown key 'bans' (known keys: sets, deny, allow-only, layers, reachable, \
            co-reach, target-config, require-backed, doc-modules, doc-packages, root)",
          "p.toml:2:5: selector 'set:zz' in set 'a' names an unknown set (defined: a, b, c)"])]

/-- `[[deny]]` cases, as `cases`. -/
def denyCases : Array (String × String × Except (Array String) (Array String)) :=
  #[ -- The two forms, string versus array fields, defaults.
    ("[[deny]] tables",
      "[[deny]]\nfrom = \"mod:A\"\nto = [\"mod:B\", \"mod:C!\"]\nreason = \"r1\"\n\n\
        [[deny]]\nfrom = [\"mod:X\"]\nto = \"external:Lean\"\ntransitive = true\n\
        wrappers = \"mod:W!\"\nreason = \"r2\"\n",
      .ok
        #["order: ",
          "deny#1@1:0 from[mod:A@2:7 deny1.from] to[mod:B@3:6 deny1.to, mod:C!@3:15 deny1.to] \
            reason=\"r1\"",
          "deny#2@6:0 from[mod:X@7:8 deny2.from] to[external:Lean@8:5 deny2.to] transitive \
            wrappers[mod:W!@10:11 deny2.wrappers] reason=\"r2\""]),
    ("inline tables",
      "deny = [{ from = \"mod:A\", to = \"mod:B\", reason = \"r\" }, \
        { from = \"mod:C\", to = \"mod:D\", reason = \"s\", transitive = false }]\n",
      .ok
        #["order: ", "deny#1@1:8 from[mod:A@1:17 deny1.from] to[mod:B@1:31 deny1.to] reason=\"r\"",
          "deny#2@1:56 from[mod:C@1:65 deny2.from] to[mod:D@1:79 deny2.to] reason=\"s\""]),
    ("wrappers as an array, with sets",
      "[sets]\ncore = [\"pkg:core\"]\n\n[[deny]]\nfrom = \"set:core\"\nto = \"keyword:k\"\n\
        wrappers = [\"mod:W!\", \"set:core\"]\nreason = \"r\"\n",
      .ok
        #["core@2:7 [pkg:core@2:8 select(core)]", "order: core",
          "deny#1@4:0 from[set:core@5:7 deny1.from] to[keyword:k@6:5 deny1.to] \
            wrappers[mod:W!@7:12 deny1.wrappers, set:core@7:22 deny1.wrappers] reason=\"r\""]),
    -- The shape of `deny`.
    ("deny = 1", "deny = 1\n",
      .error #["p.toml:1:7: 'deny' must be an array of tables, such as [[deny]]"]),
    ("[deny]", "[deny]\nfrom = \"pkg:a\"\n",
      .error #["p.toml:1:0: 'deny' must be an array of tables, such as [[deny]]"]),
    ("deny = []", "deny = []\n", .error #["p.toml:1:7: 'deny' is empty (omit it)"]),
    ("deny = [1]", "deny = [1]\n",
      .error #["p.toml:1:8: deny rule 1 must be a table, found an integer"]),
    -- Every load-time error of a deny table.
    ("missing keys", "[[deny]]\ntransitive = false\n",
      .error
        #["p.toml:1:0: deny rule 1 has no 'from'", "p.toml:1:0: deny rule 1 has no 'to'",
          "p.toml:1:0: deny rule 1 has no 'reason'"]),
    ("missing keys come before the entries' errors", "[[deny]]\nto = 1\n",
      .error
        #["p.toml:1:0: deny rule 1 has no 'from'", "p.toml:1:0: deny rule 1 has no 'reason'",
          "p.toml:2:5: deny rule 1: 'to' must be a selector or an array of selectors, found an \
            integer"]),
    ("an unknown key", denyWith "wrapper = \"mod:W\"\n",
      .error
        #["p.toml:5:10: deny rule 1: unknown key 'wrapper' (expected from, to, transitive, \
            wrappers, reason)"]),
    ("from, to and wrappers not selectors",
      "[[deny]]\nfrom = 1\nto = { a = 1 }\nwrappers = true\nreason = \"r\"\n",
      .error
        #["p.toml:2:7: deny rule 1: 'from' must be a selector or an array of selectors, found \
            an integer",
          "p.toml:3:5: deny rule 1: 'to' must be a selector or an array of selectors, found a \
            table",
          "p.toml:4:11: deny rule 1: 'wrappers' must be a selector or an array of selectors, \
            found a boolean"]),
    ("empty lists", "[[deny]]\nfrom = []\nto = []\nwrappers = []\nreason = \"r\"\n",
      .error
        #["p.toml:2:7: deny rule 1: 'from' is empty", "p.toml:3:5: deny rule 1: 'to' is empty",
          "p.toml:4:11: deny rule 1: 'wrappers' is empty (omit it)"]),
    ("an element not a string", denyWith "wrappers = [\"mod:W\", true]\n",
      .error
        #["p.toml:5:21: deny rule 1 ('wrappers'): expected a selector string, found a boolean"]),
    ("a malformed selector", "[[deny]]\nfrom = \"mod:A\"\nto = [\"pkg:\"]\nreason = \"r\"\n",
      .error #["p.toml:3:6: invalid selector 'pkg:': nothing after 'pkg:'"]),
    ("transitive not a boolean", denyWith "transitive = \"yes\"\n",
      .error #["p.toml:5:13: deny rule 1: 'transitive' must be true or false, found a string"]),
    ("reason not a string", "[[deny]]\nfrom = \"mod:A\"\nto = \"mod:B\"\nreason = 7\n",
      .error #["p.toml:4:9: deny rule 1: 'reason' must be a string, found an integer"]),
    ("reason blank", "[[deny]]\nfrom = \"mod:A\"\nto = \"mod:B\"\nreason = \"  \"\n",
      .error #["p.toml:4:9: deny rule 1: 'reason' is empty"]),
    ("a rule with errors keeps its number",
      "[[deny]]\nto = \"mod:B\"\n\n[[deny]]\nfrom = \"mod:A\"\nto = \"mod:B\"\nreason = 1\n",
      .error
        #["p.toml:1:0: deny rule 1 has no 'from'", "p.toml:1:0: deny rule 1 has no 'reason'",
          "p.toml:7:9: deny rule 2: 'reason' must be a string, found an integer"]),
    -- References.
    ("an unknown set",
      "[sets]\ncore = [\"pkg:core\"]\n\n[[deny]]\nfrom = \"set:core\"\nto = \"set:cor\"\n\
        reason = \"r\"\n",
      .error
        #["p.toml:6:5: selector 'set:cor' in deny rule 1 ('to') names an unknown set \
            (defined: core)"]),
    ("an unknown set inside imports:",
      "[sets]\ncore = [\"pkg:core\"]\n\n[[deny]]\nfrom = \"set:core\"\nto = \"imports:set:nope\"\n\
        reason = \"r\"\n",
      .error
        #["p.toml:6:5: selector 'imports:set:nope' in deny rule 1 ('to') names an unknown set \
            (defined: core)"]),
    ("an unknown set with no sets", denyWith "wrappers = [\"mod:W\", \"set:w\"]\n",
      .error
        #["p.toml:5:21: selector 'set:w' in deny rule 1 ('wrappers') names an unknown set \
            (the policy defines no sets)"]),
    -- A rule and a set with errors: shape and syntax in source order, then the
    -- sets' references, then the rules'.
    ("a rule and a set with errors",
      "[[deny]]\nfrom = \"set:nope\"\nto = []\nreason = \"r\"\n\n[sets]\na = [\"set:zz\"]\nb = []\n",
      .error
        #["p.toml:3:5: deny rule 1: 'to' is empty", "p.toml:8:4: set 'b' is empty",
          "p.toml:7:5: selector 'set:zz' in set 'a' names an unknown set (defined: a, b)",
          "p.toml:2:7: selector 'set:nope' in deny rule 1 ('from') names an unknown set \
            (defined: a, b)"])]

/-- An allow-only table with `from`, `allow` and `reason`, then `extra` lines. -/
def allowOnlyWith (extra : String) : String :=
  s!"[[allow-only]]\nfrom = \"mod:A\"\nallow = \"mod:B\"\nreason = \"r\"\n{extra}"

/-- `[[allow-only]]` cases, as `cases`. -/
def allowOnlyCases : Array (String × String × Except (Array String) (Array String)) :=
  #[ -- The two forms, string versus array fields, `except` absent and present.
    ("[[allow-only]] tables",
      "[[allow-only]]\nfrom = \"mod:A\"\nallow = [\"mod:B\", \"external:Init\"]\nreason = \"r1\"\n\n\
        [[allow-only]]\nfrom = [\"mod:X\"]\nexcept = \"mod:X.T!\"\nallow = \"mod:C!\"\n\
        reason = \"r2\"\n",
      .ok
        #["order: ",
          "allow-only#1@1:0 from[mod:A@2:7 allow-only1.from] allow[mod:B@3:9 allow-only1.allow, \
            external:Init@3:18 allow-only1.allow] reason=\"r1\"",
          "allow-only#2@6:0 from[mod:X@7:8 allow-only2.from] except[mod:X.T!@8:9 \
            allow-only2.except] allow[mod:C!@9:8 allow-only2.allow] reason=\"r2\""]),
    ("inline tables",
      "allow-only = [{ from = \"mod:A\", allow = \"mod:B\", reason = \"r\" }, \
        { from = \"mod:C\", except = [\"mod:C.T\"], allow = \"mod:D\", reason = \"s\" }]\n",
      .ok
        #["order: ",
          "allow-only#1@1:14 from[mod:A@1:23 allow-only1.from] allow[mod:B@1:40 \
            allow-only1.allow] reason=\"r\"",
          "allow-only#2@1:65 from[mod:C@1:74 allow-only2.from] except[mod:C.T@1:93 \
            allow-only2.except] allow[mod:D@1:113 allow-only2.allow] reason=\"s\""]),
    ("sets in every field",
      "[sets]\ncore = [\"pkg:core\"]\n\n[[allow-only]]\nfrom = \"set:core\"\n\
        except = [\"mod:A!\", \"set:core\"]\nallow = \"set:core\"\nreason = \"r\"\n",
      .ok
        #["core@2:7 [pkg:core@2:8 select(core)]", "order: core",
          "allow-only#1@4:0 from[set:core@5:7 allow-only1.from] except[mod:A!@6:10 \
            allow-only1.except, set:core@6:20 allow-only1.except] allow[set:core@7:8 \
            allow-only1.allow] reason=\"r\""]),
    -- The shape of `allow-only`.
    ("allow-only = 1", "allow-only = 1\n",
      .error #["p.toml:1:13: 'allow-only' must be an array of tables, such as [[allow-only]]"]),
    ("[allow-only]", "[allow-only]\nfrom = \"pkg:a\"\n",
      .error #["p.toml:1:0: 'allow-only' must be an array of tables, such as [[allow-only]]"]),
    ("allow-only = []", "allow-only = []\n",
      .error #["p.toml:1:13: 'allow-only' is empty (omit it)"]),
    ("allow-only = [1]", "allow-only = [1]\n",
      .error #["p.toml:1:14: allow-only rule 1 must be a table, found an integer"]),
    -- Every load-time error of an allow-only table.
    ("missing keys", "[[allow-only]]\nexcept = \"mod:A\"\n",
      .error
        #["p.toml:1:0: allow-only rule 1 has no 'from'",
          "p.toml:1:0: allow-only rule 1 has no 'allow'",
          "p.toml:1:0: allow-only rule 1 has no 'reason'"]),
    ("missing keys come before the entries' errors", "[[allow-only]]\nallow = 1\n",
      .error
        #["p.toml:1:0: allow-only rule 1 has no 'from'",
          "p.toml:1:0: allow-only rule 1 has no 'reason'",
          "p.toml:2:8: allow-only rule 1: 'allow' must be a selector or an array of selectors, \
            found an integer"]),
    ("an unknown key", allowOnlyWith "allows = \"mod:W\"\n",
      .error
        #["p.toml:5:9: allow-only rule 1: unknown key 'allows' (expected from, except, allow, \
            reason)"]),
    ("from, except and allow not selectors",
      "[[allow-only]]\nfrom = 1\nexcept = { a = 1 }\nallow = true\nreason = \"r\"\n",
      .error
        #["p.toml:2:7: allow-only rule 1: 'from' must be a selector or an array of selectors, \
            found an integer",
          "p.toml:3:9: allow-only rule 1: 'except' must be a selector or an array of selectors, \
            found a table",
          "p.toml:4:8: allow-only rule 1: 'allow' must be a selector or an array of selectors, \
            found a boolean"]),
    ("empty lists", "[[allow-only]]\nfrom = []\nexcept = []\nallow = []\nreason = \"r\"\n",
      .error
        #["p.toml:2:7: allow-only rule 1: 'from' is empty",
          "p.toml:3:9: allow-only rule 1: 'except' is empty (omit it)",
          "p.toml:4:8: allow-only rule 1: 'allow' is empty"]),
    ("an element not a string", allowOnlyWith "except = [\"mod:W\", true]\n",
      .error
        #["p.toml:5:19: allow-only rule 1 ('except'): expected a selector string, found a \
            boolean"]),
    ("a malformed selector",
      "[[allow-only]]\nfrom = \"mod:A\"\nallow = [\"pkg:\"]\nreason = \"r\"\n",
      .error #["p.toml:3:9: invalid selector 'pkg:': nothing after 'pkg:'"]),
    ("reason not a string", "[[allow-only]]\nfrom = \"mod:A\"\nallow = \"mod:B\"\nreason = false\n",
      .error #["p.toml:4:9: allow-only rule 1: 'reason' must be a string, found a boolean"]),
    ("reason blank", "[[allow-only]]\nfrom = \"mod:A\"\nallow = \"mod:B\"\nreason = \"  \"\n",
      .error #["p.toml:4:9: allow-only rule 1: 'reason' is empty"]),
    ("a rule with errors keeps its number",
      "[[allow-only]]\nallow = \"mod:B\"\n\n[[allow-only]]\nfrom = \"mod:A\"\nallow = \"mod:B\"\n\
        reason = 1\n",
      .error
        #["p.toml:1:0: allow-only rule 1 has no 'from'",
          "p.toml:1:0: allow-only rule 1 has no 'reason'",
          "p.toml:7:9: allow-only rule 2: 'reason' must be a string, found an integer"]),
    -- References.
    ("an unknown set",
      "[sets]\napi = [\"pkg:core\"]\n\n[[allow-only]]\nfrom = \"set:ap\"\nallow = \"set:api\"\n\
        reason = \"r\"\n",
      .error
        #["p.toml:5:7: selector 'set:ap' in allow-only rule 1 ('from') names an unknown set \
            (defined: api)"]),
    ("an unknown set in allow with no sets",
      "[[allow-only]]\nfrom = \"mod:A\"\nallow = [\"mod:B\", \"set:w\"]\nreason = \"r\"\n",
      .error
        #["p.toml:3:18: selector 'set:w' in allow-only rule 1 ('allow') names an unknown set \
            (the policy defines no sets)"]),
    ("unknown sets in both kinds of rule: deny's first",
      "[[allow-only]]\nfrom = \"set:a\"\nallow = \"mod:B\"\nreason = \"r\"\n\n\
        [[deny]]\nfrom = \"set:d\"\nto = \"mod:B\"\nreason = \"r\"\n",
      .error
        #["p.toml:7:7: selector 'set:d' in deny rule 1 ('from') names an unknown set (the \
            policy defines no sets)",
          "p.toml:2:7: selector 'set:a' in allow-only rule 1 ('from') names an unknown set (the \
            policy defines no sets)"]),
    ("a deny rule and an allow-only rule",
      "[[deny]]\nfrom = \"mod:A\"\nto = \"mod:B\"\nreason = \"r\"\n\n" ++ allowOnlyWith "",
      .ok
        #["order: ", "deny#1@1:0 from[mod:A@2:7 deny1.from] to[mod:B@3:5 deny1.to] reason=\"r\"",
          "allow-only#1@6:0 from[mod:A@7:7 allow-only1.from] allow[mod:B@8:8 allow-only1.allow] \
            reason=\"r\""])]

/-- A `[layers]` table whose line 2 is one classify entry (`core`,
`mod:C`, its `select` at 2:39), then `extra` lines. -/
def layersWith (extra : String) : String :=
  s!"[layers]\nclassify = [\{ layer = \"core\", select = \"mod:C\" }]\n{extra}"

/-- `[layers]` with one classify entry written as `entry` on line 2. -/
def layersEntry (entry : String) : String :=
  s!"[layers]\nclassify = [{entry}]\n"

/-- The message for an `allow` element that is no pair, at `pos`. -/
def notPair (pos : String) : String :=
  s!"p.toml:{pos}: layers: allow entry 1 must be a pair of layer names [importer, imported], \
    such as [\"implementation\", \"core\"]"

/-- `[layers]` cases, as `cases`. -/
def layersCases : Array (String × String × Except (Array String) (Array String)) :=
  #[ -- The three forms.
    ("[layers] table",
      "[layers]\nclassify = [\n  { layer = \"core\", select = \"mod:C\" },\n  \
        { layer = \"iface\", select = [\"mod:I\", \"mod:J\"] },\n]\ndefault = \"impl\"\n\
        allow = [[\"iface\", \"core\"], [\"impl\", \"core\"]]\nreason = \"why\"\n",
      .ok
        #["order: ",
          "layers@1:0 classify[core@3:2(mod:C@3:29 layers1), iface@4:2(mod:I@4:31 layers2, \
            mod:J@4:40 layers2)] default=impl@6:10 allow[iface>core@7:9, impl>core@7:28] \
            reason=\"why\""]),
    ("inline", "layers = { classify = [{ layer = \"core\", select = \"mod:C\" }] }\n",
      .ok
        #["order: ",
          "layers@1:9 classify[core@1:23(mod:C@1:50 layers1)] default=- allow[] reason=-"]),
    ("sub-tables",
      "[layers]\ndefault = \"impl\"\n\n[[layers.classify]]\nlayer = \"core\"\nselect = \"mod:C\"\n",
      .ok
        #["order: ",
          "layers@1:0 classify[core@4:0(mod:C@6:9 layers1)] default=impl@2:10 allow[] \
            reason=-"]),
    ("same-package = \"allow\"", layersWith "same-package = \"allow\"\n",
      .ok
        #["order: ",
          "layers@1:0 classify[core@2:12(mod:C@2:39 layers1)] default=- allow[] reason=-"]),
    ("a self pair and a default that is a classify layer",
      layersWith "default = \"core\"\nallow = [[\"core\", \"core\"]]\n",
      .ok
        #["order: ",
          "layers@1:0 classify[core@2:12(mod:C@2:39 layers1)] default=core@3:10 \
            allow[core>core@4:9] reason=-"]),
    -- The shape of `layers`.
    ("layers = []", "layers = []\n",
      .error #["p.toml:1:9: 'layers' must be a table, such as [layers]"]),
    ("[[layers]]", "[[layers]]\nclassify = []\n",
      .error #["p.toml:1:0: 'layers' must be a table, such as [layers]"]),
    ("no classify", "[layers]\ndefault = \"x\"\n",
      .error #["p.toml:1:0: layers has no 'classify'"]),
    ("classify = 1", "[layers]\nclassify = 1\n",
      .error
        #["p.toml:2:11: layers: 'classify' must be an array of tables, such as [[layers.classify]]"]),
    ("classify = []", "[layers]\nclassify = []\n",
      .error #["p.toml:2:11: layers: 'classify' is empty"]),
    -- Every load-time error of a classify entry.
    ("an entry not a table", layersEntry "\"mod:C\"",
      .error #["p.toml:2:12: layers classify entry 1 must be a table, found a string"]),
    ("missing keys, in order", layersEntry "{}",
      .error
        #["p.toml:2:12: layers classify entry 1 has no 'layer'",
          "p.toml:2:12: layers classify entry 1 has no 'select'"]),
    ("missing keys come before the entry's errors", layersEntry "{ select = 1 }",
      .error
        #["p.toml:2:12: layers classify entry 1 has no 'layer'",
          "p.toml:2:23: layers classify entry 1: 'select' must be a selector or an array of \
            selectors, found an integer"]),
    ("an unknown entry key", layersEntry "{ layer = \"core\", select = \"mod:C\", kind = 1 }",
      .error
        #["p.toml:2:55: layers classify entry 1: unknown key 'kind' (expected layer, select)"]),
    ("layer = 1", layersEntry "{ layer = 1, select = \"mod:C\" }",
      .error
        #["p.toml:2:22: layers classify entry 1: 'layer' must be a layer name, found an integer"]),
    ("layer = \"a b\"", layersEntry "{ layer = \"a b\", select = \"mod:C\" }",
      .error
        #["p.toml:2:22: layers classify entry 1: invalid layer name 'a b' (use letters, digits, \
            '-' and '_')"]),
    ("select = 3", layersEntry "{ layer = \"core\", select = 3 }",
      .error
        #["p.toml:2:39: layers classify entry 1: 'select' must be a selector or an array of \
            selectors, found an integer"]),
    ("select = []", layersEntry "{ layer = \"core\", select = [] }",
      .error #["p.toml:2:39: layers classify entry 1: 'select' is empty"]),
    ("select = [1]", layersEntry "{ layer = \"core\", select = [1] }",
      .error
        #["p.toml:2:40: layers classify entry 1 ('select'): expected a selector string, found an \
            integer"]),
    ("select = [\"Core\"]", layersEntry "{ layer = \"core\", select = [\"Core\"] }",
      .error
        #["p.toml:2:40: invalid selector 'Core': expected '<kind>:<value>', such as \
            'mod:Editor.Api'"]),
    -- Every load-time error of the table's other keys.
    ("default = 1", layersWith "default = 1\n",
      .error #["p.toml:3:10: layers: 'default' must be a layer name, found an integer"]),
    ("default = \"a b\"", layersWith "default = \"a b\"\n",
      .error #["p.toml:3:10: layers: invalid layer name 'a b' (use letters, digits, '-' and '_')"]),
    ("allow = \"x\"", layersWith "allow = \"x\"\n",
      .error
        #["p.toml:3:8: layers: 'allow' must be an array of layer pairs, such as \
            [[\"implementation\", \"core\"]], found a string"]),
    ("allow = []", layersWith "allow = []\n",
      .error #["p.toml:3:8: layers: 'allow' is empty (omit it)"]),
    ("allow = [[\"a\"]]", layersWith "allow = [[\"a\"]]\n", .error #[notPair "3:9"]),
    ("allow = [[\"a\", 1]]", layersWith "allow = [[\"a\", 1]]\n", .error #[notPair "3:9"]),
    ("allow = [1]", layersWith "allow = [1]\n", .error #[notPair "3:9"]),
    ("a repeated pair", layersWith "allow = [[\"core\", \"core\"], [\"core\", \"core\"]]\n",
      .error #["p.toml:3:27: layers: allow entry 2 repeats allow entry 1 ([\"core\", \"core\"])"]),
    ("an unknown layer on each side, importer first", layersWith "allow = [[\"x\", \"y\"]]\n",
      .error
        #["p.toml:3:10: layers: allow entry 1 names layer 'x', which neither a classify entry nor \
            'default' declares (layers: core)",
          "p.toml:3:15: layers: allow entry 1 names layer 'y', which neither a classify entry nor \
            'default' declares (layers: core)"]),
    ("the unknown-layer errors come after the table's others",
      "[layers]\nallow = [[\"core\", \"impl\"]]\nclassify = [{ layer = \"core\", select = 1 }]\n\
        default = \"dflt\"\n",
      .error
        #["p.toml:3:39: layers classify entry 1: 'select' must be a selector or an array of \
            selectors, found an integer",
          "p.toml:2:18: layers: allow entry 1 names layer 'impl', which neither a classify entry \
            nor 'default' declares (layers: core, dflt)"]),
    ("the unknown-layer check is skipped when an entry's layer is bad",
      "[layers]\nclassify = [{ layer = 1, select = \"mod:C\" }]\nallow = [[\"x\", \"core\"]]\n",
      .error
        #["p.toml:2:22: layers classify entry 1: 'layer' must be a layer name, found an integer"]),
    ("the unknown-layer check is skipped when default is bad",
      layersWith "default = \"a b\"\nallow = [[\"x\", \"core\"]]\n",
      .error #["p.toml:3:10: layers: invalid layer name 'a b' (use letters, digits, '-' and '_')"]),
    ("same-package = \"check\"", layersWith "same-package = \"check\"\n",
      .error
        #["p.toml:3:15: layers: 'same-package' must be \"allow\": imports within one package are \
            always allowed"]),
    ("same-package = true", layersWith "same-package = true\n",
      .error
        #["p.toml:3:15: layers: 'same-package' must be \"allow\": imports within one package are \
            always allowed"]),
    ("reason = \"\"", layersWith "reason = \"\"\n",
      .error #["p.toml:3:9: layers: 'reason' is empty"]),
    ("reason = false", layersWith "reason = false\n",
      .error #["p.toml:3:9: layers: 'reason' must be a string, found a boolean"]),
    ("an unknown key", layersWith "allows = 1\n",
      .error
        #["p.toml:3:9: layers: unknown key 'allows' (expected classify, default, allow, \
            same-package, reason)"]),
    -- References.
    ("an unknown set in select",
      layersEntry "{ layer = \"core\", select = [\"mod:C\", \"set:l\"] }",
      .error
        #["p.toml:2:49: selector 'set:l' in layers classify entry 1 names an unknown set (the \
            policy defines no sets)"]),
    ("unknown sets in all three kinds of rule, in text order",
      "[[deny]]\nfrom = \"set:d\"\nto = \"mod:B\"\nreason = \"r\"\n\n[[allow-only]]\n\
        from = \"set:a\"\nallow = \"mod:B\"\nreason = \"r\"\n\n[layers]\n\
        classify = [{ layer = \"core\", select = \"set:l\" }]\n",
      .error
        #["p.toml:2:7: selector 'set:d' in deny rule 1 ('from') names an unknown set (the \
            policy defines no sets)",
          "p.toml:7:7: selector 'set:a' in allow-only rule 1 ('from') names an unknown set (the \
            policy defines no sets)",
          "p.toml:12:39: selector 'set:l' in layers classify entry 1 names an unknown set (the \
            policy defines no sets)"]),
    ("unknown sets in all three kinds of rule, the text reversed",
      "[layers]\nclassify = [{ layer = \"core\", select = \"set:l\" }]\n\n[[allow-only]]\n\
        from = \"set:a\"\nallow = \"mod:B\"\nreason = \"r\"\n\n[[deny]]\nfrom = \"set:d\"\n\
        to = \"mod:B\"\nreason = \"r\"\n",
      .error
        #["p.toml:10:7: selector 'set:d' in deny rule 1 ('from') names an unknown set (the \
            policy defines no sets)",
          "p.toml:5:7: selector 'set:a' in allow-only rule 1 ('from') names an unknown set (the \
            policy defines no sets)",
          "p.toml:2:39: selector 'set:l' in layers classify entry 1 names an unknown set (the \
            policy defines no sets)"])]

/-- `[[root]]`'s cases: the valid forms and every load-time error. -/
def rootCases : Array (String × String × Except (Array String) (Array String)) :=
  #[("one root", "[[root]]\nmodule = \"Gen\"\npath = \".lake/build/root/Gen.lean\"\n",
      .ok #["order: ", "root#1@1:0 Gen=.lake/build/root/Gen.lean"]),
    ("two roots, inline, escaped name and '..'",
      "root = [\n  { module = \"«my-mod».X\", path = \"../x/X.lean\" },\n  \
        { module = \"Y\", path = \"y.lean\" },\n]\n",
      .ok #["order: ", "root#1@2:2 «my-mod».X=../x/X.lean", "root#2@3:2 Y=y.lean"]),
    ("roots are not rules", s!"{denyWith ""}\n[[root]]\nmodule = \"G\"\npath = \"g.lean\"\n",
      .ok
        #["order: ", "deny#1@1:0 from[mod:A@2:7 deny1.from] to[mod:B@3:5 deny1.to] reason=\"r\"",
          "root#1@6:0 G=g.lean"]),
    ("root = \"x\"", "root = \"x\"\n",
      .error #["p.toml:1:7: 'root' must be an array of tables, such as [[root]]"]),
    ("root = []", "root = []\n", .error #["p.toml:1:7: 'root' is empty (omit it)"]),
    ("root = [1]", "root = [1]\n",
      .error #["p.toml:1:8: root 1 must be a table, found an integer"]),
    ("no module, no path", "[[root]]\n",
      .error #["p.toml:1:0: root 1 has no 'module'", "p.toml:1:0: root 1 has no 'path'"]),
    ("unknown key", "[[root]]\nmodule = \"G\"\npath = \"g.lean\"\nfile = 1\n",
      .error #["p.toml:4:7: root 1: unknown key 'file' (expected module, path)"]),
    ("module not a string", "[[root]]\nmodule = [\"G\"]\npath = \"g.lean\"\n",
      .error #["p.toml:2:9: root 1: 'module' must be a string, found an array"]),
    ("module not a name", "[[root]]\nmodule = \"G..H\"\npath = \"g.lean\"\n",
      .error #["p.toml:2:9: root 1: 'module': 'G..H' is not a module name"]),
    ("path not a string", "[[root]]\nmodule = \"G\"\npath = 1\n",
      .error #["p.toml:3:7: root 1: 'path' must be a string, found an integer"]),
    ("path empty", "[[root]]\nmodule = \"G\"\npath = \"\"\n",
      .error #["p.toml:3:7: root 1: 'path' must not be empty"]),
    ("path absolute", "[[root]]\nmodule = \"G\"\npath = \"/g.lean\"\n",
      .error #["p.toml:3:7: root 1: 'path' must be relative to the workspace directory"]),
    ("duplicate module and path",
      "[[root]]\nmodule = \"G\"\npath = \"g.lean\"\n[[root]]\nmodule = \"G\"\npath = \"g.lean\"\n",
      .error
        #["p.toml:4:0: root 2: module G is already declared by root 1",
          "p.toml:4:0: root 2: path 'g.lean' is already declared by root 1"])]

/-- `Policy.rootsOfToml` reads only `root`: other keys, even unknown or
broken ones, are not checked; a bad root table still is. -/
def rootsOnlyFailures : IO (Array String) := do
  let cases : Array (String × String × Except (Array String) (Array String)) :=
    #[("no root", "bans = 1\n", .ok #[]),
      ("broken rules ignored",
        "bans = 1\n[[deny]]\nfrom = 1\n[[root]]\nmodule = \"G\"\npath = \"g.lean\"\n",
        .ok #["root#1@4:0 G=g.lean"]),
      ("bad root reported", "bans = 1\n[[root]]\nmodule = \"G\"\n",
        .error #["p.toml:2:0: root 1 has no 'path'"])]
  let mut fs := #[]
  for (name, src, want) in cases do
    let got ←
      match ← Toml.parseLocated "p.toml" src with
      | .error es =>
        pure (.error es)
      | .ok entries =>
        pure ((Policy.rootsOfToml "p.toml" entries).map (·.map renderRoot))
    let same :=
      match got, want with
      | .ok a, .ok b => a == b
      | .error a, .error b => a == b
      | _, _ => false
    unless same do
      fs := fs.push s!"rootsOfToml {name}: expected {repr want}, got {repr got}"
  return fs

/-- The policy README.md's "A policy, sketched" shows, verbatim. -/
def readmeSketch : String :=
  "# lean-deny.toml

[sets]
core = [\"pkg:editor\"]
core-api = [\"mod:Editor.Api\", \"lib:EditorInterfaces\"]

# The core depends on no feature package, not even indirectly.
[[deny]]
from = \"set:core\"
to = \"keyword:editor-feature\"
transitive = true
reason = \"a package may depend on the core, and the core on no package\"

# Plain modules stay clear of Lean's frontend.
[[deny]]
from = \"mod:Editor.Text\"
to = \"external:Lean.Elab\"
transitive = true
reason = \"text handling must not pull in the elaborator\"

# A feature package's library uses the core's API and nothing else of it.
[[allow-only]]
from = \"keyword:editor-feature\"
allow = [\"set:core-api\", \"external:Init\", \"external:Std\"]
reason = \"packages import the core's API alone\"

# Three layers: implementations go through interfaces, never each other.
[layers]
classify = [
  { layer = \"core\", select = \"set:core\" },
  { layer = \"interface\", select = \"keyword:editor-interface\" },
]
default = \"implementation\"
allow = [
  [\"interface\", \"core\"],
  [\"implementation\", \"core\"],
  [\"implementation\", \"interface\"],
]
"

/-- The README's sketched policy loads, with every rule. -/
def sketchFailures : IO (Array String) := do
  match ← load readmeSketch with
  | .error es =>
    return #[s!"README sketch: expected it to load, got {repr es}"]
  | .ok p =>
    if p.deny.size == 2 && p.allowOnly.size == 1 && p.layers?.isSome && p.ruleCount == 4 then
      return #[]
    return #[s!"README sketch: expected 2 deny rules, 1 allow-only rule and [layers], got \
        {repr (renderPolicy p)}"]

def renderResult : Except (Array String) (Array String) → String
  | .ok xs => s!"ok {repr xs}"
  | .error es => s!"error {repr es}"

/-- The renderings of `Use` and `SelectorRef`. -/
def renderingFailures : Array String :=
  let r (use : Use) : SelectorRef := { text := "mod:X", sel := .mod `X false, pos? := none, use }
  let want :=
    [(r (.setSelect "core"), "selector 'mod:X' in set 'core'"),
      (r (.setExcept "core"), "selector 'mod:X' in the except list of set 'core'"),
      (r (.rule "deny" 2 "from"), "selector 'mod:X' in deny rule 2 ('from')"),
      (r (.rule "allow-only" 2 "except"), "selector 'mod:X' in allow-only rule 2 ('except')"),
      (r (.layer 2), "selector 'mod:X' in layers classify entry 2"),
      (r .commandLine, "selector 'mod:X'")]
  let clause :=
    if (Use.layer 2).clause == " in layers classify entry 2" then #[]
    else #[s!"clause: got {repr (Use.layer 2).clause}"]
  let fs :=
    clause ++
      want.toArray.filterMap fun (ref, w) =>
        if ref.describe == w then none
        else some s!"describe: expected {repr w}, got {repr ref.describe}"
  let locs :=
    [(Policy.locate "p.toml" (some { line := 3, column := 0 }) "m", "p.toml:3:0: m"),
      (Policy.locate "p.toml" none "m", "p.toml: m"),
      (Policy.posText "p.toml" (some { line := 4, column := 7 }), "p.toml:4:7"),
      (Policy.posText "p.toml" none, "p.toml")]
  fs ++
    locs.toArray.filterMap fun (got, w) =>
      if got == w then none else some s!"locate: expected {repr w}, got {repr got}"

/-- `[[require-backed]]`: the two forms of `packages`, and every load-time
error. -/
def requireBackedCases : Array (String × String × Except (Array String) (Array String)) :=
  #[("require-backed, one selector", "[[require-backed]]\npackages = \"pkg:a\"\nreason = \"r\"\n",
      .ok
        #["order: ",
          "require-backed#1@1:0 packages[pkg:a@2:11 require-backed1.packages] reason=\"r\""]),
    ("require-backed, an array of selectors",
      "[[require-backed]]\npackages = [\"pkg:a\", \"keyword:impl\"]\nreason = \"r\"\n",
      .ok
        #["order: ",
          "require-backed#1@1:0 packages[pkg:a@2:12 require-backed1.packages, \
            keyword:impl@2:21 require-backed1.packages] reason=\"r\""]),
    ("require-backed, no packages", "[[require-backed]]\nreason = \"r\"\n",
      .error #["p.toml:1:0: require-backed rule 1 has no 'packages'"]),
    ("require-backed, no reason", "[[require-backed]]\npackages = \"pkg:a\"\n",
      .error #["p.toml:1:0: require-backed rule 1 has no 'reason'"]),
    ("require-backed, empty packages", "[[require-backed]]\npackages = []\nreason = \"r\"\n",
      .error #["p.toml:2:11: require-backed rule 1: 'packages' is empty"]),
    ("require-backed, wrong types", "[[require-backed]]\npackages = 1\nreason = 2\n",
      .error
        #["p.toml:2:11: require-backed rule 1: 'packages' must be a selector or an array of \
            selectors, found an integer",
          "p.toml:3:9: require-backed rule 1: 'reason' must be a string, found an integer"]),
    ("require-backed, a blank reason", "[[require-backed]]\npackages = \"pkg:a\"\nreason = \"\"\n",
      .error #["p.toml:3:9: require-backed rule 1: 'reason' is empty"]),
    ("require-backed, an unknown key",
      "[[require-backed]]\npackages = \"pkg:a\"\nfrom = \"pkg:x\"\nreason = \"r\"\n",
      .error
        #["p.toml:3:7: require-backed rule 1: unknown key 'from' (expected packages, reason)"]),
    ("require-backed, not an array", "require-backed = 1\n",
      .error
        #["p.toml:1:17: 'require-backed' must be an array of tables, such as [[require-backed]]"]),
    ("require-backed, an unknown set",
      "[[require-backed]]\npackages = \"set:nope\"\nreason = \"r\"\n",
      .error
        #["p.toml:2:11: selector 'set:nope' in require-backed rule 1 ('packages') names an \
            unknown set (the policy defines no sets)"])]

/-- A doc-modules table with the given lines after its header. -/
def docTable (lines : String) : String :=
  s!"[[doc-modules]]\n{lines}"

/-- A doc-modules table's lines: `file`, `section`, `prefix`, `modules` and
`reason`, each valid. -/
def docLines : String :=
  "file = \"docs/m.md\"\nsection = \"Mods\"\nprefix = \"A.\"\nmodules = \"mod:A\"\n\
    reason = \"r\"\n"

/-- `[[doc-modules]]`: the two forms of `modules`, and every load-time
error. -/
def docModulesCases : Array (String × String × Except (Array String) (Array String)) :=
  #[("doc-modules, one selector", docTable docLines,
      .ok
        #["order: ",
          "doc-modules#1@1:0 file=\"docs/m.md\" section=\"Mods\" prefix=\"A.\" \
            modules[mod:A@5:10 doc-modules1.modules] reason=\"r\""]),
    ("doc-modules, an array of selectors",
      docTable
        "file = \"m.md\"\nsection = \"S\"\nprefix = \"A.\"\n\
        modules = [\"mod:A\", \"pkg:a\"]\nreason = \"r\"\n",
      .ok
        #["order: ",
          "doc-modules#1@1:0 file=\"m.md\" section=\"S\" prefix=\"A.\" \
            modules[mod:A@5:11 doc-modules1.modules, pkg:a@5:20 doc-modules1.modules] \
            reason=\"r\""]),
    ("doc-modules, every key missing", "[[doc-modules]]\n",
      .error
        #["p.toml:1:0: doc-modules rule 1 has no 'file'",
          "p.toml:1:0: doc-modules rule 1 has no 'section'",
          "p.toml:1:0: doc-modules rule 1 has no 'prefix'",
          "p.toml:1:0: doc-modules rule 1 has no 'modules'",
          "p.toml:1:0: doc-modules rule 1 has no 'reason'"]),
    ("doc-modules, empty values",
      docTable "file = \"\"\nsection = \"  \"\nprefix = \"\"\nmodules = []\nreason = \"\"\n",
      .error
        #["p.toml:2:7: doc-modules rule 1: 'file' must not be empty",
          "p.toml:3:10: doc-modules rule 1: 'section' is empty",
          "p.toml:4:9: doc-modules rule 1: 'prefix' is empty",
          "p.toml:5:10: doc-modules rule 1: 'modules' is empty",
          "p.toml:6:9: doc-modules rule 1: 'reason' is empty"]),
    ("doc-modules, wrong types",
      docTable "file = 1\nsection = true\nprefix = []\nmodules = 2\nreason = 3\n",
      .error
        #["p.toml:2:7: doc-modules rule 1: 'file' must be a string, found an integer",
          "p.toml:3:10: doc-modules rule 1: 'section' must be a string, found a boolean",
          "p.toml:4:9: doc-modules rule 1: 'prefix' must be a string, found an array",
          "p.toml:5:10: doc-modules rule 1: 'modules' must be a selector or an array of \
            selectors, found an integer",
          "p.toml:6:9: doc-modules rule 1: 'reason' must be a string, found an integer"]),
    ("doc-modules, an absolute file",
      docTable
        "file = \"/docs/m.md\"\nsection = \"S\"\nprefix = \"A.\"\nmodules = \"mod:A\"\n\
        reason = \"r\"\n",
      .error
        #["p.toml:2:7: doc-modules rule 1: 'file' must be relative to the workspace directory"]),
    ("doc-modules, an unknown key", docTable (docLines ++ "heading = \"S\"\n"),
      .error
        #["p.toml:7:10: doc-modules rule 1: unknown key 'heading' (expected file, section, \
            prefix, modules, reason)"]),
    ("doc-modules, not an array", "doc-modules = 1\n",
      .error #["p.toml:1:14: 'doc-modules' must be an array of tables, such as [[doc-modules]]"]),
    ("doc-modules, an unknown set",
      docTable
        "file = \"m.md\"\nsection = \"S\"\nprefix = \"A.\"\nmodules = \"set:nope\"\n\
        reason = \"r\"\n",
      .error
        #["p.toml:5:10: selector 'set:nope' in doc-modules rule 1 ('modules') names an unknown \
            set (the policy defines no sets)"])]

/-- A `[layers]` table of two lines, `classify` and `default` (no `allow`,
so it allows nothing), before a doc-packages table. -/
def layersTable : String :=
  "[layers]\nclassify = [{ layer = \"core\", select = \"pkg:core\" }]\ndefault = \"impl\"\n"

/-- `[layers]` (lines 1 to 3), then a doc-packages table (header on line 4)
with the given lines after its header. -/
def pkgTable (lines : String) : String :=
  s!"{layersTable}[[doc-packages]]\n{lines}"

/-- A doc-packages table's lines: `file`, `section`, the three columns,
`packages` and `reason`, each valid. -/
def pkgLines : String :=
  "file = \"docs/p.md\"\nsection = \"Pkgs\"\npackage-column = \"Package\"\n\
    layer-column = \"Layer\"\nrequires-column = \"Requires, beside the core\"\n\
    packages = \"set:default\"\nreason = \"r\"\n"

/-- The rendered `[layers]` of `layersTable`. -/
def layersRendered : String :=
  "layers@1:0 classify[core@2:12(pkg:core@2:39 layers1)] default=impl@3:10 allow[] reason=-"

/-- `layersRendered` two lines down, after a two-line `[sets]`. -/
def layersAfterSets : String :=
  "layers@3:0 classify[core@4:12(pkg:core@4:39 layers1)] default=impl@5:10 allow[] reason=-"

/-- `[[doc-packages]]`: `requires-except` absent, a name and an array, and
every load-time error. -/
def docPackagesCases : Array (String × String × Except (Array String) (Array String)) :=
  let sets := "[sets]\ndefault = [\"pkg:a\"]\n"
  #[("doc-packages, no requires-except", sets ++ pkgTable pkgLines,
      .ok
        #["default@2:10 [pkg:a@2:11 select(default)]", "order: default", layersAfterSets,
          "doc-packages#1@6:0 file=\"docs/p.md\" section=\"Pkgs\" \
            columns=\"Package\",\"Layer\",\"Requires, beside the core\" \
            packages[set:default@12:11 doc-packages1.packages] except[] reason=\"r\""]),
    ("doc-packages, requires-except a name, columns trimmed",
      pkgTable
        "file = \"p.md\"\nsection = \"S\"\npackage-column = \" P \"\nlayer-column = \"L\"\n\
        requires-column = \"R\"\npackages = [\"pkg:a\", \"pkg:b\"]\nrequires-except = \"core\"\n\
        reason = \"r\"\n",
      .ok
        #["order: ", layersRendered,
          "doc-packages#1@4:0 file=\"p.md\" section=\"S\" columns=\"P\",\"L\",\"R\" \
            packages[pkg:a@10:12 doc-packages1.packages, pkg:b@10:21 doc-packages1.packages] \
            except[core@11:18] reason=\"r\""]),
    ("doc-packages, requires-except an array",
      sets ++ pkgTable (pkgLines ++ "requires-except = [\"core\", \"base\"]\n"),
      .ok
        #["default@2:10 [pkg:a@2:11 select(default)]", "order: default", layersAfterSets,
          "doc-packages#1@6:0 file=\"docs/p.md\" section=\"Pkgs\" \
            columns=\"Package\",\"Layer\",\"Requires, beside the core\" \
            packages[set:default@12:11 doc-packages1.packages] except[core@14:19, base@14:27] \
            reason=\"r\""]),
    ("doc-packages, every required key missing", pkgTable "",
      .error
        #["p.toml:4:0: doc-packages rule 1 has no 'file'",
          "p.toml:4:0: doc-packages rule 1 has no 'section'",
          "p.toml:4:0: doc-packages rule 1 has no 'package-column'",
          "p.toml:4:0: doc-packages rule 1 has no 'layer-column'",
          "p.toml:4:0: doc-packages rule 1 has no 'requires-column'",
          "p.toml:4:0: doc-packages rule 1 has no 'packages'",
          "p.toml:4:0: doc-packages rule 1 has no 'reason'"]),
    ("doc-packages, empty values",
      pkgTable
        "file = \"\"\nsection = \" \"\npackage-column = \"\"\nlayer-column = \" \"\n\
        requires-column = \"\"\npackages = []\nrequires-except = []\nreason = \"\"\n",
      .error
        #["p.toml:5:7: doc-packages rule 1: 'file' must not be empty",
          "p.toml:6:10: doc-packages rule 1: 'section' is empty",
          "p.toml:7:17: doc-packages rule 1: 'package-column' is empty",
          "p.toml:8:15: doc-packages rule 1: 'layer-column' is empty",
          "p.toml:9:18: doc-packages rule 1: 'requires-column' is empty",
          "p.toml:10:11: doc-packages rule 1: 'packages' is empty",
          "p.toml:11:18: doc-packages rule 1: 'requires-except' is empty (omit it)",
          "p.toml:12:9: doc-packages rule 1: 'reason' is empty"]),
    ("doc-packages, wrong types",
      pkgTable
        "file = 1\nsection = true\npackage-column = []\nlayer-column = 2\nrequires-column = 3\n\
        packages = 4\nrequires-except = 5\nreason = 6\n",
      .error
        #["p.toml:5:7: doc-packages rule 1: 'file' must be a string, found an integer",
          "p.toml:6:10: doc-packages rule 1: 'section' must be a string, found a boolean",
          "p.toml:7:17: doc-packages rule 1: 'package-column' must be a string, found an array",
          "p.toml:8:15: doc-packages rule 1: 'layer-column' must be a string, found an integer",
          "p.toml:9:18: doc-packages rule 1: 'requires-column' must be a string, found an integer",
          "p.toml:10:11: doc-packages rule 1: 'packages' must be a selector or an array of \
            selectors, found an integer",
          "p.toml:11:18: doc-packages rule 1: 'requires-except' must be a package name or an \
            array of package names, found an integer",
          "p.toml:12:9: doc-packages rule 1: 'reason' must be a string, found an integer"]),
    ("doc-packages, bad requires-except names",
      pkgTable
        (pkgLines.replace "set:default" "pkg:a" ++ "requires-except = [\"core\", 1, \" \"]\n"),
      .error
        #["p.toml:12:27: doc-packages rule 1 ('requires-except'): expected a package name string, \
            found an integer",
          "p.toml:12:30: doc-packages rule 1 ('requires-except'): a package name is empty"]),
    ("doc-packages, an absolute file",
      pkgTable
        (("/docs/p.md").intercalate ((pkgLines.replace "set:default" "pkg:a").splitOn "docs/p.md")),
      .error
        #["p.toml:5:7: doc-packages rule 1: 'file' must be relative to the workspace directory"]),
    ("doc-packages, duplicate columns",
      pkgTable
        "file = \"p.md\"\nsection = \"S\"\nrequires-column = \"P\"\npackage-column = \"P\"\n\
        layer-column = \" P\"\npackages = \"pkg:a\"\nreason = \"r\"\n",
      .error
        #["p.toml:9:15: doc-packages rule 1: 'layer-column' names the same column as \
            'package-column' ('P')",
          "p.toml:7:18: doc-packages rule 1: 'requires-column' names the same column as \
            'package-column' ('P')"]),
    ("doc-packages, an unknown key",
      pkgTable (pkgLines.replace "set:default" "pkg:a" ++ "heading = \"S\"\n"),
      .error
        #["p.toml:12:10: doc-packages rule 1: unknown key 'heading' (expected file, section, \
            package-column, layer-column, requires-column, packages, requires-except, reason)"]),
    ("doc-packages, no [layers]",
      "[[doc-packages]]\n" ++ pkgLines.replace "set:default" "pkg:a" ++ "[[doc-packages]]\n" ++
        pkgLines.replace "set:default" "pkg:a",
      .error
        #["p.toml:1:0: doc-packages rule 1: the policy has no [layers], which gives each \
            package's layer",
          "p.toml:9:0: doc-packages rule 2: the policy has no [layers], which gives each \
            package's layer"]),
    ("doc-packages, not an array", "doc-packages = 1\n",
      .error #["p.toml:1:15: 'doc-packages' must be an array of tables, such as [[doc-packages]]"]),
    ("doc-packages, an unknown set", pkgTable pkgLines,
      .error
        #["p.toml:10:11: selector 'set:default' in doc-packages rule 1 ('packages') names an \
            unknown set (the policy defines no sets)"])]

def run : IO (Array String) := do
  let mut fs := renderingFailures ++ (← sketchFailures) ++ (← rootsOnlyFailures)
  for (name, src, want) in
    cases ++ denyCases ++ allowOnlyCases ++ layersCases ++ requireBackedCases ++ docModulesCases ++
      docPackagesCases ++
      rootCases do
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
