# Rules

Every rule kind `lean-deny.toml` takes: its keys, what it checks, its errors and what a violation looks like. Selectors and `[sets]` are in [policy.md](policy.md).

## deny

A `[[deny]]` rule says the modules of `from` must not import the modules of
`to`:

```toml
[[deny]]
from = "set:core"
to = "keyword:editor-implementation"
transitive = true
wrappers = ["mod:Editor.Adapters.Fs"]
reason = "the core imports no package"
```

| Key | Required | Value |
|---|---|---|
| `from` | yes | a selector, or a non-empty array of selectors (their union) |
| `to` | yes | the same |
| `transitive` | no | `true` or `false` (default `false`: direct imports only) |
| `wrappers` | no | a selector, or a non-empty array of selectors (default none) |
| `reason` | yes | a non-blank string, printed with every violation |

Rules are numbered `deny rule 1`, `deny rule 2`, … in the order they are
written. Both `[[deny]]` tables and an inline `deny = [{ … }, …]` work.

- **Direct** (`transitive = false`): every import from a module of `from` to
  a module of `to` is a violation, reported once per (importer, imported)
  pair, with the first such `import` as its witness. Every import counts:
  plain, `meta`, `public`, and Lean's implicit `Init` imports (so
  `to = "external:Init"` bites every module of `from` that is not
  `prelude`).
- **Transitive** (`transitive = true`): every module of `from` that reaches a
  module of `to` through one or more imports is a violation, reported once
  per `from` module, with a shortest import chain as its witness. Among
  equally short chains, the witness is the one found first when each
  module's imports are read in source order.
- The graph holds only the external modules the workspace imports directly,
  and they import nothing in it, so a chain ends at the first external
  module: `to = "external:Lean.Elab"` sees a module that imports
  `Lean.Elab.Command`, not one that imports `Lean`, which imports it.

**Wrappers** are the modules allowed to import `to` (cargo-deny's
`wrappers`). A `from` module that is a wrapper is excused, in both modes. A
transitive rule never follows the imports of a wrapper, so a chain that
passes through one is allowed; a chain that avoids every wrapper is still a
violation. A wrapper that is itself in `to` still counts as reached: a
chain into it is a violation, since a chain stops at the first module of
`to` it reaches.

A wrapper selector must excuse something. A wrapper module is used when it
is the first wrapper on a chain from `from` to `to`: for a direct rule, it
is in `from` and imports a module of `to`; for a transitive rule, it is in
`from`, or reached from `from` without passing through another wrapper or a
module of `to`, and some module of `to` is reachable from it. A selector none
of whose modules is used is an error. A wrapper module in `to` is never
used, in either mode: no module of `to` is in `from`, and a chain stops at
it. When every module a selector matches is in `to`, the error says so: list
the module that imports it instead. One used module is enough, so
`wrappers = ["mod:Editor.Adapters"]` may cover several adapters of which
only some import `to`. Removing an unused selector never changes the rule's
result.

Each of these is an error (exit 2), reported at the policy's
`file:line:column`:

- a malformed rule: `deny` not an array of tables, a missing `from`, `to` or
  `reason`, an unknown key, an empty list, a blank `reason`, a value of the
  wrong kind, or a malformed selector;
- a `set:` that names no set;
- a selector in `from`, `to` or `wrappers` that matches no module, named
  with its rule and field (`selector 'mod:Core.Apii' in deny rule 1
  ('from') matches no module: …`);
- a `from` selector that matches only external modules, which import
  nothing in the graph, so the rule could never bite;
- `from` and `to` sharing modules (take them out of one side with a set's
  `except`);
- a wrapper selector that excuses nothing.

A rule with one of these errors is not evaluated further, so one mistake gives
one error. When the policy has any error, no violation is reported: a policy
known to be wrong gives no result to trust.

A violation is printed as a block on stdout: the rule, where it is written,
and its reason, then each import of the chain with its file and line (paths
relative to the workspace). Blocks come in rule order, then by importing
module in the order `graph` lists modules, then, for a direct rule, in the
order the imports are written. A summary line follows the last block, and
`check` exits 1. From
`tests/fixtures/deny-transitive-bites`, whose first rule bites three times:

```
deny rule 1 (lean-deny.toml:5:0): the app never reaches the core's primitives
  App.lean:2: App imports Core.Api
  core/Core/Api.lean:5: Core.Api imports Core.Types
  core/Core/Types.lean:3: Core.Types imports Core.Prim
deny rule 1 (lean-deny.toml:5:0): the app never reaches the core's primitives
  AppTest.lean:1: AppTest imports App
  App.lean:2: App imports Core.Api
  core/Core/Api.lean:5: Core.Api imports Core.Types
  core/Core/Types.lean:3: Core.Types imports Core.Prim
…
lean-deny: 4 violations in 2 of 2 rules
```

When every rule holds, `check` prints `lean-deny: ok (2 rules)` and exits 0.

## allow-only

An `[[allow-only]]` rule says what the modules of `from` may import from
outside their own package: every such import must land in `allow`.

```toml
[[allow-only]]
from = "keyword:editor-package"
except = ["lib:FeatTest"]
allow = ["set:core-api", "external:Init", "external:Std"]
reason = "a package's library imports the core's API alone"
```

| Key | Required | Value |
|---|---|---|
| `from` | yes | a selector, or a non-empty array of selectors (their union) |
| `except` | no | the same (default none): modules taken out of `from` |
| `allow` | yes | the same |
| `reason` | yes | a non-blank string, printed with every violation |

Rules are numbered `allow-only rule 1`, `allow-only rule 2`, … in the order
they are written, apart from the deny rules' numbers. Both `[[allow-only]]`
tables and an inline `allow-only = [{ … }, …]` work.

What is checked: each import of a module the rule governs (below) whose
target is outside the importer's own package, that is, in another package
or outside the workspace. Every import counts: plain, `meta`, `public`, and
Lean's implicit `Init` imports, so `allow` normally lists `external:Init`.
Imports within the importer's own package are never checked. A violation is
reported once per (importer, imported) pair, with the first such `import`
as its witness.

**Tiers.** A rule *covers* the workspace modules of `from` minus `except`.
A module is *governed* by the most specific rule covering it: the rule
whose covered modules are a subset of every other covering rule's. Only
that rule's `allow` applies to the module; it is not combined with the
`allow` of the rules around it, so each tier restates what it keeps. A
module that no rule covers is not checked. For example, a library, its
tests and a linked test, the way editor-project's package-imports check
sorts a package's imports:

```toml
[sets]
core-api = ["lib:EditorApi"]
core-doubles = ["lib:EditorTestDoubles"]
linked-kit = ["lib:EditorLinkedKit"]
tests = ["lib:FeatTest", "lib:OtherTest"]

[[allow-only]]
from = "keyword:editor-package"
allow = ["set:core-api", "external:Init", "external:Std"]
reason = "a package's library imports the core's API alone"

[[allow-only]]
from = "set:tests"
allow = ["set:core-api", "set:core-doubles", "external:Init", "external:Std"]
reason = "tests may also use the core's test doubles"

[[allow-only]]
from = "mod:FeatTest.Linked"
allow = ["set:core-api", "set:core-doubles", "set:linked-kit", "external:Init"]
reason = "linked tests may also use the linked kit"
```

The second rule governs the test modules, nested inside the first; the third
governs `FeatTest.Linked` and the modules under it, nested inside the
second. Writing the tiers disjointly instead, with `except = "set:tests"` in
the first rule, means the same. There is no wildcard selector: name test
libraries with `lib:` or `mod:`, or gather them in a set.

lean-deny checks every import that leaves a package, not only the imports
of one core package, so `allow` must also list whatever else a package may
import: `external:` modules, and other packages it may use (such as
`keyword:editor-interface`).

Each of these is an error (exit 2), reported at the policy's
`file:line:column`:

- a malformed rule: `allow-only` not an array of tables, a missing `from`,
  `allow` or `reason`, an unknown key, an empty list, a blank `reason`, a
  value of the wrong kind, or a malformed selector;
- a `set:` that names no set;
- a selector in `from`, `except` or `allow` that matches no module, named
  with its rule and field;
- a `from` selector that matches only external modules;
- an `except` selector that removes no module from `from`, and a rule its
  `except` leaves covering no workspace module;
- two rules that cover exactly the same modules, and rules that overlap
  without one nesting in the other, so that no rule is the most specific
  for the modules they share (the error lists them);
- a rule that governs no module, a more specific rule governing each module
  it covers;
- an `allow` selector that allows nothing: no module the rule governs
  imports a module it matches from outside its own package. One used module
  is enough.

When the policy has any error, no violation is reported. Violations are
printed as for `deny`, deny rules' first, then the allow-only rules' in rule
order, then by importing module in the order `graph` lists modules, then in
the order the imports are written. From `tests/fixtures/allow-only-tiers`,
where a feature library imports a test double and a test library makes the
same import and holds:

```
allow-only rule 1 (lean-deny.toml:10:0): a package's library imports the core's API alone
  leaky/Leaky.lean:2: Leaky imports CoreTest.Fake
lean-deny: 1 violation in 1 of 2 rules
```

## layers

The `[layers]` table puts every package of the workspace in one layer and
says which layers a package may import from. This is editor-project's
three-layer rule (its `tools/layer-imports-check.sh`, deleted from
editor-project at `d51fe135`; see
[docs/editor-project-acceptance.md](docs/editor-project-acceptance.md)):

```toml
[layers]
classify = [
  { layer = "core", select = "pkg:editor" },
  { layer = "interface", select = "keyword:editor-interface" },
]
default = "implementation"     # a misspelt keyword makes a package more refused, never less
allow = [ ["interface", "core"], ["implementation", "core"], ["implementation", "interface"] ]
same-package = "allow"
```

| Key | Required | Value |
|---|---|---|
| `classify` | yes | a non-empty array of tables `{ layer, select }` (or `[[layers.classify]]` tables): `layer` a layer name, `select` a selector or a non-empty array of selectors (their union) |
| `default` | no | a layer name: the layer of every package no classify entry selects |
| `allow` | no | a non-empty array of `[importer, imported]` pairs of layer names (default none) |
| `same-package` | no | `"allow"`, its only value: imports within one package are always allowed |
| `reason` | no | a non-blank string; when given, it starts every violation's header |

Layer names use letters, digits, `-` and `_`, as set names do. There is at
most one `[layers]` table (`layers = { … }` works too), and it counts as one
rule.

**Classification is per package.** A classify entry puts every package its
selectors match in its layer, and it must select whole packages: matching
some modules of a package but not others is an error, so select packages
with `pkg:`, `keyword:`, or a set of them. A package that two entries select
is an error, even when they name the same layer (take it out of one with a
set's `except`). A package that no entry selects is in `default`; with no
`default`, it is an error, so every package must be classified. Making the
default the most restricted layer, as above, means a package whose
`keywords` are misspelt is refused more, never less.

**What is judged:** each direct import from a module of one package to a
module of another package, of every kind (plain, `meta`, `public`). It holds
when (importer's layer, imported's layer) is an `allow` pair. Imports within
one package are never judged, nor are imports of modules outside the
workspace (`Init`, `Std`, `Lean`, …), which are in no layer: `deny` and
`allow-only` cover those. Only listed pairs are allowed, same-layer pairs
included: `["interface", "interface"]` allows imports between two
interface packages, and without it they are refused. editor-project's
script allows interface → interface, so a policy that mirrors it exactly
adds that pair once two interface packages import each other (an unused
pair is an error, below).

A violation is reported once per (importer, imported) pair, with the first
such `import` as its witness. Its header names both packages and their
layers, after the `reason` when there is one. Violations come after the
deny and allow-only rules', by importing module in the order `graph` lists
modules, then in the order the imports are written. From
`tests/fixtures/layers-bites`:

```
layers (lean-deny.toml:7:0): app (implementation) may not import plugin (implementation)
  App.lean:3: App imports Plugin
layers (lean-deny.toml:7:0): app (implementation) may not import typo (implementation)
  App.lean:4: App imports Typo
layers (lean-deny.toml:7:0): editor (core) may not import plugin (implementation)
  editor/Editor.lean:2: Editor imports Plugin
layers (lean-deny.toml:7:0): iface (interface) may not import typo (implementation)
  iface/Iface.lean:2: Iface imports Typo
lean-deny: 4 violations in 1 of 1 rule
```

Each of these is an error (exit 2), reported at the policy's
`file:line:column`:

- a malformed table: `layers` not a table, a missing or empty `classify`, a
  classify entry that is not a table or lacks `layer` or `select`, an
  invalid layer name, an `allow` element that is not a pair of strings, a
  pair listed twice, a `same-package` other than `"allow"`, a blank
  `reason`, an unknown key, a value of the wrong kind, or a malformed
  selector;
- a `set:` that names no set;
- an `allow` pair naming a layer that neither a classify entry nor
  `default` declares;
- a classify selector that matches no module, or only modules outside the
  workspace;
- a classify entry that splits a package (it names one module it matches
  and one it does not);
- a package in two or more classify entries, or, with no `default`, in
  none;
- a `default` layer that holds no package, because the classify entries
  select every package;
- an `allow` pair that allows nothing: no module of a package in the first
  layer imports a module of another package in the second.

When the policy has any error, no violation is reported.

## reachable

A `[[reachable]]` rule says every module of `must-cover` is a module of
`from` or imported by one, directly or not. This is editor-project's core
imports rule 2: every `Editor.…` module the build reaches is the core's
root or imported by it, so a rule about the root is a rule about every core
module.

```toml
[sets]
core-modules = { select = ["mod:Editor"], except = ["mod:Editor!"] }

[[reachable]]
from = "mod:Editor.Core!"
must-cover = "set:core-modules"
reason = "the core's root holds the whole core"
```

| Key | Required | Value |
|---|---|---|
| `from` | yes | a selector or a non-empty array of selectors (their union): the roots |
| `must-cover` | yes | a selector or a non-empty array of selectors (their union): the modules the roots must reach |
| `reason` | yes | a non-blank string, printed with every violation |

Rules are numbered `reachable rule 1`, `reachable rule 2`, … in the order
they are written, apart from the other kinds' numbers. Both `[[reachable]]`
tables and an inline `reachable = [{ … }, …]` work.

**The closure** of a rule is the modules of `from` and every module they
import, directly or not, through every kind of import (plain, `meta`,
`import all`, and Lean's implicit `Init` imports). It is reflexive: a `from`
module covers itself, so `from` and `must-cover` may overlap.

**What is checked:** every module of `must-cover` in the loaded graph, which
is what the build reaches: the libraries' modules, the executables' roots
(a package's test executables among them), the declared roots
(`[[root]]`), and a library's modules that its roots do not reach but
other modules import.
Each one outside the closure is one violation, in the order `graph` lists
modules. Modules outside the workspace that `must-cover` matches are
ignored: they have no file, and are not the build's to cover. Violations
come after the other kinds', and each names the uncovered module and its
file instead of a chain. From `tests/fixtures/reachable-bites`:

```
reachable rule 1 (lean-deny.toml:5:0): the app's root holds the whole package: AppTest is outside the import closure of App
  AppTest.lean: AppTest
reachable rule 1 (lean-deny.toml:5:0): the app's root holds the whole package: Main is outside the import closure of App
  Main.lean: Main
reachable rule 2 (lean-deny.toml:10:0): the implementation holds the whole core: Core.Api is outside the import closure of Core.Impl
  core/Core/Api.lean: Core.Api
reachable rule 2 (lean-deny.toml:10:0): the implementation holds the whole core: Core.Macros is outside the import closure of Core.Impl
  core/Core/Macros.lean: Core.Macros
lean-deny: 4 violations in 2 of 2 rules
```

The header names the `from` modules when there are at most three, and
otherwise counts them (`'from' (5 modules)`). In `--format json` the
violation's `chain` is empty and its `module` names the module and its file
([docs/check-json.md](check-json.md)); in `--format github` it is a
file-level annotation on that file, with no line.

Each of these is an error (exit 2), reported at the policy's
`file:line:column`:

- a malformed rule: `reachable` not an array of tables, a missing `from`,
  `must-cover` or `reason`, an empty selector array, a blank `reason`, an
  unknown key, a value of the wrong kind, or a malformed selector;
- a `set:` that names no set;
- a selector that matches no module;
- a `from` selector that matches only modules outside the workspace, which
  import nothing in the graph;
- a `must-cover` selector that matches only modules outside the workspace,
  which the rule does not check;
- a rule every workspace module of whose `must-cover` is in `from`, so it
  checks nothing.

When the policy has any error, no violation is reported.

## co-reach

A `[[co-reach]]` rule says every module of `roots` that reaches a module of
`if-reaches` also reaches every module of `must-reach`. This is
editor-project's core imports rule 3: every executable root that reaches
the config elaborator adapter also reaches the config base, since the
elaborator imports the base's modules at runtime and each must be linked
in. `deny` forbids reach and `allow-only` limits direct imports; neither can
say it.

```toml
[[co-reach]]
roots = ["mod:EditorSetRoot!", "mod:FfiTest!", "set:package-linked-roots"]
if-reaches = "mod:Editor.Config.Elaborate!"
must-reach = "mod:Editor!"
reason = "every executable root that reaches the elaborator links the config base"
```

| Key | Required | Value |
|---|---|---|
| `roots` | yes | a selector or a non-empty array of selectors (their union): the roots, each checked alone |
| `if-reaches` | yes | a selector or a non-empty array of selectors (their union): a root that reaches **any** of them is checked |
| `must-reach` | yes | a selector or a non-empty array of selectors (their union): such a root must reach **every** one of them |
| `reason` | yes | a non-blank string, printed with every violation |

Rules are numbered `co-reach rule 1`, `co-reach rule 2`, … in the order they
are written, apart from the other kinds' numbers. Both `[[co-reach]]` tables
and an inline `co-reach = [{ … }, …]` work.

**The closure** of a root is the root and every module it imports, directly
or not, through every kind of import (plain, `meta`, `import all`, and
Lean's implicit `Init` imports). It is reflexive: a root that is itself an
`if-reaches` module triggers the rule, and a root that is itself a
`must-reach` module reaches it.

**What is checked:** each root, in the order `graph` lists modules. A root
whose closure holds no `if-reaches` module is skipped. A root whose closure
holds one but misses some `must-reach` module is one violation, naming the
root and every missing module. Its chain is a shortest import chain from the
root to the nearest `if-reaches` module, the witness that the rule applies;
when the root is itself one, the chain is empty and the root's file is
printed instead. Only workspace modules and declared roots are checked:
modules outside the workspace that a selector matches are dropped.
Violations come after the other kinds'. From `tests/fixtures/co-reach-bites`:

```
co-reach rule 1 (lean-deny.toml:6:0): every root that uses the core's types is the executable: AppTest reaches Core.Types but not Main
  AppTest.lean:1: AppTest imports App
  App.lean:2: App imports Core.Api
  core/Core/Api.lean:5: Core.Api imports Core.Types
co-reach rule 2 (lean-deny.toml:12:0): every core module links the macros and the base: Core.Impl is in 'if-reaches' but does not reach Base and Core.Macros
  core/Core/Impl.lean: Core.Impl
lean-deny: 2 violations in 2 of 2 rules
```

In `--format json` the violation's `module` is the root, its `chain` the
witness, and its `missing` the missing modules, each with its file
([docs/check-json.md](check-json.md)); in `--format github` it is
annotated on the chain's first import, or, with an empty chain, on the
root's file with no line.

Each of these is an error (exit 2), reported at the policy's
`file:line:column`:

- a malformed rule: `co-reach` not an array of tables, a missing `roots`,
  `if-reaches`, `must-reach` or `reason`, an empty selector array, a blank
  `reason`, an unknown key, a value of the wrong kind, or a malformed
  selector;
- a `set:` that names no set;
- a selector that matches no module;
- a `roots` selector that matches only modules outside the workspace, which
  import nothing in the graph;
- an `if-reaches` or `must-reach` selector that matches only modules outside
  the workspace, which the rule does not check;
- a rule none of whose roots reaches an `if-reaches` module, so it holds of
  nothing: `co-reach rule 1: no module of 'roots' reaches a module of
  'if-reaches', so the rule holds of nothing`.

When the policy has any error, no violation is reported.

## target-config

A `[[target-config]]` rule is about Lake targets rather than imports: every
`lean_lib` and `lean_exe` it selects loads a given plugin (Lake's `plugins`
option), or has a module that imports a given module, directly or not. This
is editor-project's "Lint plugins" rule: every library and executable of the
core and of every package loads the build's linters as a plugin, or imports
the core's `Lint`, so that no target goes unlinted.

```toml
[[target-config]]
targets = ["pkg:editor-core", "pkg:compile", "pkg:compile-api"]
load-plugin = "@editor-core/lintShared"
or-imports = "lib:editor-core/Lint"
reason = "a target that loads no plugin is never linted"
```

| Key | Required | Value |
|---|---|---|
| `targets` | yes | a `pkg:<package>`, `lib:<lib>` or `lib:<package>/<lib>` selector, or a non-empty array of them: the targets checked |
| `except` | no | the same forms: targets left out |
| `load-plugin` | yes | a Lake target name: `<target>`, `<package>/<target>` or `@<package>/<target>` |
| `or-imports` | no | a selector or a non-empty array of selectors, any form: a target that imports one of these modules passes too |
| `reason` | yes | a non-blank string, printed with every violation |

Rules are numbered `target-config rule 1`, `target-config rule 2`, … in the
order they are written, apart from the other kinds' numbers. Both
`[[target-config]]` tables and an inline `target-config = [{ … }, …]` work.

**The targets** of `pkg:p` are every `lean_lib` and every `lean_exe` of
package `p`; those of `lib:` are that one library, even one with no modules.
`except` removes targets the same way. A module selector (`mod:`,
`keyword:`, `external:`, `set:`, `imports:`) is an error in `targets` and
`except`: a target is not a module.

**A target's plugins** are the ones Lake applies to it: its package's
`plugins` (a package-level `plugins = [...]` in `lakefile.toml`, as
editor-project's packages write it), then its own. A plugin **is**
`load-plugin` when it is a package target with that target name and, when
`load-plugin` names a package, that package. A plugin written without a
package (`plugins = ["lintShared"]`) is the target's own package's, as Lake
reads it, so it is `@lint/lintShared` in package `lint` and not in any
other; a `load-plugin` written without a package (`lintShared`) matches that
target name in any package. A facet key such as
`@editor-core/Lint:shared` never matches, and `load-plugin` is not looked up
in the workspace: Lake fetches a plugin only when it builds, which lean-deny
never does. Plugins given through `moreLeanArgs` (`--plugin`) are not seen.

**A target imports** an `or-imports` module when one of its modules has that
module in its import closure, through at least one import of any kind
(directly or not; a module does not import itself). A library's modules are
the modules it owns; an executable's is its root module alone, the only one
Lake elaborates with the executable's plugins.

**What is checked:** each selected target that neither loads the plugin nor
imports an `or-imports` module is one violation, naming its package, its
kind and name, and the reason, and pointing at the package's lakefile (Lake
keeps no line for a target). Violations come after the other kinds', by
package in Lake's order, then libraries, then executables, each in lakefile
order. From `tests/fixtures/target-config-bites`:

```
target-config rule 1 (lean-deny.toml:5:0): a target that loads no plugin is never linted: lean_lib pkgb/PkgBExtra does not load @lint/lintShared and imports no module of lib:lint/Lint or mod:LintTest!
  pkgb/lakefile.toml: lean_lib PkgBExtra
target-config rule 1 (lean-deny.toml:5:0): a target that loads no plugin is never linted: lean_exe pkgb/pkgb-tool does not load @lint/lintShared and imports no module of lib:lint/Lint or mod:LintTest!
  pkgb/lakefile.toml: lean_exe pkgb-tool
target-config rule 2 (lean-deny.toml:12:0): the user library loads the linters: lean_lib user/User does not load lint/lintShared
  user/lakefile.toml: lean_lib User
lean-deny: 3 violations in 2 of 2 rules
```

In `--format json` the violation's `target` holds the package, the kind, the
name, the lakefile and the target's plugins
([docs/check-json.md](check-json.md)); in `--format github` it is a
file-level annotation on the lakefile, with no line.

Each of these is an error (exit 2), reported at the policy's
`file:line:column`:

- a malformed rule: `target-config` not an array of tables, a missing
  `targets`, `load-plugin` or `reason`, an empty selector array, a blank
  `reason`, an unknown key, a value of the wrong kind, or a malformed
  selector;
- a selector in `targets` or `except` that is not `pkg:` or `lib:`;
- a `load-plugin` that is not a target name (a facet `:`, a module `+`, an
  empty part, more than one `/`);
- a `set:` that names no set;
- a `targets` or `except` selector that names no package, a package with no
  `lean_lib` or `lean_exe`, or no library; a `lib:<lib>` two packages declare;
- an `or-imports` selector that matches no module, or only modules outside
  the workspace;
- an `except` entry that removes no selected target, or an `except` that
  removes every one, so the rule checks nothing.

When the policy has any error, no violation is reported.

## require-backed

A `[[require-backed]]` rule says a package declares every workspace package
it imports: for each package it selects, every import from one of the
package's modules into a module of another workspace package is backed by
a direct `require` of that package in the importing package's lakefile.

```toml
[[require-backed]]
packages = ["pkg:app", "keyword:editor-implementation"]
reason = "a set may drop any implementation package and still build"
```

| Key | Required | Value |
|---|---|---|
| `packages` | yes | a selector or a non-empty array of selectors (their union), any form: the packages judged |
| `reason` | yes | a non-blank string, printed with every violation |

Rules are numbered `require-backed rule 1`, `require-backed rule 2`, … in
the order they are written, apart from the other kinds' numbers. Both
`[[require-backed]]` tables and an inline `require-backed = [{ … }, …]`
work.

**Why:** Lake resolves a workspace's packages from their `require`s,
transitively. If package Q imports interface package I but reaches I only
through implementation package P's `require`, dropping P from a set's
requires drops I too and breaks Q. editor-project's "Leave-out" rule (every
implementation package can be left out of a set and the set still builds)
is this rule plus the three-layer rule (see "layers" above; no package imports an
implementation package), checked statically: lean-deny never runs `lake
update` or `lake build`.

**The packages** judged are those of the workspace modules `packages`
matches. A rule judges whole packages: like a `[layers]` classify entry, it
must not match some modules of a package and not others. Select packages
with `pkg:`, `keyword:`, or a set of them.

**Backed:** an import from a module of judged package A into a module of
another workspace package B is backed when A's lakefile `require`s B
directly (the names compared as written in the lakefiles; `lean-deny graph`
lists each package's requires). Imports within a package, of modules
outside the workspace (`Init`, `Lean`, …) and to or from a declared root (a
root is in no package) are not judged. Every import kind counts: plain,
`meta`, `public` and `all`.

**What is checked:** each (importing module, imported module) pair whose
import is not backed is one violation, naming the importing package, the
imported package, the importing module and the reason; its chain is the
first such import directive, and a last line lists what the importing
package does require. Violations come after the other kinds', by importing
module (sorted by library), then imports in source order. From
`tests/fixtures/require-backed-bites`, where `require-ws` requires `impl`
and `impl` requires `iface`:

```
require-backed rule 1 (lean-deny.toml:5:0): a set may drop any implementation package and still build: App (package require-ws) imports package iface, which require-ws does not require directly
  App.lean:2: App imports Iface
  lakefile.toml: require-ws requires impl
lean-deny: 1 violation in 1 of 1 rule
```

`App`'s import of `Impl` is backed by `require-ws`'s direct require, so it
is not reported. In `--format json` the violation's `require` holds the
importing package, the imported package, the lakefile and its requires
([docs/check-json.md](check-json.md)); in `--format github` it is
annotated on the import.

Each of these is an error (exit 2), reported at the policy's
`file:line:column`:

- a malformed rule: `require-backed` not an array of tables, a missing
  `packages` or `reason`, an empty selector array, a blank `reason`, an
  unknown key (`require-backed rule 1: unknown key 'from' (expected
  packages, reason)`), a value of the wrong kind, or a malformed selector;
- a `set:` that names no set;
- a selector that matches no module, or only modules in no package
  (modules outside the workspace, or declared roots);
- a rule that splits a package: `require-backed rule 1 splits package 'app':
  it matches App but not App.Extra; …`.

When the policy has any error, no violation is reported.

## doc-modules

A `[[doc-modules]]` rule says a Markdown section names exactly a set of
modules: the backticked module names starting with `prefix` in section
`section` of `file` are the workspace modules `modules` matches, no more and
no fewer.

```toml
[sets]
doc-mods = { select = ["mod:Doc"], except = ["mod:Doc!"] }

[[doc-modules]]
file = "docs/modules.md"
section = "The modules"
prefix = "Doc."
modules = "set:doc-mods"
reason = "the module map names every module"
```

| Key | Required | Value |
|---|---|---|
| `file` | yes | a non-empty path relative to the workspace directory: the Markdown file |
| `section` | yes | a non-blank string: the text of the section's heading, matched exactly (trimmed) |
| `prefix` | yes | a non-empty string: a backticked name is listed only when it starts with it (write `Doc.`, with the dot; a plain string prefix) |
| `modules` | yes | a selector or a non-empty array of selectors (their union), any form: the modules the section must list |
| `reason` | yes | a non-blank string, printed with every violation |

Rules are numbered `doc-modules rule 1`, `doc-modules rule 2`, … in the
order they are written, apart from the other kinds' numbers. Both
`[[doc-modules]]` tables and an inline `doc-modules = [{ … }, …]` work.
"Every module but the root" is written with a `[sets]` entry's `except`, as
above.

**Why:** a design document's module map goes stale silently when a module
is added, renamed or removed. This rule keeps such a list honest without
lean-deny knowing anything about the document beyond the heading.

**What is read** (a small subset of Markdown):

- **Headings:** ATX headings only (`#` to `######`, at most 3 spaces of
  indent, then a space or the end of the line; an optional closing run of
  `#` is dropped). Setext headings (text underlined with `=` or `-`) are
  not recognised. The heading must appear exactly once.
- **The section** is the lines after the heading, up to the next heading of
  the same or a higher level, or the end of the file. Deeper subsections
  are included.
- **Fenced code blocks** (` ``` ` or `~~~`) are skipped: a heading or a name
  inside one does not count.
- **Code spans** are found within one line, as CommonMark delimits them (a
  run of backticks closed by a run of the same length); a span never
  crosses a line, which is enough for table cells and list items.
- **A name** is a span holding one or more `.`-separated components of
  ASCII letters, digits, `_` and `'`, not starting with a digit. Paths
  (`Doc/A.lean`, `lean/Doc/`) and other text are not names. `«»`-escaped
  names are not recognised.
- **Listed** names are the names that start with `prefix`; others (such as
  `Nat.succ` with prefix `Doc.`) are ignored.

**The modules** are the workspace modules and declared roots `modules`
matches; a module outside the workspace in a mixed match is ignored.

**What is checked:** the listed names and the modules' names are compared
as sets; order and counts in the document are never checked, so a name
listed twice is one name. Each module the section does not list is one
violation, naming the module, the file and the section; then each listed
name that is not one of the modules is one violation, naming the name, the
file and the section. Violations come after the other kinds': missing
modules sorted by library, then extra names in order of first appearance.
From `tests/fixtures/doc-modules-missing`:

```
doc-modules rule 1 (lean-deny.toml:5:0): the module map names every module: Doc.B is not listed in section 'Missing' of docs/modules.md
  Doc/B.lean: Doc.B
  docs/modules.md:16: section 'Missing'
lean-deny: 1 violation in 1 of 1 rule
```

An extra name's block ends in the line listing it,
`  docs/modules.md:23: Doc.Gone`. In `--format json` the violation's `doc`
holds whether the name is missing or extra, the name, the file, the section
and the line ([docs/check-json.md](check-json.md)); in `--format
github` it is annotated on the Markdown file, at the section's heading
(missing) or the name's line (extra).

The file is read after the workspace's graph loads. Each of these is an
error (exit 2), reported at the policy's `file:line:column`:

- a malformed rule: `doc-modules` not an array of tables, a missing `file`,
  `section`, `prefix`, `modules` or `reason`, an empty `file`, `prefix` or
  selector array, a blank `section` or `reason`, an absolute `file`, an
  unknown key (`doc-modules rule 1: unknown key 'heading' (expected file,
  section, prefix, modules, reason)`), a value of the wrong kind, or a
  malformed selector;
- a `set:` that names no set;
- a selector that matches no module, or only modules outside the workspace;
- a matched module whose name does not start with `prefix`, which the
  section could never list: `doc-modules rule 1: 'modules' matches Doc,
  which does not start with the prefix 'Doc.', so the section cannot list
  it` (with ` (and K more)` after the name when others do too);
- a missing or unreadable file: `doc-modules rule 1: no file
  'docs/missing.md' in the workspace (looking for heading 'The modules')`;
- a heading not in the file, `doc-modules rule 1: no heading 'Nope' in
  'docs/modules.md'`, or appearing more than once, `doc-modules rule 1:
  heading 'Twice' appears 2 times in 'docs/modules.md' (lines 35 and 37)`.

A rule's selector errors and its file's error are both reported. When the
policy has any error, no violation is reported.

## doc-packages

A `[[doc-packages]]` rule says a Markdown table has one row per package of
a set, and that each row gives the package's layer, as `[layers]` puts it,
and its direct requires, as its lakefile writes them.

```toml
[layers]
classify = [{ layer = "core", select = "pkg:core" }, { layer = "interface", select = "pkg:api" }]
default = "implementation"
allow = [...]

[[doc-packages]]
file = "docs/packages.md"
section = "The packages"
package-column = "Package"
layer-column = "Layer"
requires-column = "Requires, beside the core"
packages = ["pkg:api", "pkg:impl"]
requires-except = "core"
reason = "the module map has one row per package"
```

| Key | Required | Value |
|---|---|---|
| `file` | yes | a non-empty path relative to the workspace directory: the Markdown file |
| `section` | yes | a non-blank string: the text of the section's heading, matched exactly (trimmed) |
| `package-column`, `layer-column`, `requires-column` | yes | non-blank strings: the header cells of the package, layer and requires columns, matched exactly (trimmed); the three must differ |
| `packages` | yes | a selector or a non-empty array of selectors (their union), any form, selecting whole packages: the packages the table must have a row for |
| `requires-except` | no | a package name or a non-empty array of them: packages left out of every requires comparison (the core every package requires) |
| `reason` | yes | a non-blank string, printed with every violation |

Rules are numbered `doc-packages rule 1`, `doc-packages rule 2`, … in the
order they are written, apart from the other kinds' numbers. Both
`[[doc-packages]]` tables and an inline `doc-packages = [{ … }, …]` work. A
policy with a doc-packages rule must have `[layers]`, which gives each
package's layer.

**Why:** a design document's table of packages, their layers and what they
require goes stale silently when a package is added, moves layer or gains
a require. This rule keeps such a table honest from what lean-deny already
knows: `[layers]` and the lakefiles.

**What is read:** headings, the section and fences as for
[doc-modules](#doc-modules), and then:

- **A top-level table** starts at a header row whose first character is `|`
  (column 0, no indent), followed by a delimiter row (`|---|:-:|`, as many
  cells as the header). Its rows are the following lines starting with `|`
  in column 0; a blank line or any other line ends it. A table nested in a
  list item (its rows indented) or in a fenced code block is ignored.
- **The table checked** is the first top-level table in the section whose
  header has all three named columns. Earlier tables without them are
  skipped; later tables are not read. Every other column is ignored.
- **Cells** are split on `|` (`\|` is a literal `|`) and trimmed. A row's
  package is the first backticked name in its package cell; its layer is
  its layer cell (or the name in a cell that is one backticked name); its
  requires are every backticked name in its requires cell, or none for a
  cell that is exactly `none`.

**What is checked:** each package `packages` matches with no row is one
violation; then, each row in document order: a row naming a package
`packages` does not match is one violation; otherwise a layer cell other
than the package's `[layers]` layer is one violation, naming the package,
both layers and the file; and requires that differ, as sets, from the
package's direct requires less `requires-except` are one violation, naming
the package and the names missing and extra. Row order and duplicate rows
are not checked. Violations come after the other kinds': missing packages
by name, then rows in document order. From `tests/fixtures/doc-packages-broken`:

```
doc-packages rule 1 (lean-deny.toml:14:0): the package table has one row per package: package impl has no row in section 'Broken' of docs/packages.md
  docs/packages.md:30: section 'Broken'
doc-packages rule 1 (lean-deny.toml:14:0): the package table has one row per package: section 'Broken' of docs/packages.md has a row for gone, which 'packages' does not match
  docs/packages.md:34: gone
doc-packages rule 1 (lean-deny.toml:14:0): the package table has one row per package: section 'Broken' of docs/packages.md gives api layer implementation, but [layers] puts it in interface
  docs/packages.md:35: api
doc-packages rule 1 (lean-deny.toml:14:0): the package table has one row per package: section 'Broken' of docs/packages.md gives api requires impl, but api requires nothing directly: extra impl
  docs/packages.md:35: api
lean-deny: 4 violations in 1 of 2 rules
```

In `--format json` the violation's `packageRow` holds its kind (`missing`,
`extra`, `layer`, `requires`), the package, the file, the section, the
line, both layers and the missing and extra requires
([docs/check-json.md](check-json.md)); in `--format github` it is
annotated on the Markdown file, at the section's heading (a missing row)
or the row's line (the others).

The file is read after the workspace's graph loads. Each of these is an
error (exit 2), reported at the policy's `file:line:column`:

- a malformed rule: `doc-packages` not an array of tables, a missing key
  (all but `requires-except`), an empty `file`, column or selector array,
  a blank `section` or `reason`, an absolute `file`, an empty
  `requires-except` array or name, two columns with the same name, an
  unknown key (`doc-packages rule 1: unknown key 'heading' (expected file,
  section, package-column, layer-column, requires-column, packages,
  requires-except, reason)`), a value of the wrong kind, or a malformed
  selector;
- a policy with no `[layers]`: `doc-packages rule 1: the policy has no
  [layers], which gives each package's layer`;
- a `set:` that names no set;
- a selector that matches no module, or only modules in no package, or a
  rule that splits a package (as for [require-backed](#require-backed));
- a `requires-except` name the workspace has no package of:
  `doc-packages rule 1: 'requires-except' names package 'kernel', which
  the workspace does not have`;
- a missing or unreadable file, or a heading missing or appearing more than
  once, as for doc-modules;
- a section with no top-level table, or none with every named column:
  `doc-packages rule 1: no top-level table in section 'No requires' of
  'docs/packages.md' has the columns 'Package', 'Layer' and 'Requires'
  (the first, at line 39, has no 'Requires')`;
- a row whose package cell names no package in backticks, whose layer cell
  is empty, or whose requires cell is neither `none` nor backticked names:
  `doc-packages rule 1: 'docs/packages.md':14: the 'Package' cell names no
  package in backticks`.

A rule's selector errors and its file's error are both reported. A
`[layers]` that does not resolve reports its own errors only. When the
policy has any error, no violation is reported.
