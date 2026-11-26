# lean-deny

[![Licence: GPL-3.0-or-later](https://img.shields.io/badge/licence-GPL--3.0--or--later-blue)](LICENSE)

Dependency policy checks for Lean 4 / Lake workspaces.

lean-deny reads the module graph that Lake resolves for a workspace and
checks it against rules you keep as data, in `lean-deny.toml`. A broken rule
is printed with the import chain that breaks it, and the command exits
non-zero. It is to Lake roughly what [cargo-deny]'s `bans` are to Cargo: the
place a monorepo says "package A must not depend on package B" and has the
build hold it.

> **Status: early.** `lean-deny check` runs: it loads the workspace's module
> graph through Lake and exits with the codes below. It reads the `[sets]`
> table and the `[[deny]]`, `[[allow-only]]`, `[layers]` and `[[reachable]]` rules of
> `lean-deny.toml`, checks that every selector matches, and exits 1 with
> the violations when a rule is broken. Any other top-level key is an
> error, never silently ignored. `lean-deny explain` lists the modules a
> selector matches, and `lean-deny graph` prints the graph it loads, as
> text, JSON or DOT. `check` prints its report as text, JSON or GitHub
> annotations. The plan lives in the rdm project `lean-deny` (roadmaps `foundation` and
> `policy-rules`).

[cargo-deny]: https://github.com/EmbarkStudios/cargo-deny

## Why

Lean's imports are what hold a large codebase's structure together: a core
that must not know about its plugins, interface packages that implementations
go through, test helpers that must not leak into libraries. Lake enforces
none of that, and the usual stopgaps are shell scripts that grep `import`
lines, or a reviewer's memory.

lean-deny makes those rules data, checks them with compiled code against the
graph Lake itself resolves, and refuses to pass by checking nothing: a rule
whose selector matches no module, or an exception that excuses no import, is
an error, so renaming a module cannot silently turn a rule off.

The closest existing thing is Mathlib's `directoryDependency` linter, which
forbids imports between module prefixes. It is hard-coded to Mathlib and runs
per file, so it sees direct imports only. lean-deny is a general,
configurable version that also checks transitive dependencies.

## What it checks

All rules work on one graph: every module of the workspace, the `lean_lib`
and package it belongs to, the package's `keywords`, and each direct import
with its file and line. Lake resolves it; lean-deny builds nothing, but it
does run code: loading the workspace elaborates the `lakefile.lean` of the
workspace and of each dependency, as `lake` does (see "Using it with Lake").
Executables' root modules are in the graph too, and modules from outside the
workspace (`Init`, `Lean`, `Std`, …) appear as the external targets of direct
imports.

| Rule | Says | cargo-deny analogue |
|---|---|---|
| `deny` | Modules in A must not import modules in B, directly or (with `transitive = true`) through others. `wrappers` name the modules allowed to. | `bans.deny` with `wrappers` |
| `allow-only` | What a module of A imports from outside its own package must be in a listed set. Nested rules give tiers, such as a library versus its tests: the most specific rule covering a module applies. | none |
| `layers` | Every package is in one layer, chosen by selectors such as `pkg:` or `keyword:`; every import between two packages must be an allowed (importer layer, imported layer) pair. | none |
| `reachable` | Every module in B is a module of A or imported by one, directly or not: nothing in B lies outside A's import closure. | none |

### Selectors

Every rule names its sets of modules with selectors. `pkg:`, `lib:`,
`mod:` and `keyword:` match modules of the workspace only (a dependency
package's modules are workspace modules); `external:` matches modules from
outside it only. `mod:` also matches the policy's declared roots (see
"Declared roots"); `pkg:`, `lib:` and `keyword:` never do.

| Selector | Matches |
|---|---|
| `pkg:<name>` | every module of a Lake package, including its executables' root modules |
| `lib:<lib>`, `lib:<pkg>/<lib>` | every module of a `lean_lib`; a module two libraries list is in both. Not an executable's root, unless a library lists it too. When several packages declare a `lean_lib` of that name, `lib:<lib>` is an error: write `lib:<pkg>/<lib>` |
| `mod:<Prefix>` | that module and every module under it, by name component: `mod:App` matches `App` and `App.Shared`, not `AppTest` |
| `mod:<Exact>!` | that module alone |
| `keyword:<kw>` | every module of every package whose lakefile declares `keywords = ["<kw>"]` (matched exactly) |
| `external:<Prefix>` | modules from outside the workspace, such as `Lean`, `Std` or `Lake`, by name component. The graph holds only those the workspace imports directly |
| `set:<name>` | a named set from the policy's `[sets]` table |
| `imports:<selector>` | the workspace modules that the modules `<selector>` matches import directly |

Module names are written as in `import` (`mod:«my-mod».X`). `lean-deny
explain <selector>` prints what a selector matches.

`imports:<selector>` derives a set from the graph's edges. It is one hop, not
the closure: `imports:mod:App!` is what `App` imports, not what those modules
import in turn. External modules (`Init`, `Lean`, …) are left out; workspace
modules and declared roots are kept, and a declared root counts as an
importer too (`imports:mod:EditorSetRoot!`). The inner selector keeps its own
meaning: `imports:mod:Core.Api!` is what `Core.Api` alone imports,
`imports:mod:Core` what every module under `Core` imports (a module the
inner selector matches stays in if another one imports it). It nests:
`imports:set:entry` and `imports:imports:mod:Main!` (two hops). An
`imports:` selector that resolves to no module is an error, as any selector
is.

### Sets

`[sets]` names sets of modules, for rules (and `explain`) to use as
`set:<name>`. A set is a list of selectors, their union, or a table whose
`except` list is taken away from the union of its `select` list:

```toml
[sets]
core-api = ["mod:Editor.Api", "lib:EditorInterfaces"]
core = { select = ["pkg:editor", "set:core-api"], except = ["mod:Editor.Testing"] }

[sets.plugins]
select = ["keyword:editor-feature"]
except = ["set:core"]
```

Set names use letters, digits, `-` and `_`. Each of these is an error
(exit 2), reported at the policy's `file:line:column` (the column is
0-based, as Lean prints it):

- a selector that matches no module, such as a misspelt or renamed module,
  or an `imports:` selector whose modules import no workspace module;
- a `lib:<lib>` that several packages declare (ambiguous);
- an `except` entry that removes no module from its set;
- a set that its `except` list leaves empty;
- a `set:` (also inside `imports:`) that names no set, or a set that refers
  to itself, directly or through other sets;
- a malformed selector or set, or an unknown key.

A mistake is reported once. When a set's `select` list already has an error,
or names a set that has one, the set's modules are not all known, so the two
`except` errors above are not reported for it.

Every set is checked, whether a rule uses it or not, so a set no rule uses
is fine.

### Declared roots

Some modules no Lake target declares: a root module a Lake facet generates
under `.lake/build/` from a target list, say, which imports every entry
module of a plugin host. A `[[root]]` table declares one, so the graph has it
and its imports:

```toml
[[root]]
module = "EditorSetRoot"
path = ".lake/build/root/EditorSetRoot.lean"
```

- `module` is the module's name, written as in `import`.
- `path` is its file, **relative to the workspace directory** (the
  `--workspace` directory, not the policy's directory nor the working
  directory), with `/` separators; `..` is allowed, an absolute path is not.
- No two tables may declare one module or one path.

lean-deny reads the file's header the way Lake reads any module's, resolves
its imports as Lake does, and adds the root to the graph as a node of its
own kind (`declared root`), with no package and no owner. A library module
that only a declared root imports is in the graph too, owned by its library.
lean-deny never generates the file and never runs Lake to write it: build
the workspace (or the facet) first. Each of these is an error (exit 2):

- a declared root whose file does not exist;
- a declared root that a Lake target already provides (a library module
  with a file, or an executable's root);
- an import from a declared root that Lake resolves to a workspace library
  but whose file does not exist, with the same message as for any module;
- a malformed `[[root]]` table.

How the rules see a declared root:

- `mod:` matches it, by name component and with `!`; `pkg:`, `lib:`,
  `keyword:` and `external:` never do.
- `imports:` sees it both ways: `imports:mod:<root>!` is what the root
  imports, and a module that imports a declared root has it among its
  imports.
- `deny`: as any module, in `from`, `to` or `wrappers`.
- `allow-only`: a declared root is in no package, so **every** one of its
  imports is judged, its implicit `Init` imports included.
- `layers`: a declared root is in no package, so its imports are never
  judged, as importer or imported, and a classify selector that matches only
  declared roots (or those and external modules) is an error.

Declared roots are not rules: `ok (N rules)` does not count them.

### deny

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

### allow-only

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

### layers

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

### reachable

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
([docs/check-json.md](docs/check-json.md)); in `--format github` it is a
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

## A policy, sketched

```toml
# lean-deny.toml

[sets]
core = ["pkg:editor"]
core-api = ["mod:Editor.Api", "lib:EditorInterfaces"]

# The core depends on no feature package, not even indirectly.
[[deny]]
from = "set:core"
to = "keyword:editor-feature"
transitive = true
reason = "a package may depend on the core, and the core on no package"

# Plain modules stay clear of Lean's frontend.
[[deny]]
from = "mod:Editor.Text"
to = "external:Lean.Elab"
transitive = true
reason = "text handling must not pull in the elaborator"

# A feature package's library uses the core's API and nothing else of it.
[[allow-only]]
from = "keyword:editor-feature"
allow = ["set:core-api", "external:Init", "external:Std"]
reason = "packages import the core's API alone"

# Three layers: implementations go through interfaces, never each other.
[layers]
classify = [
  { layer = "core", select = "set:core" },
  { layer = "interface", select = "keyword:editor-interface" },
]
default = "implementation"
allow = [
  ["interface", "core"],
  ["implementation", "core"],
  ["implementation", "interface"],
]
```

A broken rule is reported like this (see "deny" above; `--format json` and
`--format github` are under "In CI"):

```
deny rule 1 (lean-deny.toml:8:0): a package may depend on the core, and the core on no package
  Editor/Core/Commands.lean:4: Editor.Core.Commands imports Editor.Core.Menus
  Editor/Core/Menus.lean:7: Editor.Core.Menus imports Compile.Api
lean-deny: 1 violation in 1 of 4 rules
```

## editor-project, as the acceptance test

[docs/editor-project-acceptance.md](docs/editor-project-acceptance.md)
writes editor-project's four import checks (core, package, host and layer
imports) as one policy,
[`examples/editor-project/lean-deny.toml`](examples/editor-project/lean-deny.toml),
runs it over a copy of editor-project with
[`examples/editor-project/acceptance.sh`](examples/editor-project/acceptance.sh),
and shows each rule biting on an edit that breaks it. What lean-deny cannot
express yet is listed there as tasks. It is confirmed by `lake build`, then
the script exiting 0 with `acceptance: every expectation held`, then the
`rdm verify` command (below), then an empty `git status --porcelain`.

## Using it with Lake

Add lean-deny as a dependency, so Lake builds it with your workspace's own
toolchain:

```toml
# lakefile.toml
[[require]]
name = "lean-deny"
git = "https://github.com/leanmacs/lean-deny"
rev = "v0.1.0"
```

Then either run it directly:

```sh
lake exe lean-deny check
```

or make it your package's lint driver, so `lake lint` runs it:

```toml
lintDriver = "«lean-deny»/«lean-deny»"
lintDriverArgs = ["check"]
```

The guillemets are needed: Lake reads `lintDriver` with `String.toName`,
which turns a bare hyphenated name such as `lean-deny` into an anonymous
name, and then reports an unknown lint driver package. `lake lint` exits with
lean-deny's exit code, and `lake lint -- <args>` appends arguments after
`check`, for example `lake lint -- --config ci/lean-deny.toml`.

lean-deny reads the workspace in-process through Lake's API, so it needs no
custom Lake facet in your workspace; `lake exe` and `lake lint` cover it.

Reading the workspace runs its code. Lake's loader elaborates the
`lakefile.lean` of the workspace and of every dependency in-process, so
`lean-deny check` runs that code exactly as running `lake` would. Do not
point it at a workspace you would not run `lake build` in. (A package
configured by `lakefile.toml` is declarative; nothing in it is run.)

The workspace must have a `lake-manifest.json` (run `lake update` or any
`lake build` once): lean-deny never resolves or fetches dependencies itself.

### Commands

| Command | Status | Does |
|---|---|---|
| `lean-deny check [--workspace <dir>] [--config <file>] [--format text\|json\|github]` | implemented | Check the policy. Prints `lean-deny: ok (N rules)` when every rule holds, or each violation and a summary line (see "deny", "allow-only", "layers" and "reachable"). `--workspace` defaults to `.`; `--config` defaults to `<workspace>/lean-deny.toml`, and an explicit path is relative to the working directory. `--format` defaults to `text`; `json` is versioned and documented in [`docs/check-json.md`](docs/check-json.md); `github` prints GitHub annotations (see "In CI"). The exit code is the same in every format. |
| `lean-deny graph [--workspace <dir>] [--config <file>] [--format text\|json\|dot] [--level module\|lib\|package]` | implemented | Print the resolved graph (see "Seeing the graph"). Defaults: `--workspace .`, `--config <workspace>/lean-deny.toml`, `--format text`, `--level module`. Reads the policy only for its `[[root]]` tables (see "Declared roots"); every other key is ignored. A default policy that does not exist gives no declared roots; a policy that is not valid TOML gives a warning and no declared roots. |
| `lean-deny --help`, `lean-deny --version` | implemented | Print usage or the version. |
| `lean-deny explain [--workspace <dir>] [--config <file>] <selector>` | implemented | List the modules a selector matches, one per line, in the order `graph` prints them. A selector that matches nothing exits 2. The policy (`--config`, default `<workspace>/lean-deny.toml`) is read in full only for a selector that names a set (`set:x`, `imports:set:x`), and then only that set and the sets it refers to are resolved; for any other selector only its `[[root]]` tables are read, as for `graph`. |

### Exit codes

| Code | Meaning |
|---|---|
| 0 | Every rule holds (`check`), the graph was printed (`graph`), or at least one matching module was printed (`explain`). |
| 1 | At least one rule is broken (a `deny`, `allow-only`, `layers` or `reachable` violation). The violations and a summary go to stdout. |
| 2 | The command line, the policy or the workspace is bad: a usage error, a missing or malformed policy, an unknown policy key, a workspace that is missing or that Lake cannot load, a selector that matches nothing, a wrapper that excuses nothing, a deny rule whose `from` and `to` share modules, a `from` selector that matches only external modules, an `except` entry that removes nothing, an `allow` entry that allows nothing, allow-only rules that cover the same modules or overlap without nesting, an allow-only rule that covers or governs no module, a layers classify entry that splits a package, a package in two classify entries or in no layer, a layer that holds no package or that an allow pair names but nothing declares, a layers allow pair that allows nothing, a `must-cover` selector that matches only external modules, a reachable rule whose `must-cover` lies inside its `from`, a malformed `[[root]]` table, a declared root whose file is missing or that a Lake target already provides. No violation is reported then. The same for `graph`, which reads only the policy's `[[root]]` tables (and only warns on a policy that is not valid TOML), and for `explain`, which reads the policy in full only for a selector that names a set. Any internal error is also 2, never 1. |

`--format` changes only what `check` prints, never its exit code; a usage
error, a bad `--format` included, is always text on stderr. With
`--format json` stdout holds a JSON document for exit 2 too, and the
diagnostics still go to stderr.

### In CI

`check --format github` prints each violation as a GitHub Actions error
annotation on the import that starts its chain (file and line), with the
rule, its reason and the whole chain in the message, so it shows on the
pull request's diff; a policy error is annotated on `lean-deny.toml`. Paths
are relative to the working directory, so run it from the repository root.
With lean-deny as the lint driver:

```yaml
# .github/workflows/lean-deny.yml
name: lean-deny
on: [push, pull_request]
jobs:
  lean-deny:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Install elan
        run: |
          curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
          echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
      - name: Check the dependency policy
        run: lake lint -- --format github
```

`lake lint` builds lean-deny with the workspace's toolchain and exits with
its code: 1 fails the step on a violation, 2 on a bad policy or workspace.
Without `lintDriver`, run `lake exe lean-deny check --format github`.
`--format json` (schema in [`docs/check-json.md`](docs/check-json.md))
suits other CI systems and tools: stdout is one JSON document for every
outcome, exit 2 included.

### Seeing the graph

`lean-deny graph` prints the graph the rules will see, grouped at one of
three levels:

- `module`: every module, and one edge per (importer, imported) pair.
- `lib`: one node per `lean_lib` and per `lean_exe` (`<pkg>/lib/<lib>`,
  `<pkg>/exe/<exe>`). A module listed by two libraries counts in both, as
  `lib:` selectors will see it; an executable's root module is its own
  `exe` node.
- `package`: one node per package.

A declared root (see "Declared roots") is its own node at every level: at
module level `EditorSetRoot (.lake/build/root/EditorSetRoot.lean): declared
root`, above it `root/EditorSetRoot`, so its imports stay visible.

Above module level, modules from outside the workspace collapse to their
first name component (`external/Lean` holds `Lean.Data.Json`); these are
direct import targets only. Imports inside one node are not drawn as an
edge. Every edge lists the imports behind it (its witnesses), with file and
line, including Lean's implicit `Init` imports, so it is clear why the edge
exists. Paths are relative to the workspace. `--format json` is for tools;
its schema is versioned and documented in
[`docs/graph-json.md`](docs/graph-json.md). `--format dot` is for Graphviz
(`lean-deny graph --level lib --format dot | dot -Tsvg > graph.svg`).

## Later

Possible later checks, beyond import rules:

- coverage: every module matching a selector is reached from a given root
- target configuration: every library and executable loads a given plugin
- licences: an SPDX allowlist over the workspace's packages
- sources: allowed git hosts, pinned revisions, no stray path dependencies
- toolchain consistency: every dependency's `lean-toolchain` matches the root's

## Development

```sh
lake build --wfail && lake test
```

`lake test` runs `lean-deny-test`: unit tests of the command-line parser (`cli`),
of the selector syntax (`selector`), of the policy loader on TOML texts
(`policy`), of the import-line parser (`header`), and of the graph builder and its
queries on hand-written graphs (`query`); of the module, lib and package
views on a hand-written graph (`view`); of what selectors and sets match
on a hand-written graph (`resolve`); of `deny` rules on hand-written
graphs, from the policy's text to what `check` prints (`deny`), and of
`allow-only` rules, `[layers]` and `[[reachable]]` rules the same way
(`allow-only`, `layers`, `reachable`); of the
renderings, including the
golden JSON `tests/fixtures/graph-json-module/expected.stdout` (`render`);
of the check report's JSON and GitHub renderings, including the golden
`tests/fixtures/check-json-deny/expected.stdout` (`report`);
exact checks of the graph loaded for `tests/fixtures/spike-ws` and
`tests/fixtures/graph-ws` (`graph`); the fixture runner's own checks
(`harness`); and every fixture under `tests/fixtures/`. `lake test -- <name>...` runs only the named fixtures.

A fixture is a directory holding a `fixture.toml`:

```toml
run  = "direct"   # or "lake"
args = ["check"]  # direct: lean-deny's arguments; lake: lake's, e.g. ["lint"]
exit = 0
```

plus `expected.stdout` and `expected.stderr` (a missing file means "expected
empty"), and whatever workspace or policy files the case needs. The command
runs with the fixture directory as its working directory.

- `direct` runs the built `lean-deny` binary. Its stdout and stderr must
  match exactly.
- `lake` runs the same toolchain's `lake` (for `lake exe` and `lake lint`
  cases, whose `lakefile.toml` requires lean-deny with `path = "../../.."`).
  stdout must match exactly; the expected stderr need only occur in the
  actual one, since Lake prints build progress there. These fixtures must
  carry a `lean-toolchain` equal to the root's and a committed
  `lake-manifest.json`.
- Before comparing, the fixture's absolute path becomes `<fixture>` and the
  repository's becomes `<repo>`.
- A directory without a `fixture.toml` is a failure, not a skip.

Each rule kind is tested by fixtures where the rule holds and where it is
broken (`deny-*` for `deny`, most over the `graph-ws` workspace;
`allow-only-*` for `allow-only`, over the `tier-ws` workspace; `layers-*`
for `layers`, over the `layer-ws` and `layer-bad-ws` workspaces;
`reachable-*` for `reachable`, over `graph-ws`);
`check-json-*` and `check-github-*` for `--format json` and `github` (over
the same workspaces), and `lake-lint-github` for
`lake lint -- --format github`. The `editor-acceptance-*` fixtures run a
cut-down copy of the editor-project policy (`examples/editor-project/`) over
`editor-ws`, a miniature editor-project, where it holds, and
`editor-broken-ws`, where each rule bites. After
`lake build --wfail && lake test`, `git status --porcelain` must print
nothing; CI checks that too.

The sources are formatted and linted with
[lean-fmt](https://github.com/jcreinhold/lean-fmt). After `lake build`, at
the repo root, check them with

```sh
lake -d tools/lean-fmt exe lean-fmt format --check --root .
lake -d tools/lean-fmt exe lean-fmt check --root .
```

and rewrite them with

```sh
lake -d tools/lean-fmt exe lean-fmt format --root .
lake -d tools/lean-fmt exe lean-fmt check --fix --root .
```

`check` reads the built `.olean` files, so `lake build` comes first.
lean-fmt is hosted in `tools/lean-fmt/`, a Lake package with no Lean source
whose one `require` is lean-fmt: lean-deny itself requires no git
repository, and a workspace that requires lean-deny fetches nothing for it.
The first run clones lean-fmt into `tools/lean-fmt/.lake` and builds it,
which needs the network once. `lean-fmt.toml` excludes `tests/**`: the
fixtures are separate workspaces, some deliberately malformed, whose bytes
their expected outputs pin. lean-fmt's releases are tagged with the Lean
toolchain they build with: bump `rev` in `tools/lean-fmt/lakefile.toml`
together with both `lean-toolchain` files, then run
`lake -d tools/lean-fmt update --keep-toolchain` at the repo root.

The project's `rdm verify` command, and what CI runs, is the build and tests
followed by both lean-fmt checks:

```sh
lake build --wfail && lake test && lake -d tools/lean-fmt exe lean-fmt format --check --root . && lake -d tools/lean-fmt exe lean-fmt check --root .
```

## Licence

GPL-3.0-or-later. See [`LICENSE`](LICENSE).

lean-deny is meant to run as a separate program (`lake exe`, `lake lint`).
Our reading, following the FSF's GPL FAQ on separate programs, is that
requiring it to check a workspace does not put that workspace's code under
the GPL; importing its `LeanDeny` library into your own code does. This is
not legal advice.
