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
> graph through Lake and exits with the codes below. No rule kinds exist yet,
> so the only policy it accepts is an empty one; any key in
> `lean-deny.toml` is an error, never silently ignored. `lean-deny graph`
> prints the graph it loads, as text, JSON or DOT. The rule syntax below
> is a draft and will change. The plan lives in the rdm project `lean-deny`
> (roadmaps `foundation` and `policy-rules`).

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
| `allow-only` | What A imports from outside its own package must be in a listed set. Nested rules give tiers, such as a library versus its tests. | none |
| `layers` | Packages are sorted into layers by name or keyword; an import between packages must go in an allowed direction. | none |

### Selectors

Every rule names its sets of modules with selectors:

| Selector | Matches |
|---|---|
| `pkg:<name>` | every module of a Lake package |
| `lib:<name>` | every module of a `lean_lib` |
| `mod:<Prefix>` | that module and every module under it |
| `mod:<Exact>!` | that module alone |
| `keyword:<kw>` | every module of every package whose lakefile declares `keywords = ["<kw>"]` |
| `external:<Prefix>` | modules from outside the workspace, such as `Lean`, `Std` or `Lake` |
| `set:<name>` | a named set from the policy's `[sets]` table |

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

A violation would be reported like this (format not final):

```
error: deny rule 1: a package may depend on the core, and the core on no package
  Editor/Core/Commands.lean:4: Editor.Core.Commands imports Editor.Core.Menus
  Editor/Core/Menus.lean:7: Editor.Core.Menus imports Compile.Api
  Compile.Api belongs to package `compile`, which has keyword `editor-feature`

1 violation in 1 rule
```

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
| `lean-deny check [--workspace <dir>] [--config <file>]` | implemented | Check the policy. `--workspace` defaults to `.`; `--config` defaults to `<workspace>/lean-deny.toml`, and an explicit path is relative to the working directory. |
| `lean-deny graph [--workspace <dir>] [--format text\|json\|dot] [--level module\|lib\|package]` | implemented | Print the resolved graph (see "Seeing the graph"). Defaults: `--workspace .`, `--format text`, `--level module`. Does not read the policy. |
| `lean-deny --help`, `lean-deny --version` | implemented | Print usage or the version. |
| `lean-deny check --format text\|json\|github` | planned | `github` prints annotations for pull requests. |
| `lean-deny explain <selector>` | planned | List the modules a selector matches. |

### Exit codes

| Code | Meaning |
|---|---|
| 0 | Every rule holds (`check`), or the graph was printed (`graph`). |
| 1 | At least one rule is broken. Reserved for rule violations; with no rule kinds yet, nothing produces it. |
| 2 | The command line, the policy or the workspace is bad: a usage error, a missing or malformed policy, an unknown policy key, a workspace that is missing or that Lake cannot load (later also a selector that matches nothing, or an unused wrapper). The same for `graph`, minus the policy. Any internal error is also 2, never 1. |

### Seeing the graph

`lean-deny graph` prints the graph the rules will see, grouped at one of
three levels:

- `module`: every module, and one edge per (importer, imported) pair.
- `lib`: one node per `lean_lib` and per `lean_exe` (`<pkg>/lib/<lib>`,
  `<pkg>/exe/<exe>`). A module listed by two libraries counts in both, as
  `lib:` selectors will see it; an executable's root module is its own
  `exe` node.
- `package`: one node per package.

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
of the import-line parser (`header`), and of the graph builder and its
queries on hand-written graphs (`query`); of the module, lib and package
views on a hand-written graph (`view`); of the renderings, including the
golden JSON `tests/fixtures/graph-json-module/expected.stdout` (`render`);
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

Each rule kind will be tested by small fixture workspaces, one where the rule
holds and one where it is broken. After `lake build --wfail && lake test`,
`git status --porcelain` must print nothing; CI checks that too.

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
