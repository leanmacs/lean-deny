# lean-deny

[![Licence: GPL-3.0-or-later](https://img.shields.io/badge/licence-GPL--3.0--or--later-blue)](LICENSE)

Dependency policy checks for Lean 4 / Lake workspaces.

lean-deny reads the module graph that Lake resolves for a workspace and
checks it against rules you keep as data, in `lean-deny.toml`. A broken rule
is printed with the import chain that breaks it, and the command exits
non-zero. It is to Lake roughly what [cargo-deny]'s `bans` are to Cargo: the
place a monorepo says "package A must not depend on package B" and has the
build hold it.

> **Status: planned, not yet implemented.** This README describes the
> intended design. The policy syntax and commands below are drafts and will
> change; nothing here runs yet. The plan lives in the rdm project
> `lean-deny` (roadmaps `foundation` and `policy-rules`).

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
with its file and line. Lake resolves it; lean-deny builds nothing.

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

or make it your package's lint driver, so `lake lint` runs it (exact syntax
to be confirmed):

```toml
lintDriver = "lean-deny/lean-deny"
lintDriverArgs = ["check"]
```

### Commands (planned)

| Command | Does |
|---|---|
| `lean-deny check [--workspace <dir>] [--config <file>] [--format text\|json\|github]` | Check the policy. `github` prints annotations for pull requests. |
| `lean-deny graph [--format text\|json\|dot] [--level module\|lib\|package]` | Print the resolved graph. |
| `lean-deny explain <selector>` | List the modules a selector matches. |

### Exit codes

| Code | Meaning |
|---|---|
| 0 | Every rule holds. |
| 1 | At least one rule is broken. |
| 2 | The command line, the policy or the workspace is bad: a parse error, a selector that matches nothing, an unused wrapper, or a workspace Lake cannot load. |

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

This is also the project's `rdm verify` command. Each rule kind is tested by
small fixture workspaces under `tests/fixtures/`, one where the rule holds
and one where it is broken.

## Licence

GPL-3.0-or-later. See [`LICENSE`](LICENSE).

lean-deny is meant to run as a separate program (`lake exe`, `lake lint`).
Our reading, following the FSF's GPL FAQ on separate programs, is that
requiring it to check a workspace does not put that workspace's code under
the GPL; importing its `LeanDeny` library into your own code does. This is
not legal advice.
