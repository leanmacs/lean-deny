# lean-deny

[![Licence: GPL-3.0-or-later](https://img.shields.io/badge/licence-GPL--3.0--or--later-blue)](LICENSE)

Dependency rules for Lean 4 / Lake workspaces, checked against the module
graph Lake resolves. Write rules like "the core never imports a plugin" in
`lean-deny.toml`. `lean-deny check` prints the import chain behind each rule
that breaks and exits non-zero. It is to Lake roughly what [cargo-deny]'s
`bans` are to Cargo.

[cargo-deny]: https://github.com/EmbarkStudios/cargo-deny

## Install

Add it to your workspace's `lakefile.toml`, so Lake builds it with your
toolchain:

```toml
[[require]]
name = "lean-deny"
git = "https://github.com/leanmacs/lean-deny"
rev = "main"  # or pin a commit
```

The workspace needs a `lake-manifest.json` (`lake update` once).

## Quick start

Write a `lean-deny.toml` at the workspace root:

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

Then run:

```sh
lake exe lean-deny check
```

When every rule holds it prints `lean-deny: ok (4 rules)` and exits 0. A
broken rule is printed with the chain that breaks it:

```
deny rule 1 (lean-deny.toml:8:0): a package may depend on the core, and the core on no package
  Editor/Core/Commands.lean:4: Editor.Core.Commands imports Editor.Core.Menus
  Editor/Core/Menus.lean:7: Editor.Core.Menus imports Compile.Api
lean-deny: 1 violation in 1 of 4 rules
```

A policy that can't check anything is an error, not a pass. For example, a
selector that matches no module after a rename fails with exit code 2.

## Selectors

Rules name modules with selectors:

| Selector | Matches |
|---|---|
| `pkg:<name>` | every module of a Lake package |
| `lib:<lib>` | every module of a `lean_lib` |
| `mod:<Prefix>`, `mod:<Exact>!` | a module and everything under it, or that module alone |
| `keyword:<kw>` | every module of every package with that lakefile keyword |
| `external:<Prefix>` | modules outside the workspace, such as `Lean` or `Std` |
| `set:<name>` | a named set from `[sets]` |
| `imports:<selector>` | the workspace modules those modules import directly |

`lean-deny explain <selector>` lists what a selector matches. More detail,
including `[sets]` with `except` and `[[root]]` for generated modules, is in
[docs/policy.md](docs/policy.md).

## Rules

| Rule | Says |
|---|---|
| `deny` | Modules in A must not import modules in B, directly or transitively; `wrappers` may. |
| `allow-only` | What A imports from outside its own package must be in a listed set. |
| `layers` | Every package is in a layer; imports between packages must follow allowed layer pairs. |
| `reachable` | Every module in B is in A's import closure. |
| `co-reach` | A root whose closure holds a module of A also holds every module of B. |
| `target-config` | Every `lean_lib` and `lean_exe` of a set loads a given Lake plugin. |
| `require-backed` | An import into another workspace package is backed by a direct `require`. |
| `doc-modules` | A Markdown section lists exactly a set's modules. |
| `doc-packages` | A Markdown table has one row per package, with its layer and requires. |

Each rule's keys, errors and output are in [docs/rules.md](docs/rules.md).

## Commands

```sh
lean-deny check   [--workspace <dir>] [--config <file>] [--format text|json|github]
lean-deny explain [--workspace <dir>] [--config <file>] <selector>
lean-deny graph   [--workspace <dir>] [--config <file>] [--format text|json|dot] [--level module|lib|package]
```

Exit codes: `0` ok, `1` a rule is broken, `2` a bad command line, policy or
workspace.

## In CI

`--format github` prints violations as annotations on the pull request's
diff:

```yaml
- name: Check the dependency policy
  run: lake exe lean-deny check --format github
```

`--format json` ([schema](docs/check-json.md)) is for other tools. To run
lean-deny as your `lake lint` driver, see [docs/usage.md](docs/usage.md).

**Loading a workspace runs its `lakefile.lean` files, as `lake` does.** Only
point lean-deny at workspaces you would build.

## Documentation

- [docs/usage.md](docs/usage.md): `lake lint`, every command option, exit
  codes, CI output, and `lean-deny graph`.
- [docs/policy.md](docs/policy.md): selectors, `[sets]` and declared roots.
- [docs/rules.md](docs/rules.md): reference for every rule kind.
- [docs/check-json.md](docs/check-json.md),
  [docs/graph-json.md](docs/graph-json.md): JSON output schemas.
- [docs/editor-project-acceptance.md](docs/editor-project-acceptance.md): a
  full policy for a large workspace, with each rule shown to bite.
- [docs/development.md](docs/development.md): building, testing and
  formatting lean-deny. Contributors and agents start at
  [AGENTS.md](AGENTS.md).

## Licence

GPL-3.0-or-later. See [`LICENSE`](LICENSE).
