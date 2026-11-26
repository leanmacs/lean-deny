# Packages and the core

A miniature of editor-project's `docs/design/packages.md`, "The module
map", for the editor-acceptance fixtures.

## The module map

### The core's modules

Every module under `lean/Editor/`, each named in full once, by class. The
config base, `lean/Editor.lean`, is not one of them.

| Modules | Count | Class | A package may import it |
|---|---|---|---|
| The core's root: `Editor.Core` | 1 | core | no |
| The hosts: `Editor.Headless`, `Editor.Main`, `Editor.Window.Real` | 3 | core | no |
| The loop: `Editor.Loop` | 1 | core | no |
| The models of the ports: `Editor.Text.Model` | 1 | core | in tests |
| The linked test kit: `Editor.Test.Linked.Rig` | 1 | core | in a linked test |
| The headless fixture harness: `Editor.Test.Fixture.Main` | 1 | core | no |
| The model test kit: `Editor.Test.Kit` | 1 | core | in tests |
| The config session: `Editor.Config.Elaborate`, `Editor.Config.Lakefile` | 2 | core | no |
| The raw bindings: `Editor.Ffi.Text` | 1 | core | no |
| The real bindings: `Editor.Text.Real` | 1 | core | no |
| The editor API: `Editor.Api` | 1 | core | yes |
| The typed time bounds: `Editor.Bound` | 1 | core | yes |

### The packages

One row a package of the default set: its layer as its lakefile declares
it, what it requires beside the core, the extension points it registers at
and reads.

| Package | Layer | Requires, beside the core | Extension points it registers at | Extension points it reads |
|---|---|---|---|---|
| `shell-api` | implementation | none | none | none |
| `compile-api` | interface | `shell-api` | none | none |
| `shell` | implementation | `shell-api` | none | none |
| `compile` | implementation | `compile-api` | none | none |
| `shipped-themes` | implementation | none | none | none |

A first-party package outside the default set has no row above, but one of
its own here, which the rule does not read:

| Package | Layer | Requires, beside the core | Extension points it registers at | Extension points it reads |
|---|---|---|---|---|
| `acp` | implementation | `shell-api` | none | none |
