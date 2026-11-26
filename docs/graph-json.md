# `lean-deny graph --format json`: schema version 1

```
lean-deny graph [--workspace <dir>] [--config <file>] [--format text|json|dot]
                [--level module|lib|package]
```

`lean-deny graph` loads the module graph of the Lake workspace at `<dir>`
(default `.`) and prints it, grouped at a level (default `module`), as text
(default), JSON or Graphviz DOT. It reads the policy (`--config`, default
`<dir>/lean-deny.toml`) only for its `[[root]]` tables, the declared roots
(README, "Declared roots"); every other key is ignored, not checked. A
default policy file that does not exist gives no declared roots; one that is
not valid TOML gives a warning on stderr and no declared roots. On success
it exits 0 and prints the rendering on stdout and nothing on stderr
except those warnings; a usage error, a missing `--config` file, a bad `[[root]]`
table, a declared root whose file is missing or that a Lake target already
provides, or a workspace that is missing or that Lake cannot load exits 2
with diagnostics on stderr.

This page specifies the JSON. The golden file
[`tests/fixtures/graph-json-module/expected.stdout`](../tests/fixtures/graph-json-module/expected.stdout)
is a worked example: the module-level graph of the fixture workspace
`tests/fixtures/graph-ws` (three packages, a module shared by two libraries,
an executable, imports from `Init` and `Lean`).

## The graph and its levels

The graph's **modules** are every module of every `lean_lib` and every
`lean_exe` root of the workspace's packages, plus the **external** modules
that some workspace module imports directly (`Init`, `Lean.Data.Json`, ...).
The policy's **declared roots** (`[[root]]`) are modules too: modules no
Lake target lists, read from their files, such as a root a Lake facet
generates. Their imports seed the search for library modules no root of
their library reaches. Its **imports** are the `import` directives of each
workspace module and declared root, plus
the two imports of `Init` (plain and `meta`) Lean adds to every module that
is not `prelude`; these are flagged `implicit`.

The level groups modules into **nodes**:

| Level | A workspace module is in | An external module is in | A declared root is in | Node ids |
|---|---|---|---|---|
| `module` | its own node | its own node | its own node | the module name |
| `lib` | the node of **each** target listing it: every `lean_lib` whose modules include it, and the `lean_exe` whose root it is | `external/<Root>` | its own node, `root/<Module>` | `<pkg>/lib/<lib>`, `<pkg>/exe/<exe>`, `external/<Root>`, `root/<Module>` |
| `package` | its package's node | `external/<Root>` | its own node, `root/<Module>` | `<pkg>`, `external/<Root>`, `root/<Module>` |

`<Root>` is the first component of the external module's name:
`Lean.Data.Json` is in `external/Lean`. A declared root has no package and
no target, so above module level it is its own node, `root/<Module>`; its
imports would otherwise vanish there.

- A module listed by two libraries (`App.Shared` in `App` and `AppTest` in
  graph-ws) is a member of both nodes; its imports leave both, and imports of
  it reach both.
- An executable's root is a member of its `exe` node at lib level, and of its
  package at package level.
- Every `lean_lib`, `lean_exe` (lib level) and package (package level) is a
  node, even with no modules. An external node exists only when some module
  imports into it.
- An **edge** joins two nodes when some module of the first imports some
  module of the second; it carries every such import, its **witnesses**. At
  module level that is one edge per (importer, imported) pair, carrying each
  directive (`App -> Init` carries the two implicit imports). Above module
  level an import between two modules of one node is not an edge (no
  self-edges); at module level a self-edge cannot occur.

## Top level

```
{
  "schemaVersion": 1,
  "level": "module" | "lib" | "package",
  "packages": [Package],
  "nodes": [Node],
  "edges": [Edge]
}
```

| Key | Type | Meaning |
|---|---|---|
| `schemaVersion` | number | `1` for this schema. |
| `level` | string | The level the nodes and edges are grouped at. |
| `packages` | array | Every package of the workspace, in Lake's order: the root package first, then its dependencies. The same at every level. |
| `nodes` | array | The nodes at this level. |
| `edges` | array | The edges at this level. |

### Package

| Key | Type | Meaning |
|---|---|---|
| `name` | string | The package name. |
| `root` | boolean | Whether it is the workspace's root package. |
| `dir` | string | Its directory (see "Paths"); `.` for the root package. |
| `configFile` | string | Its `lakefile.toml` or `lakefile.lean`. |
| `keywords` | array of strings | Its `keywords`, as declared. |
| `remoteUrl` | string or null | Lake's `remoteUrl` (the git URL of a git dependency); null when empty, as for a path dependency or the root. |
| `requires` | array of strings | The names of its `require`s, in declaration order. |
| `libs` | array | Its `lean_lib`s: `{"name": string, "roots": [module name], "globs": [string]}`. Globs are printed as Lake prints them (`App.*`, `Core.+`, `AppTest`). |
| `exes` | array | Its `lean_exe`s: `{"name": string, "root": module name}`. |

### Node

Every node has `id`, `kind` and `name`; the other keys depend on the level,
and every node of one level has the same keys (`null` or `[]` when there is
no value).

| Key | Levels | Type | Meaning |
|---|---|---|---|
| `id` | all | string | Unique among the nodes; what edges refer to. |
| `kind` | all | string | `module` level: `"module"`, `"root"` or `"external"`. `lib`: `"lib"`, `"exe"`, `"root"` or `"external"`. `package`: `"package"`, `"root"` or `"external"`. `"root"` is a declared root. |
| `name` | all | string | The module name, target name, package name, or external root (`Lean`). |
| `package` | module, lib | string or null | The package the module or target belongs to; null for external nodes and declared roots. |
| `owners` | module | array | The targets listing the module, `{"kind": "lib" \| "exe", "target": string}`, sorted by kind then name; `[]` for external nodes and declared roots. |
| `file` | module | string or null | The module's source file (a declared root's file too); null for external nodes. |
| `isModule` | module | boolean | The header starts with `module` (the module system is on). |
| `isPrelude` | module | boolean | The header says `prelude` (no implicit `Init` imports). |
| `modules` | lib, package | array of strings | The node's member modules. |

### Edge

| Key | Type | Meaning |
|---|---|---|
| `from` | string | The importing node's `id`. |
| `to` | string | The imported node's `id`. |
| `count` | number | The number of imports behind the edge: the length of `imports`, at least 1. |
| `imports` | array | The imports behind the edge (Import). |

### Import

| Key | Type | Meaning |
|---|---|---|
| `importer` | string | The importing module. |
| `imported` | string | The imported module. |
| `file` | string | The importer's source file. |
| `line` | number or null | The 1-based line of the directive's first token; null exactly for implicit imports. |
| `public` | boolean | The directive says `public`. |
| `meta` | boolean | The directive says `meta`. |
| `all` | boolean | The directive says `import all`. |
| `exported` | boolean | Lean's meaning: a `public import`, or any import in a file that is not a `module`. |
| `implicit` | boolean | One of the two `Init` imports Lean adds to every module that is not `prelude`. |

## Ordering

Every array is in a fixed order, so the same workspace always prints the
same bytes (with the same toolchain):

- `packages`: Lake's order, root first.
- `nodes`: workspace nodes and declared roots, then external nodes, each
  sorted by `id`
  (code-point order of the string, so `App.Shared` comes before `AppTest`).
- `modules`: by module name, as a string.
- `owners`: by kind (`lib` before `exe`), then target name.
- `edges`: by the position of `from` in `nodes`, then the position of `to`.
- `imports`: by importer name (as a string), then source order, so one
  importer's implicit `Init` pair comes first, then its directives as
  written.

Key order within an object is **not** significant; read the output with a
JSON parser.

## Names and paths

- Module names (`id` and `name` at module level, `modules`, `importer`,
  `imported`, `roots`, `root`, and the `<Root>` of external ids) are written
  as Lean writes them, with `«»` around components that need them
  (`«my-mod».X`).
- Package and target names are written as `lakefile.toml` writes them,
  without `«»` (`graph-ws`, `graph-app`); so are the `<pkg>` and target parts
  of lib- and package-level ids.
- Paths are relative to the workspace root, with `/` separators; the root
  itself is `.`. A path outside the root (a path `require` pointing outside
  it) is printed absolute. The workspace root itself is not printed.

## Versioning

`schemaVersion` changes only on an incompatible change: removing or renaming
a key, or changing what a value means. Adding a key is compatible and does
not change it, so consumers must ignore keys they do not know. Adding a
`kind` value is compatible too (`"root"` was added within version 1, for
declared roots), so consumers must tolerate kinds they do not know.

## Text and DOT

The text format is for people and carries the same information as the JSON
nodes and edges, with each witness as
`<file>[:<line>]: <importer>: <directive>[ (implicit)]`; it may change
without notice. The DOT format draws the nodes and edges; edges whose
witnesses are all implicit are dotted, external nodes are dashed, edges are
labelled with their count above module level, and below package level each
package is a cluster. A declared root is in no cluster, a plain box; in the
text format a module-level root reads
`<Module> (<file>): declared root[; module][, prelude]`.
