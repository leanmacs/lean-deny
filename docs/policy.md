# Selectors, sets and declared roots

How a policy names modules. Every rule in [rules.md](rules.md) takes these.

## Selectors

Every rule names its sets of modules with selectors. `pkg:`, `lib:`,
`mod:` and `keyword:` match modules of the workspace only (a dependency
package's modules are workspace modules); `external:` matches modules from
outside it only. `mod:` also matches the policy's declared roots (see
"Declared roots" below); `pkg:`, `lib:` and `keyword:` never do.

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

## Sets

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

## Declared roots

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
