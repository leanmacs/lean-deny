# `lean-deny check --format json`: schema version 1

```
lean-deny check [--workspace <dir>] [--config <file>] [--format text|json|github]
```

`lean-deny check` loads the policy (`--config`, default
`<workspace>/lean-deny.toml`) and the module graph of the Lake workspace at
`<dir>` (default `.`), and checks every rule of the policy against the
graph. It exits 0 when every rule holds, 1 when at least one rule is broken,
and 2 when the policy, the workspace or the graph is bad. The exit code is
the same in every format.

With `--format json`, stdout is exactly one JSON document, ending in one
newline, for every outcome, exit 2 included, so a CI step can always parse
it. The diagnostics still go to stderr, one `lean-deny: error:` line each.
A usage error, a bad `--format` value included, is text on stderr with
nothing on stdout: the command line did not parse, so no format is known.

This page specifies the JSON. The golden file
[`tests/fixtures/check-json-deny/expected.stdout`](../tests/fixtures/check-json-deny/expected.stdout)
is a worked example: the fixture workspace `tests/fixtures/graph-ws` checked
against a policy with one direct and one transitive deny rule, each broken
once. [`tests/fixtures/check-json-reachable/expected.stdout`](../tests/fixtures/check-json-reachable/expected.stdout)
is one for reachable rules (an empty `chain`, a `module`),
[`tests/fixtures/check-json-co-reach/expected.stdout`](../tests/fixtures/check-json-co-reach/expected.stdout)
one for co-reach rules (a `module`, a witness `chain` or an empty one, and
`missing`),
[`tests/fixtures/check-json-target-config/expected.stdout`](../tests/fixtures/check-json-target-config/expected.stdout)
one for target-config rules (an empty `chain`, a `target`),
[`tests/fixtures/check-json-require-backed/expected.stdout`](../tests/fixtures/check-json-require-backed/expected.stdout)
one for require-backed rules (a one-import `chain`, a `require`),
[`tests/fixtures/check-json-doc-modules/expected.stdout`](../tests/fixtures/check-json-doc-modules/expected.stdout)
one for doc-modules rules (an empty `chain`, a `doc`, a `module` or none), and
[`tests/fixtures/check-json-policy-error/expected.stdout`](../tests/fixtures/check-json-policy-error/expected.stdout)
one for exit 2.

## Top level

```
{
  "schemaVersion": 1,
  "ok": boolean,
  "outcome": "holds" | "violation" | "error",
  "policy": string,
  "rules": number | null,
  "brokenRules": number,
  "violations": [Violation],
  "errors": [Error],
  "summary": string
}
```

Every key is always present.

| Key | Type | Meaning |
|---|---|---|
| `schemaVersion` | number | `1` for this schema; independent of graph JSON's. |
| `ok` | boolean | True exactly when the exit code is 0. |
| `outcome` | string | `holds` (exit 0), `violation` (exit 1) or `error` (exit 2). |
| `policy` | string | The policy path as given (`--config`, or `<workspace>/lean-deny.toml`; `lean-deny.toml` for workspace `.`), as messages print it. |
| `rules` | number or null | The policy's rule count (each `[[deny]]`, `[[allow-only]]`, `[[reachable]]`, `[[co-reach]]`, `[[target-config]]`, `[[require-backed]]` and `[[doc-modules]]` table, and `[layers]` as one); null when the policy did not load. |
| `brokenRules` | number | Rules with at least one violation; 0 when `outcome` is `error`. |
| `violations` | array | Every violation, in report order (Violation); `[]` unless `outcome` is `violation`. |
| `errors` | array | Every diagnostic, in the order stderr prints them (Error); `[]` unless `outcome` is `error`. |
| `summary` | string | The text format's last line: `lean-deny: ok (3 rules)`, `lean-deny: 2 violations in 2 of 2 rules`, or `lean-deny: 4 errors`. |

### Violation

| Key | Type | Meaning |
|---|---|---|
| `rule` | object | The rule it breaks (Rule). |
| `message` | string | The text header after the position: the reason; for `layers`, `<reason>: <detail>` or the detail alone; for `reachable`, `co-reach`, `target-config`, `require-backed` and `doc-modules`, `<reason>: <detail>`. |
| `detail` | string or null | What this violation is beyond the reason: for `layers`, `app (implementation) may not import plugin (implementation)`; for `reachable`, `AppTest is outside the import closure of App` (the `from` modules named when there are at most three, else `'from' (5 modules)`); for `co-reach`, `AppTest reaches Core.Types but not Main`, or, when the root is itself an `if-reaches` module, `Core.Impl is in 'if-reaches' but does not reach Base and Core.Macros` (every missing module named); for `target-config`, `lean_lib pkgb/PkgBExtra does not load @lint/lintShared`, followed by ` and imports no module of lib:lint/Lint` when the rule has `or-imports` (its selectors as written, joined by ` or `); for `require-backed`, `App (package require-ws) imports package iface, which require-ws does not require directly`; for `doc-modules`, `Doc.B is not listed in section 'Missing' of docs/modules.md` for a missing module, or `section 'Extra' of docs/modules.md lists Doc.Gone, which 'modules' does not match` for an extra name (the Markdown file relative to the workspace root); null for the other kinds. |
| `chain` | array | The imports that break the rule, as graph JSON's Import objects ([`graph-json.md`](graph-json.md), "Import"): consecutive (each step's `imported` is the next's `importer`); exactly one for a direct deny rule, an allow-only rule, `layers` and `require-backed` (the first unbacked import directive of the importing module into the imported one); a shortest chain for a transitive deny rule; `[]` for `reachable`, which no import breaks; for `co-reach`, a shortest chain from the root to the nearest `if-reaches` module, the witness that the rule applies, or `[]` when the root is itself one; `[]` for `target-config`, which is about a target's configuration, not an import; `[]` for `doc-modules`, which is about a document. A consumer must not assume a non-empty chain for kind `reachable`, `co-reach`, `target-config` or `doc-modules`. |
| `module` | object or null | For `reachable`, the module the rule does not reach; for `co-reach`, the root the rule is broken for; for a `doc-modules` missing module, that module (`null` for an extra name): `{"name": string, "file": string}`, `file` relative to the workspace root when under it (with `/` separators), otherwise as is, like chain files. `null` for the other kinds. |
| `missing` | array | For `co-reach`, the `must-reach` modules outside the root's closure, at least one, in the order `graph` lists modules, each an object as `module`. `[]` for the other kinds. |
| `target` | object or null | For `target-config`, the target the rule is broken for (Target). `null` for the other kinds (and `module` is `null` for `target-config`). |
| `require` | object or null | For `require-backed`, the package dependency no direct require backs (Require). `null` for the other kinds (and `module`, `target` are `null`, `missing` is `[]`, for `require-backed`). |
| `doc` | object or null | For `doc-modules`, the name missing from or extra in the Markdown section (Doc). `null` for the other kinds (and `target`, `require` are `null`, `missing` is `[]`, for `doc-modules`). |

### Target

| Key | Type | Meaning |
|---|---|---|
| `package` | string | The target's package, as its lakefile names it (unescaped). |
| `kind` | string | `lib` for a `lean_lib`, `exe` for a `lean_exe`. |
| `name` | string | The library's or executable's name (unescaped). |
| `file` | string | The package's lakefile, relative to the workspace root when under it, otherwise as is, like chain files. Lake keeps no line for a target. |
| `plugins` | array of strings | The target's effective plugins, as Lake applies them (its package's `plugins`, then its own), each a Lake build key as the Lake CLI writes it: `@editor-core/lintShared`, a bare `lintShared` when the package is elided. |

### Require

| Key | Type | Meaning |
|---|---|---|
| `package` | string | The importing package, as its lakefile names it (unescaped). |
| `imported` | string | The imported package, which `package` does not require directly (unescaped). |
| `file` | string | The importing package's lakefile, relative to the workspace root when under it, otherwise as is, like chain files. |
| `requires` | array of strings | The importing package's direct requires, as its lakefile writes them, in lakefile order; `[]` when it requires nothing. |

Example:

```json
"require": {"package": "require-ws", "imported": "iface", "file": "lakefile.toml", "requires": ["impl"]}
```

### Doc

| Key | Type | Meaning |
|---|---|---|
| `kind` | string | `missing` (a module `modules` matches that the section does not list) or `extra` (a name with the prefix that the section lists but `modules` does not match). |
| `name` | string | The module name, as the section would write it (`Doc.B`). |
| `file` | string | The Markdown file, relative to the workspace root when under it, otherwise as is, like chain files. |
| `section` | string | The heading's text, as the rule's `section` writes it. |
| `line` | number | 1-based: the heading's line for `missing`, the name's first listing for `extra`. |

Example:

```json
"doc": {"kind": "missing", "name": "Doc.B", "file": "docs/modules.md", "section": "Missing", "line": 16}
```

### Rule

| Key | Type | Meaning |
|---|---|---|
| `kind` | string | `deny`, `allow-only`, `layers`, `reachable`, `co-reach`, `target-config`, `require-backed` or `doc-modules`. |
| `index` | number | 1-based among the policy's tables of that kind, in source order; always 1 for `layers`. |
| `label` | string | `deny rule 1`, `allow-only rule 2`, `layers`, `reachable rule 1`, `co-reach rule 1`, `target-config rule 1`, `require-backed rule 1`, `doc-modules rule 1`: how messages name the rule. |
| `file` | string | The policy path (as `policy`). |
| `line` | number or null | The rule table's 1-based line: its `[[deny]]`/`[[allow-only]]`/`[layers]`/`[[reachable]]`/`[[co-reach]]`/`[[target-config]]`/`[[require-backed]]`/`[[doc-modules]]` header, or the `{` of an inline table. |
| `column` | number or null | Its 0-based column, as Lean and Lake print columns (0 for a header). |
| `reason` | string or null | The rule's `reason` as written; null only for `layers` without one. |

### Error

| Key | Type | Meaning |
|---|---|---|
| `file` | string or null | The policy path when the diagnostic is about a place in the policy; null for workspace and Lake errors. |
| `line` | number or null | 1-based line in `file`, when known. |
| `column` | number or null | 0-based column, when known. |
| `message` | string | The diagnostic without its location prefix. The stderr line is `lean-deny: error: ` + `<file>:<line>:<column>: ` (as far as known) + `message`. |

## Ordering

- `violations`: in the order the text prints them. That is deny rules, then
  allow-only rules, then `layers`, then reachable rules, then co-reach
  rules, then target-config rules, then require-backed rules, then
  doc-modules rules, each in source order. Within a rule, by importing module in the order `graph` lists them,
  then by import directive in source order (direct deny rules, allow-only,
  layers, require-backed), or one per `from` module (transitive deny rules); within a
  reachable rule, by uncovered module in the order `graph` lists them;
  within a co-reach rule, one per root, by root in the order `graph` lists
  them; within a target-config rule, one per target, by package in the
  order `graph` lists packages (Lake's), then libraries, then executables,
  each in lakefile order; within a doc-modules rule, the missing modules in
  the order `graph` lists them, then the extra names in order of first
  appearance in the section.
- `chain`: from the importer in the rule's scope to the module that breaks
  it.
- `errors`: the order stderr prints them.

Key order within an object is **not** significant; read the output with a
JSON parser. The bytes are still deterministic for a given workspace and
toolchain.

## Names and paths

- Module names (`importer`, `imported`) are written as Lean writes them,
  with `«»` around components that need them (`«my-mod».X`).
- Chain `file`s, `module.file`, each `missing[].file`, `target.file`, `require.file` and `doc.file` are relative to the workspace root, with
  `/` separators, as in graph JSON; a file outside the workspace root stays
  as it is.
- `policy`, `rule.file` and `error.file` are the policy path as given on the
  command line (relative to the working directory), or
  `<workspace>/lean-deny.toml`.

## Versioning

The same rule as graph JSON: `schemaVersion` changes only on an
incompatible change: removing or renaming a key, or changing what a value
means. Adding a key is compatible and does not change it, so consumers must
ignore keys they do not know. A change to graph JSON's Import object is a
change to `chain`, so it bumps both schemas.

The `[[reachable]]` rule kind added the Violation key `module` and the Rule
`kind` value `reachable` without a bump: adding a key and a kind is
compatible. No existing key changes meaning for a policy without a
`[[reachable]]` table (`module` is `null` there), and a policy with one needs
a lean-deny that knows it anyway. A consumer must not assume a non-empty
`chain` for kind `reachable`.

The `[[co-reach]]` rule kind added the Violation key `missing` and the Rule
`kind` value `co-reach`, again without a bump: `missing` is `[]` for every
other kind, and `module` and `chain` keep their meaning (for `co-reach`,
`module` is the root and `chain` the witness to its trigger, possibly
empty).

The `[[target-config]]` rule kind added the Violation key `target` and the
Rule `kind` value `target-config`, again without a bump: `target` is `null`
for every other kind; for `target-config`, `chain` and `missing` are `[]`
and `module` is `null`.

The `[[require-backed]]` rule kind added the Violation key `require` and the
Rule `kind` value `require-backed`, again without a bump: `require` is
`null` for every other kind; for `require-backed`, `chain` is exactly one
import, `missing` is `[]`, and `module` and `target` are `null`.

The `[[doc-modules]]` rule kind added the Violation key `doc` and the Rule
`kind` value `doc-modules`, again without a bump: `doc` is `null` for every
other kind; for `doc-modules`, `chain` and `missing` are `[]`, `target` and
`require` are `null`, and `module` is set for a missing module and `null`
for an extra name.

## Text and GitHub

- The text format (the default) is for people. It prints a block per
  violation, a header `<label> (<policy>:<line>:<column>): <message>` and
  then `  <file>[:<line>]: <importer> imports <imported>[ (implicit)]` per
  step (for a reachable rule, one line `  <file>: <module>` naming the
  uncovered module instead; for a co-reach rule, the witness chain from the
  root, or, when it is empty, the root's `  <file>: <module>` line; for a
  target-config rule, one line `  <lakefile>: lean_lib <name>` or
  `  <lakefile>: lean_exe <name>`; for a require-backed rule, the one
  unbacked import, then `  <lakefile>: <package> requires <r1, r2>` or
  `  <lakefile>: <package> requires nothing`; for a doc-modules rule, a
  missing module's `  <file>: <module>` line and then
  `  <markdown>:<line>: section '<section>'`, or an extra name's
  `  <markdown>:<line>: <name>`), and then the summary line. It may change
  without notice.
- `--format github` prints GitHub Actions workflow commands. Each violation
  is one command,
  `::error file=<file>,line=<line>,title=lean-deny%3A <label>::<the text block, newline-separated>`,
  placed on the import that starts its chain. With no `line` property, that
  import is an implicit `Init` import. A reachable violation has no chain:
  its command is a file-level annotation on the uncovered module's file,
  `::error file=<file>,title=lean-deny%3A reachable rule <n>::<text block>`,
  with no `line`. A co-reach violation is placed on its witness chain's
  first import (in the root's file), or, when the chain is empty, is a
  file-level annotation on the root's file, with no `line`. A
  target-config violation is a file-level annotation on its target's
  package lakefile, with no `line`. A require-backed violation is placed
  on its one import, its text block ending in the requires line. A
  doc-modules violation is placed on its Markdown file, at the section's
  heading (a missing module) or at the name's first listing (an extra
  name). On exit 2 it prints one command per
  diagnostic,
  `::error file=<policy>,line=<line>,col=<column+1>,title=lean-deny%3A error::<message>`,
  each property only when known (`col` is 1-based, as GitHub counts). It
  ends with the summary line, as plain text. Its paths are relative to the
  working directory, so run it from the repository root. Escaping: in
  messages `%` becomes `%25`, CR `%0D` and LF `%0A`; in property values,
  also `:` becomes `%3A` and `,` `%2C`.
