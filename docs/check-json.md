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
`missing`), and
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
| `rules` | number or null | The policy's rule count (each `[[deny]]`, `[[allow-only]]`, `[[reachable]]` and `[[co-reach]]` table, and `[layers]` as one); null when the policy did not load. |
| `brokenRules` | number | Rules with at least one violation; 0 when `outcome` is `error`. |
| `violations` | array | Every violation, in report order (Violation); `[]` unless `outcome` is `violation`. |
| `errors` | array | Every diagnostic, in the order stderr prints them (Error); `[]` unless `outcome` is `error`. |
| `summary` | string | The text format's last line: `lean-deny: ok (3 rules)`, `lean-deny: 2 violations in 2 of 2 rules`, or `lean-deny: 4 errors`. |

### Violation

| Key | Type | Meaning |
|---|---|---|
| `rule` | object | The rule it breaks (Rule). |
| `message` | string | The text header after the position: the reason; for `layers`, `<reason>: <detail>` or the detail alone; for `reachable` and `co-reach`, `<reason>: <detail>`. |
| `detail` | string or null | What this violation is beyond the reason: for `layers`, `app (implementation) may not import plugin (implementation)`; for `reachable`, `AppTest is outside the import closure of App` (the `from` modules named when there are at most three, else `'from' (5 modules)`); for `co-reach`, `AppTest reaches Core.Types but not Main`, or, when the root is itself an `if-reaches` module, `Core.Impl is in 'if-reaches' but does not reach Base and Core.Macros` (every missing module named); null for the other kinds. |
| `chain` | array | The imports that break the rule, as graph JSON's Import objects ([`graph-json.md`](graph-json.md), "Import"): consecutive (each step's `imported` is the next's `importer`); exactly one for a direct deny rule, an allow-only rule and `layers`; a shortest chain for a transitive deny rule; `[]` for `reachable`, which no import breaks; for `co-reach`, a shortest chain from the root to the nearest `if-reaches` module, the witness that the rule applies, or `[]` when the root is itself one. A consumer must not assume a non-empty chain for kind `reachable` or `co-reach`. |
| `module` | object or null | For `reachable`, the module the rule does not reach; for `co-reach`, the root the rule is broken for: `{"name": string, "file": string}`, `file` relative to the workspace root when under it (with `/` separators), otherwise as is, like chain files. `null` for the other kinds. |
| `missing` | array | For `co-reach`, the `must-reach` modules outside the root's closure, at least one, in the order `graph` lists modules, each an object as `module`. `[]` for the other kinds. |

### Rule

| Key | Type | Meaning |
|---|---|---|
| `kind` | string | `deny`, `allow-only`, `layers`, `reachable` or `co-reach`. |
| `index` | number | 1-based among the policy's tables of that kind, in source order; always 1 for `layers`. |
| `label` | string | `deny rule 1`, `allow-only rule 2`, `layers`, `reachable rule 1`, `co-reach rule 1`: how messages name the rule. |
| `file` | string | The policy path (as `policy`). |
| `line` | number or null | The rule table's 1-based line: its `[[deny]]`/`[[allow-only]]`/`[layers]`/`[[reachable]]`/`[[co-reach]]` header, or the `{` of an inline table. |
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
  rules, each in source order. Within a rule, by importing module in the order `graph` lists them,
  then by import directive in source order (direct deny rules, allow-only,
  layers), or one per `from` module (transitive deny rules); within a
  reachable rule, by uncovered module in the order `graph` lists them;
  within a co-reach rule, one per root, by root in the order `graph` lists
  them.
- `chain`: from the importer in the rule's scope to the module that breaks
  it.
- `errors`: the order stderr prints them.

Key order within an object is **not** significant; read the output with a
JSON parser. The bytes are still deterministic for a given workspace and
toolchain.

## Names and paths

- Module names (`importer`, `imported`) are written as Lean writes them,
  with `«»` around components that need them (`«my-mod».X`).
- Chain `file`s, `module.file` and each `missing[].file` are relative to the workspace root, with
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

## Text and GitHub

- The text format (the default) is for people. It prints a block per
  violation, a header `<label> (<policy>:<line>:<column>): <message>` and
  then `  <file>[:<line>]: <importer> imports <imported>[ (implicit)]` per
  step (for a reachable rule, one line `  <file>: <module>` naming the
  uncovered module instead; for a co-reach rule, the witness chain from the
  root, or, when it is empty, the root's `  <file>: <module>` line), and
  then the summary line. It may change
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
  file-level annotation on the root's file, with no `line`. On exit 2 it prints one command per
  diagnostic,
  `::error file=<policy>,line=<line>,col=<column+1>,title=lean-deny%3A error::<message>`,
  each property only when known (`col` is 1-based, as GitHub counts). It
  ends with the summary line, as plain text. Its paths are relative to the
  working directory, so run it from the repository root. Escaping: in
  messages `%` becomes `%25`, CR `%0D` and LF `%0A`; in property values,
  also `:` becomes `%3A` and `,` `%2C`.
