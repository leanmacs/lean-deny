# Using lean-deny

How lean-deny runs with Lake, its commands and exit codes, its CI output, and
the graph it checks. The README covers installing it.

## With Lake

`lake exe lean-deny check` runs it directly. To have `lake lint` run it, make
it your package's lint driver:

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
custom Lake facet in your workspace.

Reading the workspace runs its code. Lake's loader elaborates the
`lakefile.lean` of the workspace and of every dependency in-process, so
`lean-deny check` runs that code exactly as running `lake` would. Do not
point it at a workspace you would not run `lake build` in. (A package
configured by `lakefile.toml` is declarative; nothing in it is run.)

The workspace must have a `lake-manifest.json` (run `lake update` or any
`lake build` once): lean-deny never resolves or fetches dependencies itself.

## Commands

| Command | Does |
|---|---|
| `lean-deny check [--workspace <dir>] [--config <file>] [--format text\|json\|github]` | Check the policy. Prints `lean-deny: ok (N rules)` when every rule holds, or each violation and a summary line (see [rules.md](rules.md)). `--workspace` defaults to `.`; `--config` defaults to `<workspace>/lean-deny.toml`, and an explicit path is relative to the working directory. `--format` defaults to `text`; `json` is versioned and documented in [`check-json.md`](check-json.md); `github` prints GitHub annotations (see "In CI" below). The exit code is the same in every format. |
| `lean-deny graph [--workspace <dir>] [--config <file>] [--format text\|json\|dot] [--level module\|lib\|package]` | Print the resolved graph (see "Seeing the graph" below). Defaults: `--workspace .`, `--config <workspace>/lean-deny.toml`, `--format text`, `--level module`. Reads the policy only for its `[[root]]` tables (see [policy.md](policy.md#declared-roots)); every other key is ignored. A default policy that does not exist gives no declared roots; a policy that is not valid TOML gives a warning and no declared roots. |
| `lean-deny --help`, `lean-deny --version` | Print usage or the version. |
| `lean-deny explain [--workspace <dir>] [--config <file>] <selector>` | List the modules a selector matches, one per line, in the order `graph` prints them. A selector that matches nothing exits 2. The policy (`--config`, default `<workspace>/lean-deny.toml`) is read in full only for a selector that names a set (`set:x`, `imports:set:x`), and then only that set and the sets it refers to are resolved; for any other selector only its `[[root]]` tables are read, as for `graph`. |

## Exit codes

| Code | Meaning |
|---|---|
| 0 | Every rule holds (`check`), the graph was printed (`graph`), or at least one matching module was printed (`explain`). |
| 1 | At least one rule is broken (a `deny`, `allow-only`, `layers`, `reachable`, `co-reach`, `target-config`, `require-backed`, `doc-modules` or `doc-packages` violation). The violations and a summary go to stdout. |
| 2 | The command line, the policy or the workspace is bad: a usage error, a missing or malformed policy, an unknown key, a workspace Lake cannot load, a selector that matches nothing, or any rule-specific error listed in [rules.md](rules.md) and [policy.md](policy.md). No violation is reported then. `graph` reads only the policy's `[[root]]` tables (and only warns on a policy that is not valid TOML); `explain` reads the policy in full only for a selector that names a set. An internal error is also 2, never 1. |

`--format` changes only what `check` prints, never its exit code; a usage
error, a bad `--format` included, is always text on stderr. With
`--format json` stdout holds a JSON document for exit 2 too, and the
diagnostics still go to stderr.

## In CI

`check --format github` prints each violation as a GitHub Actions error
annotation on the import that starts its chain (file and line), with the
rule, its reason and the whole chain in the message, so it shows on the
pull request's diff: a `deny`, `allow-only`, `layers`, `co-reach` or
`require-backed` violation on its import, a `reachable` violation (and a
`co-reach` one with an empty chain) on its module's file, a `target-config`
violation on its package's lakefile, a `doc-modules` violation on its
Markdown file, at the section's heading (a missing module) or the name's
line (an extra name), a `doc-packages` violation on its Markdown file, at
the section's heading (a missing row) or the row's line (the others); a
policy error is annotated on `lean-deny.toml`. Paths
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
`--format json` (schema in [`check-json.md`](check-json.md))
suits other CI systems and tools: stdout is one JSON document for every
outcome, exit 2 included.

## Seeing the graph

`lean-deny graph` prints the graph the rules will see, grouped at one of
three levels:

- `module`: every module, and one edge per (importer, imported) pair.
- `lib`: one node per `lean_lib` and per `lean_exe` (`<pkg>/lib/<lib>`,
  `<pkg>/exe/<exe>`). A module listed by two libraries counts in both, as
  `lib:` selectors will see it; an executable's root module is its own
  `exe` node.
- `package`: one node per package.

At every level, the text output starts with the workspace's packages, in
Lake's order, each with its direct requires as its lakefile writes them
(`graph-ws: requires core`, `base: requires nothing`): what a
`require-backed` rule compares imports against. (JSON already has them, as
each package's `requires`.)

A declared root (see [policy.md](policy.md#declared-roots)) is its own node at every level: at
module level `EditorSetRoot (.lake/build/root/EditorSetRoot.lean): declared
root`, above it `root/EditorSetRoot`, so its imports stay visible.

Above module level, modules from outside the workspace collapse to their
first name component (`external/Lean` holds `Lean.Data.Json`); these are
direct import targets only. Imports inside one node are not drawn as an
edge. Every edge lists the imports behind it (its witnesses), with file and
line, including Lean's implicit `Init` imports, so it is clear why the edge
exists. Paths are relative to the workspace. `--format json` is for tools;
its schema is versioned and documented in
[`graph-json.md`](graph-json.md). `--format dot` is for Graphviz
(`lean-deny graph --level lib --format dot | dot -Tsvg > graph.svg`).
