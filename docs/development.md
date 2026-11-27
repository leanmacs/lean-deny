# Development

Building, testing and formatting lean-deny. How to work on it is in
[`AGENTS.md`](../AGENTS.md).

## The gate

What must pass before a change lands, and what CI runs (it is also the
project's `rdm verify` command):

```sh
lake build --wfail && lake test && lake -d tools/lean-fmt exe lean-fmt format --check --root . && lake -d tools/lean-fmt exe lean-fmt check --root .
```

Afterwards `git status --porcelain` must print nothing; CI checks that too.

## Tests

`lake test` runs `lean-deny-test`: unit tests of the command-line parser (`cli`),
of the selector syntax (`selector`), of the policy loader on TOML texts
(`policy`), of the import-line parser (`header`), and of the graph builder and its
queries on hand-written graphs (`query`); of the module, lib and package
views on a hand-written graph (`view`); of what selectors and sets match
on a hand-written graph (`resolve`); of `deny` rules on hand-written
graphs, from the policy's text to what `check` prints (`deny`), and of
`allow-only` rules, `[layers]`, `[[reachable]]`, `[[co-reach]]`,
`[[target-config]]`, `[[require-backed]]`, `[[doc-modules]]` and
`[[doc-packages]]` rules the same way (`allow-only`, `layers`, `reachable`,
`co-reach`, `target-config`, `require-backed`, `doc-modules`,
`doc-packages`); of the Markdown section and table reading behind
`[[doc-modules]]` and `[[doc-packages]]` on strings (`doc-section`); of the
renderings, including the
golden JSON `tests/fixtures/graph-json-module/expected.stdout` (`render`);
of the check report's JSON and GitHub renderings, including the golden
`tests/fixtures/check-json-deny/expected.stdout` (`report`);
exact checks of the graph loaded for `tests/fixtures/spike-ws`,
`tests/fixtures/graph-ws` and `tests/fixtures/target-ws` (`graph`); the fixture runner's own checks
(`harness`); and every fixture under `tests/fixtures/`. `lake test -- <name>...` runs only the named fixtures.

## Fixtures

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
`reachable-*` for `reachable` and `co-reach-*` for `co-reach`, over
`graph-ws`; `target-config-*` for `target-config`, over `target-ws`;
`require-backed-*` for `require-backed`, over `require-ws`; `doc-modules-*`
for `doc-modules`, over `doc-ws`; `doc-packages-*` for `doc-packages`, over
`doc-pkg-ws`);
`check-json-*` and `check-github-*` for `--format json` and `github` (over
the same workspaces), and `lake-lint-github` for
`lake lint -- --format github`. The `editor-acceptance-*` fixtures run a
cut-down copy of the editor-project policy (`examples/editor-project/`) over
`editor-ws`, a miniature editor-project, where it holds, and
`editor-broken-ws`, where each rule bites. After
`lake build --wfail && lake test`, `git status --porcelain` must print
nothing; CI checks that too.

## Formatting

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
