# AGENTS.md

How to work in this repository: the practices every change follows.

- What lean-deny does, for users: [`README.md`](README.md), with the
  reference in `docs/` ([`usage.md`](docs/usage.md),
  [`policy.md`](docs/policy.md), [`rules.md`](docs/rules.md) and the JSON
  schemas).
- How to build, test and format it, and what must pass before a change
  lands: [`docs/development.md`](docs/development.md).
- Why the graph comes from Lake's in-process API, and other recorded
  decisions: [`docs/decisions/`](docs/decisions/).
- Plans live in the rdm project `lean-deny`. Use the rdm CLI, not the plan
  files.

Read the documents for the area you are changing before you change it. When
behaviour a user can see changes, update the reference in `docs/` in the
same change. Keep the README short: it shows how to start, and `docs/` holds
the detail.

## The gate

The gate is `lake build --wfail`, `lake test` and the two lean-fmt checks,
run together as one command in `docs/development.md` and by CI. Each step
passes by its exit status alone.

- A new check is a Lean test in `LeanDenyTest/` or a fixture under
  `tests/fixtures/`, never a shell script.
- `examples/editor-project/acceptance.sh` is an acceptance run against a
  real workspace, not part of the gate. Don't add checks to it that a test or
  fixture could make.
- A reviewer can treat the tests as the evidence that a change works.

## Test-driven development

Write all code test-first:

1. **Red**: write a failing test for the next small piece of behaviour. Run
   it and confirm it fails for the reason you expect.
2. **Green**: write the minimum code that makes the test pass.
3. **Refactor**: clean up the test and the implementation while the suite
   stays green.

- Write production code only in response to a failing test.
- Start every bug fix with a test that reproduces the bug.
- Keep tests fast and deterministic. Build test inputs from small fixture
  data checked into the repo, or construct them in code.

## Architecture: a pure core, Lake and IO at the edge

lean-deny is a pure core with thin adapters around it.

- **One adapter reaches Lake.** `LeanDeny/Graph/LakeApi.lean` is the only
  module that uses Lake's build API. It hands over a plain `Snapshot`
  (`LeanDeny/Graph/Raw.lean`). Everything after it never touches Lake: the
  graph builder, selectors and sets, every rule, and the renderings.
- **Rules are pure.** A rule module in `LeanDeny/Rules/` takes the graph,
  the resolved policy and plain data, and returns violations. Reading files
  a rule needs, such as the Markdown that `doc-modules` and `doc-packages`
  check, happens in the command (`LeanDeny/Check.lean`). The rule gets the
  text.
- **Commands wire it together.** `Check.lean`, `Explain.lean` and
  `GraphCmd.lean` load, resolve, check and print. Keep decisions out of them
  and in the pure modules, where tests reach them.
- Put a helper that several rule kinds share in `LeanDeny/Rules/Common.lean`.
  Put a graph query that several rule kinds share in
  `LeanDeny/Graph/Query.lean`. Don't write a second copy.

### Prefer an existing library

Where a library fits a job, use it and pin its exact version. Write our own
only when no library fits or a measured problem requires it, and record why
in `docs/decisions/`.

## Tests

- Test the pure core on hand-written values: graphs built in code, policies
  from TOML strings, Markdown from strings. No Lake workspace is needed for
  those.
- Keep a module's tests in `LeanDenyTest/`, in the test module named for
  the area it covers (the `deny` rule's tests in `LeanDenyTest/Deny.lean`).
  Add a new suite to `TestMain.lean`'s list.
- Test the binary end to end with fixtures (`docs/development.md`,
  "Fixtures"). Each rule kind has fixtures where it holds and where it bites,
  over a small workspace checked into `tests/fixtures/`. Prefer extending an
  existing workspace over adding a new one.
- Its output is what the command delivers, so a fixture pins its stdout and
  stderr exactly. When a change alters output on purpose, update the expected
  files in the same change and say so in the commit message.
- Test behaviour, never source text. Don't write a test that greps `LeanDeny/`
  for a call or a name. Enforce a rule about code with types, visibility or a
  lint.

## Hermetic tests

Every test runs anywhere with only `lake`, in any order, and leaves the
machine as it found it.

- When a test needs real files, create them in a fresh temporary directory
  owned by that test and pass the path in explicitly. Leave the working
  directory, `$HOME`, environment variables and this repository's git state
  untouched.
- Set up the state a test needs inside the test, so it passes on a clean
  checkout. After the gate, `git status --porcelain` prints nothing.
- Lake-run fixtures carry their own `lean-toolchain` (equal to the root's)
  and a committed `lake-manifest.json`, so they fetch nothing.

## Toolchain

Lean is pinned in `lean-toolchain`. Lake's API changes between releases, so
bump it on purpose, in its own commit. Bump `tools/lean-fmt`'s
`lean-toolchain` and its lean-fmt `rev` in that same commit
(`docs/development.md`, "Formatting"), and fix the build there too.

## Conventional commits

Format every commit message as a
[Conventional Commit](https://www.conventionalcommits.org/en/v1.0.0/):
`<type>(<optional scope>): <imperative summary>`, with types `feat`, `fix`,
`refactor`, `test`, `docs`, `chore`, `build`, `ci`, `perf`, `style`. Scopes
in use: `graph`, `policy`, `rules`, `check`, `cli`, `explain`, `fixtures`,
`acceptance`, `docs`.

## Landing work on `main`

Only reviewed work lands. The worktree must be clean, and the gate must pass
on the result before `main` moves. Never force-push `main`.
