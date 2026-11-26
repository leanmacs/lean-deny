# editor-project's import rules as a lean-deny policy

## What this is

This is the acceptance test of the `policy-rules` roadmap: editor-project's
four import checks, written as one lean-deny policy, run over editor-project,
and each rule seen to bite on an edit that should break it.

- editor-project revision: `4df216a8` (its `main` on 2026-11-26).
- The checks were shell scripts, `tools/core-imports-check.sh`,
  `tools/package-imports-check.sh`, `tools/host-imports-check.sh` and
  `tools/layer-imports-check.sh`. editor-project deleted them at `d51fe135`
  ("refactor(gate): state structure rules as agent rules and delete their
  shell checkers"), together with the Lake facets they queried. The
  translation here is of the scripts at `78d9d9ea` (`d51fe135^`),
  cross-checked against `.agents/rules/structure.md`, which states the
  rules now ("Core imports", "Host imports", "What a package may import",
  "Three layers").
- Adopting lean-deny in editor-project is editor-project's own rdm task
  `lean-structure-rules-tool`, not this repository's. Nothing here changes
  editor-project.

The files:

| File | What |
|---|---|
| [`examples/editor-project/lean-deny.toml`](../examples/editor-project/lean-deny.toml) | The policy over editor-project's `packages/` workspace: nine rules. |
| [`examples/editor-project/lean-deny.core.toml`](../examples/editor-project/lean-deny.core.toml) | Core rules 4 and 5 over the `lean/` workspace alone: two rules. |
| [`examples/editor-project/acceptance.sh`](../examples/editor-project/acceptance.sh) | The run: copies editor-project out, checks both baselines and every breaking edit, and checks that nothing under editor-project changed. |
| `tests/fixtures/editor-ws`, `editor-broken-ws`, `editor-acceptance-holds`, `editor-acceptance-bites` | A miniature editor-project and the policy cut down to it, so that `lake test` shows every rule biting (see "The fixtures"). |

## Loading editor-project

**Toolchain.** `lean/lean-toolchain` is `leanprover/lean4:v4.35.0`, and
`packages/lean-toolchain` is a symlink to it. lean-deny's toolchain is the
same, so lean-deny's Lake elaborates editor-project's `lean/lakefile.lean`
(about 2000 lines of Lake DSL and code) with the Lake it was written for. If
the two toolchains ever diverge, that lakefile is the first thing to break,
since it uses Lake's API directly.

**Two workspaces.**

- `packages/` is the default package set: a root package `default-set` with
  no modules, which requires the core (`../lean`, Lake package `editor-core`)
  and every default package by path. Its manifest is committed. It loads as
  one workspace holding everything: 45 packages, 1003 module nodes, 8019
  import edges. 18 packages declare the keyword `editor-interface`, `evil`
  declares `editor-input-scheme`, and the other 23 declare none.
- `lean/` alone is `editor-core`, with no requires. It loads too.

There is one policy for each. A selector naming a package (`pkg:compile`)
matches nothing in `lean/`, which is an error, so the rules that name
packages are only in the `packages/` policy, and the `lean/` policy holds
the two core rules that name none.

**Loading writes in the workspace.** Loading `packages/` writes
`packages/.lake/config/<n>/lakefile.olean` and its `.trace` (the elaborated
`editor-core` lakefile), and creates an empty `lean/.lake/`; loading `lean/`
writes `lean/.lake/config/`. editor-project already has both directories, so
a run in place would write into them. That is why every run here is against
a copy, and why the script refuses to finish clean if anything under
editor-project changed. (The README says only `<workspace>/.lake/config/` is
written; the empty `.lake/` of a path dependency is the one extra, and it is
harmless.)

**Timing.** The first load of a fresh copy takes about 3.5 s, most of it
Lake compiling `lean/lakefile.lean`. Later loads of the same copy take about
0.6 s.

**lean-deny cannot load `packages/` at `4df216a8`.** It exits 2 with

```
lean-deny: error: <work>/pristine/packages/compile/CompileTest/Support/Compile.lean:36: import of Editor.Test.Shell: Lake resolves it to library Editor of package editor-core, but no such module file exists
```

The file exists. `lean_lib Editor` has `roots := #[Editor, Editor.Core]`,
and Lake's `modules` facet for a library with roots holds the roots and the
modules of that library they import. No root reaches `Editor.Test.Shell`:
only the tests of `shell`, `version-control`, `compile-api` and `compile`
import it (15 import lines). So lean-deny never lists the module, and the
graph builder reports a missing file. That is a lean-deny loader gap (task
`load-unreached-library-modules`).

It is also an editor-project finding: core rule 2 ("every `Editor.…` module
the build reaches is in `Editor.Core`'s closure") is broken at `4df216a8`.
The deleted script would not have caught it either: its roots were the
core's test executables and the two generated roots, not the packages'
tests. Over all 282 `Editor.*` files, `Editor.Test.Shell` is the only one
outside `Editor.Core`'s closure.

So the acceptance baseline adds `import Editor.Test.Shell` to the copy's
`lean/Editor/Core.lean`, after `import Editor.Test.Restore`. That is the
fix rule 2 prescribes ("Import a new core module from the root in the change
that adds it"), and with it the workspace loads. The script skips it once
editor-project's `Editor.Core` imports the module itself. `lean/` alone
loads without it, since no core module imports `Editor.Test.Shell`.

**The generated roots are not in the graph.** The package-set build writes
two root modules, `EditorSetRoot` and `EditorSetFixtures`, into
`packages/.lake/build/root/` from a facet (`setRoot`, `fixturesRoot`, and
`generatedLib` with `roots := #[]`). No `lean_lib` or `lean_exe` declares
them, and their files exist only after a build. Their text is fixed by
`rootSource` and `fixturesRootSource` in `lean/lakefile.lean`: `import
Editor`, `import Editor.Main` (or `Editor.Test.Fixture.Main`), then one
import per entry module `<P>.EditorPackage`. So the host's modules are the
closure of `Editor`, `Editor.Main` and `Editor.Test.Fixture.Main`, all in
`editor-core`, and the 24 entry modules each import only their own package's
`<P>.Compiled` (and `Evil.Theorems`). The policy names these by hand (tasks
`generated-root-modules` and `derived-selectors`).

**A core-to-package import is visible.** In the `packages/` workspace Lake
resolves imports across the whole workspace, so `import Compile.Compiled` in
`lean/Editor/Main.lean` is an edge of the graph, and deny rule 1, the host
rule and `[layers]` all see it. (Lake itself refuses that import when the
core builds alone in `lean/`.)

**Paths outside the workspace directory print absolute.** The workspace is
`packages/` and the core is `../lean`, outside it. lean-deny prints a path
outside the workspace directory as it is, so every chain step in the core
prints as `/…/lean/Editor/Main.lean:1`, while a package's step prints as
`compile/Compile.lean:1`. The script writes the work directory as `<work>`,
so the outputs below read `<work>/edit/lean/…` (task
`relative-paths-outside-root`).

## The policy

The policy keeps the scripts' rule order, so the labels are stable:

| Label | Script rule |
|---|---|
| deny rule 1 | core imports, rule 1 |
| deny rule 2 | core imports, rule 4 |
| deny rule 3 | core imports, rule 5 |
| deny rule 4 | host imports |
| allow-only rules 1 to 4 | package imports: library, tests, linked test, linked test's root |
| `layers` | layer imports |

In `lean-deny.core.toml`, deny rule 1 is core rule 4 and deny rule 2 is
core rule 5.

**Every package but the core.** `set:packages` is
`keyword:editor-interface`, `keyword:editor-input-scheme` and the 23 other
packages by `pkg:` name. lean-deny has no selector for "every package" to
take the core out of (task `workspace-selector`).

**Package imports judge every import that leaves a package.** The script
judged only imports *of the core's modules*. lean-deny's `allow-only` judges
every import that leaves the importing package, so each tier also allows
`set:packages` (package-to-package imports are the layer rule's business)
and `set:toolchain` (`Init`, `Std`, `Lean`, `Lake`, which the script never
judged). That gives exactly the script's verdicts.

**Each tier's allowance is one set.** `library-may` is the API, the packages
and the toolchain; `test-may` adds the test doubles; `linked-may` adds the
linked test kit; `linked-root-may` adds the root's extras. lean-deny makes
an `allow` selector that allows nothing an error, per selector, and a tier
such as the linked roots does not use every part of its allowance. Bundling
keeps each tier's meaning the script's, and the bundle is still checked to
be used.

**The script's classification order is `except`.** The script classified a
core module as linked kit, else test double, else core interface, else
internal, else API. The sets do the same: `doubles` excludes `linked-kit`;
`internal` excludes `doubles`, which takes `Editor.Config.Packages` and
`Editor.Config.Elaborator.{Model,Contract}` out of `Editor.Config…`; `api`
is `lib:Editor` and `lib:FilesApi` minus the other three. Every other module
of `editor-core` (`ModelTest…`, `Lint`, the fixtures) is in no allowance,
as the script refused "any module of the core's Lake package not named
`Editor.…`".

**Patterns are enumerated as of `4df216a8`.** lean-deny has no glob selector
(task `glob-selector`), so the script's patterns become lists:
`Editor.*.Model` and the modules under one become 14 prefix selectors,
`Editor.*Contract` 21 modules, `Editor.*.Cases` 3, `Editor.*.Real` 13,
`<P>Test` 43 prefixes, `<P>Test.Linked` 13 prefixes (`VcApiTest.Linked`,
which has submodules only, included), its root 12 modules, and
`*.EditorPackage` 24. These fail open: a new `Editor.Foo.Model` is in no
list, so it falls into `api`, and a package's library may import it.

**Names that match nothing cannot be written.** The script reserves
`Editor.Internal…`, `Editor.*.Kit` and the core's `*ApiTest.Linked…`, and
none has a module today. A selector that matches nothing is an error, so the
policy leaves them out, and the first module under one would fall into
`api` (task `reserved-namespace-selector`).

**The host.** The host roots are the generated roots' imports other than
the entry modules, named by hand: `mod:Editor!`, `mod:Editor.Main!`,
`mod:Editor.Test.Fixture.Main!`. The feature modules are the 24 entry
modules and their 25 direct imports, enumerated (see "The host check and
selectors").

**Core rule 1 is in its standing form.** `structure.md` states it as "the
core imports no package", and that is deny rule 1. The script's own form
was "the root reaches no *moving* module", a feature whose edges from the
core are cut but which has not moved out yet, with no moving module by
default, so with none named it held of nothing. While a feature is moving
out, the policy would add

```toml
[[deny]]
from = "mod:Editor.Core!"
to = "mod:Editor.<Feature>"
transitive = true
reason = "..."
```

No edit here exercises that form.

## Rule by rule

| Script | Rule (the script's numbering) | lean-deny rule | Fidelity |
|---|---|---|---|
| core imports | 1: the root reaches no moving module | deny rule 1 | The standing form, "the core imports no package", transitive. The moving form is a second `deny` per moving feature, as above. |
| core imports | 2: every `Editor.…` module the build reaches is in the root's closure | none | A coverage rule, which lean-deny does not have: task `coverage-rules`. Broken at `4df216a8` (`Editor.Test.Shell`). |
| core imports | 3: a root that reaches the elaborator adapter reaches the config base | none | No rule kind says "if a root reaches A it reaches B": task `reach-implies-reach`. Its roots include the generated ones: task `generated-root-modules`. |
| core imports | 4: the config base and `ModelTest` are plain Lean | deny rule 2 (core policy: 1) | The same semantics as the script: both see the direct imports of `Lean`/`Lake` (or a module under either) by the modules in the closure. Both share the limit that task `external-transitive-reach` describes: an import of an external module that itself reaches Lean's frontend is not seen. |
| core imports | 5: `ModelTest` reaches no `Editor.Ffi` module | deny rule 3 (core policy: 2) | Exact. |
| package imports | library: the core's API alone | allow-only rule 1 | The tiers and allowances equal the script's kinds and lists as of `4df216a8`. Patterns enumerated (task `glob-selector`); "every package" enumerated (task `workspace-selector`); `Editor.Internal…`, `Editor.*.Kit` and the core's `*ApiTest.Linked…` left out (task `reserved-namespace-selector`). |
| package imports | test: also the test doubles | allow-only rule 2 | As above. The more specific rule governs a test module, so the library rule does not also judge it. |
| package imports | linked test: also the linked test kit | allow-only rule 3 | As above. |
| package imports | linked test's root: also the real bindings, the headless host and the config base | allow-only rule 4 | As above. `Editor.Window.Real` and `Editor.WindowCheck.Real` are excepted from the root's extras, as in the script. |
| host imports | the host's modules reach no feature module | deny rule 4 | The roots are named from `rootSource` by hand (task `generated-root-modules`); the feature modules are enumerated (task `derived-selectors`). |
| layer imports | the core imports no package | `layers` | Exact. |
| layer imports | no package imports an implementation package | `layers` | Exact: `implementation` is the default layer, so a misspelt keyword makes a package more refused, never less, as in the script. |
| layer imports | an import within one package is allowed | `layers` | `same-package = "allow"`. |
| layer imports | everything else is allowed | `layers` | The four pairs, interface → interface included: two such imports exist at `4df216a8`. |

The scripts exited 2 when a rule would hold of nothing, so that they could
not pass by checking nothing. lean-deny's errors (exit 2) do the same work:

| Script guard (exit 2) | lean-deny |
|---|---|
| Lake answers nothing for a root; a list or root that fell behind the build | Every selector must match a module of the workspace: a renamed module is an error, not a rule that holds. |
| No root of the build reaches the elaborator adapter (core rule 3) | No rule (rule 3 is task `reach-implies-reach`, which should keep this guard). |
| The package check has no line to check | Every `allow` selector must allow something: some module the rule governs imports a module it matches from outside its own package. An allow-only rule must govern some module. |
| The layer check has no line with a core module as importer | Every `allow` pair must allow an import, and the default layer must hold a package. |
| The host check finds no list module among the root's imports | Every selector of deny rule 4 must match. |

## The host check and selectors

Can selectors express "the root's imports other than the `*.EditorPackage`
modules"? No, for three reasons:

1. The root is in no graph. The package-set build generates it, and no Lake
   target declares it (task `generated-root-modules`).
2. Nothing derives a set from the graph's edges: "the modules the entry
   modules import directly" cannot be written (task `derived-selectors`).
3. `*.EditorPackage` is a pattern (task `glob-selector`).

So the policy restates the root's imports by hand from `rootSource`
(`set:host-roots`) and lists the feature modules (`set:entry-modules` and
their direct imports, `set:feature-modules`). It bites, as the `host` edit
shows, but a new package's entry module is outside the rule until someone
adds it to both lists.

## The runs

The run, at the root of lean-deny's repository:

```sh
lake build
examples/editor-project/acceptance.sh /path/to/editor-project /path/to/work-dir
```

The script copies editor-project's `lean/` and `packages/` (without `.lake/`
and `target/`) into `<work dir>/pristine` and never points lean-deny, or any
command that writes, at editor-project itself: it reads the revision with
`git --no-optional-locks rev-parse` and copies with `rsync`. It prints the
as-is load (its exit is printed, not asserted), applies the baseline fix,
checks both baselines, then, for each edit, starts from a fresh copy of the
pristine tree, prepends one `import` line to one file, and runs `check`. For
each run it asserts three things: the exit code; that the rules whose
violations are printed are exactly the expected ones, so no other rule
bites; and the summary line, matched as a whole line. At the end it fails if
anything under editor-project is newer than its start stamp (`.git/` too,
but for `.git/worktrees/`, which other checkouts' own git commands refresh).
No edited file starts with `module` or `prelude`, so a prepended import keeps
the header valid.

The whole confirmation, in order:

1. `lake build`.
2. `examples/editor-project/acceptance.sh <editor-project> <work dir>` exits
   0, its last line is `acceptance: every expectation held`, and it printed
   no `MISMATCH` (which includes "files under editor-project changed").
3. `lake build --wfail && lake test` and both lean-fmt checks (the
   `rdm verify` command in the README), which run the `editor-acceptance-*`
   fixtures.
4. `git status --porcelain` in lean-deny's repository prints nothing.

If editor-project's tree drifts, a run still ends with the check that
nothing under editor-project changed and the verdict, `acceptance: some
expectation failed`, and exits 1. A file the script edits that is gone (one
in the edit table, or `lean/Editor/Core.lean` for the baseline fix) prints
`MISMATCH: <file> is not in editor-project any more; update the edit table
in acceptance.sh` (or `the baseline fix`), and that edit is skipped. A module
the policy names that is gone makes each check print lean-deny's located
error and `exit 2`, then `MISMATCH: expected exit 0` (or `1`). Then update
the edit table in the script, or the enumerations in the policy, and the
revision at the top of this page.

The edits:

| id | Breaks | File (in the copy) | Added import | Exit | Rules that bite |
|---|---|---|---|---|---|
| core-1 | core 1: the core imports no package | `lean/ModelTest/Editor/Bound.lean` | `CompileApi` | 1 | deny rule 1 ×2, `layers` |
| core-4 | core 4: the base and `ModelTest` are plain Lean | `lean/Editor/Bound.lean` | `Lean.Data.Json` | 1 | deny rule 2 ×2 |
| core-4-lean | the same, over `lean/` with the core policy | `lean/Editor/Bound.lean` | `Lean.Data.Json` | 1 | deny rule 1 ×2 |
| core-5 | core 5: `ModelTest` reaches no `Editor.Ffi` | `lean/ModelTest/Editor/Bound.lean` | `Editor.Ffi.Text` | 1 | deny rule 3 |
| core-5-lean | the same, over `lean/` with the core policy | `lean/ModelTest/Editor/Bound.lean` | `Editor.Ffi.Text` | 1 | deny rule 2 |
| host | host: the host reaches no feature module | `lean/Editor/Main.lean` | `Compile.Compiled` | 1 | deny rule 4, deny rule 1 ×2, `layers` |
| package-library | package: a library imports the API alone | `packages/compile/Compile.lean` | `Editor.Loop` | 1 | allow-only rule 1 |
| package-library-double | package: a library may not import a test double | `packages/compile/Compile.lean` | `Editor.Text.Model` | 1 | allow-only rule 1 |
| package-test | package: a test may import the doubles, not the linked kit | `packages/compile/CompileTest/Compile.lean` | `Editor.Test.Linked.Rig` | 1 | allow-only rule 2 |
| package-linked | package: a linked-test module gets the linked kit, not the root's extras | `packages/compile/CompileTest/Linked/Compile.lean` | `Editor.Headless` | 1 | allow-only rule 3 |
| package-linked-root | package: even the linked root may not import a raw binding | `packages/compile/CompileTest/Linked.lean` | `Editor.Ffi.Text` | 1 | allow-only rule 4 |
| layers | layers: no package imports an implementation package | `packages/compile/Compile.lean` | `Shell` | 1 | `layers` |
| control-test-double | control: a test may import a double | `packages/compile/CompileTest/Compile.lean` | `Editor.Text.Model` | 0 | none |
| control-test-fake | control: a test may import a fake | `packages/compile/CompileTest/Compile.lean` | `Editor.Job.Fake` | 0 | none |
| control-linked-root-real | control: the linked root may import a real binding | `packages/compile/CompileTest/Linked.lean` | `Editor.Text.Real` | 0 | none |

Every edit that breaks one script rule bites only that rule's lean-deny
rule, except where the edit necessarily breaks more: `core-1` and `host` add
an import from the core to a package, which `layers` refuses too, and
`host`'s import is in `Editor.Main`, which `Editor.Core` reaches, so deny
rule 1 bites as well. The controls show the tiers are precise, not just
strict: `Editor.Text.Model` imported by `Compile.lean`, a library, bites
allow-only rule 1 (`package-library-double`), and imported by a test it
holds (`control-test-double`); and the linked root may import a real binding
(`control-linked-root-real`) though not a raw one (`package-linked-root`).

The output of one real run follows, as the script printed it, block by
block. The work directory is written `<work>`; core paths print absolute
(see "Loading editor-project"), and the `lean/` runs print paths relative to
`lean/`.

The run begins with the revision line:

```
editor-project: 4df216a8f4e0876510885f53886377626d8b8b19
```

### load the packages/ workspace as it is

editor-project as it is, before the baseline fix: lean-deny cannot load it (see "Loading editor-project").

```
== load the packages/ workspace as it is
lean-deny: error: <work>/pristine/packages/compile/CompileTest/Support/Compile.lean:36: import of Editor.Test.Shell: Lake resolves it to library Editor of package editor-core, but no such module file exists
exit 2
```

### baseline: Editor.Core imports Editor.Test.Shell

The baseline fix is applied to the pristine copy; it prints nothing else.

```
== baseline: Editor.Core imports Editor.Test.Shell
```

### baseline: packages/

Every rule holds over the baseline `packages/`.

```
== baseline: packages/
lean-deny: ok (9 rules)
exit 0
```

### baseline: lean/

Both core rules hold over `lean/` alone.

```
== baseline: lean/
lean-deny: ok (2 rules)
exit 0
```

### core-1: lean/ModelTest/Editor/Bound.lean imports CompileApi

A core module (the model tests') imports an interface package: the core imports no package, and the core layer may import no other layer.

```
== core-1: lean/ModelTest/Editor/Bound.lean imports CompileApi
deny rule 1 (examples/editor-project/lean-deny.toml:150:0): a package may depend on the core, and the core on no package (core imports check, rule 1)
  <work>/edit/lean/ModelTest.lean:16: ModelTest imports ModelTest.Editor.Bound
  <work>/edit/lean/ModelTest/Editor/Bound.lean:1: ModelTest.Editor.Bound imports CompileApi
deny rule 1 (examples/editor-project/lean-deny.toml:150:0): a package may depend on the core, and the core on no package (core imports check, rule 1)
  <work>/edit/lean/ModelTest/Editor/Bound.lean:1: ModelTest.Editor.Bound imports CompileApi
layers (examples/editor-project/lean-deny.toml:199:0): three layers (layer imports check): editor-core (core) may not import compile-api (interface)
  <work>/edit/lean/ModelTest/Editor/Bound.lean:1: ModelTest.Editor.Bound imports CompileApi
lean-deny: 3 violations in 2 of 9 rules
exit 1
```

### core-4: lean/Editor/Bound.lean imports Lean.Data.Json

The base's module `Editor.Bound`, which `Editor` and `ModelTest` both reach, imports a module under `Lean`.

```
== core-4: lean/Editor/Bound.lean imports Lean.Data.Json
deny rule 2 (examples/editor-project/lean-deny.toml:157:0): the config base and the model tests' root are plain Lean (core imports check, rule 4)
  <work>/edit/lean/Editor.lean:5: Editor imports Editor.Jumps.Go
  <work>/edit/lean/Editor/Jumps/Go.lean:2: Editor.Jumps.Go imports FilesApi
  <work>/edit/lean/FilesApi.lean:1: FilesApi imports Editor.Extension
  <work>/edit/lean/Editor/Extension.lean:2: Editor.Extension imports Editor.Setup
  <work>/edit/lean/Editor/Setup.lean:21: Editor.Setup imports Editor.Window
  <work>/edit/lean/Editor/Window.lean:1: Editor.Window imports Editor.Bound
  <work>/edit/lean/Editor/Bound.lean:1: Editor.Bound imports Lean.Data.Json
deny rule 2 (examples/editor-project/lean-deny.toml:157:0): the config base and the model tests' root are plain Lean (core imports check, rule 4)
  <work>/edit/lean/ModelTest.lean:16: ModelTest imports ModelTest.Editor.Bound
  <work>/edit/lean/ModelTest/Editor/Bound.lean:1: ModelTest.Editor.Bound imports Editor.Bound
  <work>/edit/lean/Editor/Bound.lean:1: Editor.Bound imports Lean.Data.Json
lean-deny: 2 violations in 1 of 9 rules
exit 1
```

### core-4-lean: lean/Editor/Bound.lean imports Lean.Data.Json

The same edit over `lean/` alone, with the core policy.

```
== core-4-lean: lean/Editor/Bound.lean imports Lean.Data.Json
deny rule 1 (examples/editor-project/lean-deny.core.toml:8:0): the config base and the model tests' root are plain Lean (core imports check, rule 4)
  Editor.lean:5: Editor imports Editor.Jumps.Go
  Editor/Jumps/Go.lean:2: Editor.Jumps.Go imports FilesApi
  FilesApi.lean:1: FilesApi imports Editor.Extension
  Editor/Extension.lean:2: Editor.Extension imports Editor.Setup
  Editor/Setup.lean:21: Editor.Setup imports Editor.Window
  Editor/Window.lean:1: Editor.Window imports Editor.Bound
  Editor/Bound.lean:1: Editor.Bound imports Lean.Data.Json
deny rule 1 (examples/editor-project/lean-deny.core.toml:8:0): the config base and the model tests' root are plain Lean (core imports check, rule 4)
  ModelTest.lean:16: ModelTest imports ModelTest.Editor.Bound
  ModelTest/Editor/Bound.lean:1: ModelTest.Editor.Bound imports Editor.Bound
  Editor/Bound.lean:1: Editor.Bound imports Lean.Data.Json
lean-deny: 2 violations in 1 of 2 rules
exit 1
```

### core-5: lean/ModelTest/Editor/Bound.lean imports Editor.Ffi.Text

A module `ModelTest` reaches imports a raw binding.

```
== core-5: lean/ModelTest/Editor/Bound.lean imports Editor.Ffi.Text
deny rule 3 (examples/editor-project/lean-deny.toml:164:0): model-test links no Rust library (core imports check, rule 5)
  <work>/edit/lean/ModelTest.lean:16: ModelTest imports ModelTest.Editor.Bound
  <work>/edit/lean/ModelTest/Editor/Bound.lean:1: ModelTest.Editor.Bound imports Editor.Ffi.Text
lean-deny: 1 violation in 1 of 9 rules
exit 1
```

### core-5-lean: lean/ModelTest/Editor/Bound.lean imports Editor.Ffi.Text

The same edit over `lean/` alone, with the core policy.

```
== core-5-lean: lean/ModelTest/Editor/Bound.lean imports Editor.Ffi.Text
deny rule 2 (examples/editor-project/lean-deny.core.toml:14:0): model-test links no Rust library (core imports check, rule 5)
  ModelTest.lean:16: ModelTest imports ModelTest.Editor.Bound
  ModelTest/Editor/Bound.lean:1: ModelTest.Editor.Bound imports Editor.Ffi.Text
lean-deny: 1 violation in 1 of 2 rules
exit 1
```

### host: lean/Editor/Main.lean imports Compile.Compiled

A host module imports a feature module; it is also a core module importing a package.

```
== host: lean/Editor/Main.lean imports Compile.Compiled
deny rule 1 (examples/editor-project/lean-deny.toml:150:0): a package may depend on the core, and the core on no package (core imports check, rule 1)
  <work>/edit/lean/Editor/Core.lean:23: Editor.Core imports Editor.Main
  <work>/edit/lean/Editor/Main.lean:1: Editor.Main imports Compile.Compiled
deny rule 1 (examples/editor-project/lean-deny.toml:150:0): a package may depend on the core, and the core on no package (core imports check, rule 1)
  <work>/edit/lean/Editor/Main.lean:1: Editor.Main imports Compile.Compiled
deny rule 4 (examples/editor-project/lean-deny.toml:171:0): the host is handed its packages as a value and names none of them (host imports check)
  <work>/edit/lean/Editor/Main.lean:1: Editor.Main imports Compile.Compiled
layers (examples/editor-project/lean-deny.toml:199:0): three layers (layer imports check): editor-core (core) may not import compile (implementation)
  <work>/edit/lean/Editor/Main.lean:1: Editor.Main imports Compile.Compiled
lean-deny: 4 violations in 3 of 9 rules
exit 1
```

### package-library: packages/compile/Compile.lean imports Editor.Loop

A package's library imports an internal module of the core (the loop).

```
== package-library: packages/compile/Compile.lean imports Editor.Loop
allow-only rule 1 (examples/editor-project/lean-deny.toml:178:0): a package's library imports the core's API alone (package imports check)
  compile/Compile.lean:1: Compile imports Editor.Loop
lean-deny: 1 violation in 1 of 9 rules
exit 1
```

### package-library-double: packages/compile/Compile.lean imports Editor.Text.Model

A package's library imports a test double, which only its tests may.

```
== package-library-double: packages/compile/Compile.lean imports Editor.Text.Model
allow-only rule 1 (examples/editor-project/lean-deny.toml:178:0): a package's library imports the core's API alone (package imports check)
  compile/Compile.lean:1: Compile imports Editor.Text.Model
lean-deny: 1 violation in 1 of 9 rules
exit 1
```

### package-test: packages/compile/CompileTest/Compile.lean imports Editor.Test.Linked.Rig

A package's test module, outside its linked test, imports the linked test kit.

```
== package-test: packages/compile/CompileTest/Compile.lean imports Editor.Test.Linked.Rig
allow-only rule 2 (examples/editor-project/lean-deny.toml:183:0): a package's tests may also import the core's test doubles (package imports check)
  compile/CompileTest/Compile.lean:1: CompileTest.Compile imports Editor.Test.Linked.Rig
lean-deny: 1 violation in 1 of 9 rules
exit 1
```

### package-linked: packages/compile/CompileTest/Linked/Compile.lean imports Editor.Headless

A module under the linked test's root imports the headless host, which only the root may.

```
== package-linked: packages/compile/CompileTest/Linked/Compile.lean imports Editor.Headless
allow-only rule 3 (examples/editor-project/lean-deny.toml:188:0): a package's linked test may also import the linked test kit (package imports check)
  compile/CompileTest/Linked/Compile.lean:1: CompileTest.Linked.Compile imports Editor.Headless
lean-deny: 1 violation in 1 of 9 rules
exit 1
```

### package-linked-root: packages/compile/CompileTest/Linked.lean imports Editor.Ffi.Text

The linked test's root imports a raw binding, which no module of a package may.

```
== package-linked-root: packages/compile/CompileTest/Linked.lean imports Editor.Ffi.Text
allow-only rule 4 (examples/editor-project/lean-deny.toml:193:0): a linked test's root may also import the real bindings, the headless host and the config base (package imports check)
  compile/CompileTest/Linked.lean:1: CompileTest.Linked imports Editor.Ffi.Text
lean-deny: 1 violation in 1 of 9 rules
exit 1
```

### layers: packages/compile/Compile.lean imports Shell

An implementation package imports another implementation package.

```
== layers: packages/compile/Compile.lean imports Shell
layers (examples/editor-project/lean-deny.toml:199:0): three layers (layer imports check): compile (implementation) may not import shell (implementation)
  compile/Compile.lean:1: Compile imports Shell
lean-deny: 1 violation in 1 of 9 rules
exit 1
```

### control-test-double: packages/compile/CompileTest/Compile.lean imports Editor.Text.Model

Control: a package's test imports a test double. It holds.

```
== control-test-double: packages/compile/CompileTest/Compile.lean imports Editor.Text.Model
lean-deny: ok (9 rules)
exit 0
```

### control-test-fake: packages/compile/CompileTest/Compile.lean imports Editor.Job.Fake

Control: a package's test imports a fake. It holds.

```
== control-test-fake: packages/compile/CompileTest/Compile.lean imports Editor.Job.Fake
lean-deny: ok (9 rules)
exit 0
```

### control-linked-root-real: packages/compile/CompileTest/Linked.lean imports Editor.Text.Real

Control: the linked test's root imports a real binding. It holds.

```
== control-linked-root-real: packages/compile/CompileTest/Linked.lean imports Editor.Text.Real
lean-deny: ok (9 rules)
exit 0
```

It ends with the verdict:

```
acceptance: every expectation held
```

## The fixtures

editor-project is not available in CI, and its tree changes daily, so "each
rule bites" would otherwise be a one-off log on this page. The fixtures make
it part of `lake test`:

- `tests/fixtures/editor-ws` is a miniature editor-project. A root package
  `default-set` requires the core `editor-core` (in `lean/`: libraries
  `Editor` with roots `Editor` and `Editor.Core`, `FilesApi`, `FilesApiTest`
  and `ModelTests`, and the executable `model-test` rooted at `ModelTest`),
  two interface packages (`shell-api`, `compile-api`, the second importing
  the first) and two implementation packages (`shell`, `compile`, the
  latter with its tests, linked test and linked test's root). Every rule of
  the policy holds over it.
- `tests/fixtures/editor-broken-ws` is the same workspace plus one breaking
  import per rule, appended after the existing ones.
- `tests/fixtures/editor-acceptance-holds` runs the policy cut down to these
  modules (the same set names, rules, order and reasons) over `editor-ws`:
  `lean-deny: ok (9 rules)`.
- `tests/fixtures/editor-acceptance-bites` runs the same policy over
  `editor-broken-ws`: `lean-deny: 15 violations in 9 of 9 rules`. Deny rule
  1 bites four times (`Editor.Core` through `Editor.Main`, `Editor.Main`,
  `ModelTest` through `ModelTest.Bound`, `ModelTest.Bound`), deny rule 2
  twice, `layers` three times (compile → shell, editor-core → compile,
  editor-core → compile-api), and every other rule once.

The fixtures are a model of editor-project's structure, not a copy of it:
each `.lean` file holds only `import` lines (two hold none), with
editor-project's module and package names and none of its source. Their
lakefiles are TOML, so loading them runs no code, and they write nothing.
The `ModelTests` library matters: without it `ModelTest.Bound` would belong
to no target and become an external node, and deny rules 1 and 3 would not
see through it. editor-project has that library too.

## Gaps

"Unlanded" below means introduced by the `policy-rules` roadmap and not yet
on `main`.

| Gap | Task |
|---|---|
| Core rule 2: every `Editor.…` module the build reaches is in `Editor.Core`'s closure. A coverage rule; its roots are the build's, which include the generated roots and should include the packages' test executables. editor-project breaks it at `4df216a8`. | `coverage-rules` |
| Core rule 3: a root that reaches the elaborator adapter also reaches the config base. No rule kind says "if r reaches A then r reaches B". | `reach-implies-reach` |
| The generated roots (`EditorSetRoot`, `EditorSetFixtures`) are declared by no Lake target, so they are outside the graph; the host rule and core rules 2 and 3 are about them. | `generated-root-modules` |
| The feature modules are "the entry modules and what they import directly": no selector derives a set from the graph's edges. | `derived-selectors` |
| Patterns (`Editor.*.Model`, `Editor.*Contract`, `Editor.*.Cases`, `Editor.*.Real`, `Editor.*.Kit`, `<P>Test`, `<P>Test.Linked`, `*.EditorPackage`) are enumerated, and the enumerations fail open: a new match lands in `api`. | `glob-selector` |
| "Every package but the core" is enumerated: a new implementation package declares no keyword and is outside `set:packages` until listed. | `workspace-selector` |
| `Editor.Internal…` and `Editor.*.Kit` have no module yet, so a selector naming them is an error; they are left out, and a first module there falls into `api`. | `reserved-namespace-selector` |
| lean-deny cannot load a workspace where a module of a `roots` library that no root reaches is imported by another package (`Editor.Test.Shell` at `4df216a8`). | `load-unreached-library-modules` |
| Core rule 4 sees only direct imports of `Lean`/`Lake`, as the script did (not a regression). | `external-transitive-reach` |
| Paths outside the workspace directory (the core's, `../lean`) print absolute. | `relative-paths-outside-root` |
| (Out of scope here.) editor-project's lint-plugins check: every target loads a given plugin. | `target-config-rules` |

## For editor-project's adoption

This is input for editor-project's task `lean-structure-rules-tool`:

- Run `lean-deny check` in `packages/`, the default set. There, Lake's
  `.lake/` writes are editor-project's own build directory, so a run in
  place is fine; it is only this repository's acceptance run that must use a
  copy.
- The baseline needs `Editor.Test.Shell` imported by `Editor.Core` (which is
  also what editor-project's own core rule 2 asks for), or lean-deny's task
  `load-unreached-library-modules`.
- Keep the enumerations in the policy in sync with the tree until the
  `glob-selector`, `derived-selectors` and `workspace-selector` tasks land.
- Build lean-deny with editor-project's toolchain (they are equal now), so
  its Lake elaborates editor-project's `lean/lakefile.lean` as editor-project's
  Lake does.
