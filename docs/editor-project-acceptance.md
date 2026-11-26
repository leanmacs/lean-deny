# editor-project's import rules as a lean-deny policy

## What this is

This is the acceptance test of the `policy-rules`,
`editor-project-parity` and `editor-project-module-map-leave-out`
roadmaps: editor-project's in-scope structure rules (its four import
checks, every bullet of "Host imports", its lint-plugins rule,
"Leave-out", and "Module map": columns 1 to 3 of "The packages", and "The
core's modules"), written as one lean-deny policy of seventeen rules, run
over editor-project, and each rule seen to bite on an edit that should
break it ("Section by section" lists them).

- editor-project revision: `1101b2069f1e` (its HEAD on 2026-11-26). The run
  under "The runs" is at that revision: the script archives editor-project's
  HEAD and prints it, and the recorded output starts with that line. The
  fourteen earlier rules give the same results as at `acfed133`, the
  revision recorded before: between the two, only a comment line of
  `packages/lakefile.toml` differs under `lean/` and `packages/`. Figures
  pinned to an earlier revision (`4df216a8`, `0e608324`, `acfed133`) say so.
- "Leave-out" and "Module map" (require-backed rule 1, doc-modules rule 1,
  doc-packages rule 1) follow `.agents/rules/structure.md` at `1101b206`.
- The host rules (deny rules 4 to 6) follow `.agents/rules/structure.md`'s
  "Host imports" at `acfed133`. Its fixture support wording dates from
  `5c64af98`, an ancestor of `0e608324`; `acfed133` added the default set's
  first fixture support module (see "The host check and selectors").
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
| [`examples/editor-project/lean-deny.toml`](../examples/editor-project/lean-deny.toml) | The policy over editor-project's `packages/` workspace: seventeen rules. |
| [`examples/editor-project/lean-deny.core.toml`](../examples/editor-project/lean-deny.core.toml) | Core rules 4 and 5 over the `lean/` workspace alone: two rules. |
| [`examples/editor-project/acceptance.sh`](../examples/editor-project/acceptance.sh) | The run: copies editor-project's HEAD out (`git archive` of `lean/`, `packages/` and `docs/design/packages.md`), checks both baselines and every breaking edit, and checks that nothing under editor-project changed. |
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
  one workspace holding everything. At `acfed133`, `lean-deny graph
  --format json` over the copy gives 45 packages, 1011 module nodes and
  8076 import edges with no policy (the copy has no `lean-deny.toml`), and
  1014 nodes and 8135 edges with the policy's two declared roots (at
  `4df216a8`, with no policy, it was 1003 and 8019). 18 packages declare the
  keyword `editor-interface`, `evil` declares `editor-input-scheme`, and the
  other 23 declare none.
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

**lean-deny now loads `packages/` at `4df216a8` unmodified.** Before
roadmap `editor-project-parity` phase 1
(`phase-1-load-unreached-library-modules`) it exited 2 with

```
lean-deny: error: <work>/pristine/packages/compile/CompileTest/Support/Compile.lean:36: import of Editor.Test.Shell: Lake resolves it to library Editor of package editor-core, but no such module file exists
```

The file exists. `lean_lib Editor` has `roots := #[Editor, Editor.Core]`,
and Lake's `modules` facet for a library with roots holds the roots and the
modules of that library they import. No root reaches `Editor.Test.Shell`:
only the tests of `shell`, `version-control`, `compile-api` and `compile`
import it (15 import lines). So lean-deny never listed the module, and the
graph builder reported a missing file. That loader gap is fixed: a module no
`modules` facet lists, but that a workspace module imports and Lake resolves
to a workspace library with an existing file, is now loaded and owned by
that library, so `Editor.Test.Shell` is a module of `editor-core/lib/Editor`
(282 modules).

It is still an editor-project finding: core rule 2 ("every `Editor.…` module
the build reaches is in `Editor.Core`'s closure") is broken at `4df216a8`,
at `0e608324`, at `acfed133` and at `1101b206`. The deleted script would not have caught it either: its
roots were the core's test executables and the two generated roots, not the
packages' tests. Over all 282 `Editor.*` files, `Editor.Test.Shell` is the
only one outside `Editor.Core`'s closure.

The policy states rule 2 as `reachable rule 1` (README, "reachable"), and
the acceptance baseline over the unmodified copy expects exactly that
violation: `Editor.Test.Shell is outside the import closure of Editor.Core`,
with the module's file. The fix rule 2 prescribes ("Import a new core
module from the root in the change that adds it") is editor-project's to
make; the script no longer applies it to its copy, so the rule is seen to
bite. The `lean/` policy does not state the rule: over `lean/` alone no
module imports `Editor.Test.Shell`, so it is not loaded and the rule would
hold vacuously there.

**The generated roots are declared roots.** The package-set build writes
two root modules, `EditorSetRoot` and `EditorSetFixtures`, into
`packages/.lake/build/root/` from a facet (`setRoot`, `fixturesRoot`, and
`generatedLib` with `roots := #[]`). No `lean_lib` or `lean_exe` declares
them, and their files exist only after a build. The policy declares both
with `[[root]]` tables (README, "Declared roots"), each a module name and
its path relative to the workspace directory, `packages/`:

```toml
[[root]]
module = "EditorSetRoot"
path = ".lake/build/root/EditorSetRoot.lean"
```

lean-deny reads each file's header as Lake reads any module's, so both roots
are nodes of the graph with the imports their files hold, and no import is
listed by hand. lean-deny never generates them: `acceptance.sh` does, in its
copy, right after copying (`lake -d packages query :editorRoot` writes
`EditorSetRoot.lean`; `lake -d packages build --no-build :editorFixtures`
writes `EditorSetFixtures.lean` from the facet's own code, then fails by
design, since `--no-build` refuses the link). A missing file is an error
that says to build first. Their text is fixed by `rootSource` and
`fixturesRootSource` in `lean/lakefile.lean`: `import Editor`, `import
Editor.Main` (or `Editor.Test.Fixture.Main`), then one import per entry
module `<P>.EditorPackage`, 25 at `acfed133`; the fixture harness's root
then imports each fixture support module `<P>Test.FixtureSupport` the
set's packages declare, one at `acfed133` (`WorkspaceTest.FixtureSupport`).
So the host's modules are the closure of `Editor`, `Editor.Main` and
`Editor.Test.Fixture.Main`, all in `editor-core`, and the entry modules
each import only their own package's `<P>.Compiled` (and `Evil.Theorems`;
`ShippedThemes.EditorPackage` imports its library root `ShippedThemes`).
The policy derives the four host sets from the roots' imports with
`imports:` selectors (README, "Selectors"), so none is listed by hand:

```toml
entry-modules = { select = ["imports:mod:EditorSetRoot!"], except = ["mod:Editor"] }
fixture-support = { select = ["imports:mod:EditorSetFixtures!"], except = ["set:entry-modules", "mod:Editor"] }
host-roots = { select = ["imports:mod:EditorSetRoot!", "imports:mod:EditorSetFixtures!"], except = ["set:entry-modules", "set:fixture-support"] }
feature-modules = ["set:entry-modules", "imports:set:entry-modules"]
```

At editor-project `acfed133` that gives 25 entry modules (the 24 the policy
once listed by hand and `ShippedThemes.EditorPackage`, which it lacked), 1
fixture support module, the 3 host roots, and 51 feature modules: the 25
entry modules and their 26 direct imports (the 24 `<P>.Compiled`,
`Evil.Theorems` and `ShippedThemes`), checked with `explain`. A package
added to the generated roots, or a fixture support module added to the
harness's, is covered without editing the policy.

**A core-to-package import is visible.** In the `packages/` workspace Lake
resolves imports across the whole workspace, so `import Compile.Compiled` in
`lean/Editor/Main.lean` is an edge of the graph, and deny rule 1, the host
rule and `[layers]` all see it. (Lake itself refuses that import when the
core builds alone in `lean/`.)

**The module map is outside both workspaces.** The two doc rules read
`docs/design/packages.md`, which is in neither `lean/` nor `packages/`.
lean-deny reads a doc rule's `file` relative to the workspace directory
(only an absolute path is refused), so from `packages/` the policy writes
`file = "../docs/design/packages.md"`, and the violation lines print that
path as written (`../docs/design/packages.md:3313: …`). That is why the
script archives that one file beside `lean/` and `packages/`.

**Paths outside the workspace directory print absolute.** The workspace is
`packages/` and the core is `../lean`, outside it. lean-deny prints a path
outside the workspace directory as it is, so every chain step in the core
prints as `/…/lean/Editor/Main.lean:1`, while a package's step prints as
`compile/Compile.lean:1`. The script writes the work directory as `<work>`,
so the outputs below read `<work>/edit/lean/…` (task
`relative-paths-outside-root`).

## The policy

The policy keeps the scripts' rule order, so the labels are stable; the two
host rules the script lacked are inserted right after deny rule 4, so that
no other label moved:

| Label | Script rule |
|---|---|
| deny rule 1 | core imports, rule 1 |
| deny rule 2 | core imports, rule 4 |
| deny rule 3 | core imports, rule 5 |
| deny rule 4 | host imports (`structure.md` "Host imports", bullet 1) |
| deny rule 5 | `structure.md` "Host imports", bullet 2: an entry module imports package modules and nothing else |
| deny rule 6 | `structure.md` "Host imports", bullet 3: only the fixture harness's root imports a fixture support module |
| allow-only rules 1 to 4 | package imports: library, tests, linked test, linked test's root |
| `layers` | layer imports |
| reachable rule 1 | core imports, rule 2 |
| co-reach rule 1 | core imports, rule 3 |
| target-config rule 1 | lint plugins (`.agents/rules/structure.md`, "Lint plugins") |
| require-backed rule 1 | `structure.md` "Leave-out", with `layers` |
| doc-modules rule 1 | `structure.md` "Module map", bullet 2: "The core's modules" |
| doc-packages rule 1 | `structure.md` "Module map", bullet 3: "The packages", columns 1 to 3 |

The three Leave-out and Module map rules come after the earlier kinds, so
no earlier label moved.

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

**Patterns are enumerated as of `4df216a8`** (and still complete at
`acfed133`, counted over the graph). lean-deny has no glob selector
(task `glob-selector`), so the script's patterns become lists:
`Editor.*.Model` and the modules under one become 14 prefix selectors,
`Editor.*Contract` 21 modules, `Editor.*.Cases` 3, `Editor.*.Real` 13,
`<P>Test` 43 prefixes, `<P>Test.Linked` 13 prefixes (`VcApiTest.Linked`,
which has submodules only, included), its root 12 modules, and
and that is all (the entry modules, `*.EditorPackage`, are derived from the
generated roots instead). These fail open: a new `Editor.Foo.Model` is in no
list, so it falls into `api`, and a package's library may import it.

**Names that match nothing cannot be written.** The script reserves
`Editor.Internal…`, `Editor.*.Kit` and the core's `*ApiTest.Linked…`, and
none has a module today. A selector that matches nothing is an error, so the
policy leaves them out, and the first module under one would fall into
`api` (task `reserved-namespace-selector`).

**The host.** `structure.md` ("Host imports") calls host modules what the
generated roots import "apart from the entry modules (`….EditorPackage`)
and the fixture support modules (`<P>Test.FixtureSupport`)", and a feature
module "an entry module or a module an entry module imports directly". Four
sets state that, all derived with `imports:` (see "The host check and
selectors"):

- `set:entry-modules`: the editor's root's (`EditorSetRoot`) imports but the
  core's. That root imports no fixture support module, so none can count as
  an entry module.
- `set:fixture-support`: the fixture harness's root's (`EditorSetFixtures`)
  imports but the entry modules and the core's.
- `set:host-roots`: both roots' imports but the entry and fixture support
  modules (`Editor`, `Editor.Main`, `Editor.Test.Fixture.Main`).
- `set:feature-modules`: the entry modules and their direct imports.

Deny rule 4 (bullet 1) forbids the host roots from reaching a feature
module. Deny rule 5 (bullet 2) forbids an entry module from importing
anything but a package module. It is a `deny` of `pkg:editor-core` and the
toolchain (`Std`, `Lean`, `Lake`; Lean's implicit `Init` is no import line),
not an `allow-only` with `allow = "set:packages"`: no entry module imports
another package at `acfed133`, so that `allow` would allow nothing, which
is an error (exit 2). Deny rule 6 (bullet 3) forbids `EditorSetRoot` from
reaching a fixture support module, transitively. The bullet says "only
the fixture harness's generated root imports it, never the editor's root";
this reads it as "of the two generated roots, only the fixture harness's",
with "never the editor's root" meaning "not linked into the editor". It is not "no other
module at all": editor-project's own model test
`WorkspaceTest.WorkspaceTest.FixtureSupport` imports
`WorkspaceTest.FixtureSupport`, and the module's docstring, written with
that test, says "only the fixture harness's root imports it". The bullet's
first half ("it may import what a test module may") is allow-only rule 2
already: `WorkspaceTest.FixtureSupport` is under `mod:WorkspaceTest`, in
`set:package-tests`.

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

**Core rule 3 lists its roots.** The rule is about every executable root of
the build, and lean-deny has no selector for executables, so co-reach rule
1's `roots` names them: the two generated roots (`EditorSetRoot`,
`EditorSetFixtures`), the core's `lean_exe` roots (`FfiTest`, `ConfigTest`,
`ModelTest`, `ContractTest`, `LintTest`), the package linked tests' roots
(`set:package-linked-roots`, linked with `editorLinked`) and the 43 packages'
model-test `lean_exe` roots (`<P>Test.Model`): 62 roots at `0e608324` and
at `acfed133`. A
library root is not an executable: `Editor.Core` reaches
`Editor.Config.Elaborate` without `Editor`, and selecting it would be a false
violation. The list is inline in the rule rather than a new set, so no other
rule's line moves. At `0e608324` and at `acfed133` (counted over the
`graph --format json` output) 10 of the 62 reach the elaborator
(`EditorSetRoot`, `EditorSetFixtures`, `FfiTest`, `ConfigTest`, and the
linked roots of `compile`, `evil`, `ex`, `files`, `themes` and `workspace`),
and every one reaches `Editor`, so the rule holds; `EditorSetRoot`'s witness
is `EditorSetRoot` → `Editor.Main` → `Editor.Headless` →
`Editor.Config.Elaborate`. A new executable root is outside the rule until
it is listed.

**Lint plugins.** `.agents/rules/structure.md` ("Lint plugins") says every
`lean_lib` and `lean_exe` of the core and of every package loads the
build's linters as a plugin (`plugins`, the core's `lintPlugin`), or imports
the core's `Lint`; `docs/packages/word-count`, a package written as a
user's, is exempt. Target-config rule 1 says it: `load-plugin =
"@editor-core/lintShared"`, `or-imports = "lib:editor-core/Lint"`, over the
core and the 43 packages of the set, listed by `pkg:` (`targets` takes only
`pkg:` and `lib:`, and there is no "every package" selector, task
`workspace-selector`). A target's plugins are the ones Lake applies: the
package's `plugins` then the target's own. That matters, since every TOML
package sets `plugins = ["@editor-core/lintShared"]` at package level, while
the core's `lakefile.lean` writes `plugins := lintPlugin` per target. At
`0e608324` and at `acfed133` the rule checks 146 targets (the core's 12 libraries and 5
executables, and 2 libraries and 1 executable per package): 14 of the
core's load the plugin themselves, every package target loads it through
its package, and the core's `Lint`, `LintTests` and `lint-test` load none
but import `Lint`'s modules, `lint-test`'s root only through
`LintTest.Lint.*`, which is why `or-imports` counts indirect imports.
`word-count` is not in the `packages/` workspace, and `agents-api` and
`acp` are not in the default set, so none of the three is checked.

**Leave-out.** `structure.md` ("Leave-out") says every implementation
package can be dropped from a set's `[[require]]`s and the set still
builds, and that it follows from the three-layer rule. Its check by hand
is a `lake update` and a build; the policy states it statically, from the
graph: `layers` (no package imports an implementation package) and
require-backed rule 1 over `set:packages`, every cross-package import of a
default-set package backed by a direct `[[require]]` of the importing
package. Together they mean no package reaches what it imports only
through an implementation package another set could drop. The core is
left out: it requires nothing and imports no package (deny rule 1).

**Module map.** `structure.md` ("Module map") asks that "The core's
modules" in `docs/design/packages.md` name every `Editor.…` module and no
others (doc-modules rule 1: `prefix = "Editor."`, `modules =
"set:core-modules"`, the modules under `lean/Editor/`, 283 at `1101b206`,
equal to `find lean/Editor -name '*.lean' | wc -l` in the copy and to the
sum of the table's counts), and that each package of the default set have
a row with its layer, registrations and reads (doc-packages rule 1 over
"The packages": a row for each of `set:packages`'s 43 packages, its
`Layer` cell equal to the layer `[layers]` gives it, and its `Requires,
beside the core` cell equal to its direct requires but `editor-core`). The
core's `lean-deny.core.toml` has no doc rule: over `lean/` alone
`Editor.Test.Shell` is not loaded, so doc-modules would report it as a
name the table has and the workspace lacks.

## Rule by rule

| Script | Rule (the script's numbering) | lean-deny rule | Fidelity |
|---|---|---|---|
| core imports | 1: the root reaches no moving module | deny rule 1 | The standing form, "the core imports no package", transitive. The moving form is a second `deny` per moving feature, as above. |
| core imports | 2: every `Editor.…` module the build reaches is in the root's closure | reachable rule 1 | `from = "mod:Editor.Core!"`, `must-cover = "set:core-modules"` (`mod:Editor` except the config base `Editor`, which `Editor.Core` does not import and the script's `Editor.*` did not match). The build's reach is the loaded graph: the libraries' modules, the executables' roots (the packages' tests among them), the declared roots and the modules phase 1 loads, so the packages' tests count, which the script's roots missed. Broken at `4df216a8`, `0e608324` and `acfed133` (`Editor.Test.Shell`), which the baseline reports. |
| core imports | 3: a root that reaches the elaborator adapter reaches the config base | co-reach rule 1 | Exact, over the listed executable roots (see "Core rule 3 lists its roots"): `if-reaches = "mod:Editor.Config.Elaborate!"`, `must-reach = "mod:Editor!"`, closures reflexive and through every import kind. The generated roots are among them, as declared roots. Holds at `0e608324` and `acfed133`. |
| core imports | 4: the config base and `ModelTest` are plain Lean | deny rule 2 (core policy: 1) | The same semantics as the script: both see the direct imports of `Lean`/`Lake` (or a module under either) by the modules in the closure. Both share the limit that task `external-transitive-reach` describes: an import of an external module that itself reaches Lean's frontend is not seen. |
| core imports | 5: `ModelTest` reaches no `Editor.Ffi` module | deny rule 3 (core policy: 2) | Exact. |
| package imports | library: the core's API alone | allow-only rule 1 | The tiers and allowances equal the script's kinds and lists as of `4df216a8`. Patterns enumerated (task `glob-selector`); "every package" enumerated (task `workspace-selector`); `Editor.Internal…`, `Editor.*.Kit` and the core's `*ApiTest.Linked…` left out (task `reserved-namespace-selector`). |
| package imports | test: also the test doubles | allow-only rule 2 | As above. The more specific rule governs a test module, so the library rule does not also judge it. |
| package imports | linked test: also the linked test kit | allow-only rule 3 | As above. |
| package imports | linked test's root: also the real bindings, the headless host and the config base | allow-only rule 4 | As above. `Editor.Window.Real` and `Editor.WindowCheck.Real` are excepted from the root's extras, as in the script. |
| host imports | the host's modules reach no feature module | deny rule 4 | Exact, for `structure.md`'s bullet 1 at `acfed133`. The generated roots are in the graph (declared roots); the entry modules are the editor's root's imports outside `Editor`, the fixture support modules the fixture harness's root's other imports outside `Editor`, the host roots both roots' remaining imports, and the feature modules the entry modules and their direct imports, all derived with `imports:`. |
| host imports (`structure.md` only) | an entry module imports package modules and nothing else | deny rule 5 | Exact: an entry module may import no module of `editor-core` and nothing under `Std`, `Lean` or `Lake`. The script had no such check. |
| host imports (`structure.md` only) | only the fixture harness's root imports a fixture support module, never the editor's root | deny rule 6 | `EditorSetRoot` reaches no fixture support module, transitively; read as "of the two generated roots" (see "The host"). A fixture support module the editor's root imported directly would count as an entry module instead: see "Gaps". Its first half, "it may import what a test module may", is allow-only rule 2. |
| layer imports | the core imports no package | `layers` | Exact. |
| layer imports | no package imports an implementation package | `layers` | Exact: `implementation` is the default layer, so a misspelt keyword makes a package more refused, never less, as in the script. |
| layer imports | an import within one package is allowed | `layers` | `same-package = "allow"`. |
| layer imports | everything else is allowed | `layers` | The four pairs, interface → interface included: two such imports exist at `4df216a8`. |
| Leave-out (`structure.md` only) | every implementation package can be dropped from a set's requires and the set still builds | `layers` + require-backed rule 1 | Static, from the graph, as `structure.md` says it follows from the three layers: no `lake update` or build. Every import kind and every module of a package (its tests included) counts. `set:packages` is enumerated (task `workspace-selector`). Holds at `1101b206`. |
| Module map (`structure.md` only) | bullet 2: "The core's modules" names every `Editor.…` module and no others | doc-modules rule 1 | Exact: 283 modules at `1101b206`. Holds at `1101b206`. |
| Module map (`structure.md` only) | bullet 3: each default-set package has a row with its layer, registrations and reads | doc-packages rule 1 | Columns 1 to 3: the package, its layer as `[layers]` puts it, its requires beside `editor-core`. Columns 4 and 5 (registrations and reads) are not checked: they need elaborated Lean, a non-goal of the roadmap. The section's second table (`agents-api`, `acp`) is not read: the rule reads the first table with the three columns, and `structure.md` asks only for the default set's rows. Holds at `1101b206`. |
| lint plugins | every `lean_lib` and `lean_exe` of the core and of every package loads the lint plugin or imports `Lint` | target-config rule 1 | Exact for `plugins`: each target's effective plugins, its package's included, as Lake applies them; `or-imports` read directly or not (`lint-test`'s root imports `Lint` only through `LintTest.Lint.*`). A plugin given as a facet key (`@editor-core/Lint:shared`) or through `moreLeanArgs` (`--plugin`) is not seen; editor-project uses neither. The packages are enumerated (task `workspace-selector`). `word-count` is not in the workspace; `agents-api` and `acp` are not in the default set. Holds at `0e608324` and `acfed133`. |

The scripts exited 2 when a rule would hold of nothing, so that they could
not pass by checking nothing. lean-deny's errors (exit 2) do the same work:

| Script guard (exit 2) | lean-deny |
|---|---|
| Lake answers nothing for a root; a list or root that fell behind the build | Every selector must match a module of the workspace: a renamed module is an error, not a rule that holds. |
| No root of the build reaches the elaborator adapter (core rule 3) | A co-reach rule none of whose roots reaches an `if-reaches` module is an error: `co-reach rule 1: no module of 'roots' reaches a module of 'if-reaches', so the rule holds of nothing`. |
| The package check has no line to check | Every `allow` selector must allow something: some module the rule governs imports a module it matches from outside its own package. An allow-only rule must govern some module. |
| The layer check has no line with a core module as importer | Every `allow` pair must allow an import, and the default layer must hold a package. |
| The host check finds no list module among the root's imports | Every selector of deny rules 4 to 6 must match, and a derived set its `except` empties is an error. |

## Section by section

Every in-scope section of editor-project's `.agents/rules/structure.md`,
each of its bullets, the rule or rules that state it, and the breaking edit
or edits that bite each (the edit ids are those of "The runs"; "+" marks a
rule that bites beside the main one).

| Section | Bullet | Rule(s) | Breaking edit(s) |
|---|---|---|---|
| Core imports | 1: every `Editor.…` module the build reaches is in `Editor.Core`'s closure | reachable rule 1 | `core-2`, and the baseline's finding, `Editor.Test.Shell` |
| Core imports | 2: the core imports no package | deny rule 1 (+ `layers`) | `core-1` (also `host`, `host-shipped-themes`) |
| Core imports | 3: a root that reaches the config elaborator reaches the config base | co-reach rule 1 | `core-3` |
| Core imports | 4: the config base and `ModelTest` are plain Lean | deny rule 2; core policy deny rule 1 | `core-4`; `core-4-lean` |
| Core imports | 5: `ModelTest` reaches no raw binding (`Editor.Ffi`) | deny rule 3; core policy deny rule 2 | `core-5`; `core-5-lean` |
| Host imports | 1: the host's modules import no feature module | deny rule 4 | `host`, `host-shipped-themes`, `host-entry-core` |
| Host imports | 2: the host names no package; an entry module imports package modules and nothing else | deny rule 4, deny rule 5 | `host-entry-lean` (deny rule 5), `host-entry-core` (both) |
| Host imports | 3: a fixture support module is a test module, imported only by the fixture harness's root | allow-only rule 2, deny rule 6 | `fixture-support-test` (allow-only rule 2), `host-fixture-support` (deny rule 6) |
| What a package may import | the four tiers: library, tests, linked test, linked test's root | allow-only rules 1 to 4 | `package-library`, `package-library-double` (1); `package-test`, `fixture-support-test` (2); `package-linked` (3); `package-linked-root`, `package-linked-root-window`, `package-linked-root-window-check` (4); the controls `control-test-double`, `control-test-fake`, `control-linked-root-real` hold |
| Three layers | core, interface, implementation | `layers` | `layers` (also `core-1`, `host`, `host-shipped-themes`) |
| Lint plugins | every `lean_lib` and `lean_exe` loads the lint plugin or imports `Lint` | target-config rule 1 | `lint-plugin-package`, `lint-plugin-core` |
| Leave-out | every implementation package can be dropped from a set's requires | `layers`, require-backed rule 1 | `require-backed`; `layers` bites both |
| Module map | 1: update the map in the same change | what bullets 2 and 3 check | (bullets 2 and 3) |
| Module map | 2: "The core's modules" names every `Editor.…` module and no others | doc-modules rule 1 | `doc-modules` |
| Module map | 3: each default-set package has a row with its layer (columns 1 to 3) | doc-packages rule 1 | `doc-packages` |

Every one of the seventeen rules of the `packages/` policy, and both of the
core policy, has an edit that adds a violation of it beyond the baseline's.

## The host check and selectors

Can selectors express "the root's imports other than the `*.EditorPackage`
modules"? Yes. Three things stood in the way:

1. The root was in no graph: the package-set build generates it, and no Lake
   target declares it. It is now, as a declared root (`[[root]]`).
2. Nothing derived a set from the graph's edges. `imports:<selector>` does
   now: `imports:mod:EditorSetRoot!` is the root's imports, and
   `imports:set:entry-modules` the modules the entry modules import directly.
3. `*.EditorPackage` is a pattern (task `glob-selector`). It is no longer
   needed: the editor's root imports exactly `Editor`, the host's main
   module and the entry modules, so `except = ["mod:Editor"]` leaves the
   entry modules. The fixture harness's root also imports the fixture
   support modules after them, so the entry modules come from
   `EditorSetRoot` alone, and the fixture support modules are what
   `EditorSetFixtures` imports beyond them and the core's.

So the policy derives `set:entry-modules`, `set:fixture-support`,
`set:host-roots` and `set:feature-modules` from the roots. It bites, as the
`host` edit shows, and the `host-shipped-themes` edit (`Editor.Main`
importing `ShippedThemes.EditorPackage`, the entry module the old
hand-written list lacked) bites deny rule 4 too. A new package's entry
module is in the rule as soon as the generated roots import it.

**The drift at `acfed133`, and why it was the policy's.** Until this
revision the policy derived `entry-modules` as every import of either root
but the core's (`root-imports = ["imports:mod:EditorSetRoot!",
"imports:mod:EditorSetFixtures!"]`, `except = ["mod:Editor"]`). Run at
`acfed133`, that policy gave deny rule 4 three times in the baseline:
`Editor` reaching `Editor.Completion.Filtering`, `Editor.Main` reaching
`Editor.Process.Model`, and `Editor.Test.Fixture.Main` reaching
`Editor.Test.Fixture.Support`. "Host imports" did not change between
`0e608324` and `acfed133` (`git diff 0e608324 acfed133 --
.agents/rules/structure.md` touches only "The wiring set's runs"); its
fixture support wording came at `5c64af98`, an ancestor of `0e608324`. The
tree changed: `acfed133` added the default set's first fixture support
module, `packages/workspace/WorkspaceTest/FixtureSupport.lean`, which
`EditorSetFixtures` imports last, and whose first three imports are those
three core modules. No entry module imports a core module (none of the 25
`….EditorPackage` files has an `import Editor…` line). The old derivation
counted `WorkspaceTest.FixtureSupport` as an entry module, so its direct
imports became feature modules. By the rule's text it is a fixture support
module, which the host modules leave out, and the three core modules are
imported directly by no entry module, so they are no feature modules and
the host may reach them. All three hits were the policy's error, not
editor-project findings; the restated sets above give the baseline's one
violation again. The fixtures guard it: over `editor-ws`, whose fixture
harness root imports `CompileTest.FixtureSupport` (which imports
`Editor.Api`, a core module the host reaches), the old derivation gives
deny rule 4 twice.

**An entry module that imports a core module.** Should one, that module is
a feature module by the literal definition ("a module an entry module
imports directly", core or not), so a host module reaching it breaks bullet
1 (deny rule 4), and bullet 2 forbids the import itself (deny rule 5): the
core is no package. The two agree, and the `host-entry-core` edit shows
both biting. It does not arise at `acfed133`.

## The runs

The run, at the root of lean-deny's repository:

```sh
lake build
examples/editor-project/acceptance.sh /path/to/editor-project /path/to/work-dir
```

The script reads editor-project's HEAD with `git --no-optional-locks
rev-parse --verify HEAD` (it needs a git checkout, else it exits 2),
prints it as `editor-project: <sha>`, and extracts that one revision's
`lean/`, `packages/` and `docs/design/packages.md` with `git
--no-optional-locks archive <sha> lean packages docs/design/packages.md |
tar -x` into `<work dir>/pristine`: committed files only, so
nothing uncommitted or untracked, and no `.lake/` or `target/`, and a HEAD
that moves meanwhile cannot split the run. It then checks that both
lakefiles and the module map arrived (POSIX `sh` has no `pipefail`). It never points
lean-deny, or any command that writes, at editor-project itself. It generates
the two declared roots in the copy (see "Loading editor-project"; a root
that is not written is a `MISMATCH`), and every edit's copy carries them. It
prints the as-is load (its exit is printed, not asserted), checks both
baselines (the `packages/` one expecting exactly reachable rule 1's
`Editor.Test.Shell` violation and its module line, so no co-reach,
require-backed, doc-modules or doc-packages violation), then, for each edit, starts from a fresh copy of the
pristine tree, prepends one `import` line to one file, and runs `check`;
then, for each sed edit, starts again from a fresh copy, applies one
`sed` script to one file (a lakefile, the core's root, or the module map),
and runs `check` (an edit whose file is gone,
or whose script changes nothing, is a `MISMATCH`); then, for the
new-module edit, starts again from a fresh copy, creates one empty module
file and prepends an import of it to one file, and runs `check` (a module
file that already exists is a `MISMATCH`, so the edit cannot add nothing). For
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
expectation failed`, and exits 1. A file in the edit table that is gone
prints `MISMATCH: <file> is not in editor-project any more; update the edit
table in acceptance.sh`, and that edit is skipped. A module the policy names
that is gone makes each check print lean-deny's located error and `exit 2`,
then `MISMATCH: expected exit 0` (or `1`). Once editor-project's
`Editor.Core` imports `Editor.Test.Shell`, every `packages/` run prints one
violation fewer and mismatches; then drop `reachable rule 1` from the
baseline and the edit table (`core-2` keeps it, with one violation). Then update
the edit table in the script, or the enumerations in the policy, and the
revision at the top of this page.

The edits. Every `packages/` run also reports the baseline's violation,
reachable rule 1 (`Editor.Test.Shell`), which the script expects and the
table leaves out; a control edit's exit is 1 for that violation alone.

| id | Breaks | File (in the copy) | Added import | Exit | Rules that bite (beyond the baseline's) |
|---|---|---|---|---|---|
| core-1 | core 1: the core imports no package | `lean/ModelTest/Editor/Bound.lean` | `CompileApi` | 1 | deny rule 1 ×2, `layers` |
| core-3 | core 3: a root that reaches the elaborator reaches the base | `lean/ContractTest.lean` | `Editor.Config.Elaborate` | 1 | co-reach rule 1 |
| core-4 | core 4: the base and `ModelTest` are plain Lean | `lean/Editor/Bound.lean` | `Lean.Data.Json` | 1 | deny rule 2 ×2 |
| core-4-lean | the same, over `lean/` with the core policy | `lean/Editor/Bound.lean` | `Lean.Data.Json` | 1 | deny rule 1 ×2 |
| core-5 | core 5: `ModelTest` reaches no `Editor.Ffi` | `lean/ModelTest/Editor/Bound.lean` | `Editor.Ffi.Text` | 1 | deny rule 3 |
| core-5-lean | the same, over `lean/` with the core policy | `lean/ModelTest/Editor/Bound.lean` | `Editor.Ffi.Text` | 1 | deny rule 2 |
| host | host: the host reaches no feature module | `lean/Editor/Main.lean` | `Compile.Compiled` | 1 | deny rule 4, deny rule 1 ×2, `layers` |
| host-shipped-themes | host: the host reaches no entry module, derived from the generated roots | `lean/Editor/Main.lean` | `ShippedThemes.EditorPackage` | 1 | deny rule 4, deny rule 1 ×2, `layers` |
| host-entry-core | host 1 and 2: an entry module imports a core module, which so becomes a feature module the host reaches | `packages/compile/Compile/EditorPackage.lean` | `Editor.Text` | 1 | deny rule 4 ×3 (from `Editor`, `Editor.Main`, `Editor.Test.Fixture.Main`), deny rule 5 |
| host-entry-lean | host 2: an entry module imports package modules and nothing else | `packages/compile/Compile/EditorPackage.lean` | `Lean.Data.Json` | 1 | deny rule 5 |
| host-fixture-support | host 3: the editor's root never imports a fixture support module | `packages/workspace/Workspace/Compiled.lean` | `WorkspaceTest.FixtureSupport` | 1 | deny rule 6 |
| fixture-support-test | host 3: a fixture support module may import what a test module may, no more | `packages/workspace/WorkspaceTest/FixtureSupport.lean` | `Editor.Test.Linked.Rig` | 1 | allow-only rule 2 |
| package-library | package: a library imports the API alone | `packages/compile/Compile.lean` | `Editor.Loop` | 1 | allow-only rule 1 |
| package-library-double | package: a library may not import a test double | `packages/compile/Compile.lean` | `Editor.Text.Model` | 1 | allow-only rule 1 |
| package-test | package: a test may import the doubles, not the linked kit | `packages/compile/CompileTest/Compile.lean` | `Editor.Test.Linked.Rig` | 1 | allow-only rule 2 |
| package-linked | package: a linked-test module gets the linked kit, not the root's extras | `packages/compile/CompileTest/Linked/Compile.lean` | `Editor.Headless` | 1 | allow-only rule 3 |
| package-linked-root | package: even the linked root may not import a raw binding | `packages/compile/CompileTest/Linked.lean` | `Editor.Ffi.Text` | 1 | allow-only rule 4 |
| package-linked-root-window | package: the linked root may not import the window binding, excepted from its extras | `packages/compile/CompileTest/Linked.lean` | `Editor.Window.Real` | 1 | allow-only rule 4 |
| package-linked-root-window-check | the same, for the window check's binding | `packages/compile/CompileTest/Linked.lean` | `Editor.WindowCheck.Real` | 1 | allow-only rule 4 |
| layers | layers: no package imports an implementation package | `packages/compile/Compile.lean` | `Shell` | 1 | `layers`, require-backed rule 1 |
| require-backed | Leave-out: a package imports an interface package it reaches only transitively | `packages/version-control/VersionControl/Log.lean` | `CompileApi` | 1 | require-backed rule 1 (`version-control` requires `project-api`, which requires `compile-api`) |
| control-test-double | control: a test may import a double | `packages/compile/CompileTest/Compile.lean` | `Editor.Text.Model` | 1 | none |
| control-test-fake | control: a test may import a fake | `packages/compile/CompileTest/Compile.lean` | `Editor.Job.Fake` | 1 | none |
| control-linked-root-real | control: the linked root may import a real binding | `packages/compile/CompileTest/Linked.lean` | `Editor.Text.Real` | 1 | none |

The sed edits each remove or change one line (exit 1, beyond the
baseline's violation): the two lint edits each drop one plugin, and
`core-2` drops one import from the core's root. Reachable rule 1's only
violation at HEAD is the baseline's, so `core-2` is its breaking edit.

| id | Breaks | File (in the copy) | sed script | Rules that bite (beyond the baseline's) |
|---|---|---|---|---|
| lint-plugin-package | lint plugins, through a package-level `plugins` (TOML) | `packages/compile/lakefile.toml` | `/^plugins = \["@editor-core\/lintShared"\]$/d` | target-config rule 1 ×3 (`Compile`, `CompileTest`, `compile-test`) |
| lint-plugin-core | lint plugins, through a target's `plugins` (Lean DSL) | `lean/lakefile.lean` | `s/^lean_lib ExtensionFixture where plugins := lintPlugin$/lean_lib ExtensionFixture/` | target-config rule 1 (`ExtensionFixture`, which imports only `Editor.…` modules) |
| core-2 | core 2: import a new core module from the root | `lean/Editor/Core.lean` | `/^import Editor\.Test\.Linked\.Frames$/d` | reachable rule 1 (`Editor.Test.Linked.Frames`, still imported by `ThemesTest.Linked.Themes`), 2 violations against the baseline's 1 |
| doc-packages | Module map 3: a package's row gives its layer | `docs/design/packages.md` | `/^. .shell-api. /s/ interface / implementation /` (the table is `\|`-delimited, so `.` stands for `\|` and the backticks) | doc-packages rule 1 (`shell-api`'s row, line 3423) |

The new-module edit adds an empty module file and prepends an import of it
to one file (exit 1, beyond the baseline's violation):

| id | Breaks | New file (in the copy) | Importing file | New module | Rules that bite (beyond the baseline's) |
|---|---|---|---|---|---|
| doc-modules | Module map 2: "The core's modules" names every `Editor.…` module | `lean/Editor/Unlisted.lean` (empty) | `lean/Editor/Core.lean`, so reachable rule 1 stays at the baseline's | `Editor.Unlisted` | doc-modules rule 1 |

Every edit that breaks one script rule bites only that rule's lean-deny
rule, except where the edit necessarily breaks more: `core-1`, `host` and
`host-shipped-themes` add an import from the core to a package, which
`layers` refuses too; `layers` adds an import of an implementation
package, and no implementation package requires another, so
require-backed rule 1 bites too (Leave-out needs both rules, and any
`layers` edit of that shape breaks both); and the two host edits' import is in `Editor.Main`,
which `Editor.Core` reaches, so deny rule 1 bites as well; and
`host-entry-core` breaks host bullets 1 and 2 at once, by design (see "The
host check and selectors"). With the old
hand-written entry-module list, `host-shipped-themes` gave `3 violations in
2 of 9 rules` (before reachable rule 1): deny rule 4 missed it. The controls show the tiers are
precise, not just strict: `Editor.Text.Model` imported by `Compile.lean`, a library, bites
allow-only rule 1 (`package-library-double`), and imported by a test it
holds (`control-test-double`); and the linked root may import a real binding
(`control-linked-root-real`) though not a raw one (`package-linked-root`),
nor the two real bindings its extras except (`package-linked-root-window`,
`package-linked-root-window-check`). With that `except` removed from the
policy, both of those edits hold, so it is the `except` that bites.

The output of one real run follows, as the script printed it, block by
block. The work directory is written `<work>`; core paths print absolute
(see "Loading editor-project"), and the `lean/` runs print paths relative to
`lean/`. Every `packages/` run reports the baseline's reachable rule 1
violation, since no edit imports `Editor.Test.Shell`.

The run begins with the revision line, the HEAD the script read and
archived:

```
editor-project: 1101b2069f1e047544f4ecd2fecc6b04463d6fa3
```

### load the packages/ workspace as it is

editor-project as it is: lean-deny loads it (see "Loading editor-project"). This run reads no policy (the copy has no `lean-deny.toml`), so it has no declared roots.

```
== load the packages/ workspace as it is
exit 0
```

### baseline: packages/

The unmodified `packages/` breaks exactly one rule, once: reachable rule 1
reports `Editor.Test.Shell`, outside `Editor.Core`'s closure (editor-project's
core rule 2 finding). The script also asserts the module line. Co-reach rule
1 holds: every listed root that reaches the elaborator reaches the base.
Leave-out and the module map hold too: require-backed rule 1, doc-modules
rule 1 and doc-packages rule 1 report nothing at `1101b206`, so this run
adds no finding for editor-project's task `lean-structure-rules-tool`.

```
== baseline: packages/
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/pristine/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 1 violation in 1 of 17 rules
exit 1
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
deny rule 1 (examples/editor-project/lean-deny.toml:161:0): a package may depend on the core, and the core on no package (core imports check, rule 1)
  <work>/edit/lean/ModelTest.lean:16: ModelTest imports ModelTest.Editor.Bound
  <work>/edit/lean/ModelTest/Editor/Bound.lean:1: ModelTest.Editor.Bound imports CompileApi
deny rule 1 (examples/editor-project/lean-deny.toml:161:0): a package may depend on the core, and the core on no package (core imports check, rule 1)
  <work>/edit/lean/ModelTest/Editor/Bound.lean:1: ModelTest.Editor.Bound imports CompileApi
layers (examples/editor-project/lean-deny.toml:224:0): three layers (layer imports check): editor-core (core) may not import compile-api (interface)
  <work>/edit/lean/ModelTest/Editor/Bound.lean:1: ModelTest.Editor.Bound imports CompileApi
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 4 violations in 3 of 17 rules
exit 1
```

### core-3: lean/ContractTest.lean imports Editor.Config.Elaborate

The contract tests' root, an executable root that reaches neither the config elaborator nor the config base, imports the elaborator: core rule 3 wants the base linked too.

```
== core-3: lean/ContractTest.lean imports Editor.Config.Elaborate
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
co-reach rule 1 (examples/editor-project/lean-deny.toml:245:0): the elaborator imports the config base's modules at runtime, so every executable root that reaches it links the base (core imports check, rule 3): ContractTest reaches Editor.Config.Elaborate but not Editor
  <work>/edit/lean/ContractTest.lean:1: ContractTest imports Editor.Config.Elaborate
lean-deny: 2 violations in 2 of 17 rules
exit 1
```

### core-4: lean/Editor/Bound.lean imports Lean.Data.Json

The base's module `Editor.Bound`, which `Editor` and `ModelTest` both reach, imports a module under `Lean`.

```
== core-4: lean/Editor/Bound.lean imports Lean.Data.Json
deny rule 2 (examples/editor-project/lean-deny.toml:168:0): the config base and the model tests' root are plain Lean (core imports check, rule 4)
  <work>/edit/lean/Editor.lean:5: Editor imports Editor.Jumps.Go
  <work>/edit/lean/Editor/Jumps/Go.lean:2: Editor.Jumps.Go imports FilesApi
  <work>/edit/lean/FilesApi.lean:1: FilesApi imports Editor.Extension
  <work>/edit/lean/Editor/Extension.lean:2: Editor.Extension imports Editor.Setup
  <work>/edit/lean/Editor/Setup.lean:21: Editor.Setup imports Editor.Window
  <work>/edit/lean/Editor/Window.lean:1: Editor.Window imports Editor.Bound
  <work>/edit/lean/Editor/Bound.lean:1: Editor.Bound imports Lean.Data.Json
deny rule 2 (examples/editor-project/lean-deny.toml:168:0): the config base and the model tests' root are plain Lean (core imports check, rule 4)
  <work>/edit/lean/ModelTest.lean:16: ModelTest imports ModelTest.Editor.Bound
  <work>/edit/lean/ModelTest/Editor/Bound.lean:1: ModelTest.Editor.Bound imports Editor.Bound
  <work>/edit/lean/Editor/Bound.lean:1: Editor.Bound imports Lean.Data.Json
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 3 violations in 2 of 17 rules
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
deny rule 3 (examples/editor-project/lean-deny.toml:175:0): model-test links no Rust library (core imports check, rule 5)
  <work>/edit/lean/ModelTest.lean:16: ModelTest imports ModelTest.Editor.Bound
  <work>/edit/lean/ModelTest/Editor/Bound.lean:1: ModelTest.Editor.Bound imports Editor.Ffi.Text
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 2 violations in 2 of 17 rules
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
deny rule 1 (examples/editor-project/lean-deny.toml:161:0): a package may depend on the core, and the core on no package (core imports check, rule 1)
  <work>/edit/lean/Editor/Core.lean:23: Editor.Core imports Editor.Main
  <work>/edit/lean/Editor/Main.lean:1: Editor.Main imports Compile.Compiled
deny rule 1 (examples/editor-project/lean-deny.toml:161:0): a package may depend on the core, and the core on no package (core imports check, rule 1)
  <work>/edit/lean/Editor/Main.lean:1: Editor.Main imports Compile.Compiled
deny rule 4 (examples/editor-project/lean-deny.toml:182:0): the host is handed its packages as a value and names none of them (host imports check)
  <work>/edit/lean/Editor/Main.lean:1: Editor.Main imports Compile.Compiled
layers (examples/editor-project/lean-deny.toml:224:0): three layers (layer imports check): editor-core (core) may not import compile (implementation)
  <work>/edit/lean/Editor/Main.lean:1: Editor.Main imports Compile.Compiled
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 5 violations in 4 of 17 rules
exit 1
```

### host-shipped-themes: lean/Editor/Main.lean imports ShippedThemes.EditorPackage

A host module imports the entry module the old hand-written list lacked; the derived `set:feature-modules` has it, so deny rule 4 bites.

```
== host-shipped-themes: lean/Editor/Main.lean imports ShippedThemes.EditorPackage
deny rule 1 (examples/editor-project/lean-deny.toml:161:0): a package may depend on the core, and the core on no package (core imports check, rule 1)
  <work>/edit/lean/Editor/Core.lean:23: Editor.Core imports Editor.Main
  <work>/edit/lean/Editor/Main.lean:1: Editor.Main imports ShippedThemes.EditorPackage
deny rule 1 (examples/editor-project/lean-deny.toml:161:0): a package may depend on the core, and the core on no package (core imports check, rule 1)
  <work>/edit/lean/Editor/Main.lean:1: Editor.Main imports ShippedThemes.EditorPackage
deny rule 4 (examples/editor-project/lean-deny.toml:182:0): the host is handed its packages as a value and names none of them (host imports check)
  <work>/edit/lean/Editor/Main.lean:1: Editor.Main imports ShippedThemes.EditorPackage
layers (examples/editor-project/lean-deny.toml:224:0): three layers (layer imports check): editor-core (core) may not import shipped-themes (implementation)
  <work>/edit/lean/Editor/Main.lean:1: Editor.Main imports ShippedThemes.EditorPackage
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 5 violations in 4 of 17 rules
exit 1
```

### host-entry-core: packages/compile/Compile/EditorPackage.lean imports Editor.Text

An entry module imports a core module. Host imports bullet 2 forbids the
import itself (deny rule 5), and bullet 1 forbids the host from reaching
it, since a module an entry module imports directly is a feature module:
each of the three host roots reaches `Editor.Text` (deny rule 4, three
times).

```
== host-entry-core: packages/compile/Compile/EditorPackage.lean imports Editor.Text
deny rule 4 (examples/editor-project/lean-deny.toml:182:0): the host is handed its packages as a value and names none of them (host imports check)
  <work>/edit/lean/Editor.lean:7: Editor imports Editor.Text.Word
  <work>/edit/lean/Editor/Text/Word.lean:1: Editor.Text.Word imports Editor.Text
deny rule 4 (examples/editor-project/lean-deny.toml:182:0): the host is handed its packages as a value and names none of them (host imports check)
  <work>/edit/lean/Editor/Main.lean:1: Editor.Main imports Editor.Command.Append
  <work>/edit/lean/Editor/Command/Append.lean:1: Editor.Command.Append imports Editor.Text.Model
  <work>/edit/lean/Editor/Text/Model.lean:1: Editor.Text.Model imports Editor.Text
deny rule 4 (examples/editor-project/lean-deny.toml:182:0): the host is handed its packages as a value and names none of them (host imports check)
  <work>/edit/lean/Editor/Test/Fixture/Main.lean:1: Editor.Test.Fixture.Main imports Editor.InputScheme
  <work>/edit/lean/Editor/InputScheme.lean:5: Editor.InputScheme imports Editor.Scene
  <work>/edit/lean/Editor/Scene.lean:2: Editor.Scene imports Editor.Text
deny rule 5 (examples/editor-project/lean-deny.toml:190:0): an entry module imports package modules and nothing else (host imports)
  compile/Compile/EditorPackage.lean:1: Compile.EditorPackage imports Editor.Text
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 5 violations in 3 of 17 rules
exit 1
```

### host-entry-lean: packages/compile/Compile/EditorPackage.lean imports Lean.Data.Json

An entry module imports a toolchain module, which is no package module.

```
== host-entry-lean: packages/compile/Compile/EditorPackage.lean imports Lean.Data.Json
deny rule 5 (examples/editor-project/lean-deny.toml:190:0): an entry module imports package modules and nothing else (host imports)
  compile/Compile/EditorPackage.lean:1: Compile.EditorPackage imports Lean.Data.Json
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 2 violations in 2 of 17 rules
exit 1
```

### host-fixture-support: packages/workspace/Workspace/Compiled.lean imports WorkspaceTest.FixtureSupport

The workspace package's library imports its fixture support module, so the
editor's root links it (through the entry module `Workspace.EditorPackage`).

```
== host-fixture-support: packages/workspace/Workspace/Compiled.lean imports WorkspaceTest.FixtureSupport
deny rule 6 (examples/editor-project/lean-deny.toml:196:0): a fixture support module is a test module: the fixture harness's root imports it, never the editor's (host imports)
  .lake/build/root/EditorSetRoot.lean:14: EditorSetRoot imports Workspace.EditorPackage
  workspace/Workspace/EditorPackage.lean:1: Workspace.EditorPackage imports Workspace.Compiled
  workspace/Workspace/Compiled.lean:1: Workspace.Compiled imports WorkspaceTest.FixtureSupport
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 2 violations in 2 of 17 rules
exit 1
```

### fixture-support-test: packages/workspace/WorkspaceTest/FixtureSupport.lean imports Editor.Test.Linked.Rig

The fixture support module imports the linked test kit. "It may import what
a test module may", and a test module outside a linked test may not.

```
== fixture-support-test: packages/workspace/WorkspaceTest/FixtureSupport.lean imports Editor.Test.Linked.Rig
allow-only rule 2 (examples/editor-project/lean-deny.toml:208:0): a package's tests may also import the core's test doubles (package imports check)
  workspace/WorkspaceTest/FixtureSupport.lean:1: WorkspaceTest.FixtureSupport imports Editor.Test.Linked.Rig
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 2 violations in 2 of 17 rules
exit 1
```

### package-library: packages/compile/Compile.lean imports Editor.Loop

A package's library imports an internal module of the core (the loop).

```
== package-library: packages/compile/Compile.lean imports Editor.Loop
allow-only rule 1 (examples/editor-project/lean-deny.toml:203:0): a package's library imports the core's API alone (package imports check)
  compile/Compile.lean:1: Compile imports Editor.Loop
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 2 violations in 2 of 17 rules
exit 1
```

### package-library-double: packages/compile/Compile.lean imports Editor.Text.Model

A package's library imports a test double, which only its tests may.

```
== package-library-double: packages/compile/Compile.lean imports Editor.Text.Model
allow-only rule 1 (examples/editor-project/lean-deny.toml:203:0): a package's library imports the core's API alone (package imports check)
  compile/Compile.lean:1: Compile imports Editor.Text.Model
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 2 violations in 2 of 17 rules
exit 1
```

### package-test: packages/compile/CompileTest/Compile.lean imports Editor.Test.Linked.Rig

A package's test module, outside its linked test, imports the linked test kit.

```
== package-test: packages/compile/CompileTest/Compile.lean imports Editor.Test.Linked.Rig
allow-only rule 2 (examples/editor-project/lean-deny.toml:208:0): a package's tests may also import the core's test doubles (package imports check)
  compile/CompileTest/Compile.lean:1: CompileTest.Compile imports Editor.Test.Linked.Rig
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 2 violations in 2 of 17 rules
exit 1
```

### package-linked: packages/compile/CompileTest/Linked/Compile.lean imports Editor.Headless

A module under the linked test's root imports the headless host, which only the root may.

```
== package-linked: packages/compile/CompileTest/Linked/Compile.lean imports Editor.Headless
allow-only rule 3 (examples/editor-project/lean-deny.toml:213:0): a package's linked test may also import the linked test kit (package imports check)
  compile/CompileTest/Linked/Compile.lean:1: CompileTest.Linked.Compile imports Editor.Headless
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 2 violations in 2 of 17 rules
exit 1
```

### package-linked-root: packages/compile/CompileTest/Linked.lean imports Editor.Ffi.Text

The linked test's root imports a raw binding, which no module of a package may.

```
== package-linked-root: packages/compile/CompileTest/Linked.lean imports Editor.Ffi.Text
allow-only rule 4 (examples/editor-project/lean-deny.toml:218:0): a linked test's root may also import the real bindings, the headless host and the config base (package imports check)
  compile/CompileTest/Linked.lean:1: CompileTest.Linked imports Editor.Ffi.Text
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 2 violations in 2 of 17 rules
exit 1
```

### package-linked-root-window: packages/compile/CompileTest/Linked.lean imports Editor.Window.Real

The linked test's root imports the window binding, a real binding its extras except.

```
== package-linked-root-window: packages/compile/CompileTest/Linked.lean imports Editor.Window.Real
allow-only rule 4 (examples/editor-project/lean-deny.toml:218:0): a linked test's root may also import the real bindings, the headless host and the config base (package imports check)
  compile/CompileTest/Linked.lean:1: CompileTest.Linked imports Editor.Window.Real
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 2 violations in 2 of 17 rules
exit 1
```

### package-linked-root-window-check: packages/compile/CompileTest/Linked.lean imports Editor.WindowCheck.Real

The same, for the window check's binding.

```
== package-linked-root-window-check: packages/compile/CompileTest/Linked.lean imports Editor.WindowCheck.Real
allow-only rule 4 (examples/editor-project/lean-deny.toml:218:0): a linked test's root may also import the real bindings, the headless host and the config base (package imports check)
  compile/CompileTest/Linked.lean:1: CompileTest.Linked imports Editor.WindowCheck.Real
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 2 violations in 2 of 17 rules
exit 1
```

### layers: packages/compile/Compile.lean imports Shell

An implementation package imports another implementation package, which
it does not require: `layers` and require-backed rule 1 both bite.

```
== layers: packages/compile/Compile.lean imports Shell
layers (examples/editor-project/lean-deny.toml:224:0): three layers (layer imports check): compile (implementation) may not import shell (implementation)
  compile/Compile.lean:1: Compile imports Shell
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
require-backed rule 1 (examples/editor-project/lean-deny.toml:365:0): a set may drop any implementation package and still build: every package requires what it imports (leave-out): Compile (package compile) imports package shell, which compile does not require directly
  compile/Compile.lean:1: Compile imports Shell
  compile/lakefile.toml: compile requires minibuffer-api, compile-api, shell-api, editor-core
lean-deny: 3 violations in 3 of 17 rules
exit 1
```

### require-backed: packages/version-control/VersionControl/Log.lean imports CompileApi

A package imports an interface package it reaches only transitively:
`version-control` requires `project-api`, `vc-api`, `buffers-api` and
`editor-core`, and `project-api` requires `compile-api`. Nothing else
bites: `compile-api` is in `set:packages`, and `layers` allows an
interface import. The script also asserts the requires line and the
module and package named.

```
== require-backed: packages/version-control/VersionControl/Log.lean imports CompileApi
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
require-backed rule 1 (examples/editor-project/lean-deny.toml:365:0): a set may drop any implementation package and still build: every package requires what it imports (leave-out): VersionControl.Log (package version-control) imports package compile-api, which version-control does not require directly
  version-control/VersionControl/Log.lean:1: VersionControl.Log imports CompileApi
  version-control/lakefile.toml: version-control requires project-api, vc-api, buffers-api, editor-core
lean-deny: 2 violations in 2 of 17 rules
exit 1
```

### control-test-double: packages/compile/CompileTest/Compile.lean imports Editor.Text.Model

Control: a package's test imports a test double. Only the baseline's violation is reported.

```
== control-test-double: packages/compile/CompileTest/Compile.lean imports Editor.Text.Model
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 1 violation in 1 of 17 rules
exit 1
```

### control-test-fake: packages/compile/CompileTest/Compile.lean imports Editor.Job.Fake

Control: a package's test imports a fake. Only the baseline's violation is reported.

```
== control-test-fake: packages/compile/CompileTest/Compile.lean imports Editor.Job.Fake
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 1 violation in 1 of 17 rules
exit 1
```

### control-linked-root-real: packages/compile/CompileTest/Linked.lean imports Editor.Text.Real

Control: the linked test's root imports a real binding. Only the baseline's violation is reported.

```
== control-linked-root-real: packages/compile/CompileTest/Linked.lean imports Editor.Text.Real
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 1 violation in 1 of 17 rules
exit 1
```

### lint-plugin-package: packages/compile/lakefile.toml

The compile package's lakefile loses its package-level `plugins`: its two
libraries and its executable load no plugin, and none imports `Lint`.

```
== lint-plugin-package: packages/compile/lakefile.toml, sed '/^plugins = \["@editor-core\/lintShared"\]$/d'
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
target-config rule 1 (examples/editor-project/lean-deny.toml:310:0): a target that loads no plugin is never linted (lint plugins): lean_lib compile/Compile does not load @editor-core/lintShared and imports no module of lib:editor-core/Lint
  compile/lakefile.toml: lean_lib Compile
target-config rule 1 (examples/editor-project/lean-deny.toml:310:0): a target that loads no plugin is never linted (lint plugins): lean_lib compile/CompileTest does not load @editor-core/lintShared and imports no module of lib:editor-core/Lint
  compile/lakefile.toml: lean_lib CompileTest
target-config rule 1 (examples/editor-project/lean-deny.toml:310:0): a target that loads no plugin is never linted (lint plugins): lean_exe compile/compile-test does not load @editor-core/lintShared and imports no module of lib:editor-core/Lint
  compile/lakefile.toml: lean_exe compile-test
lean-deny: 4 violations in 2 of 17 rules
exit 1
```

### lint-plugin-core: lean/lakefile.lean

The core's `ExtensionFixture` library loses its `plugins := lintPlugin`.
Lake elaborates the edited `lakefile.lean`, and the library's plugins are
empty; it imports only `Editor.…` modules.

```
== lint-plugin-core: lean/lakefile.lean, sed 's/^lean_lib ExtensionFixture where plugins := lintPlugin$/lean_lib ExtensionFixture/'
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
target-config rule 1 (examples/editor-project/lean-deny.toml:310:0): a target that loads no plugin is never linted (lint plugins): lean_lib editor-core/ExtensionFixture does not load @editor-core/lintShared and imports no module of lib:editor-core/Lint
  <work>/edit/lean/lakefile.lean: lean_lib ExtensionFixture
lean-deny: 2 violations in 2 of 17 rules
exit 1
```

### core-2: lean/Editor/Core.lean

The core's root loses its import of `Editor.Test.Linked.Frames`, as if the
change that added the module had not imported it from the root. A
package's linked test (`ThemesTest.Linked.Themes`) still imports it, so the
build reaches it outside `Editor.Core`'s closure, beside the baseline's
`Editor.Test.Shell`. The script also asserts the module line.

```
== core-2: lean/Editor/Core.lean, sed '/^import Editor\.Test\.Linked\.Frames$/d'
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Linked.Frames is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Linked/Frames.lean: Editor.Test.Linked.Frames
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
lean-deny: 2 violations in 1 of 17 rules
exit 1
```

### doc-packages: docs/design/packages.md

The module map's row for `shell-api` (line 3423, in the first table of
"The packages") gets the layer `implementation`; its lakefile declares the
keyword `editor-interface`, so `[layers]` puts it in `interface`. The
script also asserts the text of the violation. The path prints as the
rule's `file` gives it, relative to `packages/`.

```
== doc-packages: docs/design/packages.md, sed '/^. .shell-api. /s/ interface / implementation /'
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
doc-packages rule 1 (examples/editor-project/lean-deny.toml:380:0): the module map has one row per default-set package, with its layer and what it requires beside the core (module map): section 'The packages' of ../docs/design/packages.md gives shell-api layer implementation, but [layers] puts it in interface
  ../docs/design/packages.md:3423: shell-api
lean-deny: 2 violations in 2 of 17 rules
exit 1
```

### doc-modules: lean/Editor/Core.lean imports Editor.Unlisted, a new lean/Editor/Unlisted.lean

A new, empty module `Editor.Unlisted` under `lean/Editor/`, imported from
the core's root so that the build loads it and reachable rule 1 stays at
the baseline's, and left out of "The core's modules". The script also
asserts the module line and the text of the violation.

```
== doc-modules: lean/Editor/Core.lean imports Editor.Unlisted, a new lean/Editor/Unlisted.lean
reachable rule 1 (examples/editor-project/lean-deny.toml:235:0): the core's root holds the whole core (core imports check, rule 2): Editor.Test.Shell is outside the import closure of Editor.Core
  <work>/edit/lean/Editor/Test/Shell.lean: Editor.Test.Shell
doc-modules rule 1 (examples/editor-project/lean-deny.toml:370:0): the module map names every module under lean/Editor/ and no other (module map): Editor.Unlisted is not listed in section 'The core's modules' of ../docs/design/packages.md
  <work>/edit/lean/Editor/Unlisted.lean: Editor.Unlisted
  ../docs/design/packages.md:3313: section 'The core's modules'
lean-deny: 2 violations in 2 of 17 rules
exit 1
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
  and `ModelTests`, and the executable `model-test` rooted at `ModelTest`,
  each loading `@editor-core/lintShared` as a plugin; and the linters, which
  load none: the library `Lint` (`Lint` imports `Lint.Wait`), the library
  `LintTests` (`LintTest.Wait` imports `Lint.Wait`) and the executable
  `lint-test` rooted at `LintTest`, which imports `LintTest.Wait`),
  two interface packages (`shell-api`, `compile-api`, the second importing
  the first) and three implementation packages (`shell`, `compile`, the
  latter with its tests, linked test and linked test's root, and
  `shipped-themes`, whose entry module imports its library root, as
  editor-project's does). `root/EditorSetRoot.lean` and
  `root/EditorSetFixtures.lean` are checked-in stand-ins for the generated
  roots (no Lake build runs in a fixture), with the same shape: `import
  Editor`, `import Editor.Main` (or `Editor.Test.Fixture.Main`), then the
  three entry modules `Compile.EditorPackage`, `Shell.EditorPackage` and
  `ShippedThemes.EditorPackage`; the fixture harness's stand-in then
  imports the fixture support module `CompileTest.FixtureSupport` (in
  `compile`'s `CompileTest` library), as editor-project's generator does,
  which imports `Compile` and the core module `Editor.Api`, as
  `WorkspaceTest.FixtureSupport` imports core modules. `Editor.Headless` imports
  `Editor.Config.Elaborate`, as editor-project's does, so `EditorSetRoot`,
  `EditorSetFixtures` and `CompileTest.Linked` reach the elaborator, each
  importing `Editor` directly. Every package but the core sets
  `plugins = ["@editor-core/lintShared"]` at package level. Every rule of the
  policy holds over it.
- `tests/fixtures/editor-broken-ws` is the same workspace plus one breaking
  import per rule, appended after the existing ones, a second for
  allow-only rule 4: the linked root imports `Editor.Window.Real`, which the
  policy's `except` takes out of the root's extras, and a second for deny
  rule 4, mirroring `host-shipped-themes`: the fixtures host root
  `Editor.Test.Fixture.Main` imports `ShippedThemes.EditorPackage`, an entry
  module only the stand-in roots name. For deny rule 5 the entry module
  `Shell.EditorPackage` imports `Std.Data.HashMap`, and the entry module
  `ShippedThemes.EditorPackage` imports the core module `Editor.Api` and
  `Lean.Data.Json`, so each of the rule's `pkg:editor-core`, `external:Std`
  and `external:Lean` targets bites (as `host-entry-core` and
  `host-entry-lean` do); for deny rule 6 the
  entry module `Compile.EditorPackage` imports `CompileTest.FixtureSupport`,
  so `EditorSetRoot` reaches it. For reachable rule 1 it adds the empty
  core module `lean/Editor/Test/Shell.lean`, imported only by the package
  test `CompileTest.Model` (its last import line), as in editor-project: it
  is loaded into library `Editor` though no root of it reaches the module,
  and it lies outside `Editor.Core`'s closure. For co-reach rule 1 its
  `root/EditorSetFixtures.lean` drops `import Editor`, so the fixture-harness
  root reaches `Editor.Config.Elaborate` (through
  `Editor.Test.Fixture.Main` and `Editor.Headless`) without the base. For
  target-config rule 1 the core's `FilesApi` library loads no plugin. For
  require-backed rule 1, compile's library module `Compile` imports
  `ShellApi`, which `compile` reaches only through `compile-api`, mirroring
  the `require-backed` edit (its import of `Shell`, for `layers`, breaks it
  too). For doc-modules rule 1, its `docs/design/packages.md` does not list
  `Editor.Test.Shell`, the module it adds, mirroring the `doc-modules`
  edit; for doc-packages rule 1, the same file gives `shell-api` the layer
  `implementation`, mirroring the `doc-packages` edit.
- Both workspaces hold `docs/design/packages.md`, a miniature of
  editor-project's module map: "The core's modules" names the 15 `Editor.…`
  modules of `editor-ws` in a table shaped like editor-project's (its
  prose names paths such as `lean/Editor/`, which the rule ignores), and
  "The packages" has a row for each of the five packages, with its layer
  and requires beside the core, then a second table of the same shape with
  a row for `acp`, a package outside the workspace, which the rule must not
  read (as editor-project's agents table).
- `tests/fixtures/editor-acceptance-holds` runs the policy cut down to these
  modules (the same set names, rules, order and reasons, and the two roots
  declared with `[[root]]`) over `editor-ws`: `lean-deny: ok (17 rules)`.
  Its doc rules read `docs/design/packages.md`, not `../docs/…`: the
  miniature's core is inside the workspace (`path = "lean"`), so the
  module map is under the workspace root.
  Its target-config rule lists the miniature's six packages. Its
  host sets are derived as the example policy's are: `set:entry-modules` is
  the three entry modules, `set:fixture-support` is
  `CompileTest.FixtureSupport`, `set:host-roots` is `Editor`, `Editor.Main`
  and `Editor.Test.Fixture.Main`, and `set:feature-modules` adds
  `Compile.Compiled`, `Shell.Compiled` and `ShippedThemes`. It also guards
  the `acfed133` derivation fix: with the old sets (every root import but
  the core's an entry module), `CompileTest.FixtureSupport` counts as an
  entry module, `Editor.Api` as a feature module, and deny rule 4 bites
  twice (`Editor.Main` and `Editor.Test.Fixture.Main`, through
  `Editor.Headless` and `Editor.Loop`).
- `tests/fixtures/editor-acceptance-bites` runs the same policy over
  `editor-broken-ws`: `lean-deny: 30 violations in 17 of 17 rules`. Deny rule
  1 bites five times (`Editor.Core` through `Editor.Main`, `Editor.Main`,
  `Editor.Test.Fixture.Main`, `ModelTest` through `ModelTest.Bound`,
  `ModelTest.Bound`), deny rule 2 twice, deny rule 4 twice (`Editor.Main`,
  `Editor.Test.Fixture.Main`), deny rule 5 three times (`Shell.EditorPackage`
  imports `Std.Data.HashMap`, `ShippedThemes.EditorPackage` imports
  `Editor.Api` and `Lean.Data.Json`), deny rule 6 once (`EditorSetRoot` →
  `Compile.EditorPackage` → `CompileTest.FixtureSupport`), allow-only rule 4 twice (`Editor.Ffi.Text`,
  `Editor.Window.Real`), `layers` four times (compile → shell,
  editor-core → compile, editor-core → shipped-themes,
  editor-core → compile-api), and every other rule once, reachable rule 1
  on `Editor.Test.Shell` (`lean/Editor/Test/Shell.lean`) and co-reach rule 1
  on `EditorSetFixtures`, which reaches `Editor.Config.Elaborate` but not
  `Editor`, and target-config rule 1 on `editor-core/FilesApi`;
  require-backed rule 1 twice (`Compile` imports `Shell` and `ShellApi`,
  and `compile` requires only `editor-core` and `compile-api`), doc-modules
  rule 1 once (`Editor.Test.Shell`) and doc-packages rule 1 once
  (`shell-api`'s layer). With any one of the three rules taken out of the
  policy, exactly its lines go (28, 29 and 29 violations), so `lake test`
  fails if one stops biting. Without the
  `except`, the `Editor.Window.Real` violation is not reported; with a
  hand-written entry-module list lacking `ShippedThemes.EditorPackage`, deny
  rule 4 misses `Editor.Test.Fixture.Main`; with deny rule 5's `to` cut to
  `external:Std`, its `Editor.Api` and `Lean.Data.Json` violations are not
  reported. The `Editor.Api` import also makes `Editor.Api` a feature
  module, which `Editor.Main` and `Editor.Test.Fixture.Main` reach through
  `Editor.Headless` and `Editor.Loop`, but deny rule 4 reports one shortest
  chain per host root, and both already have a shorter one, so it adds no
  deny rule 4 line (over `editor-ws`, the same import alone gives deny rule 4
  twice through `Editor.Loop`: a fixture-sized `host-entry-core`).

The fixtures are a model of editor-project's structure, not a copy of it:
each `.lean` file holds only `import` lines (two hold none), with
editor-project's module and package names and none of its source, and the
Markdown is a miniature of `packages.md`'s module map. Their
lakefiles are TOML, so loading them runs no code, and they write nothing.
The `ModelTests` library matters: without it `ModelTest.Bound` would belong
to no target and become an external node, and deny rules 1 and 3 would not
see through it. editor-project has that library too.

## Gaps

"Unlanded" below means introduced by the `policy-rules` roadmap and not yet
on `main`.

| Gap | Task |
|---|---|
| Patterns (`Editor.*.Model`, `Editor.*Contract`, `Editor.*.Cases`, `Editor.*.Real`, `Editor.*.Kit`, `<P>Test`, `<P>Test.Linked`) are enumerated, and the enumerations fail open: a new match lands in `api`. | `glob-selector` |
| "Every package but the core" is enumerated: a new implementation package declares no keyword and is outside `set:packages` until listed. | `workspace-selector` |
| `Editor.Internal…` and `Editor.*.Kit` have no module yet, so a selector naming them is an error; they are left out, and a first module there falls into `api`. | `reserved-namespace-selector` |
| Core rule 4 sees only direct imports of `Lean`/`Lake`, as the script did (not a regression). | `external-transitive-reach` |
| Paths outside the workspace directory (the core's, `../lean`) print absolute. | `relative-paths-outside-root` |
| The lint-plugins rule's packages are enumerated: a new package is outside target-config rule 1 until listed. | `workspace-selector` |
| The module map's columns 4 and 5 (the extension points a package registers at and reads) are not checked: they need elaborated Lean, a non-goal of roadmap `editor-project-module-map-leave-out`. | none |
| `set:packages` is enumerated: a new implementation package missing from it escapes require-backed rule 1. Its row in the module map would then show up as a doc-packages violation (`a row for X, which 'packages' does not match`), so the omission does not pass silently. | `workspace-selector` |
| A fixture support module imported directly by the editor's generated root would be derived as an entry module, so `set:fixture-support` would be empty and the check would exit 2 (`set 'fixture-support' matches no module: its except list removes every module it selects`), not report a deny rule 6 violation. It still fails the check. Telling the two apart by name (`<P>Test.FixtureSupport` against `….EditorPackage`) needs a glob selector. | `glob-selector` |

## For editor-project's adoption

This is input for editor-project's task `lean-structure-rules-tool`:

- Run `lean-deny check` in `packages/`, the default set. There, Lake's
  `.lake/` writes are editor-project's own build directory, so a run in
  place is fine; it is only this repository's acceptance run that must use a
  copy.
- The policy reports `Editor.Test.Shell` (reachable rule 1) until
  `Editor.Core` imports it, which is what editor-project's own core rule 2
  asks for. It is still the baseline's only violation at `acfed133` and at
  `1101b206`.
- Leave-out and the module map hold at `1101b206`: require-backed rule 1,
  doc-modules rule 1 and doc-packages rule 1 report nothing, so this run
  adds no finding for `lean-structure-rules-tool`.
- `packages.md` says of the module map "No gate step checks it; rdm task
  `lean-structure-rules-tool` is where automated checking comes back".
  doc-modules rule 1 and doc-packages rule 1 are that check, for "The
  core's modules" and for columns 1 to 3 of "The packages". Run from
  `packages/`, their `file` is `../docs/design/packages.md`.
- Deny rule 6 reads "Host imports" bullet 3 as "of the two generated roots,
  only the fixture harness's imports a fixture support module, and the
  editor's root does not link one"; editor-project's own model test of
  `WorkspaceTest.FixtureSupport` imports it, which the rule allows. Should
  editor-project mean "no other module at all", the rule needs a second
  `deny`.
- Keep the enumerations in the policy in sync with the tree until the
  `glob-selector` and `workspace-selector` tasks land. The host rules' sets,
  the fixture support modules included, are derived from the generated
  roots (`imports:`) and need no upkeep.
- Build lean-deny with editor-project's toolchain (they are equal now), so
  its Lake elaborates editor-project's `lean/lakefile.lean` as editor-project's
  Lake does.
