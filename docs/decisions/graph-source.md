# Decision: where lean-deny gets the module graph

- **Status:** accepted
- **Date:** 2026-11-25
- **Toolchain:** Lean 4.35.0 (commit `eb6cafb`), Lake 5.0.0-src+eb6cafb
- **Roadmap / phase:** `foundation` / `phase-1-graph-source-spike`

## Decision

lean-deny reads the graph **in-process through the Lake API** (source 1). It
loads the workspace with `Lake.loadWorkspace`, then fetches each library's
`modules` facet and each module's `input` facet with `noBuild := true`. On
both of editor-project's workspaces it gave exactly the edges Lake's own
facet gives. It keeps the `public` / `meta` / `import all` flags and the
`prelude` signal, sees every package's metadata, and works the same for
`lakefile.toml` and `lakefile.lean`. It needs no subprocess, parses no
program output, and reimplements no Lake resolution. Warm, it costs about the
same as `lake query`.

## Context

The roadmap's bar is "the graph Lake resolves, building nothing": every
module of the workspace, its `lean_lib` and package, the package's keywords,
and each direct import. lean-deny must not match on another program's
output, and must not guess at Lake's module resolution.

## Options considered

1. **In-process Lake API:** tried for real.
   `LeanDeny/Graph/LakeApi.lean` (`loadWs`, `collect`, `graph`, `pkgMeta`)
   and the `lean-deny-spike` executable ran on copies of both editor-project
   workspaces. The output was cross-checked against Lake's own facet. Stage
   times were measured inside the process.
2. **A facet the user's workspace requires, read with `lake query`:**
   assessed and timed. editor-project's `editorLayerImports` package facet
   (deleted in its commit `d51fe135`) was restored into the throwaway copy's
   `lean/lakefile.lean` only, then queried.
3. **Header parsing (`Lean.parseImports'`):** assessed. The cost of parsing
   alone was measured with `lean-deny-spike --parse-only`, which takes the
   module list from Lake and then parses each header directly.

## Results

Machine: Apple M5 Max (18 cores, 128 GiB), macOS 27.2.1 (26B131).

The workspaces are editor-project's `lean/` (a `lakefile.lean` workspace)
and `packages/` (a `lakefile.toml` package set of 44 path packages plus the
core). Both were copied from the working tree (HEAD `900ea2d2` when the spike
began) with `rsync -a --exclude .lake --exclude target --exclude node_modules`.
The copy holds 1,013 `.lean` files in 27 MB. The restored facet stayed in the
copy's `lean/lakefile.lean` for every run below, so all the cases elaborate
the same config.

Each case ran 5 times, timed with `/usr/bin/time -p`. Source 1 used the built
binary (`.lake/build/bin/lean-deny-spike`), not `lake exe`.

- **Cold:** before **each** cold run, every `.lake/config` directory under the
  copy was deleted (`find "$COPY" -path '*/.lake/config' -type d -prune -exec rm -rf {} +`),
  so each run re-elaborated every `lakefile.lean`. All 10 cold runs were
  confirmed cold by their `load` stage: 3,501–3,789 ms, against 251–314 ms
  warm. None was discarded.
- **Warm:** the config oleans were already cached.
- **Query:** source 2 was warmed once first, then each run was
  `lake query :editorLayerImports` in `lean/`, or
  `lake -d ../packages query :editorLayerImports` from `lean/`.

Wall-clock times, in seconds (min / median of 5):

| Case | `lean/` | `packages/` |
|---|---|---|
| Source 1, cold | 3.74 / 3.78 | 3.73 / 3.91 |
| Source 1, warm | 0.47 / 0.51 | 0.60 / 0.64 |
| Source 2, `lake query`, warm | 0.42 / 0.43 | 0.54 / 0.56 |
| `--parse-only` (source 1 load, then direct header parsing) | 0.49 / 0.54 | 0.68 / 0.69 |

Internal stage split, in milliseconds (min / median), measured with
`IO.monoMsNow`:

| Case | env | load | fetch (modules + input) |
|---|---|---|---|
| cold `lean/` | 63 / 66 | 3,506 / 3,539 | 108 / 110 |
| cold `packages/` | 64 / 65 | 3,501 / 3,665 | 101 / 111 |
| warm `lean/` | 77 / 78 | 251 / 288 | 101 / 102 |
| warm `packages/` | 77 / 78 | 267 / 306 | 213 / 215 |

The `--parse-only` split was: `lean/`, `modules` 101–110 ms then `parse`
29–33 ms; `packages/`, `modules` 210–216 ms then `parse` 45–57 ms. `modules`
is Lake's `lib.modules` fetch.

Counts (source 1):

| | packages | libs | modules | imports (all) | workspace edges |
|---|---|---|---|---|---|
| `lean/` | 1 | 12 | 573 | 5,091 | 3,934 |
| `packages/` | 45 | 98 | 986 | 8,699 | 6,715 |

Notes on the numbers:

- **Cold cost is config elaboration.** Load takes about 3.5 s cold against
  0.25–0.31 s warm. That is elaborating the core's 2,000-line
  `lakefile.lean`, which `lake` pays too. The first `lake query` after the
  facet was added (one run each) took 3.74 s and 3.77 s.
- **The `env` stage is a fixed cost.** It is about 65–80 ms, mostly
  `findInstall?` running `lean --print-prefix`, because a standalone binary
  is not co-located with `lean`. With `LEAN_SYSROOT` set it dropped to
  31–34 ms, and warm wall-clock to 0.38–0.45 s on both workspaces (5 runs
  each). `lake exe` sets `LAKE_HOME`; a bare binary does not, so `computeEnv`
  falls back to `LakeInstall.ofLean` (see Deviations).
- **Most of the fetch is Lake's `lib.modules`.** For libraries with
  `Glob.one` roots, `lib.modules` already walks local imports, which reads
  headers. The extra `input` fetch adds almost nothing, and parsing every
  header directly takes 29–57 ms. The `packages/` fetch varied between about
  110 ms and 220 ms across runs.

**Correctness cross-check.** Each line of `:editorLayerImports` was reduced
to (importer, imported) and to (package, importer, imported package,
imported). These were sorted, then diffed against source 1's
workspace-internal edges (those whose imported module resolves to a
workspace package):

- `lean/`: 3,934 query lines and 3,934 source-1 edges. **0 differences**
  (pairs and 4-tuples).
- `packages/`: 6,715 and 6,715. **0 differences.**

Source 1 also gave no duplicate edges, although the facet de-duplicates its
own.

**Side effects.** A stamp file was touched before each run, then
`find "$COPY" -newer .stamp -type f` was run:

- Source 1 on `lean/` wrote only `lean/.lake/config/0/lakefile.olean{,.trace}`.
- Source 1 on `packages/` wrote only
  `packages/.lake/config/26/lakefile.olean{,.trace}`. Index 26 is the core,
  the only `lakefile.lean` package in that workspace.
- The whole timing matrix, source 2 included, wrote exactly those four files.
- Using `packages/at-point` as a root wrote its own
  `at-point/.lake/config/1/lakefile.olean{,.trace}`. Each workspace root
  caches its own copy (about 5 MB) of each `lakefile.lean` dependency's config.
- A workspace with no `lake-manifest.json` is refused with an error before
  Lake runs, and nothing is written to it.
- The real editor-project was never touched. `ls -laR` of
  `lean/.lake/config` and `packages/.lake/config` was identical before and
  after the spike, and `git status` there was clean.

## Module-system and `prelude` handling

| | `public import` | `meta import` | `import all` | `module` header | `prelude` |
|---|---|---|---|---|---|
| 1. Lake API (`input` facet) | `isExported` | `isMeta` | `importAll` | `header.isModule` | no `Init` import |
| 1'. Lake API (`imports` facet) | lost | lost | lost | not visible | not visible |
| 2. `lake query` facet | only what the facet prints; `editorLayerImports` used `imports`, so lost | lost | lost | not visible | not visible |
| 3. Header parsing | `isExported` | `isMeta` | `importAll` | `isModule` | no `Init` import |

- Source 1 reads `ModuleInput.imports : Array ModuleImport`. That is
  `Lean.Import` (`module`, `isExported`, `isMeta`, `importAll`) plus
  `module? : Option Module`, Lake's resolution to a workspace module. `none`
  means a toolchain module such as `Init`, `Lean`, `Std` or `Lake`.
- `Lean.parseImports'` adds `Init` and `meta Init` unless the header says
  `prelude`, so every non-`prelude` module shows two `Init` imports.
- Outside the module system every import has `isExported = true`.
- `SpikeTest` checks all of this on the fixture `tests/fixtures/spike-ws`
  (`module`, `public import`, `meta import`, `import all`, `prelude`).
- **editor-project does not use the module system.** None of its 1,013 files
  has a `module` header or a `prelude`, and no import carries
  `public`/`meta`/`all`. The plan had expected about 175 `module` files, but
  that count came from `^module` lines inside doc comments. On the real
  workspaces every import is `exported`, plus the implicit `meta Init`. So
  the module-system forms are exercised only by the fixture.
- A source-2 facet could print the flags only by reading `input` itself, and
  then it would just be source 1 behind a subprocess.

## Package metadata available (source 1)

From `Workspace.packages` (see `pkgMeta`), every package gives:

- `baseName`
- `dir`
- `configFile`, whose extension gives the config language (`lean` or `toml`)
- `keywords`
- `remoteUrl`
- `depConfigs`: the names of its `require`s
- each `leanLib`'s `name`, `roots` and `globs`

On `packages/` this gave all 45 packages, with the `editor-interface` and
`editor-input-scheme` keywords and the full `require` lists, and all 98
libraries.

Source 2 sees the same from inside a facet. Source 3 would get none of it
without loading the configuration, and for `lakefile.lean` that means
elaborating it, which is Lake.

Things source 1 does **not** see as written, for phase 3:

- **`lean_exe` root modules that are in no `lean_lib`.** The core has five
  (`FfiTest`, `ConfigTest`, `ModelTest`, `ContractTest`, `LintTest`). Their
  imports appear only from the other side. Phase 3 should also walk
  `pkg.leanExes` roots, or say that it does not.
- **Modules two libraries share.** There are none in editor-project today.
  Source 1 would emit one row per library, while the facet listed such a
  module once.
- **The defining file and line of each import.** `ModuleInput` has the path,
  but `parseImports'` keeps no positions. The README's report format needs
  `file:line`, so phase 3 has to re-scan the header for positions.

## Consequences and risks

- **Toolchain coupling.** The binary embeds Lake and Lean 4.35.0. It reads
  `lakefile.lean` configs by elaborating them against its own `Lake` oleans
  and evaluating them in its own interpreter, so it must match the
  workspace's toolchain.
  - The config olean's trace includes the Lean githash. A lean-deny built
    with a different toolchain would therefore re-elaborate on every run and
    overwrite the workspace's cached config olean with its own, after which
    `lake` would re-elaborate again: a ping-pong.
  - A different Lake version may not accept the workspace's config at all.
  - This was not measured, because only 4.35.0 is installed here.
  - The README's distribution model (`require` lean-deny so Lake builds it
    with the workspace's own toolchain, then `lake exe lean-deny`) avoids
    the mismatch, and phase 2 should keep it.
  - A prebuilt, toolchain-independent lean-deny binary is not possible with
    this source.
- **Lake is an internal API.** `LoadConfig`, `loadWorkspace`, `runBuild`,
  `ModuleInput` and `ModuleImport` are public but not stable. Expect small
  breakages on toolchain bumps, kept within `LeanDeny/Graph/LakeApi.lean`.
- **Writes to `.lake/config`.** Loading caches each `lakefile.lean` config
  olean under `<workspace>/.lake/config/<idx>/`, exactly as `lake` does,
  including the lock file while elaborating. lean-deny writes nothing else,
  but it is not read-only.
- **No manifest, no run.** `loadWs` refuses a workspace without
  `lake-manifest.json` rather than let `loadWorkspace` fall back to
  `updateAndMaterialize`, which can clone, fetch and write a manifest. The
  user must run `lake update` (or any `lake build`) first.
- **Linking cost.**
  - `import Lake` linked statically with no extra flags; no `-lLake` was
    needed.
  - `supportInterpreter = true` is required to elaborate `lakefile.lean` in
    process.
  - The resulting executable is **185 MB**, linked only against `libc++` and
    `libSystem`, and the link takes about 0.5 s. That is fine for
    `lake exe`, but it is heavy to ship as a release artifact.
- **Header-only.** Nothing is built: `input`, `header` and `imports` are
  `buildable := false`, and the fetch runs with `noBuild := true`, so a real
  build fails instead of running.

Why not the others:

- **Source 2** is marginally faster warm (about 0.08 s, mostly the `env`
  stage) but needs:
  - a subprocess
  - parsing `lake`'s stdout, which the roadmap rules out
  - the user's workspace to load a `lakefile.lean` package that declares the
    facet, as a `require`. A `lakefile.toml` package cannot declare one,
    though, as `packages/` shows, it can query one declared by a dependency.

  With a `require` in place anyway, running the same code in-process
  (source 1) is strictly simpler.
- **Source 3** parses every header in 29–57 ms. The resolution is the hard
  part: roots, globs, `srcDir`, `require`s, manifests and `lakefile.lean`
  elaboration. Source 3 would either reimplement that or call Lake for it,
  and calling Lake for it is source 1.

## What happens to the prototype

**Kept** as the starting point for phase 3:

- `LeanDeny/Graph/LakeApi.lean`: `computeEnv`, `loadWs`, `collect`,
  `graphOf`, `graph`, `modulesOf` and `pkgMeta`, plus the `Edge` and `Row`
  types. Phase 3 reuses the loading, fetching and metadata code. It should
  replace `Row`/`Edge` with its own graph types and add exe roots and
  import positions.
- `tests/fixtures/spike-ws/` and `SpikeTest.lean` (the `lake test` driver
  `lean-deny-spike-test`) keep exercising it.
- `SpikeMain.lean` (`lean-deny-spike`) is the throwaway measuring tool.
  Phase 2 replaces it with the real `lean-deny` CLI and test harness.

## Deviations from the approved plan

- **`testDriver` is quoted.** It is `"«lean-deny-spike-test»"`. The bare
  `"lean-deny-spike-test"` resolves to `Name.anonymous` (`String.toName`
  rejects the hyphens), so `lake test` reported an unknown driver.
- **`computeEnv` has a fallback.** When `findInstall?` finds Lean but no Lake,
  it uses `LakeInstall.ofLean`. A standalone binary is neither co-located
  with `lean` nor given `LAKE_HOME`.
- **More imports were needed.** `import Lake` does not re-export
  `Lake.Load.Workspace` (`LoadConfig`, `loadWorkspace`), so the file also
  imports it. `Module` is written `Lake.Module`, because it is ambiguous with
  `Lean.Module`.
- **`--parse-only` has three stages.** It times `modules` (Lake's
  `lib.modules`) and `parse` (direct `parseImports'`) separately.
- **The fixture lib has explicit globs.** `lean_lib Fix` has
  `globs = ["Fix.+"]`, because it has no `Fix.lean` root and the default
  glob names only `Fix`.

## Addendum, 2026-11-25: phase 2 (`foundation` / `phase-2-package-and-cli`)

The record above stays as written. Phase 2 changed the prototype around it:

- **`lean-deny-spike` and `SpikeMain.lean` are gone,** replaced by the real
  `lean-deny` executable (`Main.lean`). `lean-deny check` calls
  `computeEnv`, `loadWs` and `graphOf` for real and discards the rows until
  rules exist; phase 3 replaces that call site.
- **`SpikeTest.lean` became `LeanDenyTest/Graph.lean`,** one suite of the
  `lake test` driver `lean-deny-test`, with the same checks on
  `tests/fixtures/spike-ws`, the no-manifest guard included.
- **`LeanDeny/Graph/LakeApi.lean` changed only in its error messages,**
  which lost their `lean-deny: ` prefix. The CLI prints every diagnostic
  once as `lean-deny: error: <msg>`.
- **The Lake-internal boundary now has two files.** lean-deny parses TOML
  (`lean-deny.toml`, and the harness's `fixture.toml`) with Lake's parser,
  `Lake.Toml.loadToml`, which is internal API like `loadWorkspace`. It is
  reached only through `LeanDeny/Lake/Toml.lean`, which returns plain values
  and pre-rendered `file:line:col` messages. Toolchain-bump breakage is
  expected within `LeanDeny/Graph/LakeApi.lean` and
  `LeanDeny/Lake/Toml.lean`, and nowhere else.
- **Facet integration was skipped.** A `:leanDeny` facet would run
  lean-deny inside Lake's build of the user's workspace and need a
  `lakefile.lean` to declare it; once the `require` is in place it gains
  nothing over `lake exe lean-deny check` and `lake lint` with
  `lintDriver = "«lean-deny»/«lean-deny»"`, which cover it.
