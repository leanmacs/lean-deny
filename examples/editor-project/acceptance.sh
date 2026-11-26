#!/bin/sh
# The editor-project acceptance run (docs/editor-project-acceptance.md).
#
#   examples/editor-project/acceptance.sh <editor-project dir> <work dir>
#
# Run it at the root of lean-deny's repository, after `lake build`. It never
# writes under <editor-project dir>, which must be a git checkout: it prints
# the revision at HEAD, extracts that revision's lean/ and packages/ (`git
# archive`, so nothing uncommitted or untracked, and no .lake/ or target/)
# into <work dir>/pristine, and works on copies of that copy. Loading a
# workspace writes Lake's configuration cache into the workspace's .lake/,
# which is why the run never points lean-deny at the original.
#
# The policy declares the two roots the package-set build generates under
# packages/.lake/build/root/ ([[root]]); lean-deny never runs Lake to write them,
# so the script generates them in the copy first.
#
# It checks the policy (examples/editor-project/lean-deny.toml) over the copy's
# packages/ workspace, expecting exactly one violation (editor-project's
# finding: reachable rule 1 reports Editor.Test.Shell, outside Editor.Core's
# closure), and the core policy (lean-deny.core.toml) over its lean/
# workspace, expecting exit 0; then, for each breaking edit, starts again from
# the pristine copy, adds one import line, and expects exit 1 with violations
# of exactly the named rules and no other (or, for a control edit, only the
# baseline's), and exactly the named summary line; then, for each sed edit,
# starts again from the pristine copy, applies one sed script to one file (a
# lakefile, or the core's root), and expects the same. The policy has 14
# rules and the core policy 2. Every lean-deny output is printed with the
# work directory written as <work>. It exits 0 when every expectation held and
# nothing under <editor-project dir> changed during the run, and 1 otherwise.
set -eu

usage() {
  echo "usage: examples/editor-project/acceptance.sh <editor-project dir> <work dir>" >&2
  exit 2
}
[ "$#" -eq 2 ] || usage
lean_deny=${LEAN_DENY:-.lake/build/bin/lean-deny}
policy=${POLICY:-examples/editor-project/lean-deny.toml}
core_policy=${CORE_POLICY:-examples/editor-project/lean-deny.core.toml}
[ -x "$lean_deny" ] || { echo "acceptance: no $lean_deny; run lake build first" >&2; exit 2; }
[ -f "$policy" ] && [ -f "$core_policy" ] || { echo "acceptance: run it at the root of lean-deny's repository" >&2; exit 2; }
[ -f "$1/lean/lakefile.lean" ] && [ -f "$1/packages/lakefile.toml" ] || { echo "acceptance: $1 is not editor-project" >&2; exit 2; }
source=$(cd "$1" && pwd -P)
mkdir -p "$2"
work=$(cd "$2" && pwd -P)
case $work/ in
  "$source"/*) echo "acceptance: the work directory must be outside $source" >&2; exit 2 ;;
esac

failed=0
# Run lean-deny with `$@`, print its output with the work directory as <work>,
# and compare its exit code with `$expect_exit`, the set of rules its violation
# headers name with the comma-separated `$expect_rules` (equal, so no other
# rule may bite), and its summary line with `$expect_summary` (a whole line).
run() {
  set +e
  out=$("$lean_deny" "$@" 2>&1)
  code=$?
  set -e
  printf '%s\n' "$out" | sed "s|$work|<work>|g"
  echo "exit $code"
  if [ "$code" -ne "$expect_exit" ]; then
    echo "MISMATCH: expected exit $expect_exit"
    failed=1
  fi
  got=$(printf '%s\n' "$out" | sed -nE 's/^(deny rule [0-9]+|allow-only rule [0-9]+|layers|reachable rule [0-9]+|co-reach rule [0-9]+|target-config rule [0-9]+) \(.*/\1/p' | sort -u)
  want=$(printf '%s\n' "$expect_rules" | tr , '\n' | sed '/^$/d' | sort -u)
  if [ "$got" != "$want" ]; then
    echo "MISMATCH: expected violations of exactly {$expect_rules}, got {$(printf '%s' "$got" | tr '\n' ,)}"
    failed=1
  fi
  if ! printf '%s\n' "$out" | grep -qxF "$expect_summary"; then
    echo "MISMATCH: expected the line: $expect_summary"
    failed=1
  fi
}

# One revision for the whole run, so that a HEAD that moves meanwhile cannot
# split it.
rev=$(git -C "$source" --no-optional-locks rev-parse --verify HEAD 2>/dev/null) || { echo "acceptance: $source is not a git checkout with a HEAD" >&2; exit 2; }
echo "editor-project: $rev"
rm -rf "$work/pristine" "$work/edit"
mkdir -p "$work/pristine"
# Nothing under the source may be newer than this when the run ends.
touch "$work/stamp"
git -C "$source" --no-optional-locks archive "$rev" lean packages | tar -x -C "$work/pristine"
# POSIX sh has no pipefail: check that the archive arrived.
[ -f "$work/pristine/lean/lakefile.lean" ] && [ -f "$work/pristine/packages/lakefile.toml" ] || { echo "acceptance: git archive of $rev gave no lean/ and packages/" >&2; exit 2; }

# The policy's declared roots, generated in the copy (never in the source):
# `query :editorRoot` writes EditorSetRoot.lean. `build --no-build
# :editorFixtures` fails by design, since --no-build refuses the link, but the
# facet's own FetchM code writes EditorSetFixtures.lean before any job runs.
# `cp -R` of the pristine tree carries them into every edit's copy.
(cd "$work/pristine" && lake -d packages query :editorRoot > /dev/null)
(cd "$work/pristine" && lake -d packages build --no-build :editorFixtures > /dev/null 2>&1) || true
for f in EditorSetRoot EditorSetFixtures; do
  [ -f "$work/pristine/packages/.lake/build/root/$f.lean" ] || { echo "MISMATCH: no generated $f.lean"; failed=1; }
done

echo "== load the packages/ workspace as it is"
set +e
"$lean_deny" graph --workspace "$work/pristine/packages" --level package > /dev/null 2> "$work/load.err"
code=$?
set -e
sed "s|$work|<work>|g" "$work/load.err"
echo "exit $code"

# A file the script edits that editor-project no longer has is a MISMATCH
# (`$1`, in the copy; `$2`, what to update), not an abort under `set -e`, so
# that the run still reaches the check that nothing under the source changed,
# and the verdict.
missing() {
  echo "MISMATCH: $1 is not in editor-project any more; update $2 in acceptance.sh"
  failed=1
}

# Every Editor.… module a build reaches must be in Editor.Core's closure
# (editor-project's core rule 2, reachable rule 1). Editor.Test.Shell is not:
# only a package test imports it. The baseline expects exactly that violation,
# and every packages/ edit below carries it too. Every executable root that
# reaches the config elaborator also reaches the config base (core rule 3,
# co-reach rule 1): the baseline expects no co-reach violation, and edit core-3
# makes the contract tests' root, which reaches neither, import the elaborator.
echo "== baseline: packages/"
expect_exit=1 expect_rules='reachable rule 1' expect_summary='lean-deny: 1 violation in 1 of 14 rules'
run check --workspace "$work/pristine/packages" --config "$policy"
shell_line="  $work/pristine/lean/Editor/Test/Shell.lean: Editor.Test.Shell"
if ! printf '%s\n' "$out" | grep -qxF "$shell_line"; then
  echo "MISMATCH: expected the line: $(printf '%s' "$shell_line" | sed "s|$work|<work>|g")"
  failed=1
fi
echo "== baseline: lean/"
expect_exit=0 expect_rules= expect_summary='lean-deny: ok (2 rules)'
run check --workspace "$work/pristine/lean" --config "$core_policy"

# id | workspace | file | module imported | exit | rules that bite | summary line
while IFS='|' read -r id ws file imported expect_exit expect_rules expect_summary; do
  [ -n "$id" ] || continue
  echo "== $id: $file imports $imported"
  rm -rf "$work/edit"
  cp -R "$work/pristine" "$work/edit"
  target=$work/edit/$file
  if [ ! -f "$target" ]; then
    missing "$file" "the edit table"
    continue
  fi
  { printf 'import %s\n' "$imported"; cat "$target"; } > "$target.new"
  mv "$target.new" "$target"
  if [ "$ws" = lean ]; then config=$core_policy; else config=$policy; fi
  run check --workspace "$work/edit/$ws" --config "$config"
done <<'EDITS'
core-1|packages|lean/ModelTest/Editor/Bound.lean|CompileApi|1|deny rule 1,layers,reachable rule 1|lean-deny: 4 violations in 3 of 14 rules
core-3|packages|lean/ContractTest.lean|Editor.Config.Elaborate|1|co-reach rule 1,reachable rule 1|lean-deny: 2 violations in 2 of 14 rules
core-4|packages|lean/Editor/Bound.lean|Lean.Data.Json|1|deny rule 2,reachable rule 1|lean-deny: 3 violations in 2 of 14 rules
core-4-lean|lean|lean/Editor/Bound.lean|Lean.Data.Json|1|deny rule 1|lean-deny: 2 violations in 1 of 2 rules
core-5|packages|lean/ModelTest/Editor/Bound.lean|Editor.Ffi.Text|1|deny rule 3,reachable rule 1|lean-deny: 2 violations in 2 of 14 rules
core-5-lean|lean|lean/ModelTest/Editor/Bound.lean|Editor.Ffi.Text|1|deny rule 2|lean-deny: 1 violation in 1 of 2 rules
host|packages|lean/Editor/Main.lean|Compile.Compiled|1|deny rule 4,deny rule 1,layers,reachable rule 1|lean-deny: 5 violations in 4 of 14 rules
host-shipped-themes|packages|lean/Editor/Main.lean|ShippedThemes.EditorPackage|1|deny rule 4,deny rule 1,layers,reachable rule 1|lean-deny: 5 violations in 4 of 14 rules
host-entry-core|packages|packages/compile/Compile/EditorPackage.lean|Editor.Text|1|deny rule 4,deny rule 5,reachable rule 1|lean-deny: 5 violations in 3 of 14 rules
host-entry-lean|packages|packages/compile/Compile/EditorPackage.lean|Lean.Data.Json|1|deny rule 5,reachable rule 1|lean-deny: 2 violations in 2 of 14 rules
host-fixture-support|packages|packages/workspace/Workspace/Compiled.lean|WorkspaceTest.FixtureSupport|1|deny rule 6,reachable rule 1|lean-deny: 2 violations in 2 of 14 rules
fixture-support-test|packages|packages/workspace/WorkspaceTest/FixtureSupport.lean|Editor.Test.Linked.Rig|1|allow-only rule 2,reachable rule 1|lean-deny: 2 violations in 2 of 14 rules
package-library|packages|packages/compile/Compile.lean|Editor.Loop|1|allow-only rule 1,reachable rule 1|lean-deny: 2 violations in 2 of 14 rules
package-library-double|packages|packages/compile/Compile.lean|Editor.Text.Model|1|allow-only rule 1,reachable rule 1|lean-deny: 2 violations in 2 of 14 rules
package-test|packages|packages/compile/CompileTest/Compile.lean|Editor.Test.Linked.Rig|1|allow-only rule 2,reachable rule 1|lean-deny: 2 violations in 2 of 14 rules
package-linked|packages|packages/compile/CompileTest/Linked/Compile.lean|Editor.Headless|1|allow-only rule 3,reachable rule 1|lean-deny: 2 violations in 2 of 14 rules
package-linked-root|packages|packages/compile/CompileTest/Linked.lean|Editor.Ffi.Text|1|allow-only rule 4,reachable rule 1|lean-deny: 2 violations in 2 of 14 rules
package-linked-root-window|packages|packages/compile/CompileTest/Linked.lean|Editor.Window.Real|1|allow-only rule 4,reachable rule 1|lean-deny: 2 violations in 2 of 14 rules
package-linked-root-window-check|packages|packages/compile/CompileTest/Linked.lean|Editor.WindowCheck.Real|1|allow-only rule 4,reachable rule 1|lean-deny: 2 violations in 2 of 14 rules
layers|packages|packages/compile/Compile.lean|Shell|1|layers,reachable rule 1|lean-deny: 2 violations in 2 of 14 rules
control-test-double|packages|packages/compile/CompileTest/Compile.lean|Editor.Text.Model|1|reachable rule 1|lean-deny: 1 violation in 1 of 14 rules
control-test-fake|packages|packages/compile/CompileTest/Compile.lean|Editor.Job.Fake|1|reachable rule 1|lean-deny: 1 violation in 1 of 14 rules
control-linked-root-real|packages|packages/compile/CompileTest/Linked.lean|Editor.Text.Real|1|reachable rule 1|lean-deny: 1 violation in 1 of 14 rules
EDITS

# Edits that remove or change a line rather than add an import: one sed
# script applied to one file. Every lean_lib and lean_exe of the core and of
# every package loads the lint plugin or imports the core's Lint (target-config
# rule 1): lint-plugin-package drops a package's package-level `plugins`
# (lakefile.toml, three targets) and lint-plugin-core one core library's
# `plugins := lintPlugin` (lakefile.lean). Every Editor.… module the build
# reaches is in Editor.Core's closure (core rule 2, reachable rule 1): core-2
# drops the core root's import of Editor.Test.Linked.Frames, which a package's
# linked test still imports, so reachable rule 1 reports it beside the
# baseline's Editor.Test.Shell.
# id | workspace | file | sed script | exit | rules that bite | summary line
while IFS='|' read -r id ws file script expect_exit expect_rules expect_summary; do
  [ -n "$id" ] || continue
  echo "== $id: $file, sed '$script'"
  rm -rf "$work/edit"
  cp -R "$work/pristine" "$work/edit"
  target=$work/edit/$file
  if [ ! -f "$target" ]; then
    missing "$file" "the sed edit table"
    continue
  fi
  sed -e "$script" "$target" > "$target.new"
  if cmp -s "$target" "$target.new"; then
    rm -f "$target.new"
    missing "the line '$id' edits in $file" "the sed edit table"
    continue
  fi
  mv "$target.new" "$target"
  if [ "$ws" = lean ]; then config=$core_policy; else config=$policy; fi
  run check --workspace "$work/edit/$ws" --config "$config"
  if [ "$id" = core-2 ]; then
    frames_line="  $work/edit/lean/Editor/Test/Linked/Frames.lean: Editor.Test.Linked.Frames"
    if ! printf '%s\n' "$out" | grep -qxF "$frames_line"; then
      echo "MISMATCH: expected the line: $(printf '%s' "$frames_line" | sed "s|$work|<work>|g")"
      failed=1
    fi
  fi
done <<'SED'
lint-plugin-package|packages|packages/compile/lakefile.toml|/^plugins = \["@editor-core\/lintShared"\]$/d|1|reachable rule 1,target-config rule 1|lean-deny: 4 violations in 2 of 14 rules
lint-plugin-core|packages|lean/lakefile.lean|s/^lean_lib ExtensionFixture where plugins := lintPlugin$/lean_lib ExtensionFixture/|1|reachable rule 1,target-config rule 1|lean-deny: 2 violations in 2 of 14 rules
core-2|packages|lean/Editor/Core.lean|/^import Editor\.Test\.Linked\.Frames$/d|1|reachable rule 1|lean-deny: 2 violations in 1 of 14 rules
SED

# Anywhere under the source, .git/ included, but for .git/worktrees/: it holds
# the state of editor-project's other checkouts, which git commands run in them
# refresh, and nothing here reads or writes it.
changed=$(find "$source" -path "$source/.git/worktrees" -prune -o -newer "$work/stamp" -print | head -n 5)
if [ -n "$changed" ]; then
  echo "MISMATCH: files under $source changed during the run:"
  printf '%s\n' "$changed"
  failed=1
fi

if [ "$failed" -eq 0 ]; then echo "acceptance: every expectation held"; else echo "acceptance: some expectation failed"; fi
exit "$failed"
