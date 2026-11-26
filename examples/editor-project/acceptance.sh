#!/bin/sh
# The editor-project acceptance run (docs/editor-project-acceptance.md).
#
#   examples/editor-project/acceptance.sh <editor-project dir> <work dir>
#
# Run it at the root of lean-deny's repository, after `lake build`. It never
# writes under <editor-project dir>: it copies that tree's lean/ and packages/
# (without .lake/ and target/) into <work dir>/pristine and works on copies of
# that copy. Loading a workspace writes Lake's configuration cache into the
# workspace's .lake/, which is why the run never points lean-deny at the
# original.
#
# It checks the policy (examples/editor-project/lean-deny.toml) over the copy's
# packages/ workspace and the core policy (lean-deny.core.toml) over its lean/
# workspace, expecting exit 0; then, for each breaking edit, starts again from
# the pristine copy, adds one import line, and expects exit 1 with violations
# of exactly the named rules and no other (or exit 0 for a control edit), and
# exactly the named summary line. Every lean-deny output is printed with the
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
  got=$(printf '%s\n' "$out" | sed -nE 's/^(deny rule [0-9]+|allow-only rule [0-9]+|layers) \(.*/\1/p' | sort -u)
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

echo "editor-project: $(git -C "$source" --no-optional-locks rev-parse HEAD 2>/dev/null || echo unknown)"
rm -rf "$work/pristine" "$work/edit"
mkdir -p "$work/pristine"
# Nothing under the source may be newer than this when the run ends.
touch "$work/stamp"
rsync -a --exclude .lake --exclude target "$source/lean" "$source/packages" "$work/pristine/"

echo "== load the packages/ workspace as it is"
set +e
"$lean_deny" graph --workspace "$work/pristine/packages" --level package > /dev/null 2> "$work/load.err"
code=$?
set -e
sed "s|$work|<work>|g" "$work/load.err"
echo "exit $code"

# Every Editor module a build reaches must be in Editor.Core's closure
# (editor-project's core rule 2). At 4df216a8 Editor.Test.Shell is not, and
# lean-deny cannot load the workspace then (the task named in the doc). The
# baseline adds the import that rule prescribes, as editor-project's fix would.
core=$work/pristine/lean/Editor/Core.lean
if ! grep -qx 'import Editor.Test.Shell' "$core"; then
  echo "== baseline: Editor.Core imports Editor.Test.Shell"
  awk '{ print } $0 == "import Editor.Test.Restore" { print "import Editor.Test.Shell" }' "$core" > "$core.new"
  mv "$core.new" "$core"
  grep -qx 'import Editor.Test.Shell' "$core" || { echo "MISMATCH: Editor.Core has no import Editor.Test.Restore to add it after"; failed=1; }
fi

echo "== baseline: packages/"
expect_exit=0 expect_rules= expect_summary='lean-deny: ok (9 rules)'
run check --workspace "$work/pristine/packages" --config "$policy"
echo "== baseline: lean/"
expect_summary='lean-deny: ok (2 rules)'
run check --workspace "$work/pristine/lean" --config "$core_policy"

# id | workspace | file | module imported | exit | rules that bite | summary line
while IFS='|' read -r id ws file imported expect_exit expect_rules expect_summary; do
  [ -n "$id" ] || continue
  echo "== $id: $file imports $imported"
  rm -rf "$work/edit"
  cp -R "$work/pristine" "$work/edit"
  target=$work/edit/$file
  { printf 'import %s\n' "$imported"; cat "$target"; } > "$target.new"
  mv "$target.new" "$target"
  if [ "$ws" = lean ]; then config=$core_policy; else config=$policy; fi
  run check --workspace "$work/edit/$ws" --config "$config"
done <<'EDITS'
core-1|packages|lean/ModelTest/Editor/Bound.lean|CompileApi|1|deny rule 1,layers|lean-deny: 3 violations in 2 of 9 rules
core-4|packages|lean/Editor/Bound.lean|Lean.Data.Json|1|deny rule 2|lean-deny: 2 violations in 1 of 9 rules
core-4-lean|lean|lean/Editor/Bound.lean|Lean.Data.Json|1|deny rule 1|lean-deny: 2 violations in 1 of 2 rules
core-5|packages|lean/ModelTest/Editor/Bound.lean|Editor.Ffi.Text|1|deny rule 3|lean-deny: 1 violation in 1 of 9 rules
core-5-lean|lean|lean/ModelTest/Editor/Bound.lean|Editor.Ffi.Text|1|deny rule 2|lean-deny: 1 violation in 1 of 2 rules
host|packages|lean/Editor/Main.lean|Compile.Compiled|1|deny rule 4,deny rule 1,layers|lean-deny: 4 violations in 3 of 9 rules
package-library|packages|packages/compile/Compile.lean|Editor.Loop|1|allow-only rule 1|lean-deny: 1 violation in 1 of 9 rules
package-library-double|packages|packages/compile/Compile.lean|Editor.Text.Model|1|allow-only rule 1|lean-deny: 1 violation in 1 of 9 rules
package-test|packages|packages/compile/CompileTest/Compile.lean|Editor.Test.Linked.Rig|1|allow-only rule 2|lean-deny: 1 violation in 1 of 9 rules
package-linked|packages|packages/compile/CompileTest/Linked/Compile.lean|Editor.Headless|1|allow-only rule 3|lean-deny: 1 violation in 1 of 9 rules
package-linked-root|packages|packages/compile/CompileTest/Linked.lean|Editor.Ffi.Text|1|allow-only rule 4|lean-deny: 1 violation in 1 of 9 rules
layers|packages|packages/compile/Compile.lean|Shell|1|layers|lean-deny: 1 violation in 1 of 9 rules
control-test-double|packages|packages/compile/CompileTest/Compile.lean|Editor.Text.Model|0||lean-deny: ok (9 rules)
control-test-fake|packages|packages/compile/CompileTest/Compile.lean|Editor.Job.Fake|0||lean-deny: ok (9 rules)
control-linked-root-real|packages|packages/compile/CompileTest/Linked.lean|Editor.Text.Real|0||lean-deny: ok (9 rules)
EDITS

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
