import LeanDenyTest.Cli
import LeanDenyTest.Graph
import LeanDenyTest.Header
import LeanDenyTest.Query
import LeanDenyTest.View
import LeanDenyTest.Fixtures
import LeanDenyTest.Harness

/-!
`lake test` driver. Runs the CLI parser tests, the graph checks, the fixture
runner's own checks and every fixture under `tests/fixtures/`. `lake test -- <name>…` runs only the named
fixtures. The working directory is the package root (as `lake test` sets it).
-/

open LeanDenyTest

def report (suite : String) (fs : Array String) : IO Bool := do
  if fs.isEmpty then
    IO.println s!"ok   {suite}"
    return true
  IO.eprintln s!"FAIL {suite}"
  for f in fs do IO.eprintln s!"  {f}"
  return false

def main (args : List String) : IO UInt32 := do
  let root ← IO.FS.realPath (← IO.currentDir)
  let mut ok := true
  if args.isEmpty then
    ok := (← report "cli" Cli.failures) && ok
    ok := (← report "header" (← Header.run)) && ok
    ok := (← report "query" Query.run) && ok
    ok := (← report "view" View.run) && ok
    ok := (← report "graph" (← Graph.run root)) && ok
    ok := (← report "harness" (← Harness.run root)) && ok
  let (n, failed) ← Fixtures.run root args
  IO.println s!"{n} fixtures, {failed} failed"
  return if ok && failed == 0 then 0 else 1
