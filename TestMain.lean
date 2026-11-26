import LeanDenyTest.AllowOnly
import LeanDenyTest.Cli
import LeanDenyTest.CoReach
import LeanDenyTest.Deny
import LeanDenyTest.Fixtures
import LeanDenyTest.Graph
import LeanDenyTest.Harness
import LeanDenyTest.Header
import LeanDenyTest.Layers
import LeanDenyTest.Policy
import LeanDenyTest.Query
import LeanDenyTest.Reachable
import LeanDenyTest.Render
import LeanDenyTest.Report
import LeanDenyTest.RequireBacked
import LeanDenyTest.Resolve
import LeanDenyTest.Selector
import LeanDenyTest.TargetConfig
import LeanDenyTest.View

/-!
`lake test` driver. Runs the CLI parser tests, the selector, policy and
resolution tests, the deny, allow-only, layers, reachable, co-reach,
target-config and require-backed rule tests, the graph checks, the check report's renderings, the fixture runner's own checks and every
fixture under `tests/fixtures/`. `lake test -- <name>…` runs only the named
fixtures. The working directory is the package root (as `lake test` sets it).
-/

open LeanDenyTest

def report (suite : String) (fs : Array String) : IO Bool := do
  if fs.isEmpty then
    IO.println s!"ok   {suite}"
    return true
  IO.eprintln s!"FAIL {suite}"
  for f in fs do
    IO.eprintln s!"  {f}"
  return false

def main (args : List String) : IO UInt32 := do
  let root ← IO.FS.realPath (← IO.currentDir)
  let mut ok := true
  if args.isEmpty then
    ok := (← report "cli" Cli.failures) && ok
    ok := (← report "selector" Selector.failures) && ok
    ok := (← report "policy" (← Policy.run)) && ok
    ok := (← report "header" (← Header.run)) && ok
    ok := (← report "query" Query.run) && ok
    ok := (← report "view" View.run) && ok
    ok := (← report "resolve" Resolve.run) && ok
    ok := (← report "deny" (← Deny.run)) && ok
    ok := (← report "allow-only" (← AllowOnly.run)) && ok
    ok := (← report "layers" (← Layers.run)) && ok
    ok := (← report "reachable" (← Reachable.run)) && ok
    ok := (← report "co-reach" (← CoReach.run)) && ok
    ok := (← report "target-config" (← TargetConfig.run)) && ok
    ok := (← report "require-backed" (← RequireBacked.run)) && ok
    ok := (← report "render" (← Render.run root)) && ok
    ok := (← report "report" (← Report.run root)) && ok
    ok := (← report "graph" (← Graph.run root)) && ok
    ok := (← report "harness" (← Harness.run root)) && ok
  let (n, failed) ← Fixtures.run root args
  IO.println s!"{n} fixtures, {failed} failed"
  return if ok && failed == 0 then 0 else 1
