import LeanDeny

/-!
Test driver for the graph-source spike: loads `tests/fixtures/spike-ws`
(relative to the package directory, the working directory under `lake test`)
through the in-process Lake API and checks the graph it resolves.
-/

open Lean LeanDeny.Graph.LakeApi

/-- The failures of the fixture's graph against what the spike expects. -/
def failures (rows : Array Row) : Array String := Id.run do
  let mut fs : Array String := #[]
  let fixRows := rows.filter fun r => r.pkg == `«spike-ws» && r.lib == `Fix
  unless fixRows.size == 4 && rows.size == 4 do
    fs := fs.push s!"expected 4 modules in lib Fix of package spike-ws, got {rows.map (·.module)}"
  let row? (m : Name) : Option Row := rows.find? (·.module == m)
  let edge? (src dst : Name) : Option Edge :=
    (row? src).bind fun r => r.edges.find? (·.target == dst)
  let expectEdge (src dst : Name) (ok : Edge → Bool) (what : String) : Option String :=
    match edge? src dst with
    | some e => if ok e then none else some s!"{src}→{dst} should be {what}: {repr e}"
    | none => some s!"missing edge {src}→{dst}"
  let expectRow (m : Name) (ok : Row → Bool) (what : String) : Option String :=
    match row? m with
    | some r => if ok r then none else some s!"{m} {what}: {repr r}"
    | none => some s!"missing module {m}"
  let inWs (e : Edge) := e.targetPkg? == some `«spike-ws» && e.targetLib? == some `Fix
  let checks := #[
    expectEdge `Fix.A `Fix.B (fun e => inWs e && e.isExported && !e.isMeta && !e.importAll)
      "a resolved public import",
    expectEdge `Fix.A `Fix.C (fun e => inWs e && e.isMeta && !e.isExported && !e.importAll)
      "a resolved (private) meta import",
    expectEdge `Fix.A `Fix.D (fun e => inWs e && e.importAll && !e.isMeta)
      "a resolved import all",
    expectEdge `Fix.B `Fix.C inWs "a resolved import",
    expectEdge `Fix.B `Init (·.targetPkg?.isNone) "a toolchain import (no workspace package)",
    expectRow `Fix.C (fun r => !r.importsInit && r.edges.isEmpty) "(prelude) should import nothing, not even Init",
    expectRow `Fix.A (·.isModule) "should have isModule = true",
    expectRow `Fix.D (fun r => r.importsInit && !r.isModule) "should import Init and not be a module"
  ]
  for c in checks do
    if let some f := c then fs := fs.push f
  return fs

def main : IO UInt32 := do
  let dir := (← IO.currentDir) / "tests" / "fixtures" / "spike-ws"
  let (_, rows, _) ← graph dir
  let fs := failures rows
  if fs.isEmpty then
    IO.println s!"lean-deny-spike-test: ok ({rows.size} modules)"
    return 0
  for f in fs do IO.eprintln s!"FAIL: {f}"
  return 1
