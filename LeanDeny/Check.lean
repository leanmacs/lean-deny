import LeanDeny.Cli
import LeanDeny.Exit
import LeanDeny.Load
import LeanDeny.Policy
import LeanDeny.Policy.Resolve
import LeanDeny.Rules.AllowOnly
import LeanDeny.Rules.CoReach
import LeanDeny.Rules.Deny
import LeanDeny.Rules.DocModules
import LeanDeny.Rules.DocPackages
import LeanDeny.Rules.Layers
import LeanDeny.Rules.Reachable
import LeanDeny.Rules.RequireBacked
import LeanDeny.Rules.TargetConfig

/-!
# `lean-deny check`

Resolve the workspace, load the policy, load the workspace's module graph
with the policy's declared roots (`[[root]]`),
resolve every set of the policy against it (each selector must match), then
check the policy's rules: deny rules (`LeanDeny.Rules.Deny`), then
allow-only rules (`LeanDeny.Rules.AllowOnly`), then `[layers]`
(`LeanDeny.Rules.Layers`), then reachable rules
(`LeanDeny.Rules.Reachable`), then co-reach rules (`LeanDeny.Rules.CoReach`),
then target-config rules (`LeanDeny.Rules.TargetConfig`), then
require-backed rules (`LeanDeny.Rules.RequireBacked`), then doc-modules
rules (`LeanDeny.Rules.DocModules`), then doc-packages rules
(`LeanDeny.Rules.DocPackages`). Cheap failures come first: a bad workspace
path or policy is reported before Lake runs. A doc-modules or doc-packages
rule's Markdown file is read after the graph loads, against the loaded
workspace root, so its errors join the other rule errors in rule order.

The report goes to stdout in the format `--format` names
(`LeanDeny.Report`): for text, `lean-deny: ok (N rules)` when every rule
holds (exit 0), or one block per violation and a summary line (exit 1).
Errors go to stderr in every format (exit 2), and a policy with any error
reports no violation. The exit code is the same in every format.
-/

open System

namespace LeanDeny

/-- The contents of `file` (relative to the workspace root): `none` for no
file or a directory, `some (.error e)` for a read failure. -/
def readDocContents (g : Graph.Graph) (file : String) : IO (Option (Except String String)) := do
  let path := g.root / file
  if !(← path.pathExists) || (← path.isDir) then
    return none
  try
    return some (.ok (← IO.FS.readFile path))
  catch e =>
    return some (.error (toString e))

/-- Each doc-modules rule's section, in rule order: the rule's file
(relative to the workspace root) read and its heading found, or the located
diagnostic. The only IO a doc-modules rule does. -/
def readDocSections (g : Graph.Graph) (p : Policy) : IO (Array DocRead) :=
  p.docModules.mapM fun r => return r.readResult p (← readDocContents g r.file)

/-- Each doc-packages rule's package table, in rule order, as
`readDocSections`. The only IO a doc-packages rule does. -/
def readDocTables (g : Graph.Graph) (p : Policy) : IO (Array DocPackagesRead) :=
  p.docPackages.mapM fun r => return r.readResult p (← readDocContents g r.file)

/-- Every rule of `p`, with the policy's sets resolved in `sets`, the
doc-modules rules' sections read in `docs` (`readDocSections`) and the
doc-packages rules' tables in `tables` (`readDocTables`): deny rules, then
allow-only rules, then `[layers]`, then reachable rules, then co-reach
rules, then target-config rules, then require-backed rules, then
doc-modules rules, then doc-packages rules. Every error of every kind (in
that order), or, when there is none, every violation (in that order). -/
def checkRules (g : Graph.Graph) (p : Policy) (sets : Std.HashMap String (Array Graph.NodeId))
    (docs : Array DocRead) (tables : Array DocPackagesRead := #[]) :
    Except (Array String) (Array Violation) :=
  let rs :=
    #[checkDeny g p sets, checkAllowOnly g p sets, checkLayers g p sets, checkReachable g p sets,
      checkCoReach g p sets, checkTargetConfig g p sets, checkRequireBacked g p sets,
      checkDocModules g p sets docs, checkDocPackages g p sets tables]
  let errs :=
    rs.flatMap fun
      | .error es => es
      | .ok _ => #[]
  if errs.isEmpty then
    .ok
      (rs.flatMap fun
        | .ok vs => vs
        | .error _ => #[])
  else .error errs

/-- Run `check`. Diagnostics go to stderr, one line each, in every format;
the report in `opts.format` to stdout (`LeanDeny.Report`). -/
def runCheck (opts : CheckOpts) : IO Outcome := do
  let ws := opts.workspace
  let policyPath := opts.config?.getD (defaultPolicyPath ws)
  let cwd := (← IO.FS.realPath (← IO.currentDir)).toString
  let ctx : ReportCtx := { policyPath := policyPath.toString, cwd }
  let finish (r : CheckResult) : IO Outcome := do
    if let .failed _ msgs := r then
      msgs.forM printError
    IO.print (renderCheck opts.format ctx r)
    return r.outcome
  if let .error msgs← checkWorkspaceDir ws then
    return ← finish (.failed none msgs)
  let policy ←
    match ← loadPolicy policyPath with
    | .ok p =>
      pure p
    | .error msgs =>
      return ← finish (.failed none msgs)
  let rules := some policy.ruleCount
  let g ←
    match ← loadGraph ws (rootDecls policy.path policy.roots) with
    | .ok g =>
      pure g
    | .error msgs =>
      return ← finish (.failed rules msgs)
  -- Every set is resolved, used by a rule or not, so a renamed module is
  -- caught.
  let sets ←
    match resolveSets g policy with
    | .ok sets =>
      pure sets
    | .error msgs =>
      return ← finish (.failed rules msgs)
  let docs ← readDocSections g policy
  let tables ← readDocTables g policy
  match checkRules g policy sets docs tables with
  | .error msgs =>
    finish (.failed rules msgs)
  | .ok vs =>
    finish (.checked g policy vs)

end LeanDeny
