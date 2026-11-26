import LeanDeny.Cli
import LeanDeny.Exit
import LeanDeny.Graph.View
import LeanDeny.Load
import LeanDeny.Policy
import LeanDeny.Policy.Resolve

/-!
# `lean-deny explain`

List the modules a selector matches, for authoring a policy. The policy is
read in full only for a `set:` selector; for any other selector only its
`[[root]]` tables are read (`loadRoots`), so a policy whose rules are half
written cannot stop anyone from exploring, and a policy that is not valid
TOML only warns. A selector that matches nothing is an error (exit 2), as it
is in a policy.
-/

namespace LeanDeny

/-- Run `explain`. Diagnostics go to stderr; the matched modules to stdout,
one per line, in the order `graph --level module` prints them. -/
def runExplain (opts : ExplainOpts) : IO Outcome := do
  let fail (msgs : Array String) : IO Outcome := do
    msgs.forM printError
    return .error
  let ws := opts.workspace
  if let .error msgs← checkWorkspaceDir ws then
    return ← fail msgs
  let policyPath := opts.config?.getD (defaultPolicyPath ws)
  let (policy?, roots) ←
    match opts.selector with
    | .set _ =>
      match ← loadPolicy policyPath with
      | .ok p =>
        pure (some p, p.roots)
      | .error msgs =>
        return ← fail msgs
    | _ =>
      match ← loadRoots policyPath opts.config?.isSome with
      | .ok (roots, warnings) =>
        warnings.forM printWarning
        pure (none, roots)
      | .error msgs =>
        return ← fail msgs
  -- An unknown set is reported before Lake runs.
  if let (.set n, some p) := (opts.selector, policy?) then
    if (p.findSet? n).isNone then
      return ← fail #[p.unknownSet n]
  let g ←
    match ← loadGraph ws (rootDecls policyPath.toString roots) with
    | .ok g =>
      pure g
    | .error msgs =>
      return ← fail msgs
  let ref : SelectorRef :=
    { text := opts.text, sel := opts.selector, pos? := none, use := .commandLine }
  match resolveRef g policy? ref with
  | .error msgs =>
    fail msgs
  | .ok ns =>
    for n in Graph.sortForDisplay g ns do
      IO.println n.name.toString
    return .holds

end LeanDeny
