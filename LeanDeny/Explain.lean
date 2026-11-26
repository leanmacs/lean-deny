import LeanDeny.Cli
import LeanDeny.Exit
import LeanDeny.Graph.View
import LeanDeny.Load
import LeanDeny.Policy
import LeanDeny.Policy.Resolve

/-!
# `lean-deny explain`

List the modules a selector matches, for authoring a policy. The policy is
read in full only for a selector that names a set (`set:x`,
`imports:set:x`); for any other selector only its
`[[root]]` tables are read (`loadDeclaredRoots`), so a policy whose rules are half
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
  let (policy?, roots) ←
    match opts.selector.setName? with
    | some _ =>
      let policyPath := opts.config?.getD (defaultPolicyPath ws)
      match ← loadPolicy policyPath with
      | .ok p =>
        pure (some p, rootDecls policyPath.toString p.roots)
      | .error msgs =>
        return ← fail msgs
    | _ =>
      match ← loadDeclaredRoots ws opts.config? with
      | .ok roots =>
        pure (none, roots)
      | .error msgs =>
        return ← fail msgs
  -- An unknown set is reported before Lake runs.
  if let (some n, some p) := (opts.selector.setName?, policy?) then
    if (p.findSet? n).isNone then
      return ← fail #[p.unknownSet n]
  let g ←
    match ← loadGraph ws roots with
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
