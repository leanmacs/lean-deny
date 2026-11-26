import LeanDeny.DocSection
import LeanDeny.Graph.View
import LeanDeny.Policy.Resolve
import LeanDeny.Rules.Common

/-!
# `[[doc-modules]]` rules

A doc-modules rule says the backticked module names starting with `prefix`
in section `section` of Markdown file `file` (relative to the workspace
directory) are exactly the workspace modules `modules` matches. What counts
as a heading, a section and a name is `LeanDeny.DocSection`'s. Pure: the
file is read by `LeanDeny.Check` and handed in as a `DocRead`.

- The **listed** names are the section's names that start with `prefix` (a
  plain string prefix: `Doc.`, with the dot). Any other backticked text is
  ignored.
- The **modules** are the workspace modules and declared roots `modules`
  matches. An external module in a mixed match is ignored, as reachable's
  `must-cover` does.
- The two are compared as sets: order and counts in the document are never
  checked. Each module not listed is one **missing** violation, in
  `displayOrder`; then each listed name that is not a module's is one
  **extra** violation, in order of first appearance.

A rule's selectors are resolved against the graph first. The errors, in
order: each selector that matches nothing (source order), each that matches
only modules outside the workspace, then, only if there was none, a matched
module whose name does not start with `prefix` (the section could never list
it). Then the file's error, if any: no file, a read failure, no heading, or a
heading appearing more than once. A rule with an error is not evaluated, and
any error anywhere means no violation is reported.
-/

open Lean LeanDeny.Graph

namespace LeanDeny

/-- A rule's section, or the located diagnostic for why it cannot be read. -/
abbrev DocRead :=
  Except String DocSection

/-- Rule `r`'s section, from its file's contents: `none` for no file (or a
directory), `some (.error e)` for a read failure, `some (.ok text)` for the
text. -/
def DocModulesRule.readResult (p : Policy) (r : DocModulesRule)
    (contents : Option (Except String String)) : DocRead :=
  let loc := Policy.locate p.path r.pos?
  match contents with
  | none =>
    .error <|
      loc s!"{r.label}: no file '{r.file}' in the workspace (looking for heading '{r.heading}')"
  | some (.error e) =>
    .error <| loc s!"{r.label}: cannot read '{r.file}' (looking for heading '{r.heading}'): {e}"
  | some (.ok text) =>
    match findSection text r.heading with
    | .ok s => .ok s
    | .error .notFound => .error <| loc s!"{r.label}: no heading '{r.heading}' in '{r.file}'"
    | .error (.ambiguous lines) =>
      .error <|
        loc <|
        s!"{r.label}: heading '{r.heading}' appears {lines.size} times in '{r.file}' \
            (lines {proseList (lines.map toString)})"

/-- A doc-modules rule with its selectors resolved. -/
structure DocModulesResolved where
  rule : DocModulesRule
  /-- The workspace modules and declared roots `modules` matches, sorted. -/
  modules : Array NodeId
  deriving Inhabited

/-- Resolve rule `r`'s selectors in `g`, with the policy's sets resolved in
`sets`. The errors are in the module doc's order. -/
def resolveDocModules (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId))
    (r : DocModulesRule) : Except (Array String) DocModulesResolved :=
  Id.run do
    let loc := Policy.locate p.path
    let mut errs := #[]
    let mut external := #[]
    let mut matched := #[]
    for ref in r.refs do
      match matchRef g sets ref with
      | .ok ns =>
        if !ns.isEmpty && ns.all (isExternalId g) then
          external := external.push ref
        matched := sortedUnion matched ns
      | m =>
        errs := errs.push (loc ref.pos? ((matchError? ref m).getD ""))
    for ref in external do
      let msg :=
        s!"{ref.describe} matches only modules outside the workspace, which a doc-modules rule \
          does not compare"
      errs := errs.push (loc ref.pos? msg)
    if !errs.isEmpty then
      return .error errs
    let modules := matched.filter (!isExternalId g ·)
    let unprefixed := (displayOrder g modules).filter fun m => !(nodeName g m).startsWith r.pfx
    if let some m := unprefixed[0]? then
      let more := if unprefixed.size > 1 then s!" (and {unprefixed.size - 1} more)" else ""
      let msg :=
        s!"{r.label}: 'modules' matches {nodeName g m}{more}, which does not start with the \
          prefix '{r.pfx}', so the section cannot list it"
      return .error #[loc r.pos? msg]
    return .ok { rule := r, modules }

/-- Evaluate a resolved rule against its section `s`: the missing modules in
`displayOrder`, then the extra names in order of first appearance. -/
def evalDocModules (g : Graph) (d : DocModulesResolved) (s : DocSection) : Array Violation :=
  Id.run do
    let r := d.rule
    let file := g.root / r.file
    let rel := g.relPath file
    -- The first listing of each prefixed name, in document order.
    let mut listed : Array DocName := #[]
    for n in s.names do
      if n.name.startsWith r.pfx && !listed.any (·.name == n.name) then
        listed := listed.push n
    let names := d.modules.map (nodeName g)
    let base : Violation :=
      { rule := r.ref, pos? := r.pos?, reason? := some r.reason, chain := #[] }
    let mut vs := #[]
    for m in displayOrder g d.modules do
      let name := nodeName g m
      unless listed.any (·.name == name) do
        vs :=
          vs.push
            { base with
              detail? := some s!"{name} is not listed in section '{r.heading}' of {rel}"
              module? := some m
              doc? :=
                some { kind := .missing, name, file, heading := r.heading, line := s.headingLine } }
    for n in listed do
      unless names.contains n.name do
        vs :=
          vs.push
            { base with
              detail? :=
                some
                  s!"section '{r.heading}' of {rel} lists {n.name}, which 'modules' does not match"
              doc? :=
                some
                  { kind := .extra, name := n.name, file, heading := r.heading, line := n.line } }
    return vs

/-- Every doc-modules rule of `p`, with the policy's sets resolved in `sets`
and rule `i`'s section read in `docs[i]`: the violations in rule order, or
every rule's errors in rule order (a rule's selector errors, then its file's
error). -/
def checkDocModules (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId))
    (docs : Array DocRead) : Except (Array String) (Array Violation) :=
  Id.run do
    let mut errs := #[]
    let mut vs := #[]
    for (r, i) in p.docModules.zipIdx do
      let resolved := resolveDocModules g p sets r
      let doc : DocRead :=
        docs[i]?.getD
          (.error
            (Policy.locate p.path r.pos? s!"{r.label}: internal error: its file was not read"))
      if let .error es := resolved then
        errs := errs ++ es
      if let .error e := doc then
        errs := errs.push e
      if let .ok d := resolved then
        if let .ok s := doc then
          vs := vs ++ evalDocModules g d s
    if errs.isEmpty then
      return .ok vs
    return .error errs

end LeanDeny
