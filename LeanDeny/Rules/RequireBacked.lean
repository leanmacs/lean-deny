import LeanDeny.Graph.Query
import LeanDeny.Graph.View
import LeanDeny.Policy.Resolve
import LeanDeny.Rules.Common
import LeanDeny.Rules.Layers

/-!
# `[[require-backed]]` rules

A require-backed rule says every import from a module of a package
`packages` matches into a module of another workspace package is backed by
a direct `require` of that package in the importing package's lakefile.
Lake resolves a workspace's packages from their requires transitively, so
an import reached only through another package's require breaks when that
package is dropped. Static: the requires are read from the loaded graph
(`LeanDeny.Graph.PackageInfo.requires`), never by running Lake. Pure.

- The packages judged are those of the workspace modules `packages`
  matches. The selectors must select whole packages: matching some modules
  of a package but not others is an error.
- An import from a module of judged package A into a module of another
  workspace package B is **backed** when A's lakefile requires B directly
  (the names compared as users write them, `plainName`). Imports within one
  package, imports of modules outside the workspace (so Lean's implicit
  `Init` imports) and a declared root's imports (as importer or imported: a
  root is in no package) are never judged. Every import kind counts: plain,
  `meta`, `public` and `all` alike.
- One violation per (importer, imported) pair whose import is not backed,
  the first directive in source order as its witness. Violations come by
  importing module in `displayOrder`, then its imports in source order.

A rule's selectors are resolved against the graph first. The errors, in
order: each selector that matches nothing (source order), each that matches
only modules outside the workspace or declared roots, then, only if there
was none, each package the rule splits (packages by name). A rule with an
error is not evaluated, and any error anywhere means no violation is
reported.
-/

open Lean LeanDeny.Graph

namespace LeanDeny

/-- A require-backed rule with its selectors resolved. -/
structure RequireBackedResolved where
  rule : RequireBackedRule
  /-- The packages judged, sorted by `plainName`. -/
  packages : Array Name
  deriving Inhabited

/-- The whole packages selectors `refs` match in `g`, with the policy's sets
resolved in `sets`, sorted by `plainName`; `label` and `pos?` name the rule
in a split's error. The errors, in order: each selector that matches nothing
(source order), each that matches only modules outside the workspace or
declared roots, then, only if there was none, each package the selectors
split (packages by name). Shared by require-backed and doc-packages
rules. -/
def resolvePackageRefs (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId))
    (label : String) (pos? : Option Toml.Pos) (refs : Array SelectorRef) :
    Except (Array String) (Array Name) :=
  Id.run do
    let loc := Policy.locate p.path
    let mut errs := #[]
    -- Each selector that matches only modules in no package: externals, or
    -- declared roots too (`true`).
    let mut noPackage : Array (SelectorRef × Bool) := #[]
    let mut matched : Array NodeId := #[]
    for ref in refs do
      match matchRef g sets ref with
      | .ok ns =>
        if !ns.isEmpty && ns.all fun n => (packageOf? g n).isNone then
          noPackage := noPackage.push (ref, !ns.all (isExternalId g))
        matched := sortedUnion matched ns
      | m =>
        errs := errs.push (loc ref.pos? ((matchError? ref m).getD ""))
    for (ref, hasRoot) in noPackage do
      let msg :=
        if hasRoot then
          s!"{ref.describe} matches only declared roots or modules outside the workspace, which \
            are in no package"
        else s!"{ref.describe} matches only modules outside the workspace, which are in no package"
      errs := errs.push (loc ref.pos? msg)
    if !errs.isEmpty then
      return .error errs
    let mask := memberMask g matched
    let inRule (n : NodeId) : Bool := mask[n]?.getD false
    -- Each package's modules, in `displayOrder`.
    let pkgMods : Std.HashMap Name (Array NodeId) :=
      (displayOrder g (Array.range g.nodes.size)).foldl (init := {}) fun m n =>
        match packageOf? g n with
        | some pk => m.insert pk ((m.getD pk #[]).push n)
        | none => m
    let mut packages := #[]
    for pk in workspacePackages g do
      let mods := pkgMods.getD pk #[]
      match mods.find? inRule, mods.find? (!inRule ·) with
      | some m1, some m2 =>
        let msg :=
          s!"{label} splits package '{plainName pk}': it matches {nodeName g m1} but not \
            {nodeName g m2}; the rule judges whole packages, so select them with pkg:, keyword:, \
            or a set of them"
        errs := errs.push (loc pos? msg)
      | some _, none =>
        packages := packages.push pk
      | _, _ =>
        pure ()
    if !errs.isEmpty then
      return .error errs
    return .ok packages

/-- Resolve rule `r`'s selectors in `g`, with the policy's sets resolved in
`sets`. The errors are in the module doc's order (`resolvePackageRefs`). -/
def resolveRequireBacked (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId))
    (r : RequireBackedRule) : Except (Array String) RequireBackedResolved := do
  let packages ← resolvePackageRefs g p sets r.label r.pos? r.refs
  return { rule := r, packages }

/-- Package `name`'s lakefile and direct requires, as written; a package
missing from `g.packages` requires nothing, its lakefile the workspace
root. -/
def requiresOf (g : Graph) (name : Name) : System.FilePath × Array Name :=
  match g.findPackage? name with
  | some pk => (pk.configFile, pk.requires)
  | none => (g.root, #[])

/-- The violation import `e` witnesses: a module of package `pa` imports a
module of package `pb`, which `pa` does not require directly. -/
private def violation (g : Graph) (r : RequireBackedRule) (pa pb : Name) (e : Edge) : Violation :=
  let (configFile, requires) := requiresOf g pa
  let detail :=
    s!"{nodeName g e.src} (package {plainName pa}) imports package {plainName pb}, which \
      {plainName pa} does not require directly"
  { rule := r.ref, pos? := r.pos?, reason? := some r.reason, detail? := some detail, chain := #[e],
    require? := some { pkg := pa, imported := pb, configFile, requires } }

/-- Evaluate a resolved rule: one violation per (importer, imported) pair
whose import is not backed, in report order (each workspace module of a
judged package in `displayOrder`, then its imports in source order). -/
def evalRequireBacked (g : Graph) (d : RequireBackedResolved) : Array Violation :=
  Id.run do
    let mut vs := #[]
    for f in displayOrder g ((Array.range g.nodes.size).filter (!isExternalId g ·)) do
      let some pa := packageOf? g f | continue
      unless d.packages.contains pa do
        continue
      let requires := (requiresOf g pa).2
      -- One violation per imported module: the first directive is the witness.
      let mut seen : Array NodeId := #[]
      for e in g.imports f do
        -- An external module or a declared root is in no package: not judged.
        let some pb := packageOf? g e.dst | continue
        if pa == pb || requires.any (plainName · == plainName pb) then
          continue
        unless seen.contains e.dst do
          seen := seen.push e.dst
          vs := vs.push (violation g d.rule pa pb e)
    return vs

/-- Every require-backed rule of `p`, with the policy's sets resolved in
`sets`: the violations in rule order, or every rule's errors in rule
order. -/
def checkRequireBacked (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId)) :
    Except (Array String) (Array Violation) :=
  Id.run do
    let mut errs := #[]
    let mut vs := #[]
    for r in p.requireBacked do
      match resolveRequireBacked g p sets r with
      | .error es =>
        errs := errs ++ es
      | .ok d =>
        vs := vs ++ evalRequireBacked g d
    if errs.isEmpty then
      return .ok vs
    return .error errs

end LeanDeny
