import LeanDeny.Graph.Query
import LeanDeny.Policy.Resolve
import LeanDeny.Rules.Common

/-!
# `[layers]`

Every package of the workspace is in one layer, and every direct import
from a module of one package to a module of another must be an allowed
(importer layer, imported layer) pair. Pure.

- The packages judged are those of the workspace's modules.
- A classify entry puts the packages its selectors match in its layer. It
  must select whole packages: matching some modules of a package but not
  others is an error. A package two entries select is an error. A package no
  entry selects is in `default`, or, with no `default`, an error.
- Imports within one package (`same-package = "allow"`) and imports of
  modules outside the workspace are never judged. Every other import counts:
  plain, `meta` and `public` alike. Only listed pairs are allowed, same-layer
  pairs included. One violation per (importer, imported) pair, the first
  directive in source order as its witness.

Errors, in order: each classify selector that matches nothing, each that
matches only modules outside the workspace, each entry that splits a
package; then, only if there were none, each package in two or more
entries, the packages in no layer (no `default`), and a `default` that holds
no package; then, only if there were none, each `allow` pair that allows no
import. Any error means no violation is reported.
-/

open Lean LeanDeny.Graph

namespace LeanDeny

/-- `[layers]` with its classify entries resolved: each package's layer. -/
structure LayersResolved where
  rule : LayersRule
  /-- `rule.layerNames`. -/
  layers : Array String
  /-- Each workspace package with the index into `layers` of its layer. -/
  layerOf : Std.HashMap Name Nat
  deriving Inhabited

/-- The packages of the workspace's modules, each once, sorted by
`plainName`. -/
def workspacePackages (g : Graph) : Array Name :=
  let (_, ps) :=
    (Array.range g.nodes.size).foldl (init := (({} : Std.HashSet Name), #[])) fun (seen, ps) n =>
      match packageOf? g n with
      | some p => if seen.contains p then (seen, ps) else (seen.insert p, ps.push p)
      | none => (seen, ps)
  ps.qsort fun a b => plainName a < plainName b

/-- Package names as prose, each quoted: "'a'", "'a' and 'b'". -/
private def packageList (ps : Array Name) : String :=
  proseList (ps.map fun p => s!"'{plainName p}'")

/-- Classify every package of `g`, with the policy's sets resolved in
`sets`. The errors, in order: each classify selector that matches nothing
(source order), each that matches only modules outside the workspace, each
entry (in order) that splits a package (packages by name); then, only if
there was none, each package two or more entries select (by name), the
packages in no layer when there is no `default`, and a `default` that holds
no package. -/
def resolveLayers (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId))
    (r : LayersRule) : Except (Array String) LayersResolved :=
  Id.run do
    let loc := Policy.locate p.path
    let pkgs := workspacePackages g
    -- Each package's modules, in `displayOrder`.
    let pkgMods : Std.HashMap Name (Array NodeId) :=
      (displayOrder g (Array.range g.nodes.size)).foldl (init := {}) fun m n =>
        match packageOf? g n with
        | some pk => m.insert pk ((m.getD pk #[]).push n)
        | none => m
    let mut errs := #[]
    let mut externalOnly := #[]
    -- Per classify entry: its workspace modules, or `none` when a selector
    -- of it failed.
    let mut matched : Array (Option (Array NodeId)) := #[]
    for c in r.classify do
      let mut u : Option (Array NodeId) := some #[]
      for ref in c.select do
        match matchRef g sets ref with
        | .ok ns =>
          if !ns.isEmpty && ns.all (isExternalId g) then
            externalOnly := externalOnly.push ref
          u := u.map (sortedUnion · ns)
        | m =>
          errs := errs.push (loc ref.pos? ((matchError? ref m).getD ""))
          u := none
      matched := matched.push (u.map (·.filter (!isExternalId g ·)))
    for ref in externalOnly do
      let msg :=
        s!"{ref.describe} matches only modules outside the workspace, which are in no package"
      errs := errs.push (loc ref.pos? msg)
    for (c, u?) in r.classify.zip matched do
      let some u := u? | continue
      let mask := memberMask g u
      let inU (n : NodeId) : Bool := mask[n]?.getD false
      for pk in pkgs do
        let mods := pkgMods.getD pk #[]
        if let (some m1, some m2) := (mods.find? inU, mods.find? (!inU ·)) then
          let msg :=
            s!"layers classify entry {c.index} splits package '{plainName pk}': it matches \
              {nodeName g m1} but not {nodeName g m2}; a layer holds whole packages, so select \
              them with pkg:, keyword:, or a set of them"
          errs := errs.push (loc c.pos? msg)
    if !errs.isEmpty then
      return .error errs
    -- No entry splits a package, so an entry selects a package when it
    -- matches any of its modules.
    let masks := matched.map fun u? => memberMask g (u?.getD #[])
    let selects (k : Nat) (pk : Name) : Bool :=
      (pkgMods.getD pk #[]).any fun n => (masks[k]?.bind (·[n]?)).getD false
    let layers := r.layerNames
    let layerIdx (l : String) : Nat := (layers.findIdx? (· == l)).getD 0
    let mut layerOf : Std.HashMap Name Nat := {}
    let mut unclassified := #[]
    for pk in pkgs do
      let ks := (Array.range r.classify.size).filter (selects · pk)
      match ks.toList with
      | [] =>
        match r.default? with
        | some d =>
          layerOf := layerOf.insert pk (layerIdx d)
        | none =>
          unclassified := unclassified.push pk
      | [k] =>
        layerOf := layerOf.insert pk (layerIdx ((r.classify[k]?.map (·.layer)).getD ""))
      | _ =>
        let cs := ks.filterMap (r.classify[·]?)
        let msg :=
          s!"package '{plainName pk}' is in layers classify entries \
            {proseList (cs.map (toString ·.index))}; a package is in one layer"
        errs := errs.push (loc (cs.back?.bind (·.pos?)) msg)
    if !unclassified.isEmpty then
      let one := unclassified.size == 1
      let msg :=
        s!"layers: {if one then "package" else "packages"} {packageList unclassified} \
          {if one then "is" else "are"} in no layer: no classify entry selects \
          {if one then "it" else "them"}, and there is no 'default'"
      errs := errs.push (loc r.pos? msg)
    if let some d := r.default? then
      let classified := r.classify.any (·.layer == d)
      if !classified && !pkgs.any (layerOf[·]? == some (layerIdx d)) then
        let msg :=
          s!"layers: layer '{d}' (the default) holds no package: a classify entry selects every \
            package"
        errs := errs.push (loc r.defaultPos? msg)
    if !errs.isEmpty then
      return .error errs
    return .ok { rule := r, layers, layerOf }

/-- The violation import `e` witnesses: a module of package `pa`, in layer
`la`, imports a module of package `pb`, in layer `lb`. -/
private def violation (r : LayersRule) (pa : Name) (la : String) (pb : Name) (lb : String)
    (e : Edge) : Violation :=
  let detail := s!"{plainName pa} ({la}) may not import {plainName pb} ({lb})"
  { rule := ⟨.layers, 1⟩, pos? := r.pos?, reason? := r.reason?, detail? := some detail,
    chain := #[e] }

/-- Evaluate the classified packages: the violations, in report order (each
workspace module in `displayOrder`, then its imports in source order), and,
per `allow` pair, whether it allows any import. -/
def evalLayers (g : Graph) (d : LayersResolved) : Array Violation × Array Bool :=
  Id.run do
    let pairs := d.rule.allow
    let name (l : Nat) : String := d.layers[l]?.getD ""
    let mut used := Array.replicate pairs.size false
    let mut vs := #[]
    for f in displayOrder g ((Array.range g.nodes.size).filter (!isExternalId g ·)) do
      let some pa := packageOf? g f | continue
      let some la := d.layerOf[pa]? | continue
      -- One violation per imported module: the first directive is the witness.
      let mut seen : Array NodeId := #[]
      for e in g.imports f do
        -- An external module is in no layer: not judged.
        let some pb := packageOf? g e.dst | continue
        if pa == pb then
          continue
        let some lb := d.layerOf[pb]? | continue
        match pairs.findIdx? fun q => q.importer == name la && q.imported == name lb with
        | some k =>
          used := used.set! k true
        | none =>
          unless seen.contains e.dst do
            seen := seen.push e.dst
            vs := vs.push (violation d.rule pa (name la) pb (name lb) e)
    return (vs, used)

/-- `[layers]` of `p`, with the policy's sets resolved in `sets`: `.ok #[]`
when there is none; else the violations, or every error: `resolveLayers`'s,
else each `allow` pair that allows no import (pair order). -/
def checkLayers (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId)) :
    Except (Array String) (Array Violation) :=
  match p.layers? with
  | none => .ok #[]
  | some r =>
    match resolveLayers g p sets r with
    | .error es => .error es
    | .ok d =>
      let (vs, used) := evalLayers g d
      let errs :=
        (r.allow.zip used).filterMap fun (q, u) =>
          if u then none
          else
            some <|
              Policy.locate p.path q.pos? <|
              s!"layers: allow entry {q.index} ({q.text}) allows nothing: no module of a \
                  package in layer '{q.importer}' imports a module of another package in layer \
                  '{q.imported}'"
      if errs.isEmpty then .ok vs else .error errs

end LeanDeny
