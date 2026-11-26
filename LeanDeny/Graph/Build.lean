import LeanDeny.Graph.Raw

/-!
# Building the module graph

`build` turns Lake's snapshot plus each module's parsed header into a
`Graph`. It is pure: no Lake, no IO.

- **Merging.** A module listed by several targets of one package, from the
  same file, is one node with all of them as owners. The same name from two
  files or two packages is an error: Lean could not import both, and a graph
  that picked one would check the wrong code.
- **External nodes** are the direct import targets no workspace target lists
  (`Init`, `Lean.Data.Json`, …). The toolchain's own imports are not read.
- **Unresolvable imports.** An import Lake resolves to a workspace library
  (its glob matches) whose module has no file is an error, as it is for
  Lake's build. The loader has already fetched every resolved import whose
  file exists (`LakeApi.collectAll`), so an unmerged resolved import here
  means exactly that the file is missing.
- **Positions.** Each explicit import's line comes from the header parse,
  which must agree with Lake's imports in order, name and keywords. Lean's
  two implicit `Init` imports have no line.
-/

open Lean System

namespace LeanDeny.Graph

/-- `pkg/target (file)`, for error messages. -/
private def describe (m : RawModule) : String :=
  s!"{m.owner.pkg.toString (escape := false)}/{m.owner.target.toString (escape := false)} ({m.file})"

/-- Whether Lake's import is Lean's implicit plain or `meta` `Init`. -/
private def isImplicitInit (imp : RawImport) (isMeta : Bool) : Bool :=
  imp.module == `Init && imp.isMeta == isMeta && imp.isExported && !imp.importAll

/-- One workspace module after merging, before node ids exist. -/
private structure Merged where
  first : RawModule
  owners : Array Owner
  deriving Inhabited

/-- Split Lake's imports into whether the implicit `Init` pair is present
(the module is not `prelude`) and the explicit imports, each paired with its
parsed directive; fails when the two parsers disagree. -/
private def pairUp (m : RawModule) (hdr : Array HeaderImport) :
    Except String (Bool × Array (RawImport × HeaderImport)) := do
  let msg := s!"internal error: {m.file}: the import positions disagree with Lake's header"
  let imps := m.imports
  let (hasInit, explicit) ←
    if imps.size == hdr.size + 2 then
      if h : 1 < imps.size then
        if isImplicitInit imps[0] false && isImplicitInit imps[1] true then
          pure (true, imps.extract 2 imps.size)
        else
          throw msg
      else
        throw msg
    else if imps.size == hdr.size then
      pure (false, imps)
    else
      throw msg
  let pairs := explicit.zip hdr
  for (r, h) in pairs do
    unless
      r.module == h.module && r.isMeta == h.kind.isMeta && r.importAll == h.kind.isAll &&
        r.isExported == (h.kind.isPublic || !m.isModule) do
      throw msg
  return (hasInit, pairs)

/-- Build the graph from Lake's snapshot and the explicit imports of each
module's header (`HeaderParser.parse`), keyed by module name. -/
def build (snap : Snapshot) (headers : Std.HashMap Name (Array HeaderImport)) :
    Except String Graph := do
  -- 1. Merge the (target, module) rows by name.
  let mut order : Array Name := #[]
  let mut merged : Std.HashMap Name Merged := {}
  for m in snap.modules do
    match merged[m.name]? with
    | none =>
      order := order.push m.name
      merged := merged.insert m.name { first := m, owners := #[m.owner] }
    | some g =>
      unless g.first.file == m.file && g.first.owner.pkg == m.owner.pkg do
        throw s!"module {m.name} is provided by both {describe g.first} and {describe m}"
      unless g.owners.contains m.owner do
        merged := merged.insert m.name { g with owners := g.owners.push m.owner }
  -- 2.–4. Workspace nodes, external nodes, and the unresolvable-import check.
  let mut paired : Std.HashMap Name (Bool × Array (RawImport × HeaderImport)) := {}
  let mut externals : Std.HashSet Name := {}
  for n in order do
    let g := merged[n]!
    let m := g.first
    let some hdr := headers[n]?
      | throw s!"internal error: {m.file}: no header was parsed"
    let (hasInit, pairs) ← pairUp m hdr
    paired := paired.insert n (hasInit, pairs)
    if hasInit && !merged.contains `Init then
      externals := externals.insert `Init
    for (r, h) in pairs do
      if merged.contains r.module then
        continue
      if let some (pkg, lib) := r.resolved? then
        throw
            s!"{m.file}:{h.line}: import of {r.module}: Lake resolves it to library \
          {lib.toString (escape := false)} of package {pkg.toString (escape := false)}, \
          but no such module file exists"
      externals := externals.insert r.module
  let mut names := order ++ externals.toArray
  names := names.qsort (fun a b => a.cmp b == .lt)
  let index : Std.HashMap Name NodeId :=
    names.foldl (init := {}) fun (acc : Std.HashMap Name NodeId) n => acc.insert n acc.size
  let nodes : Array Node :=
    names.map fun n =>
      match merged[n]? with
      | some g =>
        let owners := g.owners.qsort Owner.lt
        { name := n, origin := .workspace owners, file? := some g.first.file
          isModule := g.first.isModule
          isPrelude := !(paired[n]?.map (·.1) |>.getD true) }
      | none => { name := n, origin := .external, file? := none }
  -- 5. Edges, by source node, then source order.
  let mut edges : Array Edge := #[]
  let mut out : Array (Array Nat) := Array.replicate nodes.size #[]
  let mut inc : Array (Array Nat) := Array.replicate nodes.size #[]
  for src in [0:nodes.size] do
    let node := nodes[src]!
    let some (hasInit, pairs) := paired[node.name]? | continue
    let file := node.file?.getD ""
    let mut es : Array Edge := #[]
    if hasInit then
      let dst := index[`Init]!
      es :=
        es.push { src, dst, kind := {}, isExported := true, file, line? := none, implicit := true }
      es :=
        es.push
          { src, dst, kind := { isMeta := true }, isExported := true, file, line? := none
            implicit := true }
    for (r, h) in pairs do
      es :=
        es.push
          { src, dst := index[r.module]!, kind := h.kind, isExported := r.isExported
            file, line? := some h.line, implicit := false }
    -- 6. Adjacency, in edge order.
    for e in es do
      out := out.modify e.src (·.push edges.size)
      inc := inc.modify e.dst (·.push edges.size)
      edges := edges.push e
  return { root := snap.root, packages := snap.packages, nodes, index, edges, out, inc }

end LeanDeny.Graph
