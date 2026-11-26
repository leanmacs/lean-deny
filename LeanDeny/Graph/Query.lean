import LeanDeny.Graph.Model

/-!
# Queries on the module graph

Lookups, direct imports and importers, and breadth-first search for a
shortest import chain. Pure, deterministic, O(V+E) per search.
-/

open Lean

namespace LeanDeny.Graph

/-- The node of module `m`, if the graph has one. -/
def Graph.find? (g : Graph) (m : Name) : Option NodeId :=
  g.index[m]?

/-- The direct imports of node `n`, in source order (the implicit `Init`
pair first). -/
def Graph.imports (g : Graph) (n : NodeId) : Array Edge :=
  (g.out[n]?.getD #[]).filterMap (g.edges[·]?)

/-- The imports of node `n` by other nodes, by (importer, position). -/
def Graph.importers (g : Graph) (n : NodeId) : Array Edge :=
  (g.inc[n]?.getD #[]).filterMap (g.edges[·]?)

/-- Breadth-first search, layer by layer, from all of `srcs` at once,
walking only edges that satisfy `follow`. Each newly reached node is
recorded with the edge that first reached it and its distance. With
`isTarget?`, stops at the first target reached and returns it; otherwise
returns `none` after reaching everything.

Sources are not marked reached up front: a source is reached only when an
edge leads to it, so a path always has at least one edge. -/
private def bfs (g : Graph) (srcs : Array NodeId) (follow : Edge → Bool)
    (isTarget? : Option (NodeId → Bool)) : Option NodeId × Array (Option (Nat × Nat)) :=
  Id.run do
    let n := g.nodes.size
    -- Per node: the edge that first reached it and its distance from a source.
    let mut reached : Array (Option (Nat × Nat)) := Array.replicate n none
    let mut layer := (srcs.filter (· < n)).qsort (· < ·) |>.toList.eraseDups.toArray
    let mut depth := 0
    while !layer.isEmpty do
      let mut next := #[]
      for u in layer do
        for ei in g.out[u]?.getD #[] do
          let some e := g.edges[ei]? | continue
          unless follow e do
            continue
          let v := e.dst
          if reached[v]!.isSome then
            continue
          reached := reached.set! v (some (ei, depth + 1))
          if let some isTarget := isTarget? then
            if isTarget v then
              return (some v, reached)
          next := next.push v
      layer := next
      depth := depth + 1
    return (none, reached)

/-- A shortest import chain from any of `srcs` to a node satisfying
`isTarget`, walking only edges that satisfy `follow`: its edges, in order,
at least one. `none` when no target is reachable.

Targets are checked as they are reached, layer by layer, and every node's
imports are scanned in source order, so the chain has the fewest edges and
the witness among equally short chains is fixed: the one whose source comes
first by `NodeId`, then whose imports come first in source order. A source
that is also a target is found only through an edge into it. -/
def Graph.shortestPath? (g : Graph) (srcs : Array NodeId) (isTarget : NodeId → Bool)
    (follow : Edge → Bool := fun _ => true) : Option (Array Edge) :=
  Id.run do
    let (some t, reached) := bfs g srcs follow (some isTarget) | return none
    -- Walk back exactly the target's distance: a source reached later is
    -- still where a chain from its own expansion starts.
    let mut path : Array Edge := #[]
    let mut cur := t
    let mut steps := (reached[t]!.map (·.2)).getD 0
    while steps > 0 do
      let some (ei, _) := reached[cur]! | break
      let e := g.edges[ei]!
      path := path.push e
      cur := e.src
      steps := steps - 1
    return some path.reverse

/-- Every node reachable from `srcs` through at least one edge satisfying
`follow`, sorted by `NodeId`. -/
def Graph.reachable (g : Graph) (srcs : Array NodeId) (follow : Edge → Bool := fun _ => true) :
    Array NodeId :=
  Id.run do
    let (_, reached) := bfs g srcs follow none
    let mut out := #[]
    for i in [0:reached.size] do
      if reached[i]!.isSome then
        out := out.push i
    return out

end LeanDeny.Graph
