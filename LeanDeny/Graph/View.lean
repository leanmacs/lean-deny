import LeanDeny.Graph.Model

/-!
# The graph at a level

`collapse` turns the module graph into a `View`: the same graph with its
nodes grouped by module, by Lake target, or by package. Pure. One data model
serves every level, so every rendering has one shape.

- **Module level:** one node per module, one edge per (importer, imported)
  pair, carrying the import directives behind it (`App -> Init` has two: the
  implicit plain and `meta` imports).
- **Lib level:** one node per `lean_lib` and per `lean_exe`, named
  `<pkg>/lib/<lib>` and `<pkg>/exe/<exe>`. A module listed by several targets
  is a member of each (a module shared by two libraries counts in both); an
  executable's root is a member of its `exe` node.
- **Package level:** one node per package, named after it.
- **Externals,** at lib and package level, collapse to the first component of
  their name: `Lean.Data.Json` is a member of `external/Lean`.

Every target and package is a node, even with no modules. An edge between
two groups aggregates every import from a member of one to a member of the
other; imports inside one group are dropped above module level.

Order: workspace nodes, then external ones, each by id; members by name;
edges by (source, target) position; an edge's imports by importer name, then
source order.
-/

open Lean

namespace LeanDeny.Graph

/-- How finely to group the graph. -/
inductive Level where
  | module
  | lib
  | package
  deriving BEq, Repr, Inhabited, DecidableEq

def Level.toString : Level → String
  | .module => "module"
  | .lib => "lib"
  | .package => "package"

instance : ToString Level :=
  ⟨Level.toString⟩

/-- The level a command line names (`module`, `lib` or `package`). -/
def Level.parse? : String → Option Level
  | "module" => some .module
  | "lib" => some .lib
  | "package" => some .package
  | _ => none

/-- What a view node stands for. -/
inductive ViewKind where
  /-- A workspace module (module level). -/
  | module
  /-- An external module (module level) or an external root's modules. -/
  | external
  | lib
  | exe
  | package
  deriving BEq, Repr, Inhabited

def ViewKind.toString : ViewKind → String
  | .module => "module"
  | .external => "external"
  | .lib => "lib"
  | .exe => "exe"
  | .package => "package"

instance : ToString ViewKind :=
  ⟨ViewKind.toString⟩

/-- One node of a view: a module, a target, a package, or an external
group. -/
structure ViewNode where
  /-- Unique within the view: the module name, `<pkg>/lib/<lib>`,
  `<pkg>/exe/<exe>`, `<pkg>` or `external/<Root>`. -/
  id : String
  kind : ViewKind
  /-- The module, target or package name, or the external root. -/
  name : String
  /-- The package; `none` for external nodes. -/
  package? : Option Name
  /-- The graph's nodes in this group, sorted by name. -/
  members : Array NodeId
  deriving BEq, Repr, Inhabited

/-- One edge of a view: every import from a member of `src` to a member of
`dst`. -/
structure ViewEdge where
  /-- Index into `View.nodes`. -/
  src : Nat
  /-- Index into `View.nodes`. -/
  dst : Nat
  /-- Indices into `Graph.edges`: the imports behind this edge, non-empty. -/
  imports : Array Nat
  deriving BEq, Repr, Inhabited

/-- The number of imports behind the edge. -/
def ViewEdge.count (e : ViewEdge) : Nat :=
  e.imports.size

/-- The graph grouped at one level. -/
structure View where
  level : Level
  nodes : Array ViewNode
  edges : Array ViewEdge
  deriving Repr, Inhabited

/-- A package or target name as users write it in `lakefile.toml`. -/
def plainName (n : Name) : String :=
  n.toString (escape := false)

/-- The lib-level id of target `t` of kind `k` in package `pkg`:
`<pkg>/lib/<lib>` or `<pkg>/exe/<exe>`. -/
def targetId (pkg : Name) (k : TargetKind) (t : Name) : String :=
  s!"{plainName pkg}/{k}/{plainName t}"

/-- The external group of module `m`: `external/<first component>`. -/
private def externalGroup (m : Name) : String × String :=
  let root := (m.components.head?.getD m).toString
  (s!"external/{root}", root)

/-- A group before it has a position: its node, minus its members. -/
private structure Group where
  id : String
  kind : ViewKind
  name : String
  package? : Option Name

/-- The groups a graph node belongs to at a level: none or more. -/
private def groupsOf (lvl : Level) (n : Node) : Array Group :=
  match lvl, n.origin with
  | .module, .workspace os =>
    #[{ id := n.name.toString, kind := .module, name := n.name.toString,
        package? := os[0]?.map (·.pkg) }]
  | .module, .external =>
    #[{ id := n.name.toString, kind := .external, name := n.name.toString, package? := none }]
  | _, .external =>
    let (id, root) := externalGroup n.name
    #[{ id, kind := .external, name := root, package? := none }]
  | .lib, .workspace os => os.map fun o => targetGroup o.pkg o.kind o.target
  | .package, .workspace os => (os[0]?.map fun o => #[packageGroup o.pkg]).getD #[]
where
  targetGroup (pkg : Name) (k : TargetKind) (t : Name) : Group :=
    { id := targetId pkg k t, kind := if k == .lib then .lib else .exe, name := plainName t,
      package? := some pkg }
  packageGroup (pkg : Name) : Group :=
    { id := plainName pkg, kind := .package, name := plainName pkg, package? := some pkg }

/-- The groups that exist even with no members: every target (lib level) or
package (package level) of the workspace. -/
private def declaredGroups (g : Graph) : Level → Array Group
  | .module => #[]
  | .lib =>
    g.packages.flatMap fun p =>
      p.libs.map (fun l => groupsOf.targetGroup p.name .lib l.name) ++
        p.exes.map (fun x => groupsOf.targetGroup p.name .exe x.name)
  | .package => g.packages.map fun p => groupsOf.packageGroup p.name

/-- Group the graph `g` at level `lvl`. -/
def collapse (g : Graph) (lvl : Level) : View :=
  Id.run do
    -- Collect the groups, each once, with each graph node's groups by id.
    let mut groups : Std.HashMap String Group := {}
    for gr in declaredGroups g lvl do
      groups := groups.insertIfNew gr.id gr
    let mut nodeGroups : Array (Array String) := #[]
    for n in g.nodes do
      let gs := groupsOf lvl n
      for gr in gs do
        groups := groups.insertIfNew gr.id gr
      nodeGroups := nodeGroups.push (gs.map (·.id) |>.toList.eraseDups.toArray)
    -- Workspace groups first, then external ones, each by id (ids are unique).
    let key (gr : Group) : Bool × String := (gr.kind == .external, gr.id)
    let sorted :=
      groups.toArray.map (·.2) |>.qsort fun a b =>
        let (ea, ia) := key a
        let (eb, ib) := key b
        (!ea && eb) || (ea == eb && ia < ib)
    let mut pos : Std.HashMap String Nat := {}
    for h : i in [0:sorted.size] do
      pos := pos.insert sorted[i].id i
    let posOf (n : NodeId) : Array Nat := (nodeGroups[n]?.getD #[]).filterMap (pos[·]?)
    -- Members.
    let mut members : Array (Array NodeId) := Array.replicate sorted.size #[]
    for h : n in [0:g.nodes.size] do
      for p in posOf n do
        members := members.modify p (·.push n)
    let nameStr (n : NodeId) : String := (g.nodes[n]?.map (·.name.toString)).getD ""
    let nodes :=
      sorted.zipIdx.map fun (gr, i) =>
        { id := gr.id, kind := gr.kind, name := gr.name, package? := gr.package?
          members := members[i]!.qsort fun a b => nameStr a < nameStr b : ViewNode }
    -- Edges: each import joins every group of its importer to every group of
    -- what it imports.
    let mut agg : Std.HashMap (Nat × Nat) (Array Nat) := {}
    for h : i in [0:g.edges.size] do
      let e := g.edges[i]
      for s in posOf e.src do
        for d in posOf e.dst do
          if lvl != .module && s == d then
            continue
          agg :=
            agg.alter (s, d) fun
              | none => some #[i]
              | some is => some (is.push i)
    let witnessLt (a b : Nat) : Bool :=
      let na := (g.edges[a]?.map (nameStr ·.src)).getD ""
      let nb := (g.edges[b]?.map (nameStr ·.src)).getD ""
      na < nb || (na == nb && a < b)
    let edges :=
      agg.toArray |>.qsort
          (fun ((s₁, d₁), _) ((s₂, d₂), _) => s₁ < s₂ || (s₁ == s₂ && d₁ < d₂)) |>.map
        fun ((s, d), is) => { src := s, dst := d, imports := is.qsort witnessLt }
    return { level := lvl, nodes, edges }

end LeanDeny.Graph
