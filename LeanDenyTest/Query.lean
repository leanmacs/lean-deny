import LeanDeny

/-!
Tests of the graph builder (`LeanDeny.Graph.build`) and the queries
(`LeanDeny.Graph.Query`) on graphs built from hand-written snapshots, with
no Lake involved.
-/

open Lean LeanDeny.Graph

namespace LeanDenyTest.Query

/-- A hand-written module: its explicit imports (the `n`th on line `n`),
which target lists it, and its header's shape. -/
structure M where
  name : Name
  imports : Array (Name × ImportKind) := #[]
  pkg : Name := `p
  kind : TargetKind := .lib
  target : Name := `L
  file? : Option String := none
  isModule : Bool := false
  isPrelude : Bool := false

def M.file (m : M) : System.FilePath :=
  m.file?.getD s!"{m.name}.lean"

/-- The snapshot and header map Lake and the header parser would give for
`ms`. An import of a library module resolves to its first library, as Lake
picks one. -/
def mkInput (ms : Array M) : Snapshot × Std.HashMap Name (Array HeaderImport) :=
  Id.run do
    let resolve (n : Name) : Option (Name × Name) :=
      (ms.find? fun m => m.name == n && m.kind == .lib).map fun m => (m.pkg, m.target)
    let mut mods := #[]
    let mut hdrs : Std.HashMap Name (Array HeaderImport) := {}
    for m in ms do
      let implicit : Array RawImport :=
        if m.isPrelude then #[]
        else
          #[{ module := `Init, isExported := true, isMeta := false, importAll := false,
              resolved? := none },
            { module := `Init, isExported := true, isMeta := true, importAll := false,
              resolved? := none }]
      let explicit :=
        m.imports.map fun (n, k) =>
          { module := n, isExported := k.isPublic || !m.isModule, isMeta := k.isMeta,
            importAll := k.isAll
            resolved? := resolve n : RawImport }
      mods :=
        mods.push
          { name := m.name, owner := { pkg := m.pkg, kind := m.kind, target := m.target }
            file := m.file, isModule := m.isModule, imports := implicit ++ explicit }
      hdrs :=
        hdrs.insert m.name <|
          (m.imports.zipIdx.map fun ((n, k), i) => { module := n, kind := k, line := i + 1 })
    return ({ root := "/ws", packages := #[], modules := mods }, hdrs)

def mkGraph (ms : Array M) : Except String Graph :=
  let (s, h) := mkInput ms
  build s h

def plain (n : Name) : Name × ImportKind :=
  (n, {})

/-- A chain as `A>B>C`. -/
def renderPath (g : Graph) : Option (Array Edge) → String
  | none => "none"
  | some es =>
    let name (i : NodeId) := toString (g.nodes[i]?.map (·.name) |>.getD `«?»)
    match es[0]? with
    | none => "(empty)"
    | some e0 => ">".intercalate (name e0.src :: (es.map (name ·.dst)).toList)

/-- An edge as `Src>Dst:line` (`-` for no line). -/
def renderEdge (g : Graph) (e : Edge) : String :=
  let name (i : NodeId) := toString (g.nodes[i]?.map (·.name) |>.getD `«?»)
  s!"{name e.src}>{name e.dst}{if e.kind.isMeta then "[meta]" else ""}:{e.line?.map toString |>.getD "-"}"

def names (g : Graph) (ns : Array NodeId) : Array String :=
  ns.map fun i => toString (g.nodes[i]?.map (·.name) |>.getD `«?»)

/-- The main test graph:

- `S` imports `A`, then `B`; both import `T`: two equally short chains.
- `P1` reaches `T` in three steps, `Q` in one.
- `C1` and `C2` import each other.
- `K` reaches `T` only through `import all`.
- `Pre` is `prelude` and imports nothing.
- `Ext` imports the external `Lean.Data.Json`. -/
def main : Array M :=
  #[{ name := `S, imports := #[plain `A, plain `B] }, { name := `A, imports := #[plain `T] },
    { name := `B, imports := #[plain `T] }, { name := `T },
    { name := `P1, imports := #[plain `P2] }, { name := `P2, imports := #[plain `P3] },
    { name := `P3, imports := #[plain `T] }, { name := `Q, imports := #[plain `T] },
    { name := `C1, imports := #[plain `C2] }, { name := `C2, imports := #[plain `C1] },
    { name := `K, isModule := true,
      imports := #[(`T, { isAll := true }), (`S, { isPublic := true })] },
    { name := `Pre, isPrelude := true }, { name := `Ext, imports := #[plain `Lean.Data.Json] }]

def check (fs : Array String) (what : String) (got want : String) : Array String :=
  if got == want then fs else fs.push s!"{what}: expected {want}, got {got}"

def queryFailures (g : Graph) : Array String :=
  Id.run do
    let mut fs := #[]
    let id (n : Name) : NodeId := (g.find? n).getD 999999
    let is (n : Name) : NodeId → Bool := (· == id n)
    -- Nodes, in `Name.cmp` order: it compares prefixes first, so a shallower
    -- name sorts before a deeper one (`T` before `Lean.Data.Json`).
    fs :=
      check fs "node order" (toString (g.nodes.map (·.name)))
        "#[A, B, C1, C2, Ext, Init, K, P1, P2, P3, Pre, Q, S, T, Lean.Data.Json]"
    fs :=
      check fs "external nodes" (toString ((g.nodes.filter (·.origin == .external)).map (·.name)))
        "#[Init, Lean.Data.Json]"
    fs := check fs "prelude nodes" (toString ((g.nodes.filter (·.isPrelude)).map (·.name))) "#[Pre]"
    fs := check fs "find? of an unknown module" (toString (g.find? `Nope)) "none"
    -- Direct imports and importers.
    fs :=
      check fs "imports S" (toString ((g.imports (id `S)).map (renderEdge g)))
        "#[S>Init:-, S>Init[meta]:-, S>A:1, S>B:2]"
    fs := check fs "imports Pre" (toString ((g.imports (id `Pre)).map (renderEdge g))) "#[]"
    fs :=
      check fs "importers T" (toString ((g.importers (id `T)).map (renderEdge g)))
        "#[A>T:1, B>T:1, K>T:1, P3>T:1, Q>T:1]"
    fs := check fs "importers S" (toString ((g.importers (id `S)).map (renderEdge g))) "#[K>S:2]"
    let kEdges := g.imports (id `K)
    fs :=
      check fs "K's import all is not exported"
        (toString (kEdges.map fun e => (e.kind.isAll, e.isExported)))
        "#[(false, true), (false, true), (true, false), (false, true)]"
    -- Shortest paths.
    fs :=
      check fs "diamond: the first chain in source order"
        (renderPath g (g.shortestPath? #[id `S] (is `T))) "S>A>T"
    fs :=
      check fs "the shorter chain, from the second source"
        (renderPath g (g.shortestPath? #[id `P1, id `Q] (is `T))) "Q>T"
    fs :=
      check fs "sources given in any order, with duplicates"
        (renderPath g (g.shortestPath? #[id `Q, id `P1, id `Q] (is `T))) "Q>T"
    fs :=
      check fs "a source that is also a target is found through an edge"
        (renderPath g (g.shortestPath? #[id `A, id `S] (is `A))) "S>A"
    fs :=
      check fs "a source that is the only target, not imported"
        (renderPath g (g.shortestPath? #[id `A] (is `A))) "none"
    fs := check fs "an unreachable target" (renderPath g (g.shortestPath? #[id `T] (is `S))) "none"
    fs := check fs "a cycle terminates" (renderPath g (g.shortestPath? #[id `C1] (is `T))) "none"
    fs :=
      check fs "a cycle back to the source" (renderPath g (g.shortestPath? #[id `C1] (is `C1)))
        "C1>C2>C1"
    fs :=
      check fs "an external target" (renderPath g (g.shortestPath? #[id `Ext] (is `Lean.Data.Json)))
        "Ext>Lean.Data.Json"
    fs :=
      check fs "the only chain goes through import all"
        (renderPath g (g.shortestPath? #[id `K] (is `T))) "K>T"
    fs :=
      check fs "follow skips import all: a longer chain"
        (renderPath g (g.shortestPath? #[id `K] (is `T) (follow := (!·.kind.isAll)))) "K>S>A>T"
    fs :=
      check fs "follow excludes the only chain to A"
        (renderPath g (g.shortestPath? #[id `K] (is `A) (follow := (!·.kind.isPublic)))) "none"
    -- Reachable sets.
    fs := check fs "reachable from S" (toString (names g (g.reachable #[id `S]))) "#[A, B, Init, T]"
    fs := check fs "reachable from T" (toString (names g (g.reachable #[id `T]))) "#[Init]"
    fs := check fs "reachable from Pre" (toString (names g (g.reachable #[id `Pre]))) "#[]"
    fs :=
      check fs "reachable from C1" (toString (names g (g.reachable #[id `C1]))) "#[C1, C2, Init]"
    fs :=
      check fs "reachable from K, exported edges only"
        (toString (names g (g.reachable #[id `K] (·.isExported)))) "#[A, B, Init, S, T]"
    fs :=
      check fs "reachable from K, no implicit edges, no import all"
        (toString (names g (g.reachable #[id `K] fun e => !e.implicit && !e.kind.isAll)))
        "#[A, B, S, T]"
    return fs

/-- One module listed by two libraries and an executable of its package. -/
def ownerFailures : Array String :=
  match
    mkGraph
      #[{ name := `Sh, kind := .exe, target := `app }, { name := `Sh, target := `L2 },
        { name := `Sh, target := `L1 }, { name := `U, target := `L1, imports := #[plain `Sh] }] with
  | .error e => #[s!"owners: unexpected error {e}"]
  | .ok g =>
    let fs := check #[] "nodes" (toString (g.nodes.map (·.name))) "#[Init, Sh, U]"
    let owners :=
      match g.nodes[1]?.map (·.origin) with
      | some (Origin.workspace os) => toString (os.map fun o => s!"{o.pkg}/{o.kind}/{o.target}")
      | _ => "not a workspace node"
    let fs := check fs "owners" owners "#[p/lib/L1, p/lib/L2, p/exe/app]"
    check fs "edges" (toString (g.edges.map (renderEdge g)))
      "#[Sh>Init:-, Sh>Init[meta]:-, U>Init:-, U>Init[meta]:-, U>Sh:1]"

/-- `(case, input, expected error)`. -/
def errorCases : Array (String × (Snapshot × Std.HashMap Name (Array HeaderImport)) × String) :=
  #[("one module name from two packages",
      mkInput
        #[{ name := `Dup, pkg := `a, target := `A, file? := some "/a/Dup.lean" },
          { name := `Dup, pkg := `b, target := `B, file? := some "/b/Dup.lean" }],
      "module Dup is provided by both a/A (/a/Dup.lean) and b/B (/b/Dup.lean)"),
    ("one module name from two files of one package",
      mkInput
        #[{ name := `Dup, target := `A, file? := some "/p/Dup.lean" },
          { name := `Dup, kind := .exe, target := `e, file? := some "/p/exe/Dup.lean" }],
      "module Dup is provided by both p/A (/p/Dup.lean) and p/e (/p/exe/Dup.lean)"),
    ("an import Lake resolves to a module with no file",
      let (s, h) := mkInput #[{ name := `X, imports := #[plain `Missing] }]
      let s :=
        { s with
          modules :=
            s.modules.map fun m =>
              { m with
                imports :=
                  m.imports.map fun i =>
                    if i.module == `Missing then { i with resolved? := some (`p, `L) } else i } }
      (s, h),
      "X.lean:1: import of Missing: Lake resolves it to library L of package p, \
      but no such module file exists"),
    ("the header parse names another module",
      let (s, h) := mkInput #[{ name := `X, imports := #[plain `A] }]
      (s, h.insert `X #[{ module := `B, kind := {}, line := 1 }]),
      "internal error: X.lean: the import positions disagree with Lake's header"),
    ("the header parse misses an import",
      let (s, h) := mkInput #[{ name := `X, imports := #[plain `A, plain `B] }]
      (s, h.insert `X #[{ module := `A, kind := {}, line := 1 }]),
      "internal error: X.lean: the import positions disagree with Lake's header"),
    ("the header parse has other keywords",
      let (s, h) :=
        mkInput #[{ name := `X, isModule := true, imports := #[(`A, { isPublic := true })] }]
      (s, h.insert `X #[{ module := `A, kind := {}, line := 1 }]),
      "internal error: X.lean: the import positions disagree with Lake's header"),
    ("no header was parsed",
      let (s, _) := mkInput #[{ name := `X }]
      (s, {}),
      "internal error: X.lean: no header was parsed")]

def errorFailures : Array String :=
  Id.run do
    let mut fs := #[]
    for (name, (s, h), want) in errorCases do
      match build s h with
      | .ok _ =>
        fs := fs.push s!"{name}: expected the error {repr want}, but the build succeeded"
      | .error e =>
        unless e == want do
          fs := fs.push s!"{name}: expected {repr want}, got {repr e}"
    return fs

def run : Array String :=
  let main :=
    match mkGraph main with
    | .ok g => queryFailures g
    | .error e => #[s!"building the main test graph failed: {e}"]
  main ++ ownerFailures ++ errorFailures

end LeanDenyTest.Query
