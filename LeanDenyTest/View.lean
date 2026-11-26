import LeanDenyTest.Query
import LeanDenyTest.Graph

/-!
Tests of `LeanDeny.Graph.collapse` on a hand-written graph: shared modules
counted in each owner, self-edges dropped above module level, externals
grouped by their first name component, empty targets and packages kept as
nodes, and every ordering rule.
-/

open Lean LeanDeny.Graph LeanDenyTest.Query

namespace LeanDenyTest.View

/-- Package `p`: libraries `L1` (`A`, `S`) and `L2` (`B`, `S`) sharing `S`,
an executable `E` with root `Main`, and an empty library `LEmpty`. Package
`q`: library `Q` (`Q.X`, `Q.Y`, `R`); `Q.Y` is `prelude`, and `R` sorts
before `Q.X` by `Name.cmp` (so in `Graph.edges`) but after it as a string.
Package `r` has no targets. -/
def modules : Array M := #[
  { name := `A, target := `L1, imports := #[plain `S, plain `Q.X] },
  { name := `S, target := `L1, imports := #[plain `Lean.Data.Json] },
  { name := `S, target := `L2, imports := #[plain `Lean.Data.Json] },
  { name := `B, target := `L2, imports := #[plain `A, (`S, { isMeta := true })] },
  { name := `Main, kind := .exe, target := `E, imports := #[plain `A] },
  { name := `Q.X, pkg := `q, target := `Q, imports := #[plain `Q.Y, plain `Lean.Elab.Command] },
  { name := `Q.Y, pkg := `q, target := `Q, isPrelude := true },
  { name := `R, pkg := `q, target := `Q }
]

def pkg (n : Name) (libs : Array Name) (exes : Array (Name × Name)) : PackageInfo :=
  { name := n, dir := s!"/ws/{n}", configFile := s!"/ws/{n}/lakefile.toml", keywords := #[]
    remoteUrl? := none, requires := #[], isRoot := false
    libs := libs.map fun l => { name := l, roots := #[l], globs := #[] }
    exes := exes.map fun (x, r) => { name := x, root := r } }

def packages : Array PackageInfo := #[
  pkg `p #[`L1, `L2, `LEmpty] #[(`E, `Main)],
  pkg `q #[`Q] #[],
  pkg `r #[] #[]
]

/-- A node as `id kind name package [members]`. -/
def renderNode (g : Graph) (n : ViewNode) : String :=
  let ms := n.members.map fun i => (g.nodes[i]?.map (·.name.toString)).getD "?"
  s!"{n.id} {n.kind} {n.name} {(n.package?.map plainName).getD "-"} {ms}"

/-- An edge as `src -> dst: witnesses`, each witness `Importer>[meta ]Imported`. -/
def renderEdge (g : Graph) (v : View) (e : ViewEdge) : String :=
  let id (i : Nat) := (v.nodes[i]?.map (·.id)).getD "?"
  let name (i : NodeId) := (g.nodes[i]?.map (·.name.toString)).getD "?"
  let ws := e.imports.map fun i => match g.edges[i]? with
    | some x => s!"{name x.src}>{if x.kind.isMeta then "meta " else ""}{name x.dst}"
    | none => "?"
  s!"{id e.src} -> {id e.dst}: {" ".intercalate ws.toList}"

def libNodes : Array String := #[
  "p/exe/E exe E p #[Main]",
  "p/lib/L1 lib L1 p #[A, S]",
  "p/lib/L2 lib L2 p #[B, S]",
  "p/lib/LEmpty lib LEmpty p #[]",
  "q/lib/Q lib Q q #[Q.X, Q.Y, R]",
  "external/Init external Init - #[Init]",
  "external/Lean external Lean - #[Lean.Data.Json, Lean.Elab.Command]"
]

def libEdges : Array String := #[
  "p/exe/E -> p/lib/L1: Main>A",
  "p/exe/E -> external/Init: Main>Init Main>meta Init",
  "p/lib/L1 -> p/lib/L2: A>S",
  "p/lib/L1 -> q/lib/Q: A>Q.X",
  "p/lib/L1 -> external/Init: A>Init A>meta Init S>Init S>meta Init",
  "p/lib/L1 -> external/Lean: S>Lean.Data.Json",
  "p/lib/L2 -> p/lib/L1: B>A B>meta S",
  "p/lib/L2 -> external/Init: B>Init B>meta Init S>Init S>meta Init",
  "p/lib/L2 -> external/Lean: S>Lean.Data.Json",
  "q/lib/Q -> external/Init: Q.X>Init Q.X>meta Init R>Init R>meta Init",
  "q/lib/Q -> external/Lean: Q.X>Lean.Elab.Command"
]

def packageNodes : Array String := #[
  "p package p p #[A, B, Main, S]",
  "q package q q #[Q.X, Q.Y, R]",
  "r package r r #[]",
  "external/Init external Init - #[Init]",
  "external/Lean external Lean - #[Lean.Data.Json, Lean.Elab.Command]"
]

def packageEdges : Array String := #[
  "p -> q: A>Q.X",
  "p -> external/Init: A>Init A>meta Init B>Init B>meta Init Main>Init Main>meta Init S>Init S>meta Init",
  "p -> external/Lean: S>Lean.Data.Json",
  "q -> external/Init: Q.X>Init Q.X>meta Init R>Init R>meta Init",
  "q -> external/Lean: Q.X>Lean.Elab.Command"
]

def moduleNodes : Array String := #[
  "A module A p #[A]",
  "B module B p #[B]",
  "Main module Main p #[Main]",
  "Q.X module Q.X q #[Q.X]",
  "Q.Y module Q.Y q #[Q.Y]",
  "R module R q #[R]",
  "S module S p #[S]",
  "Init external Init - #[Init]",
  "Lean.Data.Json external Lean.Data.Json - #[Lean.Data.Json]",
  "Lean.Elab.Command external Lean.Elab.Command - #[Lean.Elab.Command]"
]

def moduleEdges : Array String := #[
  "A -> Q.X: A>Q.X",
  "A -> S: A>S",
  "A -> Init: A>Init A>meta Init",
  "B -> A: B>A",
  "B -> S: B>meta S",
  "B -> Init: B>Init B>meta Init",
  "Main -> A: Main>A",
  "Main -> Init: Main>Init Main>meta Init",
  "Q.X -> Q.Y: Q.X>Q.Y",
  "Q.X -> Init: Q.X>Init Q.X>meta Init",
  "Q.X -> Lean.Elab.Command: Q.X>Lean.Elab.Command",
  "R -> Init: R>Init R>meta Init",
  "S -> Init: S>Init S>meta Init",
  "S -> Lean.Data.Json: S>Lean.Data.Json"
]

def viewFailures (g : Graph) (lvl : LeanDeny.Graph.Level) (nodes edges : Array String) : Array String :=
  let v := collapse g lvl
  LeanDenyTest.Graph.compare s!"{lvl} nodes" (v.nodes.map (renderNode g)) nodes ++
  LeanDenyTest.Graph.compare s!"{lvl} edges" (v.edges.map (renderEdge g v)) edges ++
  (if v.level == lvl then #[] else #[s!"{lvl}: the view has level {v.level}"]) ++
  (v.edges.filterMap fun e =>
    if e.count == 0 then some s!"{lvl}: an edge without imports" else none)

/-- `Level.parse?` and `toString` round-trip; anything else is rejected. -/
def levelFailures : Array String :=
  let all := #[LeanDeny.Graph.Level.module, .lib, .package]
  (all.filterMap fun l =>
    if LeanDeny.Graph.Level.parse? (toString l) == some l then none else some s!"Level {l} does not round-trip") ++
  (#["", "crate", "Module", "modules"].filterMap fun s =>
    if (LeanDeny.Graph.Level.parse? s).isNone then none else some s!"Level.parse? accepts {repr s}")

def run : Array String :=
  match mkGraph modules with
  | .error e => #[s!"building the view test graph failed: {e}"]
  | .ok g =>
    let g := { g with packages }
    levelFailures ++
    viewFailures g .module moduleNodes moduleEdges ++
    viewFailures g .lib libNodes libEdges ++
    viewFailures g .package packageNodes packageEdges

end LeanDenyTest.View
