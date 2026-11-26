import LeanDeny

/-!
Graph checks: load `tests/fixtures/spike-ws` and `tests/fixtures/graph-ws`
with `LeanDeny.Graph.load`, through the in-process Lake API and the header
parser, and compare the in-memory graph with what is expected, exactly:
every node, every edge with its keywords, file and line, the package
metadata, and queries on the result. Also the no-manifest guard.
-/

open Lean LeanDeny.Graph LeanDeny.Graph.LakeApi

namespace LeanDenyTest.Graph

/-- `path` relative to the graph's root (`.` for the root itself). -/
def rel (g : Graph) (path : System.FilePath) : String :=
  g.relPath path

def unescaped (n : Name) : String :=
  n.toString (escape := false)

/-- A node as `Name origin file module-or-- prelude-or--`, where origin is
`external` or the owners as `pkg/kind/target`, comma-separated. -/
def renderNode (g : Graph) (n : Node) : String :=
  let origin :=
    match n.origin with
    | .external => "external"
    | .workspace os =>
      ",".intercalate
        (os.map fun (o : Owner) => s!"{unescaped o.pkg}/{o.kind}/{unescaped o.target}").toList
  let file := (n.file?.map (rel g)).getD "-"
  s!"{n.name} {origin} {file} {if n.isModule then "module" else "-"} \
    {if n.isPrelude then "prelude" else "-"}"

/-- An edge as `Src -> Dst [keywords] exported? implicit? file:line`. -/
def renderEdge (g : Graph) (e : Edge) : String :=
  let name (i : NodeId) := toString (g.nodes[i]?.map (·.name) |>.getD `«?»)
  let kws :=
    (if e.kind.isPublic then ["public"] else []) ++ (if e.kind.isMeta then ["meta"] else []) ++
      (if e.kind.isAll then ["all"] else [])
  let flags :=
    (if e.isExported then ["exported"] else []) ++ (if e.implicit then ["implicit"] else [])
  s!"{name e.src} -> {name e.dst} [{",".intercalate kws}] {" ".intercalate flags} \
    {rel g e.file}:{(e.line?.map toString).getD "-"}"

/-- A package as `name root? dir keywords requires libs exes`. -/
def renderPackage (g : Graph) (p : PackageInfo) : String :=
  let libs := p.libs.map fun l => s!"{l.name}{l.roots}{l.globs}"
  let exes := p.exes.map fun x => s!"{unescaped x.name}:{x.root}"
  s!"{unescaped p.name} {if p.isRoot then "root" else "dep"} {rel g p.dir} \
    {rel g p.configFile} {p.keywords} {p.requires.map unescaped} {libs} {exes} {p.remoteUrl?}"

/-- Compare two lists line by line, describing the first few differences. -/
def compare (what : String) (got want : Array String) : Array String :=
  Id.run do
    if got == want then
      return #[]
    let mut fs := #[s!"{what} differ ({want.size} expected, {got.size} found)"]
    for i in [0:max got.size want.size] do
      let g := got[i]?.getD "(none)"
      let w := want[i]?.getD "(none)"
      if g != w then
        fs := fs.push s!"  {what} {i}: expected {w}\n      got      {g}"
    return fs

def expectStr (what got want : String) : Array String :=
  if got == want then #[] else #[s!"{what}: expected {want}, got {got}"]

def spikeNodes : Array String :=
  #["Init external - - -", "Fix.A spike-ws/lib/Fix Fix/A.lean module -",
    "Fix.B spike-ws/lib/Fix Fix/B.lean - -", "Fix.C spike-ws/lib/Fix Fix/C.lean - prelude",
    "Fix.D spike-ws/lib/Fix Fix/D.lean - -"]

def spikeEdges : Array String :=
  #["Fix.A -> Init [] exported implicit Fix/A.lean:-",
    "Fix.A -> Init [meta] exported implicit Fix/A.lean:-",
    "Fix.A -> Fix.B [public] exported Fix/A.lean:3", "Fix.A -> Fix.C [meta]  Fix/A.lean:4",
    "Fix.A -> Fix.D [all]  Fix/A.lean:5", "Fix.B -> Init [] exported implicit Fix/B.lean:-",
    "Fix.B -> Init [meta] exported implicit Fix/B.lean:-",
    "Fix.B -> Fix.C [] exported Fix/B.lean:1", "Fix.D -> Init [] exported implicit Fix/D.lean:-",
    "Fix.D -> Init [meta] exported implicit Fix/D.lean:-"]

/-- The failures of `spike-ws`'s graph: four modules of one library plus
`Init`, `Fix.A`'s three import kinds, `Fix.C`'s `prelude`. -/
def spikeFailures (g : Graph) : Array String :=
  compare "spike-ws nodes" (g.nodes.map (renderNode g)) spikeNodes ++
    compare "spike-ws edges" (g.edges.map (renderEdge g)) spikeEdges

/-- `graph-ws`'s ten workspace modules and three external targets, in
`Name.cmp` order (shallower names first). -/
def graphWsNodes : Array String :=
  #["App graph-ws/lib/App App.lean - -", "AppTest graph-ws/lib/AppTest AppTest.lean - -",
    "Base base/lib/Base base/Base.lean module -", "Init external - - -",
    "Main graph-ws/exe/graph-app Main.lean - -",
    "App.Shared graph-ws/lib/App,graph-ws/lib/AppTest App/Shared.lean - -",
    "Core.Api core/lib/Core core/Core/Api.lean module -",
    "Core.Impl core/lib/Core core/Core/Impl.lean module -",
    "Core.Macros core/lib/Core core/Core/Macros.lean module -",
    "Core.Prim core/lib/Core core/Core/Prim.lean module prelude",
    "Core.Types core/lib/Core core/Core/Types.lean module -", "Lean.Data.Json external - - -",
    "Lean.Elab.Command external - - -"]

def graphWsEdges : Array String :=
  #["App -> Init [] exported implicit App.lean:-",
    "App -> Init [meta] exported implicit App.lean:-", "App -> App.Shared [] exported App.lean:1",
    "App -> Core.Api [] exported App.lean:2", "AppTest -> Init [] exported implicit AppTest.lean:-",
    "AppTest -> Init [meta] exported implicit AppTest.lean:-",
    "AppTest -> App [] exported AppTest.lean:1", "AppTest -> App.Shared [] exported AppTest.lean:2",
    "Base -> Init [] exported implicit base/Base.lean:-",
    "Base -> Init [meta] exported implicit base/Base.lean:-",
    "Main -> Init [] exported implicit Main.lean:-",
    "Main -> Init [meta] exported implicit Main.lean:-", "Main -> App [] exported Main.lean:4",
    "App.Shared -> Init [] exported implicit App/Shared.lean:-",
    "App.Shared -> Init [meta] exported implicit App/Shared.lean:-",
    "App.Shared -> Lean.Data.Json [] exported App/Shared.lean:1",
    "Core.Api -> Init [] exported implicit core/Core/Api.lean:-",
    "Core.Api -> Init [meta] exported implicit core/Core/Api.lean:-",
    "Core.Api -> Core.Types [public] exported core/Core/Api.lean:5",
    "Core.Api -> Core.Impl [all]  core/Core/Api.lean:5",
    "Core.Api -> Core.Macros [public,meta] exported core/Core/Api.lean:6",
    "Core.Api -> Base [meta]  core/Core/Api.lean:8",
    "Core.Impl -> Init [] exported implicit core/Core/Impl.lean:-",
    "Core.Impl -> Init [meta] exported implicit core/Core/Impl.lean:-",
    "Core.Impl -> Core.Types []  core/Core/Impl.lean:3",
    "Core.Macros -> Init [] exported implicit core/Core/Macros.lean:-",
    "Core.Macros -> Init [meta] exported implicit core/Core/Macros.lean:-",
    "Core.Macros -> Lean.Elab.Command [public] exported core/Core/Macros.lean:3",
    "Core.Types -> Init [] exported implicit core/Core/Types.lean:-",
    "Core.Types -> Init [meta] exported implicit core/Core/Types.lean:-",
    "Core.Types -> Core.Prim []  core/Core/Types.lean:3"]

def graphWsPackages : Array String :=
  #["graph-ws root . lakefile.toml #[] #[core] #[App#[App]#[App.*], AppTest#[AppTest]#[AppTest, App.Shared]] #[graph-app:Main] none",
    "core dep core core/lakefile.toml #[kernel, api] #[base] #[Core#[Core]#[Core.+]] #[] none",
    "base dep base base/lakefile.toml #[] #[] #[Base#[Base]#[Base]] #[] none"]

/-- The failures of `graph-ws`'s graph: the exact nodes, edges and
packages, then queries on them. -/
def graphWsFailures (g : Graph) : Array String :=
  Id.run do
    let mut fs :=
      compare "graph-ws nodes" (g.nodes.map (renderNode g)) graphWsNodes ++
        compare "graph-ws edges" (g.edges.map (renderEdge g)) graphWsEdges ++
        compare "graph-ws packages" (g.packages.map (renderPackage g)) graphWsPackages
    let id (n : Name) : NodeId := (g.find? n).getD 999999
    let path := g.shortestPath? #[id `Main] (· == id `Lean.Elab.Command)
    fs :=
      fs ++
        compare "shortest path Main to Lean.Elab.Command" ((path.getD #[]).map (renderEdge g))
          #["Main -> App [] exported Main.lean:4", "App -> Core.Api [] exported App.lean:2",
            "Core.Api -> Core.Macros [public,meta] exported core/Core/Api.lean:6",
            "Core.Macros -> Lean.Elab.Command [public] exported core/Core/Macros.lean:3"]
    fs :=
      fs ++
        compare "importers of App.Shared" ((g.importers (id `App.Shared)).map (renderEdge g))
          #["App -> App.Shared [] exported App.lean:1",
            "AppTest -> App.Shared [] exported AppTest.lean:2"]
    let names (ns : Array NodeId) := toString (ns.map fun i => (g.nodes[i]?.map (·.name)).getD `«?»)
    fs := fs ++ expectStr "reachable from Base" (names (g.reachable #[id `Base])) "#[Init]"
    fs :=
      fs ++
        expectStr "App reaches Core.Impl through import all"
          (toString ((g.reachable #[id `App]).contains (id `Core.Impl))) "true"
    fs :=
      fs ++
        expectStr "App reaches Core.Impl through exported imports"
          (toString ((g.reachable #[id `App] (·.isExported)).contains (id `Core.Impl))) "false"
    fs :=
      fs ++
        expectStr "App reaches Core.Types through exported imports"
          (toString ((g.reachable #[id `App] (·.isExported)).contains (id `Core.Types))) "true"
    return fs

/-- Whether `s` contains `sub`. -/
def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- The failures of the no-manifest guard in `loadWs`: a copy of the fixture
without its `lake-manifest.json` must be refused before Lake runs, so Lake's
`updateAndMaterialize` fallback never writes a manifest or `.lake/` into it. -/
def noManifestFailures (fixture : System.FilePath) : IO (Array String) :=
  IO.FS.withTempDir fun tmp => do
    IO.FS.createDirAll (tmp / "Fix")
    IO.FS.writeFile (tmp / "lakefile.toml") (← IO.FS.readFile (fixture / "lakefile.toml"))
    for m in ["A", "B", "C", "D"] do
      let f := s!"{m}.lean"
      IO.FS.writeFile (tmp / "Fix" / f) (← IO.FS.readFile (fixture / "Fix" / f))
    let mut fs : Array String := #[]
    match ← (snapshot tmp).toBaseIO with
    | .ok (snap, _) =>
      fs :=
        fs.push
          s!"loading a workspace without {Lake.defaultManifestFile} should fail, \
        but resolved {snap.modules.size} modules"
    | .error e =>
      let msg := toString e
      unless hasSubstr msg s!"has no {Lake.defaultManifestFile}" do
        fs := fs.push s!"expected the no-manifest guard's error, got: {msg}"
    if ← (tmp / Lake.defaultManifestFile).pathExists then
      fs := fs.push s!"{Lake.defaultManifestFile} was written into the manifest-less workspace"
    if ← (tmp / ".lake").pathExists then
      fs := fs.push ".lake/ was created in the manifest-less workspace"
    return fs

/-- Load the fixture workspace `name` and check its graph with `check`. -/
def checkFixture (root : System.FilePath) (name : String) (check : Graph → Array String) :
    IO (Array String) := do
  match ← (load (root / "tests" / "fixtures" / name)).toBaseIO with
  | .ok (g, _) =>
    return check g
  | .error e =>
    return #[s!"loading {name} failed: {e}"]

/-- The failures of `failureMessages`, which picks what a load reports for
its failed Lake fetches. The `bad-header` and `bad-headers-multi` fixtures
cover real failures; these cover the logs no fixture produces. -/
def failureMessagesFailures : Array String :=
  let silent := "a Lake fetch failed without a message"
  let check (what : String) (failures : Array (Array (Bool × String))) (want : Array String) :=
    compare s!"failure messages ({what})" (failureMessages failures) want
  check "no failures" #[] #[] ++
    check "errors only" #[#[(false, "info"), (true, "e1"), (false, "warn"), (true, "e2")]]
      #["e1", "e2"] ++
    check "no error-level entry" #[#[(false, "warn"), (false, "info")]] #["warn", "info"] ++
    check "empty log" #[#[]] #[silent] ++
    check "empty log among others" #[#[(true, "a")], #[], #[(false, "b")]] #["a", silent, "b"] ++
    check "order and dedup" #[#[(true, "b")], #[(true, "a"), (true, "b")], #[(true, "b")]]
      #["b", "a"]

/-- Run the graph checks against the fixtures under `<root>/tests/fixtures`. -/
def run (root : System.FilePath) : IO (Array String) := do
  return failureMessagesFailures ++ (← checkFixture root "spike-ws" spikeFailures) ++
      (← checkFixture root "graph-ws" graphWsFailures) ++
      (← noManifestFailures (root / "tests" / "fixtures" / "spike-ws"))

end LeanDenyTest.Graph
