import Lean.Data.Json
import LeanDeny.Graph.View

/-!
# Printing a view

`render` prints a `View` as text (for people), JSON (for tools; the schema is
in `docs/graph-json.md`) or Graphviz DOT. Pure; each rendering ends in exactly
one newline and follows the view's order.

Paths are relative to the workspace root, with `/` separators (`.` for the
root itself); a path outside the root stays absolute. Module names print as
Lean writes them (`«my-mod».X`); package and target names as `lakefile.toml`
does (`my-pkg`).
-/

open Lean

namespace LeanDeny.Graph

/-- How to print the graph. -/
inductive Format where
  | text
  | json
  | dot
  deriving BEq, Repr, Inhabited, DecidableEq

def Format.toString : Format → String
  | .text => "text"
  | .json => "json"
  | .dot => "dot"

instance : ToString Format :=
  ⟨Format.toString⟩

/-- The format a command line names (`text`, `json` or `dot`). -/
def Format.parse? : String → Option Format
  | "text" => some .text
  | "json" => some .json
  | "dot" => some .dot
  | _ => none

/-- The version of the JSON schema `render` prints (`docs/graph-json.md`). -/
def jsonSchemaVersion : Nat :=
  1

/-- An import directive in Lean's syntax: `[public ][meta ]import [all ]M`. -/
def ImportKind.directive (k : ImportKind) (m : Name) : String :=
  (if k.isPublic then "public " else "") ++ (if k.isMeta then "meta " else "") ++ "import " ++
    (if k.isAll then "all " else "") ++
    m.toString

private def nodeName (g : Graph) (n : NodeId) : Name :=
  (g.nodes[n]?.map (·.name)).getD `«?»

/-- One import, for text: `<file>[:<line>]: <importer>: <directive>[ (implicit)]`. -/
def witnessLine (g : Graph) (e : Edge) : String :=
  let pos := g.relPath e.file ++ ((e.line?.map (s!":{·}")).getD "")
  s!"{pos}: {nodeName g e.src}: {e.kind.directive (nodeName g e.dst)}\
    {if e.implicit then " (implicit)" else ""}"

/-- `1 import`, `2 imports`: `n` and `word`, plural unless `n` is 1. -/
def plural (n : Nat) (word : String) : String :=
  s!"{n} {word}{if n == 1 then "" else "s"}"

/-- The package named `n`, if the graph has it. -/
private def findPackage? (g : Graph) (n : Name) : Option PackageInfo :=
  g.packages.find? (·.name == n)

/-! ## Text -/

private def textNode (g : Graph) (v : View) (n : ViewNode) : Array String :=
  match v.level with
  | .module =>
    let m? : Option Node := n.members[0]? >>= (g.nodes[·]?)
    match m?, m?.map (·.origin) with
    | some m, some (Origin.workspace os) =>
      let owners := ", ".intercalate (os.map fun o => targetId o.pkg o.kind o.target).toList
      let flags :=
        (if m.isModule then ["module"] else []) ++ (if m.isPrelude then ["prelude"] else [])
      let flags := if flags.isEmpty then "" else "; " ++ ", ".intercalate flags
      let file := (m.file?.map g.relPath).getD "?"
      #[s!"  {n.id} ({file}): {owners}{flags}"]
    | _, _ => #[s!"  {n.id}: external"]
  | _ =>
    let kws :=
      match n.kind, n.package? >>= findPackage? g with
      | .package, some p =>
        if p.keywords.isEmpty then "" else "; keywords " ++ ", ".intercalate p.keywords.toList
      | _, _ => ""
    #[s!"  {n.id}: {plural n.members.size "module"}{kws}"] ++
      n.members.map fun m => s!"    {nodeName g m}"

private def renderText (g : Graph) (v : View) : String :=
  let id (i : Nat) := (v.nodes[i]?.map (·.id)).getD "?"
  let nodes := v.nodes.flatMap (textNode g v)
  let edges :=
    v.edges.flatMap fun e =>
      #[s!"  {id e.src} -> {id e.dst} ({plural e.count "import"})"] ++
        e.imports.filterMap fun i => g.edges[i]?.map fun x => s!"    {witnessLine g x}"
  let lines :=
    #[s!"nodes ({v.nodes.size}):"] ++ nodes ++ #["", s!"edges ({v.edges.size}):"] ++ edges
  "\n".intercalate lines.toList ++ "\n"

/-! ## JSON -/

private def jStr (s : String) : Json :=
  .str s

private def jNat (n : Nat) : Json :=
  toJson n

private def jArr (xs : Array Json) : Json :=
  .arr xs

private def jStrs (xs : Array String) : Json :=
  .arr (xs.map jStr)

private def jOpt (x? : Option Json) : Json :=
  x?.getD .null

private def packageJson (g : Graph) (p : PackageInfo) : Json :=
  Json.mkObj
    [("name", jStr (plainName p.name)), ("root", toJson p.isRoot), ("dir", jStr (g.relPath p.dir)),
      ("configFile", jStr (g.relPath p.configFile)), ("keywords", jStrs p.keywords),
      ("remoteUrl", jOpt (p.remoteUrl?.map jStr)), ("requires", jStrs (p.requires.map plainName)),
      ("libs",
        jArr
          (p.libs.map fun l =>
            Json.mkObj
              [("name", jStr (plainName l.name)), ("roots", jStrs (l.roots.map (·.toString))),
                ("globs", jStrs l.globs)])),
      ("exes",
        jArr
          (p.exes.map fun x =>
            Json.mkObj [("name", jStr (plainName x.name)), ("root", jStr x.root.toString)]))]

private def nodeJson (g : Graph) (v : View) (n : ViewNode) : Json :=
  let base := [("id", jStr n.id), ("kind", jStr n.kind.toString), ("name", jStr n.name)]
  let pkg := ("package", jOpt (n.package?.map (jStr ∘ plainName)))
  let modules := ("modules", jStrs (n.members.map fun m => (nodeName g m).toString))
  match v.level with
  | .module =>
    let m? := n.members[0]? >>= (g.nodes[·]?)
    let owners :=
      match m?.map (·.origin) with
      | some (Origin.workspace os) =>
        os.map fun o =>
          Json.mkObj [("kind", jStr (toString o.kind)), ("target", jStr (plainName o.target))]
      | _ => #[]
    Json.mkObj <|
      base ++
        [pkg, ("owners", jArr owners), ("file", jOpt (m? >>= (·.file?) |>.map (jStr ∘ g.relPath))),
          ("isModule", toJson ((m?.map (·.isModule)).getD false)),
          ("isPrelude", toJson ((m?.map (·.isPrelude)).getD false))]
  | .lib => Json.mkObj <| base ++ [pkg, modules]
  | .package => Json.mkObj <| base ++ [modules]

private def importJson (g : Graph) (e : Edge) : Json :=
  Json.mkObj
    [("importer", jStr (nodeName g e.src).toString), ("imported", jStr (nodeName g e.dst).toString),
      ("file", jStr (g.relPath e.file)), ("line", jOpt (e.line?.map jNat)),
      ("public", toJson e.kind.isPublic), ("meta", toJson e.kind.isMeta),
      ("all", toJson e.kind.isAll), ("exported", toJson e.isExported),
      ("implicit", toJson e.implicit)]

/-- The view as a JSON value (schema version `jsonSchemaVersion`). -/
def toJsonView (g : Graph) (v : View) : Json :=
  let id (i : Nat) := jStr ((v.nodes[i]?.map (·.id)).getD "?")
  Json.mkObj
    [("schemaVersion", jNat jsonSchemaVersion), ("level", jStr v.level.toString),
      ("packages", jArr (g.packages.map (packageJson g))),
      ("nodes", jArr (v.nodes.map (nodeJson g v))),
      ("edges",
        jArr
          (v.edges.map fun e =>
            Json.mkObj
              [("from", id e.src), ("to", id e.dst), ("count", jNat e.count),
                ("imports", jArr (e.imports.filterMap fun i => g.edges[i]?.map (importJson g)))]))]

/-! ## DOT -/

/-- `s` as a double-quoted DOT string: `\` and `"` escaped. -/
def dotQuote (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

private def renderDot (g : Graph) (v : View) : String :=
  Id.run do
    let id (i : Nat) := dotQuote ((v.nodes[i]?.map (·.id)).getD "?")
    let mut out := #["digraph \"lean-deny\" {", "  node [shape=box];"]
    let isExt (n : ViewNode) := n.kind == .external
    -- Module and lib level: one cluster per package, in Lake's order.
    let clustered := v.level != .package
    if clustered then
      for p in g.packages do
        let ns := v.nodes.filter fun n => n.package? == some p.name
        if ns.isEmpty then
          continue
        out := out.push s!"  subgraph {dotQuote s!"cluster_{plainName p.name}"} \{"
        out := out.push s!"    label={dotQuote (plainName p.name)};"
        for n in ns do
          out := out.push s!"    {dotQuote n.id};"
        out := out.push "  }"
    for n in v.nodes do
      if isExt n then
        out := out.push s!"  {dotQuote n.id} [style=dashed];"
      else if !clustered || n.package?.all (fun p => (findPackage? g p).isNone) then
        out := out.push s!"  {dotQuote n.id};"
    for e in v.edges do
      let allImplicit := e.imports.all fun i => (g.edges[i]?.map (·.implicit)).getD false
      let attrs :=
        (if v.level == .module then [] else [s!"label={dotQuote (toString e.count)}"]) ++
          (if allImplicit then ["style=dotted"] else [])
      let attrs := if attrs.isEmpty then "" else s!" [{", ".intercalate attrs}]"
      out := out.push s!"  {id e.src} -> {id e.dst}{attrs};"
    out := out.push "}"
    return "\n".intercalate out.toList ++ "\n"

/-- Print the view `v` of graph `g` in format `f`. -/
def render (g : Graph) (v : View) : Format → String
  | .text => renderText g v
  | .json => (toJsonView g v).pretty ++ "\n"
  | .dot => renderDot g v

end LeanDeny.Graph
