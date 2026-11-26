import Lean.Data.Name
import Std.Data.HashMap

/-!
# The module graph's data model

Plain data, independent of Lake: the graph `LeanDeny.Graph.load` builds and
every later stage (rules, printing) reads. Nothing here imports Lake or the
Lean frontend, so the model does not change when the toolchain does.

- A **node** is one module, identified by its name (Lean has one global
  module namespace). A workspace node is owned by the Lake targets
  (`lean_lib`s, `lean_exe` roots) that list it; an external node is a module
  some workspace module imports that no workspace target lists, such as
  `Init` or `Lean.Data.Json`.
- An **edge** is one `import` directive, with its keywords, its file and
  line, plus Lean's two implicit `Init` imports of every non-`prelude`
  module.
-/

open Lean System

namespace LeanDeny.Graph

/-- A node's index into `Graph.nodes`. -/
abbrev NodeId :=
  Nat

/-- The kind of Lake target that lists a module. -/
inductive TargetKind where
  | lib
  | exe
  deriving BEq, Repr, Ord, Inhabited, Hashable

instance : ToString TargetKind where
  toString
    | .lib => "lib"
    | .exe => "exe"

/-- One Lake target listing a module: a `lean_lib` whose `modules` include
it, or a `lean_exe` whose root it is. -/
structure Owner where
  pkg : Name
  kind : TargetKind
  /-- The `lean_lib` or `lean_exe` name. -/
  target : Name
  deriving BEq, Repr, Inhabited

/-- Owners sort by kind, then target name (all owners of a node share one
package). -/
def Owner.lt (a b : Owner) : Bool :=
  match compare a.kind b.kind with
  | .lt => true
  | .gt => false
  | .eq =>
    match a.target.cmp b.target with
    | .lt => true
    | .gt => false
    | .eq => a.pkg.cmp b.pkg == .lt

/-- Where a node comes from. -/
inductive Origin where
  /-- A module of the workspace, with every target listing it: non-empty,
  sorted, all in one package. -/
  | workspace (owners : Array Owner)
  /-- Not a module of any workspace target: the direct target of some
  workspace module's import. -/
  | external
  deriving BEq, Repr, Inhabited

/-- One module. -/
structure Node where
  /-- The node's identity: the module name. -/
  name : Name
  origin : Origin
  /-- The absolute source path; `none` exactly for external nodes. -/
  file? : Option FilePath
  /-- The header starts with `module` (the module system is on). -/
  isModule : Bool := false
  /-- The header says `prelude`: no implicit `Init` imports. -/
  isPrelude : Bool := false
  deriving BEq, Repr, Inhabited

/-- The keywords of an `import` directive, as written. -/
structure ImportKind where
  isPublic : Bool := false
  isMeta : Bool := false
  isAll : Bool := false
  deriving BEq, Repr, Inhabited

/-- One import: an `import` directive, or one of the implicit `Init`
imports. -/
structure Edge where
  src : NodeId
  dst : NodeId
  kind : ImportKind
  /-- Lean's meaning: `public import`, or any import of a non-`module` file. -/
  isExported : Bool
  /-- The importer's source file. -/
  file : FilePath
  /-- The 1-based line of the directive's first token; `none` only for the
  implicit `Init` imports. -/
  line? : Option Nat
  /-- One of the two imports (`Init`, `meta Init`) Lean adds unless the
  header says `prelude`. -/
  implicit : Bool
  deriving BEq, Repr, Inhabited

/-- A `lean_lib`'s configuration. -/
structure LibInfo where
  name : Name
  roots : Array Name
  globs : Array String
  deriving BEq, Repr, Inhabited

/-- A `lean_exe`'s configuration. -/
structure ExeInfo where
  name : Name
  root : Name
  deriving BEq, Repr, Inhabited

/-- Package metadata a policy can key on. -/
structure PackageInfo where
  name : Name
  dir : FilePath
  configFile : FilePath
  keywords : Array String
  /-- `none` when Lake's `remoteUrl` is empty (a path package or the root). -/
  remoteUrl? : Option String
  /-- The names of its `require`s. -/
  requires : Array Name
  libs : Array LibInfo
  exes : Array ExeInfo
  isRoot : Bool
  deriving BEq, Repr, Inhabited

/-- The module graph of a workspace. -/
structure Graph where
  /-- The workspace directory (a real path). -/
  root : FilePath
  /-- Lake's order: the root package first, then its dependencies. -/
  packages : Array PackageInfo
  /-- Sorted by `Name.cmp`; a `NodeId` is an index into this array. -/
  nodes : Array Node
  index : Std.HashMap Name NodeId
  /-- By source node, then source order (the implicit `Init` pair first). -/
  edges : Array Edge
  /-- Per node, the indices into `edges` of its imports, in source order. -/
  out : Array (Array Nat)
  /-- Per node, the indices into `edges` of its importers' imports of it, by
  (importer, position). -/
  inc : Array (Array Nat)
  deriving Inhabited

/-- `path` relative to the graph's root, with `/` separators (`.` for the
root itself); a path outside the root stays as it is. -/
def Graph.relPath (g : Graph) (path : FilePath) : String :=
  let p := path.toString
  let r := g.root.toString
  if p == r then "."
  else
    match p.dropPrefix? (r ++ "/") with
    | some rest => rest.toString
    | none => p

end LeanDeny.Graph
