import LeanDeny.Graph.Model

/-!
# The workspace snapshot `LakeApi` hands over

Plain values copied out of Lake by `LeanDeny.Graph.LakeApi.snapshot`, so the
graph builder (`LeanDeny.Graph.Build`) and its tests never touch Lake. One
`RawModule` per (target, module) occurrence: a module two targets list
appears twice, and merging is the builder's job.
-/

open Lean System

namespace LeanDeny.Graph

/-- One import of a module, as Lake parsed and resolved it. -/
structure RawImport where
  module : Name
  isExported : Bool
  isMeta : Bool
  importAll : Bool
  /-- Lake's `module?`: the (package, library) it resolves the import to, if
  any. -/
  resolved? : Option (Name × Name)
  deriving BEq, Repr, Inhabited

/-- One module of one target, with Lake's view of its header. -/
structure RawModule where
  name : Name
  owner : Owner
  /-- The absolute source path. -/
  file : FilePath
  isModule : Bool
  /-- Exactly Lake's `ModuleInput.imports`, in order: the implicit `Init`
  pair first unless the header says `prelude`. -/
  imports : Array RawImport
  deriving BEq, Repr, Inhabited

/-- One `import` directive of a header, with its line: what
`HeaderParser.parse` (`LeanDeny.Graph.Header`) returns, kept here so the
graph builder need not import Lean's parser. -/
structure HeaderImport where
  module : Name
  kind : ImportKind
  /-- The 1-based line of the directive's first token. -/
  line : Nat
  deriving BEq, Repr, Inhabited

/-- Everything the graph builder needs from Lake. -/
structure Snapshot where
  /-- The workspace directory (a real path). -/
  root : FilePath
  packages : Array PackageInfo
  modules : Array RawModule
  deriving Inhabited

end LeanDeny.Graph
