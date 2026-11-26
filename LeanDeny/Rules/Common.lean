import LeanDeny.Graph.Model
import LeanDeny.Policy

/-!
# What every rule kind shares

A violation and its rendering, and the small graph helpers the rule kinds
use: a node's name, whether it is external, its package, and whether an
import leaves its importer's package. Pure.
-/

open Lean LeanDeny.Graph

namespace LeanDeny

/-- One violation of any rule kind: the rule's label, table position and
reason, and the chain of imports that breaks it. -/
structure Violation where
  /-- "deny rule 1", "allow-only rule 2": names one rule of the policy. -/
  label : String
  /-- The rule's table. -/
  pos? : Option Toml.Pos
  reason : String
  /-- At least one edge, exactly one for a direct deny rule and an allow-only
  rule; consecutive (`chain[i].dst = chain[i+1].src`). -/
  chain : Array Edge
  deriving BEq, Repr, Inhabited

/-- The name of node `n`. -/
def nodeName (g : Graph) (n : NodeId) : String :=
  (g.nodes[n]?.map (·.name.toString)).getD "?"

/-- Node `n` is outside the workspace. -/
def isExternalId (g : Graph) (n : NodeId) : Bool :=
  (g.nodes[n]?.map (·.origin == .external)).getD false

/-- Membership in `ns`, as an array over the graph's nodes. -/
def memberMask (g : Graph) (ns : Array NodeId) : Array Bool :=
  ns.foldl (fun m i => if i < m.size then m.set! i true else m) (Array.replicate g.nodes.size false)

/-- The package of a workspace node (its owners share one); `none` for an
external node. -/
def packageOf? (g : Graph) (n : NodeId) : Option Name :=
  match g.nodes[n]?.map (·.origin) with
  | some (Origin.workspace os) => os[0]?.map (·.pkg)
  | _ => none

/-- The import leaves its importer's package: its target is external or in
another package. -/
def leavesPackage (g : Graph) (e : Edge) : Bool :=
  match packageOf? g e.src, packageOf? g e.dst with
  | some a, some b => a != b
  | _, _ => true

/-- One step of a chain: `<file>[:<line>]: <importer> imports <imported>[ (implicit)]`,
the file relative to the workspace. -/
def chainLine (g : Graph) (e : Edge) : String :=
  let pos := g.relPath e.file ++ ((e.line?.map (s!":{·}")).getD "")
  s!"{pos}: {nodeName g e.src} imports {nodeName g e.dst}{if e.implicit then " (implicit)" else ""}"

/-- A violation as a block: `<label> (<path>:<line>:<column>): <reason>`,
then one step per edge, indented two spaces. `path` is the policy's. -/
def Violation.render (g : Graph) (path : String) (v : Violation) : Array String :=
  #[s!"{v.label} ({Policy.posText path v.pos?}): {v.reason}"] ++
    v.chain.map fun e => s!"  {chainLine g e}"

end LeanDeny
