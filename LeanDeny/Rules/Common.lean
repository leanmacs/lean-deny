import LeanDeny.Graph.Model
import LeanDeny.Policy

/-!
# What every rule kind shares

A violation and its rendering, the small graph helpers the rule kinds use
(a node's name, whether it is external, its package, and whether an import
leaves its importer's package), and `proseList` for their messages. Pure.
-/

open Lean LeanDeny.Graph

namespace LeanDeny

/-- One violation of any rule kind: the rule, its table position, its
reason, what the violation is, and the chain of imports that breaks it. -/
structure Violation where
  /-- The rule it breaks. -/
  rule : RuleRef
  /-- The rule's table. -/
  pos? : Option Toml.Pos
  /-- The rule's `reason` as written: always set for deny and allow-only,
  optional for `[layers]`. -/
  reason? : Option String
  /-- What this violation is, beyond the reason: for `[layers]`,
  "app (implementation) may not import plugin (implementation)". -/
  detail? : Option String := none
  /-- At least one edge, exactly one for a direct deny rule, an allow-only
  rule and `[layers]`; consecutive (`chain[i].dst = chain[i+1].src`). -/
  chain : Array Edge
  deriving BEq, Repr, Inhabited

/-- "deny rule 1", "allow-only rule 2", "layers": names the rule. -/
def Violation.label (v : Violation) : String :=
  v.rule.label

/-- The header's text after the position: "<reason>: <detail>", the reason,
or the detail. -/
def Violation.message (v : Violation) : String :=
  match v.reason?, v.detail? with
  | some r, some d => s!"{r}: {d}"
  | some r, none => r
  | none, some d => d
  | none, none => ""

/-- Items as prose: "a", "a and b", "a, b and c"; "" for none. -/
def proseList (xs : Array String) : String :=
  match xs.back? with
  | none => ""
  | some last =>
    let init := xs.pop
    if init.isEmpty then last else s!"{", ".intercalate init.toList} and {last}"

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
the file through `path` (by default, relative to the workspace). -/
def chainLine (g : Graph) (e : Edge) (path : System.FilePath → String := g.relPath) : String :=
  let pos := path e.file ++ ((e.line?.map (s!":{·}")).getD "")
  s!"{pos}: {nodeName g e.src} imports {nodeName g e.dst}{if e.implicit then " (implicit)" else ""}"

/-- A violation as a block: `<label> (<path>:<line>:<column>): <message>`,
then one step per edge, indented two spaces. `policyPath` is the policy's;
`path` writes each step's file (as in `chainLine`). -/
def Violation.render (g : Graph) (policyPath : String) (v : Violation)
    (path : System.FilePath → String := g.relPath) : Array String :=
  #[s!"{v.label} ({Policy.posText policyPath v.pos?}): {v.message}"] ++
    v.chain.map fun e => s!"  {chainLine g e path}"

end LeanDeny
