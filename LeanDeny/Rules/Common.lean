import LeanDeny.Graph.Model
import LeanDeny.Graph.View
import LeanDeny.Policy

/-!
# What every rule kind shares

A violation and its rendering, the small graph helpers the rule kinds use
(a node's name, whether it is external, its package, and whether an import
leaves its importer's package), and `proseList` for their messages. Pure.
-/

open Lean LeanDeny.Graph

namespace LeanDeny

/-- A Lake target a target-config rule checks: a `lean_lib` or a `lean_exe`,
its package, the package's lakefile and the target's effective plugins. -/
structure TargetRef where
  pkg : Name
  kind : TargetKind
  name : Name
  /-- The package's configuration file (Lake keeps no position for a
  target). -/
  configFile : System.FilePath
  plugins : Array PluginRef
  deriving BEq, Repr, Inhabited

/-- "lean_lib" or "lean_exe". -/
def TargetRef.kindText (t : TargetRef) : String :=
  match t.kind with
  | .lib => "lean_lib"
  | .exe => "lean_exe"

/-- What a require-backed violation is about: package `pkg`'s module
imports a module of package `imported`, which `pkg`'s lakefile
(`configFile`) does not require directly; `requires` is what it does
require, as written. -/
structure RequireGap where
  pkg : Name
  imported : Name
  configFile : System.FilePath
  requires : Array Name
  deriving BEq, Repr, Inhabited

/-- One violation of any rule kind: the rule, its table position, its
reason, what the violation is, and the chain of imports that breaks it. -/
structure Violation where
  /-- The rule it breaks. -/
  rule : RuleRef
  /-- The rule's table. -/
  pos? : Option Toml.Pos
  /-- The rule's `reason` as written: always set for deny, allow-only,
  reachable, co-reach, target-config and require-backed, optional for
  `[layers]`. -/
  reason? : Option String
  /-- What this violation is, beyond the reason: for `[layers]`,
  "app (implementation) may not import plugin (implementation)"; for a
  reachable rule, "M is outside the import closure of R"; for a co-reach
  rule, "R reaches T but not M"; for a target-config rule, "lean_lib p/L
  does not load P"; for a require-backed rule, "M (package a) imports
  package b, which a does not require directly". -/
  detail? : Option String := none
  /-- At least one edge for every kind but reachable and target-config,
  whose chain is empty, and co-reach, whose chain is the witness from its root to the
  `if-reaches` module it reaches (empty when the root is itself one);
  exactly one for a direct deny rule, an allow-only rule, `[layers]` and a
  require-backed rule;
  consecutive (`chain[i].dst = chain[i+1].src`). -/
  chain : Array Edge
  /-- The module a reachable rule does not reach, or the root a co-reach
  rule is broken for; `none` for the other kinds. -/
  module? : Option NodeId := none
  /-- The `must-reach` modules a co-reach rule's root does not reach, in
  `displayOrder`; empty for the other kinds. -/
  missing : Array NodeId := #[]
  /-- The target a target-config rule is broken for; `none` for the other
  kinds. -/
  target? : Option TargetRef := none
  /-- The unbacked package dependency a require-backed rule reports; `none`
  for the other kinds. -/
  require? : Option RequireGap := none
  deriving BEq, Repr, Inhabited

/-- "deny rule 1", "allow-only rule 2", "layers", "reachable rule 1",
"co-reach rule 1", "target-config rule 1", "require-backed rule 1": names
the rule. -/
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

/-- The line naming module `n` and its file: `<file>: <module>`, the file
through `path`; just the name for a node with no file. -/
def moduleLine (g : Graph) (n : NodeId) (path : System.FilePath → String := g.relPath) : String :=
  match g.nodes[n]? >>= (·.file?) with
  | some f => s!"{path f}: {nodeName g n}"
  | none => nodeName g n

/-- A violation as a block: `<label> (<path>:<line>:<column>): <message>`,
then one step per edge, indented two spaces, and, when the chain is empty and
the violation has a module (a reachable rule's uncovered module, a co-reach
rule's root that is itself in `if-reaches`), that module's line
(`moduleLine`), indented two spaces; for a target-config rule, the target's
line, `<lakefile>: lean_lib <name>`, indented two spaces; for a
require-backed rule, after its chain, the importing package's requires,
`<lakefile>: <package> requires <r1, r2>` (or `requires nothing`), indented
two spaces. `policyPath` is
the policy's; `path` writes each file (as in `chainLine`). -/
def Violation.render (g : Graph) (policyPath : String) (v : Violation)
    (path : System.FilePath → String := g.relPath) : Array String :=
  #[s!"{v.label} ({Policy.posText policyPath v.pos?}): {v.message}"] ++
    v.chain.map (fun e => s!"  {chainLine g e path}") ++
    (if v.chain.isEmpty then (v.module?.map fun m => #[s!"  {moduleLine g m path}"]).getD #[]
    else #[]) ++
    (v.target?.map fun t =>
          #[s!"  {path t.configFile}: {t.kindText} {t.name.toString (escape := false)}"]).getD
      #[] ++
    (v.require?.map fun r =>
          #[s!"  {path r.configFile}: {plainName r.pkg} {requiresText r.requires}"]).getD
      #[]

end LeanDeny
