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

/-- Which side of a doc-modules comparison a violation is on: a module the
section does not list, or a listed name the selector does not match. -/
inductive DocGapKind where
  | missing
  | extra
  deriving BEq, Repr, Inhabited

/-- "missing" or "extra". -/
def DocGapKind.toString : DocGapKind → String
  | .missing => "missing"
  | .extra => "extra"

instance : ToString DocGapKind :=
  ⟨DocGapKind.toString⟩

/-- What a doc-modules violation is about: module name `name` is missing
from, or extra in, section `heading` of Markdown file `file` (absolute:
the workspace root joined with the rule's `file`); `line` is the heading's
line for a missing name, the name's first listing line for an extra one.
(`section` is a Lean keyword, hence the field name.) -/
structure DocGap where
  kind : DocGapKind
  name : String
  file : System.FilePath
  heading : String
  line : Nat
  deriving BEq, Repr, Inhabited

/-- What a doc-packages violation says of a package's row: the package has
no row, the row names a package the selector does not match, its layer
cell differs from `[layers]`, or its requires cell differs from the
package's direct requires. -/
inductive PackageRowKind where
  | missingRow
  | extraRow
  | layerDiffers
  | requiresDiffer
  deriving BEq, Repr, Inhabited

/-- "missing", "extra", "layer" or "requires". -/
def PackageRowKind.toString : PackageRowKind → String
  | .missingRow => "missing"
  | .extraRow => "extra"
  | .layerDiffers => "layer"
  | .requiresDiffer => "requires"

instance : ToString PackageRowKind :=
  ⟨PackageRowKind.toString⟩

/-- What a doc-packages violation is about: package `pkg` (as the row or
the lakefile writes it) and its row in the table under section `heading`
of Markdown file `file` (absolute: the workspace root joined with the
rule's `file`); `line` is the heading's line for a missing row, the row's
line otherwise. A layer violation sets `documentedLayer?` (the cell) and
`layer?` (`[layers]`'s); a requires violation sets `missingRequires` (direct
requires the cell does not name, in lakefile order) and `extraRequires`
(names the cell gives that are no direct require, in cell order). -/
structure PackageRowGap where
  kind : PackageRowKind
  pkg : String
  file : System.FilePath
  heading : String
  line : Nat
  documentedLayer? : Option String := none
  layer? : Option String := none
  missingRequires : Array String := #[]
  extraRequires : Array String := #[]
  deriving BEq, Repr, Inhabited

/-- One violation of any rule kind: the rule, its table position, its
reason, what the violation is, and the chain of imports that breaks it. -/
structure Violation where
  /-- The rule it breaks. -/
  rule : RuleRef
  /-- The rule's table. -/
  pos? : Option Toml.Pos
  /-- The rule's `reason` as written: always set for deny, allow-only,
  reachable, co-reach, target-config, require-backed, doc-modules and
  doc-packages, optional for `[layers]`. -/
  reason? : Option String
  /-- What this violation is, beyond the reason: for `[layers]`,
  "app (implementation) may not import plugin (implementation)"; for a
  reachable rule, "M is outside the import closure of R"; for a co-reach
  rule, "R reaches T but not M"; for a target-config rule, "lean_lib p/L
  does not load P"; for a require-backed rule, "M (package a) imports
  package b, which a does not require directly"; for a doc-modules rule,
  "M is not listed in section 'S' of f" or "section 'S' of f lists N,
  which 'modules' does not match"; for a doc-packages rule, "package P has
  no row in section 'S' of f", "section 'S' of f has a row for P, which
  'packages' does not match", "section 'S' of f gives P layer L, but
  [layers] puts it in K" or "section 'S' of f gives P requires A, but P
  requires B directly: missing …; extra …". -/
  detail? : Option String := none
  /-- At least one edge for every kind but reachable, target-config,
  doc-modules and doc-packages, whose chain is empty, and co-reach, whose chain is the witness from its root to the
  `if-reaches` module it reaches (empty when the root is itself one);
  exactly one for a direct deny rule, an allow-only rule, `[layers]` and a
  require-backed rule;
  consecutive (`chain[i].dst = chain[i+1].src`). -/
  chain : Array Edge
  /-- The module a reachable rule does not reach, the root a co-reach rule
  is broken for, or the module a doc-modules section does not list; `none`
  for the other kinds (and for a doc-modules extra name). -/
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
  /-- The missing or extra name a doc-modules rule reports; `none` for the
  other kinds. -/
  doc? : Option DocGap := none
  /-- The package row a doc-packages rule reports; `none` for the other
  kinds. -/
  packageRow? : Option PackageRowGap := none
  deriving BEq, Repr, Inhabited

/-- The Markdown place a doc-modules or doc-packages violation is about:
its file and line (`DocGap`'s, `PackageRowGap`'s); `none` for the other
kinds. -/
def Violation.docPlace? (v : Violation) : Option (System.FilePath × Nat) :=
  match v.doc?, v.packageRow? with
  | some d, _ => some (d.file, d.line)
  | none, some r => some (r.file, r.line)
  | none, none => none

/-- "deny rule 1", "allow-only rule 2", "layers", "reachable rule 1",
"co-reach rule 1", "target-config rule 1", "require-backed rule 1",
"doc-modules rule 1", "doc-packages rule 1": names the rule. -/
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
two spaces; for a doc-modules rule, after the missing module's line, the
section's place, `<file>:<line>: section '<section>'`, or, for an extra
name, the name's place, `<file>:<line>: <name>`, indented two spaces; for a
doc-packages rule, the section's place, `<file>:<line>: section
'<section>'`, for a missing row, or the row's place, `<file>:<line>:
<package>`, for the others, indented two spaces. `policyPath` is
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
      #[] ++
    (v.doc?.map fun d =>
          match d.kind with
          | .missing => #[s!"  {path d.file}:{d.line}: section '{d.heading}'"]
          | .extra => #[s!"  {path d.file}:{d.line}: {d.name}"]).getD
      #[] ++
    (v.packageRow?.map fun r =>
          match r.kind with
          | .missingRow => #[s!"  {path r.file}:{r.line}: section '{r.heading}'"]
          | _ => #[s!"  {path r.file}:{r.line}: {r.pkg}"]).getD
      #[]

end LeanDeny
