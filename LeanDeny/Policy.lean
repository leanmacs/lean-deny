import LeanDeny.Lake.Toml
import LeanDeny.Policy.Selector

/-!
# Policy file

`lean-deny.toml`. This version knows eleven top-level keys:

- `[sets]`: named sets of modules, each a list of selectors
  (`LeanDeny.Policy.Selector`) or a table with a `select` and an `except`
  list;
- `[[deny]]`: deny rules, each with `from`, `to`, `transitive`, `wrappers`
  and `reason` (`LeanDeny.Rules.Deny` evaluates them);
- `[[allow-only]]`: allow-only rules, each with `from`, `except`, `allow`
  and `reason` (`LeanDeny.Rules.AllowOnly` evaluates them);
- `[layers]`: one table with `classify` entries (`layer`, `select`),
  `default`, `allow` pairs of layers, `same-package` and `reason`
  (`LeanDeny.Rules.Layers` evaluates it);
- `[[reachable]]`: coverage rules, each with `from`, `must-cover` and
  `reason` (`LeanDeny.Rules.Reachable` evaluates them);
- `[[co-reach]]`: co-reach rules, each with `roots`, `if-reaches`,
  `must-reach` and `reason` (`LeanDeny.Rules.CoReach` evaluates them);
- `[[target-config]]`: rules on Lake targets, each with `targets`,
  `except`, `load-plugin`, `or-imports` and `reason`
  (`LeanDeny.Rules.TargetConfig` evaluates them);
- `[[require-backed]]`: rules on packages, each with `packages` and
  `reason`: every import from a module of a matched package into another
  workspace package is backed by a direct `require`
  (`LeanDeny.Rules.RequireBacked` evaluates them);
- `[[doc-modules]]`: rules on a Markdown file, each with `file`, `section`,
  `prefix`, `modules` and `reason`: the backticked module names starting
  with `prefix` in the file's section `section` are exactly the workspace
  modules `modules` matches (`LeanDeny.Rules.DocModules` evaluates them);
- `[[doc-packages]]`: rules on a Markdown table, each with `file`,
  `section`, `package-column`, `layer-column`, `requires-column`,
  `packages`, `requires-except` and `reason`: the first top-level table in
  the file's section `section` with the three named columns has one row per
  package `packages` matches, giving its `[layers]` layer and its direct
  requires less `requires-except` (`LeanDeny.Rules.DocPackages` evaluates
  them); a policy with one needs `[layers]`;
- `[[root]]`: declared roots, each a `module` and its file's `path`
  relative to the workspace directory: a module no Lake target declares,
  read from its file into the graph (`LeanDeny.Graph.LakeApi`). Roots are
  not rules.

Any other key is rejected rather than ignored, so a policy full of rules
cannot pass while checking nothing.

Loading checks everything that needs no graph: the file's shape, each
selector's syntax, that every `set:` (also inside `imports:`) names a set, that no set refers to
itself, and that every layer a `[layers]` `allow` pair names is declared.
Every error is collected, each starting with `<path>:<line>:<column>: `:
shape and syntax errors in source order, then
the sets' references, then the rules' references. What the selectors match
is checked against the graph later (`LeanDeny.Policy.Resolve`).
-/

open System

namespace LeanDeny

/-- Where a selector is written. Error messages name it, so an author can
find the rule a selector belongs to. -/
inductive Use where
  /-- The bare array, or the `select` list, of set `name`. -/
  | setSelect (name : String)
  /-- The `except` list of set `name`. -/
  | setExcept (name : String)
  /-- Field `field` of rule `index` (1-based, in source order among the rules
  of `kind`): `.rule "deny" 1 "to"`. -/
  | rule (kind : String) (index : Nat) (field : String)
  /-- The `select` of entry `entry` (1-based) of `[layers]`'s `classify`. -/
  | layer (entry : Nat)
  /-- `lean-deny explain <selector>`. -/
  | commandLine
  deriving BEq, Repr, Inhabited

/-- The clause a message puts after the selector: " in set 'core'",
" in the except list of set 'core'", " in deny rule 1 ('to')",
" in layers classify entry 1", or "" on the command line. -/
def Use.clause : Use → String
  | .setSelect n => s!" in set '{n}'"
  | .setExcept n => s!" in the except list of set '{n}'"
  | .rule k i f => s!" in {k} rule {i} ('{f}')"
  | .layer i => s!" in layers classify entry {i}"
  | .commandLine => ""

/-- One selector as written in the policy or on the command line. -/
structure SelectorRef where
  /-- As written, echoed in messages. -/
  text : String
  sel : Selector
  /-- `none` on the command line. -/
  pos? : Option Toml.Pos
  use : Use
  deriving BEq, Repr, Inhabited

/-- "selector 'mod:X' in set 'core'". -/
def SelectorRef.describe (r : SelectorRef) : String :=
  s!"selector '{r.text}'{r.use.clause}"

/-- One entry of `[sets]`. -/
structure SetDef where
  name : String
  /-- The position of the set's value (array or table). -/
  pos? : Option Toml.Pos
  /-- Non-empty in a valid policy. -/
  select : Array SelectorRef
  /-- Possibly empty. -/
  except : Array SelectorRef
  deriving BEq, Repr, Inhabited

/-- The kind of a policy rule. -/
inductive RuleKind where
  | deny
  | allowOnly
  | layers
  | reachable
  | coReach
  | targetConfig
  | requireBacked
  | docModules
  | docPackages
  deriving BEq, Repr, Inhabited, DecidableEq

/-- As the policy writes it: "deny", "allow-only", "layers", "reachable",
"co-reach", "target-config", "require-backed", "doc-modules",
"doc-packages". -/
def RuleKind.toString : RuleKind → String
  | .deny => "deny"
  | .allowOnly => "allow-only"
  | .layers => "layers"
  | .reachable => "reachable"
  | .coReach => "co-reach"
  | .targetConfig => "target-config"
  | .requireBacked => "require-backed"
  | .docModules => "doc-modules"
  | .docPackages => "doc-packages"

instance : ToString RuleKind :=
  ⟨RuleKind.toString⟩

/-- One rule of a policy: its kind and its 1-based index among the tables of
that kind (always 1 for `[layers]`, of which there is at most one). -/
structure RuleRef where
  kind : RuleKind
  index : Nat
  deriving BEq, Repr, Inhabited

/-- "deny rule 1", "allow-only rule 2", "layers", "reachable rule 1",
"co-reach rule 1", "target-config rule 1", "require-backed rule 1",
"doc-modules rule 1", "doc-packages rule 1". -/
def RuleRef.label (r : RuleRef) : String :=
  match r.kind with
  | .deny => s!"deny rule {r.index}"
  | .allowOnly => s!"allow-only rule {r.index}"
  | .layers => "layers"
  | .reachable => s!"reachable rule {r.index}"
  | .coReach => s!"co-reach rule {r.index}"
  | .targetConfig => s!"target-config rule {r.index}"
  | .requireBacked => s!"require-backed rule {r.index}"
  | .docModules => s!"doc-modules rule {r.index}"
  | .docPackages => s!"doc-packages rule {r.index}"

/-- One `[[deny]]` table: no module of `sources` may import a module of
`targets`, directly or (with `transitive`) through others, unless the
importer, or a module the chain passes through, is a wrapper. (`from` is a
Lean keyword, hence the field names.) -/
structure DenyRule where
  /-- 1-based, in source order among the `deny` tables; a table with errors
  keeps its number. -/
  index : Nat
  /-- The table's position: its `[[deny]]` header (column 0), or the `{` of
  an inline table. -/
  pos? : Option Toml.Pos
  /-- `from`: non-empty in a valid policy. -/
  sources : Array SelectorRef := #[]
  /-- `to`: non-empty in a valid policy. -/
  targets : Array SelectorRef := #[]
  /-- `transitive`, default `false`: direct imports only. -/
  transitive : Bool := false
  /-- `wrappers`, default none. -/
  wrappers : Array SelectorRef := #[]
  /-- `reason`: not blank in a valid policy. -/
  reason : String := ""
  deriving BEq, Repr, Inhabited

/-- The rule's reference: `deny` and its index. -/
def DenyRule.ref (r : DenyRule) : RuleRef :=
  ⟨.deny, r.index⟩

/-- "deny rule 1". -/
def DenyRule.label (r : DenyRule) : String :=
  r.ref.label

/-- One `[[allow-only]]` table: every import by a module it governs, of a
module outside that module's own package, must land in `allow`. -/
structure AllowOnlyRule where
  /-- 1-based, in source order among the `allow-only` tables; a table with
  errors keeps its number. -/
  index : Nat
  /-- The table's position: its `[[allow-only]]` header (column 0), or the
  `{` of an inline table. -/
  pos? : Option Toml.Pos
  /-- `from`: non-empty in a valid policy. -/
  sources : Array SelectorRef := #[]
  /-- `except`, default none: modules taken out of `from`. -/
  except : Array SelectorRef := #[]
  /-- `allow`: non-empty in a valid policy. -/
  allow : Array SelectorRef := #[]
  /-- `reason`: not blank in a valid policy. -/
  reason : String := ""
  deriving BEq, Repr, Inhabited

/-- The rule's reference: `allow-only` and its index. -/
def AllowOnlyRule.ref (r : AllowOnlyRule) : RuleRef :=
  ⟨.allowOnly, r.index⟩

/-- "allow-only rule 1". -/
def AllowOnlyRule.label (r : AllowOnlyRule) : String :=
  r.ref.label

/-- One `[[reachable]]` table: every module of `mustCover` is a module of
`sources` or imported by one, directly or not. -/
structure ReachableRule where
  /-- 1-based, in source order among the `reachable` tables; a table with
  errors keeps its number. -/
  index : Nat
  /-- The table's position: its `[[reachable]]` header (column 0), or the
  `{` of an inline table. -/
  pos? : Option Toml.Pos
  /-- `from`: non-empty in a valid policy. -/
  sources : Array SelectorRef := #[]
  /-- `must-cover`: non-empty in a valid policy. -/
  mustCover : Array SelectorRef := #[]
  /-- `reason`: not blank in a valid policy. -/
  reason : String := ""
  deriving BEq, Repr, Inhabited

/-- The rule's reference: `reachable` and its index. -/
def ReachableRule.ref (r : ReachableRule) : RuleRef :=
  ⟨.reachable, r.index⟩

/-- "reachable rule 1". -/
def ReachableRule.label (r : ReachableRule) : String :=
  r.ref.label

/-- One `[[co-reach]]` table: every module of `roots` whose import closure
holds a module of `ifReaches` also holds every module of `mustReach`. -/
structure CoReachRule where
  /-- 1-based, in source order among the `co-reach` tables; a table with
  errors keeps its number. -/
  index : Nat
  /-- The table's position: its `[[co-reach]]` header (column 0), or the
  `{` of an inline table. -/
  pos? : Option Toml.Pos
  /-- `roots`: non-empty in a valid policy. -/
  roots : Array SelectorRef := #[]
  /-- `if-reaches`: non-empty in a valid policy. -/
  ifReaches : Array SelectorRef := #[]
  /-- `must-reach`: non-empty in a valid policy. -/
  mustReach : Array SelectorRef := #[]
  /-- `reason`: not blank in a valid policy. -/
  reason : String := ""
  deriving BEq, Repr, Inhabited

/-- The rule's reference: `co-reach` and its index. -/
def CoReachRule.ref (r : CoReachRule) : RuleRef :=
  ⟨.coReach, r.index⟩

/-- "co-reach rule 1". -/
def CoReachRule.label (r : CoReachRule) : String :=
  r.ref.label

/-- A Lake target a `[[target-config]]` rule's `load-plugin` names:
`<target>`, `<package>/<target>` or `@<package>/<target>`. -/
structure PluginName where
  /-- The package, when given. -/
  pkg? : Option String := none
  target : String
  /-- As written. -/
  text : String
  deriving BEq, Repr, Inhabited

/-- Parse a `load-plugin` value: a target name, optionally after a package
and a `/` (the package optionally after `@`). No facet (`:`), no module
(`+`), no empty part, at most one `/`. -/
def PluginName.parse? (s : String) : Option PluginName :=
  let ok (part : String) : Bool :=
    !part.isEmpty &&
      !part.any fun c => c == ':' || c == '+' || c == '@' || c == '/' || c.isWhitespace
  match s.splitOn "/" with
  | [t] => if ok t then some { target := t, text := s } else none
  | [p, t] =>
    let p := if p.startsWith "@" then (p.drop 1).toString else p
    if ok p && ok t then some { pkg? := some p, target := t, text := s } else none
  | _ => none

/-- One `[[target-config]]` table: every `lean_lib` and `lean_exe` of
`targets` (minus `except`) loads `loadPlugin` as a plugin, or has a module
whose import closure holds a module of `orImports`. -/
structure TargetConfigRule where
  /-- 1-based, in source order among the `target-config` tables; a table with
  errors keeps its number. -/
  index : Nat
  /-- The table's position: its `[[target-config]]` header (column 0), or
  the `{` of an inline table. -/
  pos? : Option Toml.Pos
  /-- `targets`: non-empty, only `pkg:` and `lib:` selectors, in a valid
  policy. -/
  targets : Array SelectorRef := #[]
  /-- `except`: only `pkg:` and `lib:` selectors; possibly empty. -/
  except : Array SelectorRef := #[]
  /-- `load-plugin`: set in a valid policy. -/
  loadPlugin? : Option PluginName := none
  /-- `or-imports`: possibly empty. -/
  orImports : Array SelectorRef := #[]
  /-- `reason`: not blank in a valid policy. -/
  reason : String := ""
  deriving BEq, Repr, Inhabited

/-- The rule's reference: `target-config` and its index. -/
def TargetConfigRule.ref (r : TargetConfigRule) : RuleRef :=
  ⟨.targetConfig, r.index⟩

/-- "target-config rule 1". -/
def TargetConfigRule.label (r : TargetConfigRule) : String :=
  r.ref.label

/-- One `[[require-backed]]` table: for each package `packages` matches,
every import from one of its modules into a module of another workspace
package is backed by a direct `require` of that package. -/
structure RequireBackedRule where
  /-- 1-based, in source order among the `require-backed` tables; a table
  with errors keeps its number. -/
  index : Nat
  /-- The table's position: its `[[require-backed]]` header (column 0), or
  the `{` of an inline table. -/
  pos? : Option Toml.Pos
  /-- `packages`: non-empty in a valid policy. -/
  packages : Array SelectorRef := #[]
  /-- `reason`: not blank in a valid policy. -/
  reason : String := ""
  deriving BEq, Repr, Inhabited

/-- The rule's reference: `require-backed` and its index. -/
def RequireBackedRule.ref (r : RequireBackedRule) : RuleRef :=
  ⟨.requireBacked, r.index⟩

/-- "require-backed rule 1". -/
def RequireBackedRule.label (r : RequireBackedRule) : String :=
  r.ref.label

/-- One `[[doc-modules]]` table: the backticked module names starting with
`pfx` in section `heading` of Markdown file `file` are exactly the workspace
modules `modules` matches. (`section` and `prefix` are Lean keywords, hence
the field names.) -/
structure DocModulesRule where
  /-- 1-based, in source order among the `doc-modules` tables; a table with
  errors keeps its number. -/
  index : Nat
  /-- The table's position: its `[[doc-modules]]` header (column 0), or the
  `{` of an inline table. -/
  pos? : Option Toml.Pos
  /-- `file`: relative to the workspace directory, not empty in a valid
  policy. -/
  file : String := ""
  /-- `section`: an ATX heading's text, not blank in a valid policy. -/
  heading : String := ""
  /-- `prefix`: not empty in a valid policy. -/
  pfx : String := ""
  /-- `modules`: non-empty in a valid policy. -/
  modules : Array SelectorRef := #[]
  /-- `reason`: not blank in a valid policy. -/
  reason : String := ""
  deriving BEq, Repr, Inhabited

/-- The rule's reference: `doc-modules` and its index. -/
def DocModulesRule.ref (r : DocModulesRule) : RuleRef :=
  ⟨.docModules, r.index⟩

/-- "doc-modules rule 1". -/
def DocModulesRule.label (r : DocModulesRule) : String :=
  r.ref.label

/-- One `[[doc-packages]]` table: the first top-level table in section
`heading` of Markdown file `file` whose header has the columns
`packageColumn`, `layerColumn` and `requiresColumn` has one row per package
`packages` matches, giving its `[layers]` layer and its direct requires less
`requiresExcept`. (`section` is a Lean keyword, hence the field name.) -/
structure DocPackagesRule where
  /-- 1-based, in source order among the `doc-packages` tables; a table with
  errors keeps its number. -/
  index : Nat
  /-- The table's position: its `[[doc-packages]]` header (column 0), or
  the `{` of an inline table. -/
  pos? : Option Toml.Pos
  /-- `file`: relative to the workspace directory, not empty in a valid
  policy. -/
  file : String := ""
  /-- `section`: an ATX heading's text, not blank in a valid policy. -/
  heading : String := ""
  /-- `package-column`: a header cell's text, trimmed; not blank in a valid
  policy. -/
  packageColumn : String := ""
  /-- `layer-column`: as `packageColumn`. -/
  layerColumn : String := ""
  /-- `requires-column`: as `packageColumn`. -/
  requiresColumn : String := ""
  /-- `packages`: non-empty in a valid policy. -/
  packages : Array SelectorRef := #[]
  /-- `requires-except`: package names as written, each with its position;
  possibly empty. -/
  requiresExcept : Array (String × Option Toml.Pos) := #[]
  /-- `reason`: not blank in a valid policy. -/
  reason : String := ""
  deriving BEq, Repr, Inhabited

/-- The rule's reference: `doc-packages` and its index. -/
def DocPackagesRule.ref (r : DocPackagesRule) : RuleRef :=
  ⟨.docPackages, r.index⟩

/-- "doc-packages rule 1". -/
def DocPackagesRule.label (r : DocPackagesRule) : String :=
  r.ref.label

/-- One entry of `[layers]`'s `classify`: the packages `select` matches are
in `layer`. -/
structure LayerClass where
  /-- 1-based, in source order. -/
  index : Nat
  /-- The entry's `{`, or its `[[layers.classify]]` header. -/
  pos? : Option Toml.Pos
  /-- A valid layer name, or `""` after an error. -/
  layer : String := ""
  /-- Non-empty in a valid policy. -/
  select : Array SelectorRef := #[]
  deriving BEq, Repr, Inhabited

/-- One `allow` pair: a module of a package in layer `importer` may import a
module of another package in layer `imported`. -/
structure LayerPair where
  /-- 1-based, in source order among `allow`'s elements. -/
  index : Nat
  /-- The pair's `[`. -/
  pos? : Option Toml.Pos
  importer : String
  imported : String
  /-- Each name's opening `"`, for the unknown-layer error. -/
  importerPos? : Option Toml.Pos
  importedPos? : Option Toml.Pos
  deriving BEq, Repr, Inhabited

/-- `["implementation", "core"]`, as written in TOML. -/
def LayerPair.text (p : LayerPair) : String :=
  s!"[\"{p.importer}\", \"{p.imported}\"]"

/-- The `[layers]` table: every package is in one layer, and every import
between two packages must be an allowed (importer layer, imported layer)
pair. -/
structure LayersRule where
  /-- The `[layers]` header (column 0), or the `{` of `layers = { … }`. -/
  pos? : Option Toml.Pos
  classify : Array LayerClass := #[]
  /-- `default`: the layer of every package no classify entry selects. -/
  default? : Option String := none
  defaultPos? : Option Toml.Pos := none
  /-- `allow`, default none; no two pairs equal in a valid policy. -/
  allow : Array LayerPair := #[]
  /-- `reason`, optional; when given it starts every violation's header. -/
  reason? : Option String := none
  deriving BEq, Repr, Inhabited

/-- The layers it declares: each classify entry's layer by first appearance,
then `default` unless already listed. -/
def LayersRule.layerNames (r : LayersRule) : Array String :=
  let ls :=
    r.classify.foldl (init := #[]) fun acc c =>
      if c.layer.isEmpty || acc.contains c.layer then acc else acc.push c.layer
  match r.default? with
  | some d => if ls.contains d then ls else ls.push d
  | none => ls

/-- Every classify selector, in source order. -/
def LayersRule.refs (r : LayersRule) : Array SelectorRef :=
  r.classify.flatMap (·.select)

/-- One `[[root]]` table: a module no Lake target declares, such as one a
Lake facet generates, read from its file into the graph as a declared
root. -/
structure RootDef where
  /-- 1-based, in source order among the `root` tables. -/
  index : Nat
  /-- The table's position: its `[[root]]` header (column 0), or the `{` of
  an inline table. -/
  pos? : Option Toml.Pos
  module : Lean.Name
  /-- As written: `/` separators, relative to the workspace directory. -/
  path : String
  deriving BEq, Repr, Inhabited

/-- "root 1". -/
def RootDef.label (r : RootDef) : String :=
  s!"root {r.index}"

/-- A parsed policy. -/
structure Policy where
  /-- The policy path as given. It starts every message about the file. -/
  path : String
  /-- Source order. Set names are unique (Lake rejects duplicate keys). -/
  sets : Array SetDef := #[]
  /-- Indices into `sets`, each set after every set it refers to. -/
  order : Array Nat := #[]
  /-- The `[[deny]]` rules, in source order. -/
  deny : Array DenyRule := #[]
  /-- The `[[allow-only]]` rules, in source order. -/
  allowOnly : Array AllowOnlyRule := #[]
  /-- The `[layers]` table, if any (TOML allows at most one). -/
  layers? : Option LayersRule := none
  /-- The `[[reachable]]` rules, in source order. -/
  reachable : Array ReachableRule := #[]
  /-- The `[[co-reach]]` rules, in source order. -/
  coReach : Array CoReachRule := #[]
  /-- The `[[target-config]]` rules, in source order. -/
  targetConfig : Array TargetConfigRule := #[]
  /-- The `[[require-backed]]` rules, in source order. -/
  requireBacked : Array RequireBackedRule := #[]
  /-- The `[[doc-modules]]` rules, in source order. -/
  docModules : Array DocModulesRule := #[]
  /-- The `[[doc-packages]]` rules, in source order. -/
  docPackages : Array DocPackagesRule := #[]
  /-- The `[[root]]` tables, in source order. Not rules. -/
  roots : Array RootDef := #[]
  deriving Repr, Inhabited

/-- Top-level keys this version knows. -/
def knownKeys : Array String :=
  #["sets", "deny", "allow-only", "layers", "reachable", "co-reach", "target-config",
    "require-backed", "doc-modules", "doc-packages", "root"]

/-- The number of rules of every kind; `[layers]` is one rule. Declared roots
are not rules. -/
def Policy.ruleCount (p : Policy) : Nat :=
  p.deny.size + p.allowOnly.size + (if p.layers?.isSome then 1 else 0) + p.reachable.size +
    p.coReach.size +
    p.targetConfig.size +
    p.requireBacked.size +
    p.docModules.size +
    p.docPackages.size

/-- `<path>:<line>:<column>`, or `<path>` with no position. -/
def Policy.posText (path : String) (pos? : Option Toml.Pos) : String :=
  match pos? with
  | some p => s!"{path}:{p.line}:{p.column}"
  | none => path

/-- `<path>:<line>:<column>: <msg>`, or `<path>: <msg>` with no position. -/
def Policy.locate (path : String) (pos? : Option Toml.Pos) (msg : String) : String :=
  s!"{Policy.posText path pos?}: {msg}"

/-- The set named `name`. -/
def Policy.findSet? (p : Policy) (name : String) : Option SetDef :=
  p.sets.find? (·.name == name)

/-- The message for a set name the policy does not define, given on the
command line: "unknown set 'x' in 'lean-deny.toml' (defined: a, b)". -/
def Policy.unknownSet (p : Policy) (name : String) : String :=
  let defined :=
    if p.sets.isEmpty then "it defines no sets"
    else s!"defined: {", ".intercalate (p.sets.map (·.name)).toList}"
  s!"unknown set '{name}' in '{p.path}' ({defined})"

/-- Positions in source order; a missing one sorts first. -/
private def posLt : Option Toml.Pos → Option Toml.Pos → Bool
  | some a, some b => a.line < b.line || (a.line == b.line && a.column < b.column)
  | none, some _ => true
  | _, _ => false

/-- A set's selectors, `select` and `except` together, in source order. -/
def SetDef.refs (d : SetDef) : Array SelectorRef :=
  (d.select ++ d.except).qsort fun a b => posLt a.pos? b.pos?

/-- A deny rule's selectors, `from`, `to` and `wrappers` together, in source
order. -/
def DenyRule.refs (r : DenyRule) : Array SelectorRef :=
  (r.sources ++ r.targets ++ r.wrappers).qsort fun a b => posLt a.pos? b.pos?

/-- An allow-only rule's selectors, `from`, `except` and `allow` together, in
source order. -/
def AllowOnlyRule.refs (r : AllowOnlyRule) : Array SelectorRef :=
  (r.sources ++ r.except ++ r.allow).qsort fun a b => posLt a.pos? b.pos?

/-- A reachable rule's selectors, `from` and `must-cover` together, in source
order. -/
def ReachableRule.refs (r : ReachableRule) : Array SelectorRef :=
  (r.sources ++ r.mustCover).qsort fun a b => posLt a.pos? b.pos?

/-- A co-reach rule's selectors, `roots`, `if-reaches` and `must-reach`
together, in source order. -/
def CoReachRule.refs (r : CoReachRule) : Array SelectorRef :=
  (r.roots ++ r.ifReaches ++ r.mustReach).qsort fun a b => posLt a.pos? b.pos?

/-- A target-config rule's selectors, `targets`, `except` and `or-imports`
together, in source order. -/
def TargetConfigRule.refs (r : TargetConfigRule) : Array SelectorRef :=
  (r.targets ++ r.except ++ r.orImports).qsort fun a b => posLt a.pos? b.pos?

/-- A require-backed rule's selectors, `packages`, in source order. -/
def RequireBackedRule.refs (r : RequireBackedRule) : Array SelectorRef :=
  r.packages

/-- A doc-modules rule's selectors, `modules`, in source order. -/
def DocModulesRule.refs (r : DocModulesRule) : Array SelectorRef :=
  r.modules

/-- A doc-packages rule's selectors, `packages`, in source order. -/
def DocPackagesRule.refs (r : DocPackagesRule) : Array SelectorRef :=
  r.packages

/-- The set a selector names, if any: `set:n`, also inside `imports:`
(`Selector.setName?`). -/
def SelectorRef.setName? (r : SelectorRef) : Option String :=
  r.sel.setName?

/-- Errors being collected, rendered with the policy's path. -/
private structure Errors where
  path : String
  msgs : Array String := #[]

private def Errors.add (e : Errors) (pos? : Option Toml.Pos) (msg : String) : Errors :=
  { e with msgs := e.msgs.push (Policy.locate e.path pos? msg) }

/-- The selectors of one list: each string parsed, every other element an
error that starts with `ctx` (`set 'core'`, `deny rule 1 ('to')`). -/
private def parseSelectors (e : Errors) (ctx : String) (use : Use) (xs : Array Toml.LValue) :
    Errors × Array SelectorRef :=
  Id.run do
    let mut e := e
    let mut refs := #[]
    for x in xs do
      match x with
      | .string pos? s =>
        match Selector.parse s with
        | .ok sel =>
          refs := refs.push { text := s, sel, pos?, use }
        | .error reason =>
          e := e.add pos? s!"invalid selector '{s}': {reason}"
      | _ =>
        e := e.add x.pos? s!"{ctx}: expected a selector string, found {x.kindName}"
    return (e, refs)

/-- One entry of `[sets]`. Even a set with errors is returned, with the
selectors that parsed, so a reference to it is not also reported as
unknown. -/
private def parseSet (e : Errors) (name : String) (v : Toml.LValue) : Errors × SetDef :=
  Id.run do
    let mut e := e
    if !isSetName name then
      e := e.add v.pos? s!"invalid set name '{name}' (use letters, digits, '-' and '_')"
    let base : SetDef := { name, pos? := v.pos?, select := #[], except := #[] }
    match v with
    | .array pos? xs =>
      if xs.isEmpty then
        return (e.add pos? s!"set '{name}' is empty", base)
      let (e', select) := parseSelectors e s!"set '{name}'" (.setSelect name) xs
      return (e', { base with select })
    | .table pos? entries =>
      unless entries.any (·.1 == "select") do
        e := e.add pos? s!"set '{name}' has no 'select' list"
      let mut d := base
      for (k, x) in entries do
        unless k == "select" || k == "except" do
          e := e.add x.pos? s!"set '{name}': unknown key '{k}' (expected 'select' or 'except')"
          continue
        match x with
        | .array xpos? xs =>
          if xs.isEmpty then
            e :=
              e.add xpos? <|
                if k == "select" then s!"set '{name}': 'select' is empty"
                else s!"set '{name}': 'except' is empty (omit it)"
            continue
          let use := if k == "select" then Use.setSelect name else Use.setExcept name
          let (e', refs) := parseSelectors e s!"set '{name}'" use xs
          e := e'
          d := if k == "select" then { d with select := refs } else { d with except := refs }
        | _ =>
          e :=
            e.add x.pos? s!"set '{name}': '{k}' must be an array of selectors, found {x.kindName}"
      return (e, d)
    | _ =>
      return (e.add v.pos? <|
            s!"set '{name}' must be an array of selectors or a table with 'select' and \
              'except', found {v.kindName}",
          base)

/-- A rule field that holds one selector or an array of them (their union):
`none` after an error, the field's kind being wrong or the array empty. An
empty array gives "'k' is empty", or "'k' is empty (omit it)" when
`optional`. Elements go through `parseSelectors` with context
"{label} ('{k}')" and use `use`. -/
private def parseRuleSelectors (e : Errors) (label : String) (use : Use) (k : String)
    (optional : Bool) (x : Toml.LValue) : Errors × Option (Array SelectorRef) :=
  let xs? : Option (Array Toml.LValue) :=
    match x with
    | .string .. => some #[x]
    | .array _ xs => some xs
    | _ => none
  match xs? with
  | none =>
    (e.add x.pos? <|
        s!"{label}: '{k}' must be a selector or an array of selectors, found {x.kindName}",
      none)
  | some xs =>
    if xs.isEmpty then
      (e.add x.pos? <|
          if optional then s!"{label}: '{k}' is empty (omit it)" else s!"{label}: '{k}' is empty",
        none)
    else
      let (e', refs) := parseSelectors e s!"{label} ('{k}')" use xs
      (e', some refs)

/-- A rule's `reason`: a string that is not blank. -/
private def parseReason (e : Errors) (label : String) (x : Toml.LValue) : Errors × Option String :=
  match x with
  | .string _ s =>
    if s.trimAscii.toString.isEmpty then (e.add x.pos? s!"{label}: 'reason' is empty", none)
    else (e, some s)
  | _ => (e.add x.pos? s!"{label}: 'reason' must be a string, found {x.kindName}", none)

/-- A top-level array-of-tables key (`deny`, `allow-only`, `reachable`,
`co-reach`, `target-config`, `require-backed`, `doc-modules`, `doc-packages`, `root`): each table parsed by `parse` with its 1-based index and the tables parsed before
it. -/
private def parseRuleArray {α : Type} (e : Errors) (key : String) (v : Toml.LValue)
    (parse : Errors → Nat → Array α → Toml.LValue → Errors × α) : Errors × Array α :=
  Id.run do
    match v with
    | .array pos? xs =>
      let mut e := e
      if xs.isEmpty then
        e := e.add pos? s!"'{key}' is empty (omit it)"
      let mut rs := #[]
      for (x, i) in xs.zipIdx do
        let (e', r) := parse e (i + 1) rs x
        e := e'
        rs := rs.push r
      return (e, rs)
    | _ =>
      return (e.add v.pos? s!"'{key}' must be an array of tables, such as [[{key}]]", #[])

/-- The keys of a deny table, in the order messages list them. -/
private def denyKeys : Array String :=
  #["from", "to", "transitive", "wrappers", "reason"]

/-- Entry `index` (1-based) of the `deny` array. Even a rule with errors is
returned, with the selectors that parsed, so its `set:` references are still
checked. Missing keys are reported first, at the table, then each entry in
source order. -/
private def parseDeny (e : Errors) (index : Nat) (v : Toml.LValue) : Errors × DenyRule :=
  Id.run do
    let label := s!"deny rule {index}"
    let base : DenyRule := { index, pos? := v.pos? }
    let .table pos? entries := v
      | return (e.add v.pos? s!"{label} must be a table, found {v.kindName}", base)
    let mut e := e
    for k in #["from", "to", "reason"] do
      unless entries.any (·.1 == k) do
        e := e.add pos? s!"{label} has no '{k}'"
    let mut r := base
    for (k, x) in entries do
      match k with
      | "from" | "to" | "wrappers" =>
        let (e', refs?) := parseRuleSelectors e label (.rule "deny" index k) k (k == "wrappers") x
        e := e'
        let some refs := refs? | continue
        r :=
          match k with
          | "from" => { r with sources := refs }
          | "to" => { r with targets := refs }
          | _ => { r with wrappers := refs }
      | "transitive" =>
        match x with
        | .boolean _ b =>
          r := { r with transitive := b }
        | _ =>
          e := e.add x.pos? s!"{label}: 'transitive' must be true or false, found {x.kindName}"
      | "reason" =>
        let (e', reason?) := parseReason e label x
        e := e'
        if let some reason := reason? then
          r := { r with reason }
      | _ =>
        e :=
          e.add x.pos? <|
            s!"{label}: unknown key '{k}' (expected {", ".intercalate denyKeys.toList})"
    return (e, r)

/-- The keys of an allow-only table, in the order messages list them. -/
private def allowOnlyKeys : Array String :=
  #["from", "except", "allow", "reason"]

/-- Entry `index` (1-based) of the `allow-only` array, as `parseDeny`. -/
private def parseAllowOnly (e : Errors) (index : Nat) (v : Toml.LValue) : Errors × AllowOnlyRule :=
  Id.run do
    let label := s!"allow-only rule {index}"
    let base : AllowOnlyRule := { index, pos? := v.pos? }
    let .table pos? entries := v
      | return (e.add v.pos? s!"{label} must be a table, found {v.kindName}", base)
    let mut e := e
    for k in #["from", "allow", "reason"] do
      unless entries.any (·.1 == k) do
        e := e.add pos? s!"{label} has no '{k}'"
    let mut r := base
    for (k, x) in entries do
      match k with
      | "from" | "except" | "allow" =>
        let (e', refs?) :=
          parseRuleSelectors e label (.rule "allow-only" index k) k (k == "except") x
        e := e'
        let some refs := refs? | continue
        r :=
          match k with
          | "from" => { r with sources := refs }
          | "except" => { r with except := refs }
          | _ => { r with allow := refs }
      | "reason" =>
        let (e', reason?) := parseReason e label x
        e := e'
        if let some reason := reason? then
          r := { r with reason }
      | _ =>
        e :=
          e.add x.pos? <|
            s!"{label}: unknown key '{k}' (expected {", ".intercalate allowOnlyKeys.toList})"
    return (e, r)

/-- The keys of a reachable table, in the order messages list them. -/
private def reachableKeys : Array String :=
  #["from", "must-cover", "reason"]

/-- Entry `index` (1-based) of the `reachable` array, as `parseDeny`. -/
private def parseReachable (e : Errors) (index : Nat) (v : Toml.LValue) : Errors × ReachableRule :=
  Id.run do
    let label := s!"reachable rule {index}"
    let base : ReachableRule := { index, pos? := v.pos? }
    let .table pos? entries := v
      | return (e.add v.pos? s!"{label} must be a table, found {v.kindName}", base)
    let mut e := e
    for k in reachableKeys do
      unless entries.any (·.1 == k) do
        e := e.add pos? s!"{label} has no '{k}'"
    let mut r := base
    for (k, x) in entries do
      match k with
      | "from" | "must-cover" =>
        let (e', refs?) := parseRuleSelectors e label (.rule "reachable" index k) k false x
        e := e'
        let some refs := refs? | continue
        r := if k == "from" then { r with sources := refs } else { r with mustCover := refs }
      | "reason" =>
        let (e', reason?) := parseReason e label x
        e := e'
        if let some reason := reason? then
          r := { r with reason }
      | _ =>
        e :=
          e.add x.pos? <|
            s!"{label}: unknown key '{k}' (expected {", ".intercalate reachableKeys.toList})"
    return (e, r)

/-- The keys of a co-reach table, in the order messages list them. -/
private def coReachKeys : Array String :=
  #["roots", "if-reaches", "must-reach", "reason"]

/-- Entry `index` (1-based) of the `co-reach` array, as `parseDeny`. -/
private def parseCoReach (e : Errors) (index : Nat) (v : Toml.LValue) : Errors × CoReachRule :=
  Id.run do
    let label := s!"co-reach rule {index}"
    let base : CoReachRule := { index, pos? := v.pos? }
    let .table pos? entries := v
      | return (e.add v.pos? s!"{label} must be a table, found {v.kindName}", base)
    let mut e := e
    for k in coReachKeys do
      unless entries.any (·.1 == k) do
        e := e.add pos? s!"{label} has no '{k}'"
    let mut r := base
    for (k, x) in entries do
      match k with
      | "roots" | "if-reaches" | "must-reach" =>
        let (e', refs?) := parseRuleSelectors e label (.rule "co-reach" index k) k false x
        e := e'
        let some refs := refs? | continue
        r :=
          if k == "roots" then { r with roots := refs }
          else
            if k == "if-reaches" then { r with ifReaches := refs } else { r with mustReach := refs }
      | "reason" =>
        let (e', reason?) := parseReason e label x
        e := e'
        if let some reason := reason? then
          r := { r with reason }
      | _ =>
        e :=
          e.add x.pos? <|
            s!"{label}: unknown key '{k}' (expected {", ".intercalate coReachKeys.toList})"
    return (e, r)

/-- The keys of a require-backed table, in the order messages list them. -/
private def requireBackedKeys : Array String :=
  #["packages", "reason"]

/-- Entry `index` (1-based) of the `require-backed` array, as `parseDeny`. -/
private def parseRequireBacked (e : Errors) (index : Nat) (v : Toml.LValue) :
    Errors × RequireBackedRule :=
  Id.run do
    let label := s!"require-backed rule {index}"
    let base : RequireBackedRule := { index, pos? := v.pos? }
    let .table pos? entries := v
      | return (e.add v.pos? s!"{label} must be a table, found {v.kindName}", base)
    let mut e := e
    for k in requireBackedKeys do
      unless entries.any (·.1 == k) do
        e := e.add pos? s!"{label} has no '{k}'"
    let mut r := base
    for (k, x) in entries do
      match k with
      | "packages" =>
        let (e', refs?) := parseRuleSelectors e label (.rule "require-backed" index k) k false x
        e := e'
        if let some refs := refs? then
          r := { r with packages := refs }
      | "reason" =>
        let (e', reason?) := parseReason e label x
        e := e'
        if let some reason := reason? then
          r := { r with reason }
      | _ =>
        e :=
          e.add x.pos? <|
            s!"{label}: unknown key '{k}' (expected {", ".intercalate requireBackedKeys.toList})"
    return (e, r)

/-- The keys of a doc-modules table, in the order messages list them. -/
private def docModulesKeys : Array String :=
  #["file", "section", "prefix", "modules", "reason"]

/-- Entry `index` (1-based) of the `doc-modules` array, as `parseDeny`. -/
private def parseDocModules (e : Errors) (index : Nat) (v : Toml.LValue) :
    Errors × DocModulesRule :=
  Id.run do
    let label := s!"doc-modules rule {index}"
    let base : DocModulesRule := { index, pos? := v.pos? }
    let .table pos? entries := v
      | return (e.add v.pos? s!"{label} must be a table, found {v.kindName}", base)
    let mut e := e
    for k in docModulesKeys do
      unless entries.any (·.1 == k) do
        e := e.add pos? s!"{label} has no '{k}'"
    let mut r := base
    for (k, x) in entries do
      match k, x with
      | "file", .string xpos? s =>
        if s.isEmpty then
          e := e.add xpos? s!"{label}: 'file' must not be empty"
        else if (FilePath.mk s).isAbsolute || s.startsWith "/" then
          e := e.add xpos? s!"{label}: 'file' must be relative to the workspace directory"
        else
          r := { r with file := s }
      | "section", .string xpos? s =>
        if s.trimAscii.toString.isEmpty then
          e := e.add xpos? s!"{label}: 'section' is empty"
        else
          r := { r with heading := s }
      | "prefix", .string xpos? s =>
        if s.isEmpty then
          e := e.add xpos? s!"{label}: 'prefix' is empty"
        else
          r := { r with pfx := s }
      | "file", _ | "section", _ | "prefix", _ =>
        e := e.add x.pos? s!"{label}: '{k}' must be a string, found {x.kindName}"
      | "modules", _ =>
        let (e', refs?) := parseRuleSelectors e label (.rule "doc-modules" index k) k false x
        e := e'
        if let some refs := refs? then
          r := { r with modules := refs }
      | "reason", _ =>
        let (e', reason?) := parseReason e label x
        e := e'
        if let some reason := reason? then
          r := { r with reason }
      | _, _ =>
        e :=
          e.add x.pos? <|
            s!"{label}: unknown key '{k}' (expected {", ".intercalate docModulesKeys.toList})"
    return (e, r)

/-- The keys of a doc-packages table, in the order messages list them;
`requires-except` is optional. -/
private def docPackagesKeys : Array String :=
  #["file", "section", "package-column", "layer-column", "requires-column", "packages",
    "requires-except", "reason"]

/-- A doc-packages table's `requires-except`: a package name or a non-empty
array of them, each non-empty; `none` after an error. -/
private def parseRequiresExcept (e : Errors) (label : String) (x : Toml.LValue) :
    Errors × Option (Array (String × Option Toml.Pos)) :=
  Id.run do
    let k := "requires-except"
    let xs? : Option (Array Toml.LValue) :=
      match x with
      | .string .. => some #[x]
      | .array _ xs => some xs
      | _ => none
    let some xs := xs?
      |
      return (e.add x.pos? <|
            s!"{label}: '{k}' must be a package name or an array of package names, found \
              {x.kindName}",
          none)
    if xs.isEmpty then
      return (e.add x.pos? s!"{label}: '{k}' is empty (omit it)", none)
    let mut e := e
    let mut names := #[]
    let mut ok := true
    for y in xs do
      match y with
      | .string pos? s =>
        if s.trimAscii.toString.isEmpty then
          e := e.add pos? s!"{label} ('{k}'): a package name is empty"
          ok := false
        else
          names := names.push (s, pos?)
      | _ =>
        e := e.add y.pos? s!"{label} ('{k}'): expected a package name string, found {y.kindName}"
        ok := false
    return (e, if ok then some names else none)

/-- Entry `index` (1-based) of the `doc-packages` array, as `parseDeny`;
then, once every key is read, each column name that repeats an earlier one
(`package-column`, `layer-column`, `requires-column`, in that order), at
the repeating key. -/
private def parseDocPackages (e : Errors) (index : Nat) (v : Toml.LValue) :
    Errors × DocPackagesRule :=
  Id.run do
    let label := s!"doc-packages rule {index}"
    let base : DocPackagesRule := { index, pos? := v.pos? }
    let .table pos? entries := v
      | return (e.add v.pos? s!"{label} must be a table, found {v.kindName}", base)
    let mut e := e
    for k in docPackagesKeys do
      unless k == "requires-except" || entries.any (·.1 == k) do
        e := e.add pos? s!"{label} has no '{k}'"
    let mut r := base
    -- Each column parsed: its key, its trimmed name and its value's position.
    let mut columns : Array (String × String × Option Toml.Pos) := #[]
    for (k, x) in entries do
      match k, x with
      | "file", .string xpos? s =>
        if s.isEmpty then
          e := e.add xpos? s!"{label}: 'file' must not be empty"
        else if (FilePath.mk s).isAbsolute || s.startsWith "/" then
          e := e.add xpos? s!"{label}: 'file' must be relative to the workspace directory"
        else
          r := { r with file := s }
      | "section", .string xpos? s =>
        if s.trimAscii.toString.isEmpty then
          e := e.add xpos? s!"{label}: 'section' is empty"
        else
          r := { r with heading := s }
      | "package-column", .string xpos? s | "layer-column", .string xpos? s | "requires-column",
        .string xpos? s =>
        let t := s.trimAscii.toString
        if t.isEmpty then
          e := e.add xpos? s!"{label}: '{k}' is empty"
        else
          columns := columns.push (k, t, xpos?)
          r :=
            match k with
            | "package-column" => { r with packageColumn := t }
            | "layer-column" => { r with layerColumn := t }
            | _ => { r with requiresColumn := t }
      | "file", _ | "section", _ | "package-column", _ | "layer-column", _ | "requires-column", _ =>
        e := e.add x.pos? s!"{label}: '{k}' must be a string, found {x.kindName}"
      | "packages", _ =>
        let (e', refs?) := parseRuleSelectors e label (.rule "doc-packages" index k) k false x
        e := e'
        if let some refs := refs? then
          r := { r with packages := refs }
      | "requires-except", _ =>
        let (e', names?) := parseRequiresExcept e label x
        e := e'
        if let some names := names? then
          r := { r with requiresExcept := names }
      | "reason", _ =>
        let (e', reason?) := parseReason e label x
        e := e'
        if let some reason := reason? then
          r := { r with reason }
      | _, _ =>
        e :=
          e.add x.pos? <|
            s!"{label}: unknown key '{k}' (expected {", ".intercalate docPackagesKeys.toList})"
    let order := #["package-column", "layer-column", "requires-column"]
    let ordered := order.filterMap fun k => columns.find? (·.1 == k)
    for (c, i) in ordered.zipIdx do
      let (k, t, xpos?) := c
      if let some (k0, _, _) := (ordered.extract 0 i).find? (·.2.1 == t) then
        e := e.add xpos? s!"{label}: '{k}' names the same column as '{k0}' ('{t}')"
    return (e, r)

/-- The keys of a target-config table, in the order messages list them. -/
private def targetConfigKeys : Array String :=
  #["targets", "except", "load-plugin", "or-imports", "reason"]

/-- Entry `index` (1-based) of the `target-config` array, as `parseDeny`.
`targets` and `except` take only `pkg:` and `lib:` selectors; any other
form is an error and is dropped. -/
private def parseTargetConfig (e : Errors) (index : Nat) (v : Toml.LValue) :
    Errors × TargetConfigRule :=
  Id.run do
    let label := s!"target-config rule {index}"
    let base : TargetConfigRule := { index, pos? := v.pos? }
    let .table pos? entries := v
      | return (e.add v.pos? s!"{label} must be a table, found {v.kindName}", base)
    let mut e := e
    for k in #["targets", "load-plugin", "reason"] do
      unless entries.any (·.1 == k) do
        e := e.add pos? s!"{label} has no '{k}'"
    let mut r := base
    for (k, x) in entries do
      match k with
      | "targets" | "except" | "or-imports" =>
        let (e', refs?) :=
          parseRuleSelectors e label (.rule "target-config" index k) k (k != "targets") x
        e := e'
        let some refs := refs? | continue
        if k == "or-imports" then
          r := { r with orImports := refs }
          continue
        let mut kept := #[]
        for ref in refs do
          match ref.sel with
          | .pkg _ | .lib .. =>
            kept := kept.push ref
          | _ =>
            e :=
              e.add ref.pos? <|
                s!"{label} ('{k}'): '{ref.text}' is not a target selector (expected \
                  pkg:<package>, lib:<lib> or lib:<package>/<lib>)"
        r := if k == "targets" then { r with targets := kept } else { r with except := kept }
      | "load-plugin" =>
        match x with
        | .string _ s =>
          match PluginName.parse? s with
          | some n =>
            r := { r with loadPlugin? := some n }
          | none =>
            e :=
              e.add x.pos? <|
                s!"{label}: 'load-plugin' must be a Lake target name, '<target>' or \
                  '@<package>/<target>', found '{s}'"
        | _ =>
          e := e.add x.pos? s!"{label}: 'load-plugin' must be a string, found {x.kindName}"
      | "reason" =>
        let (e', reason?) := parseReason e label x
        e := e'
        if let some reason := reason? then
          r := { r with reason }
      | _ =>
        e :=
          e.add x.pos? <|
            s!"{label}: unknown key '{k}' (expected {", ".intercalate targetConfigKeys.toList})"
    return (e, r)

/-- The keys of `[layers]`, in the order messages list them. -/
private def layersKeys : Array String :=
  #["classify", "default", "allow", "same-package", "reason"]

/-- A layer name (field `k` of `label`): a string with the set-name syntax;
`none` after an error. -/
private def parseLayerName (e : Errors) (label k : String) (x : Toml.LValue) :
    Errors × Option String :=
  match x with
  | .string pos? s =>
    if isSetName s then (e, some s)
    else (e.add pos? s!"{label}: invalid layer name '{s}' (use letters, digits, '-' and '_')", none)
  | _ => (e.add x.pos? s!"{label}: '{k}' must be a layer name, found {x.kindName}", none)

/-- Entry `index` (1-based) of `[layers]`'s `classify`, as `parseDeny`: missing
keys first, at the entry, then each key in source order. -/
private def parseLayerClass (e : Errors) (index : Nat) (v : Toml.LValue) : Errors × LayerClass :=
  Id.run do
    let label := s!"layers classify entry {index}"
    let base : LayerClass := { index, pos? := v.pos? }
    let .table pos? entries := v
      | return (e.add v.pos? s!"{label} must be a table, found {v.kindName}", base)
    let mut e := e
    for k in #["layer", "select"] do
      unless entries.any (·.1 == k) do
        e := e.add pos? s!"{label} has no '{k}'"
    let mut c := base
    for (k, x) in entries do
      match k with
      | "layer" =>
        let (e', layer?) := parseLayerName e label "layer" x
        e := e'
        if let some layer := layer? then
          c := { c with layer }
      | "select" =>
        let (e', refs?) := parseRuleSelectors e label (.layer index) "select" false x
        e := e'
        if let some select := refs? then
          c := { c with select }
      | _ =>
        e := e.add x.pos? s!"{label}: unknown key '{k}' (expected layer, select)"
    return (e, c)

/-- `[layers]`'s `allow`: a non-empty array of `[importer, imported]` pairs of
strings, none repeated. -/
private def parseLayerPairs (e : Errors) (x : Toml.LValue) : Errors × Array LayerPair :=
  Id.run do
    let .array pos? xs := x
      |
      return (e.add x.pos? <|
            s!"layers: 'allow' must be an array of layer pairs, such as \
              [[\"implementation\", \"core\"]], found {x.kindName}",
          #[])
    if xs.isEmpty then
      return (e.add pos? "layers: 'allow' is empty (omit it)", #[])
    let mut e := e
    let mut pairs : Array LayerPair := #[]
    for (y, i) in xs.zipIdx do
      let index := i + 1
      let pair? : Option LayerPair :=
        match y with
        | .array ppos? ys =>
          match ys.toList with
          | [.string apos? a, .string bpos? b] =>
            some
              { index, pos? := ppos?, importer := a, imported := b, importerPos? := apos?
                importedPos? := bpos? }
          | _ => none
        | _ => none
      let some p := pair?
        |
        e :=
          e.add y.pos? <|
            s!"layers: allow entry {index} must be a pair of layer names [importer, imported], \
                such as [\"implementation\", \"core\"]"
        continue
      match pairs.find? fun q => q.importer == p.importer && q.imported == p.imported with
      | some q =>
        e := e.add p.pos? s!"layers: allow entry {index} repeats allow entry {q.index} ({p.text})"
      | none =>
        pairs := pairs.push p
    return (e, pairs)

/-- The `[layers]` table: `none` when it is not a table. A missing `classify`
is reported first, at the table, then each key in source order, then, only
when every layer is known (`classify` and every entry's `layer` parsed, and
`default` if given), each `allow` pair's names that no layer declares
(importer before imported). -/
private def parseLayers (e : Errors) (v : Toml.LValue) : Errors × Option LayersRule :=
  Id.run do
    let .table pos? entries := v
      | return (e.add v.pos? "'layers' must be a table, such as [layers]", none)
    let mut e := e
    let hasClassify := entries.any (·.1 == "classify")
    unless hasClassify do
      e := e.add pos? "layers has no 'classify'"
    let mut r : LayersRule := { pos? }
    -- Whether the declared layers are all known, so an unknown one is a real
    -- error.
    let mut declared := hasClassify
    for (k, x) in entries do
      match k with
      | "classify" =>
        match x with
        | .array xpos? xs =>
          if xs.isEmpty then
            e := e.add xpos? "layers: 'classify' is empty"
            declared := false
          for (y, i) in xs.zipIdx do
            let (e', c) := parseLayerClass e (i + 1) y
            e := e'
            if c.layer.isEmpty then
              declared := false
            r := { r with classify := r.classify.push c }
        | _ =>
          e :=
            e.add x.pos?
              "layers: 'classify' must be an array of tables, such as [[layers.classify]]"
          declared := false
      | "default" =>
        let (e', d?) := parseLayerName e "layers" "default" x
        e := e'
        match d? with
        | some d =>
          r :=
            { r with
              default? := some d, defaultPos? := x.pos? }
        | none =>
          declared := false
      | "allow" =>
        let (e', allow) := parseLayerPairs e x
        e := e'
        r := { r with allow }
      | "same-package" =>
        let isAllow :=
          match x with
          | .string _ s => s == "allow"
          | _ => false
        unless isAllow do
          e :=
            e.add x.pos? <|
              "layers: 'same-package' must be \"allow\": imports within one package are always \
                allowed"
      | "reason" =>
        let (e', reason?) := parseReason e "layers" x
        e := e'
        if reason?.isSome then
          r := { r with reason? }
      | _ =>
        e :=
          e.add x.pos? <|
            s!"layers: unknown key '{k}' (expected {", ".intercalate layersKeys.toList})"
    if declared then
      let names := r.layerNames
      for p in r.allow do
        for (l, lpos?) in [(p.importer, p.importerPos?), (p.imported, p.importedPos?)] do
          unless names.contains l do
            e :=
              e.add lpos? <|
                s!"layers: allow entry {p.index} names layer '{l}', which neither a classify \
                  entry nor 'default' declares (layers: {", ".intercalate names.toList})"
    return (e, some r)

/-- One `[[root]]` table while parsing: each field `none` until it parses. -/
private structure RootParse where
  index : Nat
  pos? : Option Toml.Pos
  module? : Option Lean.Name := none
  path? : Option String := none
  deriving Inhabited

/-- Entry `index` (1-based) of the `root` array, given the entries before
it. Missing keys are reported first, at the table, then each entry in source
order, then a module or path an earlier table already declares. -/
private def parseRoot (e : Errors) (index : Nat) (prev : Array RootParse) (v : Toml.LValue) :
    Errors × RootParse :=
  Id.run do
    let label := s!"root {index}"
    let base : RootParse := { index, pos? := v.pos? }
    let .table pos? entries := v
      | return (e.add v.pos? s!"{label} must be a table, found {v.kindName}", base)
    let mut e := e
    for k in #["module", "path"] do
      unless entries.any (·.1 == k) do
        e := e.add pos? s!"{label} has no '{k}'"
    let mut r := base
    for (k, x) in entries do
      match k, x with
      | "module", .string xpos? s =>
        match parseModuleName? s with
        | some n =>
          r := { r with module? := some n }
        | none =>
          e := e.add xpos? s!"{label}: 'module': '{s}' is not a module name"
      | "path", .string xpos? s =>
        if s.isEmpty then
          e := e.add xpos? s!"{label}: 'path' must not be empty"
        else if (FilePath.mk s).isAbsolute || s.startsWith "/" then
          e := e.add xpos? s!"{label}: 'path' must be relative to the workspace directory"
        else
          r := { r with path? := some s }
      | "module", _ | "path", _ =>
        e := e.add x.pos? s!"{label}: '{k}' must be a string, found {x.kindName}"
      | _, _ =>
        e := e.add x.pos? s!"{label}: unknown key '{k}' (expected module, path)"
    if let some m := r.module? then
      if let some q := prev.find? (·.module? == some m) then
        e := e.add pos? s!"{label}: module {m} is already declared by root {q.index}"
    if let some p := r.path? then
      if let some q := prev.find? (·.path? == some p) then
        e := e.add pos? s!"{label}: path '{p}' is already declared by root {q.index}"
    return (e, r)

/-- The roots of `root`'s tables that parsed in full. -/
private def completeRoots (rs : Array RootParse) : Array RootDef :=
  rs.filterMap fun r =>
    match r.module?, r.path? with
    | some module, some path => some { index := r.index, pos? := r.pos?, module, path }
    | _, _ => none

/-- The depth-first walk that finds cycles and the order. -/
private structure Walk where
  /-- Per set: 0 not seen, 1 on the stack, 2 done. -/
  state : Array Nat
  order : Array Nat := #[]
  errs : Errors

/-- Visit set `i`. `stack` holds each set on the walk's path with the
selector it left by. `fuel` bounds the depth (the number of sets). -/
private def visit (sets : Array SetDef) (index : String → Option Nat) :
    Nat → Nat → Array (Nat × SelectorRef) → Walk → Walk
  | 0, _, _, w => w
  | fuel + 1, i, stack, w =>
    Id.run do
      let mut w := { w with state := w.state.set! i 1 }
      let some d := sets[i]? | return w
      for r in d.refs do
        let some j := r.setName?.bind index | continue
        match w.state[j]? with
        | some 0 =>
          w := visit sets index fuel j (stack.push (i, r)) w
        | some 1 =>
          let path := stack.push (i, r)
          let k := (path.findIdx? (·.1 == j)).getD 0
          let slice := path.extract k path.size
          let name (n : Nat) : String := (sets[n]?.map (·.name)).getD ""
          let names := slice.map (name ·.1) |>.push (name j)
          w :=
            { w with
              errs :=
                w.errs.add (slice[0]?.bind (·.2.pos?))
                  s!"set '{name j}' refers to itself: {" -> ".intercalate names.toList}" }
        | _ =>
          pure ()
      return { w with
          state := w.state.set! i 2, order := w.order.push i }

/-- Check the `set:` references: each names a set, and no set refers to
itself. Returns the errors and the order. -/
private def checkRefs (e : Errors) (sets : Array SetDef) : Errors × Array Nat :=
  Id.run do
    let names := sets.map (·.name)
    let index (n : String) : Option Nat := names.findIdx? (· == n)
    let mut e := e
    for d in sets do
      for r in d.refs do
        if let some n := r.setName? then
          if (index n).isNone then
            e :=
              e.add r.pos? <|
                s!"{r.describe} names an unknown set (defined: {", ".intercalate names.toList})"
    let mut w : Walk := { state := Array.replicate sets.size 0, errs := e }
    for i in [0:sets.size] do
      if w.state[i]? == some 0 then
        w := visit sets index (sets.size + 1) i #[] w
    return (w.errs, w.order)

/-- Check that every `set:` in a rule names a set. `refs` holds each rule's
selectors (`DenyRule.refs`, `AllowOnlyRule.refs`, `LayersRule.refs`,
`ReachableRule.refs`, `CoReachRule.refs`, `TargetConfigRule.refs`,
`RequireBackedRule.refs`, `DocModulesRule.refs`, `DocPackagesRule.refs`), in
rule order. -/
private def checkRuleRefs (e : Errors) (sets : Array SetDef) (refs : Array (Array SelectorRef)) :
    Errors :=
  Id.run do
    let names := sets.map (·.name)
    let defined :=
      if names.isEmpty then "the policy defines no sets"
      else s!"defined: {", ".intercalate names.toList}"
    let mut e := e
    for rule in refs do
      for r in rule do
        if let some n := r.setName? then
          unless names.contains n do
            e := e.add r.pos? s!"{r.describe} names an unknown set ({defined})"
    return e

/-- Build the policy from the parsed TOML document at `path`. -/
def Policy.ofToml (path : String) (entries : Array (String × Toml.LValue)) :
    Except (Array String) Policy :=
  Id.run do
    let mut e : Errors := { path }
    let mut sets := #[]
    let mut deny := #[]
    let mut allowOnly := #[]
    let mut layers? := none
    let mut reachable := #[]
    let mut coReach := #[]
    let mut targetConfig := #[]
    let mut requireBacked := #[]
    let mut docModules := #[]
    let mut docPackages := #[]
    let mut roots := #[]
    for (k, v) in entries do
      if k == "sets" then
        match v with
        | .table _ es =>
          for (name, sv) in es do
            let (e', d) := parseSet e name sv
            e := e'
            sets := sets.push d
        | _ =>
          e := e.add v.pos? "'sets' must be a table, such as [sets]"
      else if k == "deny" then
        let (e', rs) := parseRuleArray e "deny" v fun e i _ x => parseDeny e i x
        e := e'
        deny := deny ++ rs
      else if k == "allow-only" then
        let (e', rs) := parseRuleArray e "allow-only" v fun e i _ x => parseAllowOnly e i x
        e := e'
        allowOnly := allowOnly ++ rs
      else if k == "layers" then
        let (e', r?) := parseLayers e v
        e := e'
        layers? := r?
      else if k == "reachable" then
        let (e', rs) := parseRuleArray e "reachable" v fun e i _ x => parseReachable e i x
        e := e'
        reachable := reachable ++ rs
      else if k == "co-reach" then
        let (e', rs) := parseRuleArray e "co-reach" v fun e i _ x => parseCoReach e i x
        e := e'
        coReach := coReach ++ rs
      else if k == "target-config" then
        let (e', rs) := parseRuleArray e "target-config" v fun e i _ x => parseTargetConfig e i x
        e := e'
        targetConfig := targetConfig ++ rs
      else if k == "require-backed" then
        let (e', rs) := parseRuleArray e "require-backed" v fun e i _ x => parseRequireBacked e i x
        e := e'
        requireBacked := requireBacked ++ rs
      else if k == "doc-modules" then
        let (e', rs) := parseRuleArray e "doc-modules" v fun e i _ x => parseDocModules e i x
        e := e'
        docModules := docModules ++ rs
      else if k == "doc-packages" then
        let (e', rs) := parseRuleArray e "doc-packages" v fun e i _ x => parseDocPackages e i x
        e := e'
        docPackages := docPackages ++ rs
      else if k == "root" then
        let (e', rs) := parseRuleArray e "root" v parseRoot
        e := e'
        roots := completeRoots rs
      else
        e := e.add v.pos? s!"unknown key '{k}' (known keys: {", ".intercalate knownKeys.toList})"
    -- A doc-packages rule compares each row's layer with `[layers]`'s.
    unless entries.any (·.1 == "layers") do
      for r in docPackages do
        e :=
          e.add r.pos? s!"{r.label}: the policy has no [layers], which gives each package's layer"
    let (e', order) := checkRefs e sets
    let refs :=
      deny.map (·.refs) ++ allowOnly.map (·.refs) ++ (layers?.map (#[·.refs])).getD #[] ++
        reachable.map (·.refs) ++
        coReach.map (·.refs) ++
        targetConfig.map (·.refs) ++
        requireBacked.map (·.refs) ++
        docModules.map (·.refs) ++
        docPackages.map (·.refs)
    let errs := checkRuleRefs e' sets refs
    if errs.msgs.isEmpty then
      return .ok
          { path, sets, order, deny, allowOnly, layers?, reachable, coReach, targetConfig,
            requireBacked, docModules, docPackages, roots }
    return .error errs.msgs

/-- Only the `[[root]]` tables of the parsed TOML document at `path`; every
other key is ignored, not checked. `graph` and `explain` (for any selector
that names no set) read a policy this way, so a policy whose rules are broken cannot
stop anyone from looking at the graph. -/
def Policy.rootsOfToml (path : String) (entries : Array (String × Toml.LValue)) :
    Except (Array String) (Array RootDef) :=
  match entries.find? (·.1 == "root") with
  | none => .ok #[]
  | some (_, v) =>
    let (e, rs) := parseRuleArray { path } "root" v parseRoot
    if e.msgs.isEmpty then .ok (completeRoots rs) else .error e.msgs

/-- The default policy file of a workspace. -/
def defaultPolicyPath (workspace : FilePath) : FilePath :=
  if workspace.toString == "." then "lean-deny.toml" else workspace / "lean-deny.toml"

/-- Load the policy at `path`, or the error messages (without any prefix). -/
def loadPolicy (path : FilePath) : IO (Except (Array String) Policy) := do
  unless ← path.pathExists do
    return .error #[s!"no policy file '{path}'"]
  if ← path.isDir then
    return .error #[s!"policy file '{path}' is a directory"]
  let input ←
    try
      IO.FS.readFile path
    catch e =>
      return .error #[s!"cannot read policy file '{path}': {e}"]
  match ← Toml.parseLocated path.toString input with
  | .error msgs =>
    return .error msgs
  | .ok entries =>
    return Policy.ofToml path.toString entries

/-- The prefix of every warning `loadRoots` gives for a policy that is not
valid TOML. -/
def ignoringRootsWarning (msg : String) : String :=
  s!"ignoring the policy's [[root]] tables: {msg}"

/-- The declared roots of the policy at `path`, for `graph` and `explain`:
only the `[[root]]` tables are read (`Policy.rootsOfToml`). A missing file
gives no roots, unless it was given explicitly (`explicit`): then it is an
error, as for `check`. A file that is not valid TOML gives no roots and one
warning per TOML message; a bad `[[root]]` table is an error. On success,
the roots and the warnings. -/
def loadRoots (path : FilePath) (explicit : Bool) :
    IO (Except (Array String) (Array RootDef × Array String)) := do
  unless ← path.pathExists do
    if explicit then
      return .error #[s!"no policy file '{path}'"]
    return .ok (#[], #[])
  if ← path.isDir then
    return .error #[s!"policy file '{path}' is a directory"]
  let input ←
    try
      IO.FS.readFile path
    catch e =>
      return .error #[s!"cannot read policy file '{path}': {e}"]
  match ← Toml.parseLocated path.toString input with
  | .error msgs =>
    return .ok (#[], msgs.map ignoringRootsWarning)
  | .ok entries =>
    return (Policy.rootsOfToml path.toString entries).map (·, #[])

end LeanDeny
