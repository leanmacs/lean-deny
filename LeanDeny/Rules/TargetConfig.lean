import LeanDeny.Graph.Query
import LeanDeny.Graph.View
import LeanDeny.Policy.Resolve
import LeanDeny.Rules.Common

/-!
# `[[target-config]]` rules

A target-config rule says every Lake target (`lean_lib`, `lean_exe`) of
`targets`, minus `except`, loads the plugin `load-plugin`, or (when
`or-imports` is given) has a module whose import closure holds a module of
`or-imports`. Pure.

- The **targets** of a `pkg:<p>` selector are every `lean_lib` and every
  `lean_exe` of package `p`; those of `lib:<l>` or `lib:<p>/<l>` are that
  one library (even one with no modules). `except` takes the same forms.
- A target's **plugins** are its effective ones, as Lake applies them: its
  package's `plugins`, then its own (`LeanDeny.Graph.LibInfo.plugins`). A
  plugin **is** `load-plugin` when it is a package target whose target
  name is the one given and, when a package is given, whose package is that
  one. A facet key (`@p/t:f`) never matches.
- A target's **modules** are, for a library, the workspace modules it owns;
  for an executable, its root module alone, the only module Lake
  elaborates with the executable's plugins. A target **imports** an
  `or-imports` module when some module of it has that module in its import
  closure through at least one import, directly or not (not reflexive),
  every import kind followed: Lean runs the `initialize` of every module
  in an importing module's closure.
- Each checked target that does neither is one violation. Violations come
  by package in the graph's order (Lake's), then libraries in lakefile
  order, then executables in lakefile order.

A rule's selectors are resolved against the graph first. The errors, in
order: each `targets`, `except` or `or-imports` selector that matches
nothing (source order), each `or-imports` selector that matches only
external modules, then, if every `targets` selector matched, each `except`
selector that removes no selected target, then, only if there was no error
so far, a rule `except` leaves with no target. A rule with an error is not
evaluated, and any error anywhere means no violation is reported.
-/

open Lean LeanDeny.Graph

namespace LeanDeny

/-- A target's place in the check order: its package's index in
`Graph.packages`, its kind (libraries first), its index in the package's
`libs` or `exes`. -/
abbrev TargetKey :=
  Nat × Nat × Nat

private def keyLt (a b : TargetKey) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)))

/-- The target at `k`. -/
def targetAt? (g : Graph) (k : TargetKey) : Option TargetRef := do
  let pk ← g.packages[k.1]?
  if k.2.1 == 0 then
    let l ← pk.libs[k.2.2]?
    return {
        pkg := pk.name, kind := .lib, name := l.name, configFile := pk.configFile
        plugins := l.plugins }
  else
    let x ← pk.exes[k.2.2]?
    return {
        pkg := pk.name, kind := .exe, name := x.name, configFile := pk.configFile
        plugins := x.plugins }

private def packageList (g : Graph) : String :=
  ", ".intercalate (g.packages.map (plainName ·.name)).toList

private def findPackage? (g : Graph) (p : String) : Option Nat :=
  g.packages.findIdx? (plainName ·.name == p)

/-- The targets a `pkg:` or `lib:` selector names, or why it names none
(the whole message after the selector's description). -/
def matchTargets (g : Graph) (s : Selector) : Except String (Array TargetKey) :=
  let libKey (pi : Nat) (l : String) : Option TargetKey :=
    (g.packages[pi]?.bind fun pk => pk.libs.findIdx? (plainName ·.name == l)).map (pi, 0, ·)
  match s with
  | .pkg p =>
    match findPackage? g p with
    | none => .error s!"matches no target: no package named '{p}' (packages: {packageList g})"
    | some pi =>
      let pk := g.packages[pi]!
      let ks :=
        (Array.range pk.libs.size).map (pi, 0, ·) ++ (Array.range pk.exes.size).map (pi, 1, ·)
      if ks.isEmpty then
        .error s!"matches no target: package '{p}' declares no lean_lib or lean_exe"
      else .ok ks
  | .lib none l =>
    let decl := (Array.range g.packages.size).filterMap fun pi => libKey pi l
    match decl.toList with
    | [] => .error s!"matches no target: no package has a lean_lib named '{l}'"
    | [k] => .ok #[k]
    | _ =>
      let names := decl.map fun k => (g.packages[k.1]?.map (plainName ·.name)).getD "?"
      .error
        s!"is ambiguous: lean_lib '{l}' is in packages {", ".intercalate names.toList}; \
        write 'lib:<package>/{l}'"
  | .lib (some p) l =>
    match findPackage? g p with
    | none => .error s!"matches no target: no package named '{p}' (packages: {packageList g})"
    | some pi =>
      match libKey pi l with
      | some k => .ok #[k]
      | none => .error s!"matches no target: package '{p}' has no lean_lib named '{l}'"
  | s => .error s!"'{s}' is not a target selector"

/-- A target-config rule with its selectors resolved. -/
structure TargetConfigResolved where
  rule : TargetConfigRule
  plugin : PluginName
  /-- The targets checked, in check order. Non-empty. -/
  targets : Array TargetRef
  /-- The workspace modules of `or-imports`, sorted; empty when it is not
  given. -/
  orImports : Array NodeId
  deriving Inhabited

/-- Resolve rule `r`'s selectors in `g`, with the policy's sets resolved in
`sets`. The errors are in the module doc's order. -/
def resolveTargetConfig (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId))
    (r : TargetConfigRule) : Except (Array String) TargetConfigResolved :=
  Id.run do
    let loc := Policy.locate p.path
    let mut errs := #[]
    let mut selected : Array TargetKey := #[]
    let mut excepts : Array (SelectorRef × Array TargetKey) := #[]
    let mut orImports := #[]
    let mut orExternal := #[]
    let mut targetsFailed := false
    for ref in r.refs do
      match ref.use with
      | .rule _ _ "or-imports" =>
        match matchRef g sets ref with
        | .ok ns =>
          orImports := sortedUnion orImports ns
          if !ns.isEmpty && ns.all (isExternalId g) then
            orExternal := orExternal.push ref
        | m =>
          errs := errs.push (loc ref.pos? ((matchError? ref m).getD ""))
      | use =>
        let isExcept := use == .rule "target-config" r.index "except"
        match matchTargets g ref.sel with
        | .ok ks =>
          if isExcept then
            excepts := excepts.push (ref, ks)
          else
            for k in ks do
              unless selected.contains k do
                selected := selected.push k
        | .error msg =>
          if !isExcept then
            targetsFailed := true
          errs := errs.push (loc ref.pos? s!"{ref.describe} {msg}")
    for ref in orExternal do
      let msg :=
        s!"{ref.describe} matches only modules outside the workspace, which a rule about \
          reach does not check"
      errs := errs.push (loc ref.pos? msg)
    if !targetsFailed then
      for (ref, ks) in excepts do
        unless ks.any selected.contains do
          errs := errs.push (loc ref.pos? s!"{ref.describe} removes no target the rule selects")
    let removed := excepts.flatMap (·.2)
    let checked := (selected.filter (!removed.contains ·)).qsort keyLt
    if errs.isEmpty && checked.isEmpty then
      let msg := s!"{r.label}: 'except' removes every target it selects, so it checks nothing"
      errs := errs.push (loc r.pos? msg)
    if !errs.isEmpty then
      return .error errs
    let some plugin := r.loadPlugin?
      | return .error #[loc r.pos? s!"{r.label} has no 'load-plugin'"]
    return .ok
        { rule := r, plugin, targets := checked.filterMap (targetAt? g)
          orImports := orImports.filter (!isExternalId g ·) }

/-- Plugin `p` is the one `n` names: a package target with `n`'s target
name, and `n`'s package when it gives one. -/
def PluginName.matches (n : PluginName) (p : PluginRef) : Bool :=
  match p.target? with
  | none => false
  | some t =>
    plainName t == n.target &&
      match n.pkg? with
      | none => true
      | some pkg => (p.pkg?.map plainName) == some pkg

/-- The modules of target `t`: a library's workspace modules, an
executable's root module. -/
def targetModules (g : Graph) (t : TargetRef) : Array NodeId :=
  (Array.range g.nodes.size).filter fun i =>
    match g.nodes[i]?.map (·.origin) with
    | some (Origin.workspace os) =>
      os.any fun o => o.pkg == t.pkg && o.kind == t.kind && o.target == t.name
    | _ => false

/-- The violation of rule `d` for target `t`. -/
def TargetConfigResolved.violation (d : TargetConfigResolved) (t : TargetRef) : Violation :=
  let imports :=
    if d.rule.orImports.isEmpty then ""
    else s!" and imports no module of {" or ".intercalate (d.rule.orImports.map (·.text)).toList}"
  let detail :=
    s!"{t.kindText} {plainName t.pkg}/{plainName t.name} does not load {d.plugin.text}{imports}"
  { rule := d.rule.ref, pos? := d.rule.pos?, reason? := some d.rule.reason, detail? := some detail
    chain := #[], target? := some t }

/-- Evaluate a resolved rule: one violation per checked target that neither
loads the plugin nor imports an `or-imports` module, in check order. -/
def evalTargetConfig (g : Graph) (d : TargetConfigResolved) : Array Violation :=
  let mask := memberMask g d.orImports
  d.targets.filterMap fun t =>
    if t.plugins.any d.plugin.matches then none
    else
      let imports :=
        !d.orImports.isEmpty && (g.reachable (targetModules g t)).any (mask[·]?.getD false)
      if imports then none else some (d.violation t)

/-- Every target-config rule of `p`, with the policy's sets resolved in
`sets`: the violations in rule order, or every rule's errors in rule
order. -/
def checkTargetConfig (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId)) :
    Except (Array String) (Array Violation) :=
  Id.run do
    let mut errs := #[]
    let mut vs := #[]
    for r in p.targetConfig do
      match resolveTargetConfig g p sets r with
      | .error es =>
        errs := errs ++ es
      | .ok d =>
        vs := vs ++ evalTargetConfig g d
    if errs.isEmpty then
      return .ok vs
    return .error errs

end LeanDeny
