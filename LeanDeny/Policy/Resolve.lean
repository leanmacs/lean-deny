import LeanDeny.Graph.Model
import LeanDeny.Graph.View
import LeanDeny.Policy

/-!
# Selectors against the graph

What each selector matches in a loaded graph, and the policy's sets
resolved to modules. Pure.

- `pkg:`, `lib:`, `mod:` and `keyword:` match workspace modules only;
  `external:` matches external ones only.
- `pkg:` and `keyword:` include executables' root modules; `lib:` does not
  (an executable's root is no library's module).
- `mod:` compares names by component: `mod:App` matches `App` and
  `App.Shared`, not `AppTest`.
- A `lib:<lib>` declared by several packages is ambiguous, an error.

A selector that matches nothing is an error. So is an `except` entry that
removes nothing from its set, and a set its `except` list empties: each
would let a rule pass by checking nothing.
-/

open Lean LeanDeny.Graph

namespace LeanDeny

/-- What a selector matches. -/
inductive MatchResult where
  /-- Non-empty, sorted. -/
  | ok (nodes : Array NodeId)
  /-- It matched nothing, and why. -/
  | nothing (reason : String)
  /-- A `lib:` that more than one package declares. -/
  | ambiguous (detail : String)
  deriving BEq, Repr, Inhabited

/-- A workspace node's owners; none for an external one. -/
private def owners (n : Node) : Array Owner :=
  match n.origin with
  | .workspace os => os
  | .external => #[]

private def isExternal (n : Node) : Bool :=
  n.origin == .external

/-- The ids of the nodes satisfying `p`, sorted. -/
private def nodesWhere (g : Graph) (p : Node → Bool) : Array NodeId :=
  Id.run do
    let mut ns := #[]
    for h : i in [0:g.nodes.size] do
      if p g.nodes[i] then
        ns := ns.push i
    return ns

/-- `.ok ns`, or `.nothing reason` when `ns` is empty. -/
private def okOr (ns : Array NodeId) (reason : Unit → String) : MatchResult :=
  if ns.isEmpty then .nothing (reason ()) else .ok ns

private def packageList (g : Graph) : String :=
  ", ".intercalate (g.packages.map (plainName ·.name)).toList

private def findPackage? (g : Graph) (p : String) : Option PackageInfo :=
  g.packages.find? (plainName ·.name == p)

/-- The modules of `lean_lib` `l` of package `pk`. -/
private def libNodes (g : Graph) (pk : PackageInfo) (l : String) : MatchResult :=
  okOr
    (nodesWhere g fun n =>
      (owners n).any fun o => o.pkg == pk.name && o.kind == .lib && plainName o.target == l)
    fun _ => s!"lean_lib '{plainName pk.name}/{l}' has no modules"

/-- What a selector other than `set:` matches in `g`. -/
def matchSelector (g : Graph) : Selector → MatchResult
  | .pkg p =>
    match findPackage? g p with
    | none => .nothing s!"no package named '{p}' (packages: {packageList g})"
    | some pk =>
      okOr (nodesWhere g fun n => (owners n).any (·.pkg == pk.name)) fun _ =>
        s!"package '{p}' has no modules"
  | .lib none l =>
    let decl := g.packages.filter fun pk => pk.libs.any (plainName ·.name == l)
    match decl.toList with
    | [] => .nothing s!"no package has a lean_lib named '{l}'"
    | [pk] => libNodes g pk l
    | _ =>
      .ambiguous <|
        s!"lean_lib '{l}' is in packages \
          {", ".intercalate (decl.map (plainName ·.name)).toList}; write 'lib:<package>/{l}'"
  | .lib (some p) l =>
    match findPackage? g p with
    | none => .nothing s!"no package named '{p}' (packages: {packageList g})"
    | some pk =>
      if pk.libs.any (plainName ·.name == l) then libNodes g pk l
      else .nothing s!"package '{p}' has no lean_lib named '{l}'"
  | .mod m exact =>
    let hit (n : Node) : Bool := if exact then n.name == m else m.isPrefixOf n.name
    okOr (nodesWhere g fun n => !isExternal n && hit n) fun _ =>
      let base :=
        if exact then s!"no workspace module named '{m}'"
        else s!"no workspace module is or is under '{m}'"
      if (nodesWhere g fun n => isExternal n && m.isPrefixOf n.name).isEmpty then base
      else s!"{base}; 'external:{m}' matches modules outside the workspace"
  | .keyword k =>
    let pkgs := g.packages.filter (·.keywords.contains k)
    if pkgs.isEmpty then .nothing s!"no package declares keyword '{k}'"
    else
      okOr (nodesWhere g fun n => (owners n).any fun o => pkgs.any (·.name == o.pkg)) fun _ =>
        s!"the packages with keyword '{k}' \
          ({", ".intercalate (pkgs.map (plainName ·.name)).toList}) have no modules"
  | .external p =>
    okOr (nodesWhere g fun n => isExternal n && p.isPrefixOf n.name) fun _ =>
      s!"no external module is or is under '{p}' \
        (the graph holds only the external modules the workspace imports directly)"
  | .set n => .nothing s!"set:{n} is resolved through the policy"

/-- The union of two sorted arrays of ids, sorted. -/
private def union (a b : Array NodeId) : Array NodeId :=
  Id.run do
    let mut out := #[]
    let mut i := 0
    let mut j := 0
    while i < a.size || j < b.size do
      match a[i]?, b[j]? with
      | some x, some y =>
        if x < y then
          out := out.push x
          i := i + 1
        else
          if y < x then
            out := out.push y
            j := j + 1
          else
            out := out.push x
            i := i + 1
            j := j + 1
      | some x, none =>
        out := out.push x
        i := i + 1
      | none, some y =>
        out := out.push y
        j := j + 1
      | none, none =>
        break
    return out

/-- The ids of sorted `a` that are not in sorted `b`, sorted. -/
private def diff (a b : Array NodeId) : Array NodeId :=
  Id.run do
    let mut out := #[]
    let mut j := 0
    for x in a do
      while b[j]?.any (· < x) do
        j := j + 1
      unless b[j]? == some x do
        out := out.push x
    return out

/-- The indices of set `start` and of every set it refers to, directly or not.
A set is marked when it is pushed, and pushed only if unmarked, so a set named
more than once (a repeated `set:`, or two paths to it) is walked once. The
walk ends when `todo` is empty; no step bound can cut it short. -/
private def closure (p : Policy) (start : Nat) : Array Bool :=
  Id.run do
    let mut seen := (Array.replicate p.sets.size false).set! start true
    let mut todo := #[start]
    repeat
      let some i := todo.back? | break
      todo := todo.pop
      for r in (p.sets[i]?.map (·.refs)).getD #[] do
        if let some n := r.setName? then
          if let some j := p.sets.findIdx? fun (d : SetDef) => d.name == n then
            unless seen[j]?.getD true do
              seen := seen.set! j true
              todo := todo.push j
    return seen

/-- Resolve every set (`only? = none`, used by `check`) or only the closure of
one set (`explain set:x`). Errors are rendered with `Policy.locate`, in
source order of the sets, then of the selectors within a set. A `set:`
selector adds no error of its own: a set it names that failed has reported
already, and the referring set goes on with what that set did match. -/
def resolveSets (g : Graph) (p : Policy) (only? : Option String := none) :
    Except (Array String) (Std.HashMap String (Array NodeId)) :=
  Id.run do
    let wanted :=
      match only? with
      | none => Array.replicate p.sets.size true
      | some n =>
        match p.sets.findIdx? fun (d : SetDef) => d.name == n with
        | some i => closure p i
        | none => Array.replicate p.sets.size false
    let mut res : Std.HashMap String (Array NodeId) := {}
    let mut failed : Std.HashSet String := {}
    let mut errs : Array (Array String) := Array.replicate p.sets.size #[]
    for i in p.order do
      unless wanted[i]?.getD false do
        continue
      let some d := p.sets[i]? | continue
      let refs := d.refs
      let results :=
        refs.map fun r =>
          match r.sel with
          | .set n => MatchResult.ok (res[n]?.getD #[])
          | s => matchSelector g s
      let mut selected := #[]
      let mut removed := #[]
      for (r, m) in refs.zip results do
        if let .ok ns := m then
          match r.use with
          | .setExcept _ =>
            removed := union removed ns
          | _ =>
            selected := union selected ns
      let mut es := #[]
      let loc (pos? : Option Toml.Pos) (msg : String) := Policy.locate p.path pos? msg
      for (r, m) in refs.zip results do
        let fromFailedSet := r.setName?.any failed.contains
        match m with
        | .nothing reason =>
          es := es.push (loc r.pos? s!"{r.describe} matches no module: {reason}")
        | .ambiguous detail =>
          es := es.push (loc r.pos? s!"{r.describe} is ambiguous: {detail}")
        | .ok ns =>
          if let .setExcept _ := r.use then
            if !ns.isEmpty && !fromFailedSet && (diff ns selected).size == ns.size then
              es := es.push (loc r.pos? s!"{r.describe} removes no module from it")
      let result := diff selected removed
      if !selected.isEmpty && result.isEmpty then
        es :=
          es.push <|
            loc d.pos?
              s!"set '{d.name}' matches no module: its except list removes every module it selects"
      if !es.isEmpty then
        failed := failed.insert d.name
        errs := errs.set! i es
      res := res.insert d.name result
    let all := errs.flatMap id
    if all.isEmpty then
      .ok res
    else
      .error all

/-- One selector, such as `explain`'s from the command line. A `set:`
selector resolves that set's closure in `p?`. A message carries the policy's
path only when the selector has a position. -/
def resolveRef (g : Graph) (p? : Option Policy) (r : SelectorRef) :
    Except (Array String) (Array NodeId) :=
  let loc (msg : String) : String :=
    match p?, r.pos? with
    | some p, some _ => Policy.locate p.path r.pos? msg
    | _, _ => msg
  match r.sel with
  | .set n =>
    match p? with
    | none => .error #[loc s!"{r.describe} needs a policy"]
    | some p =>
      if (p.findSet? n).isNone then .error #[p.unknownSet n]
      else (resolveSets g p (only? := some n)).map fun res => res[n]?.getD #[]
  | s =>
    match matchSelector g s with
    | .ok ns => .ok ns
    | .nothing reason => .error #[loc s!"{r.describe} matches no module: {reason}"]
    | .ambiguous detail => .error #[loc s!"{r.describe} is ambiguous: {detail}"]

end LeanDeny
