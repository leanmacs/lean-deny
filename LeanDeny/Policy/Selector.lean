import Lean.Data.Name

/-!
# Selectors

A selector names a set of modules: `<kind>:<value>`, such as `pkg:core`,
`lib:core/Core`, `mod:Core.Api`, `mod:Core.Api!`, `keyword:kernel`,
`external:Lean` or `set:core-api`. This module is the syntax only, pure;
`LeanDeny.Policy.Resolve` gives a selector its meaning against a graph.
-/

open Lean

namespace LeanDeny

/-- A parsed selector. -/
inductive Selector where
  /-- `pkg:<name>`: matched against the package name as written in its
  lakefile (`plainName`). -/
  | pkg (name : String)
  /-- `lib:<lib>` (`pkg? = none`) or `lib:<pkg>/<lib>`. -/
  | lib (pkg? : Option String) (name : String)
  /-- `mod:<M>` (`exact = false`: M and every module under it) or `mod:<M>!`
  (M alone). -/
  | mod (name : Name) (exact : Bool)
  /-- `keyword:<kw>`. -/
  | keyword (kw : String)
  /-- `external:<Prefix>`. -/
  | external (pfx : Name)
  /-- `set:<name>`. -/
  | set (name : String)
  deriving BEq, Repr, Inhabited

/-- A valid set name: non-empty, ASCII letters, digits, `-` and `_`. -/
def isSetName (s : String) : Bool :=
  !s.isEmpty && s.all fun c => c.isAlphanum || c == '-' || c == '_'

/-- `s` as a module name written as in `import` (`Core.Api`, `«my-mod».X`):
no empty, numeric or anonymous component. -/
private def moduleName? (s : String) : Option Name :=
  let n := s.toName
  let ok :=
    !n.isAnonymous &&
      n.components.all fun
        | .str _ c => !c.isEmpty
        | _ => false
  if ok then some n else none

private def bangReason : String :=
  "'!' (this module alone) is only valid at the end of a mod: selector"

private def moduleReason (s : String) : String :=
  s!"'{s}' is not a module name"

/-- Parse a selector. The error is the reason only, such as
`nothing after 'pkg:'`; callers add the selector, its position and its
context. -/
def Selector.parse (s : String) : Except String Selector := do
  if s.any Char.isWhitespace then
    throw "contains whitespace"
  let (kind, value) ←
    match s.splitOn ":" with
    | k :: v :: vs =>
      pure (k, ":".intercalate (v :: vs))
    | _ =>
      throw "expected '<kind>:<value>', such as 'mod:Editor.Api'"
  unless ["pkg", "lib", "mod", "keyword", "external", "set"].contains kind do
    throw s!"unknown kind '{kind}' (expected pkg, lib, mod, keyword, external or set)"
  if value.isEmpty then
    throw s!"nothing after '{kind}:'"
  -- `!` is valid only as the last character of a `mod:` value.
  let body := if kind == "mod" && value.endsWith "!" then (value.dropEnd 1).toString else value
  if body.contains '!' then
    throw bangReason
  match kind with
  | "pkg" =>
    if value.contains '/' then
      throw "a package name has no '/' (for a library, use 'lib:<package>/<lib>')"
    return .pkg value
  | "lib" =>
    match value.splitOn "/" with
    | [l] =>
      return .lib none l
    | [p, l] =>
      if p.isEmpty || l.isEmpty then
        throw "expected 'lib:<lib>' or 'lib:<package>/<lib>'"
      return .lib (some p) l
    | _ =>
      throw "expected 'lib:<lib>' or 'lib:<package>/<lib>'"
  | "mod" =>
    let some n := moduleName? body | throw (moduleReason (if body.isEmpty then value else body))
    return .mod n (body.length < value.length)
  | "keyword" =>
    return .keyword value
  | "external" =>
    let some n := moduleName? value | throw (moduleReason value)
    return .external n
  | _ =>
    unless isSetName value do
      throw s!"'{value}' is not a set name (use letters, digits, '-' and '_')"
    return .set value

/-- The canonical text of a selector: `parse (toString s) = .ok s` for every
selector `parse` returns. -/
def Selector.toString : Selector → String
  | .pkg n => s!"pkg:{n}"
  | .lib none l => s!"lib:{l}"
  | .lib (some p) l => s!"lib:{p}/{l}"
  | .mod n exact => s!"mod:{n}{if exact then "!" else ""}"
  | .keyword k => s!"keyword:{k}"
  | .external p => s!"external:{p}"
  | .set n => s!"set:{n}"

instance : ToString Selector :=
  ⟨Selector.toString⟩

end LeanDeny
