import LeanDeny.Lake.Toml
import LeanDeny.Policy.Selector

/-!
# Policy file

`lean-deny.toml`. This version knows one top-level key, `[sets]`: named
sets of modules, each a list of selectors (`LeanDeny.Policy.Selector`) or a
table with a `select` and an `except` list. No rule kinds exist yet. Any
other key is rejected rather than ignored, so a policy full of rules cannot
pass while checking nothing.

Loading checks everything that needs no graph: the file's shape, each
selector's syntax, that every `set:` names a set, and that no set refers to
itself. Every error is collected, in source order, each starting with
`<path>:<line>:<column>: `. What the selectors match is checked against the
graph later (`LeanDeny.Policy.Resolve`).
-/

open System

namespace LeanDeny

/-- Where a selector is written. Error messages name it, so an author can
find the rule a selector belongs to. Phase 2+ add one constructor per rule
kind, e.g. `| rule (kind : String) (index : Nat) (field : String)` rendered
" in deny rule 1 ('from')". -/
inductive Use where
  /-- The bare array, or the `select` list, of set `name`. -/
  | setSelect (name : String)
  /-- The `except` list of set `name`. -/
  | setExcept (name : String)
  /-- `lean-deny explain <selector>`. -/
  | commandLine
  deriving BEq, Repr, Inhabited

/-- The clause a message puts after the selector: " in set 'core'",
" in the except list of set 'core'", or "" on the command line. -/
def Use.clause : Use → String
  | .setSelect n => s!" in set '{n}'"
  | .setExcept n => s!" in the except list of set '{n}'"
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

/-- A parsed policy. -/
structure Policy where
  /-- The policy path as given. It starts every message about the file. -/
  path : String
  /-- Source order. Set names are unique (Lake rejects duplicate keys). -/
  sets : Array SetDef := #[]
  /-- Indices into `sets`, each set after every set it refers to. -/
  order : Array Nat := #[]
  deriving Repr, Inhabited

/-- Top-level keys this version knows. Phase 2+ append rule tables here. -/
def knownKeys : Array String :=
  #["sets"]

/-- `<path>:<line>:<column>: <msg>`, or `<path>: <msg>` with no position. -/
def Policy.locate (path : String) (pos? : Option Toml.Pos) (msg : String) : String :=
  match pos? with
  | some p => s!"{path}:{p.line}:{p.column}: {msg}"
  | none => s!"{path}: {msg}"

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

/-- The set a selector names, if it is a `set:` selector. -/
def SelectorRef.setName? (r : SelectorRef) : Option String :=
  match r.sel with
  | .set n => some n
  | _ => none

/-- Errors being collected, rendered with the policy's path. -/
private structure Errors where
  path : String
  msgs : Array String := #[]

private def Errors.add (e : Errors) (pos? : Option Toml.Pos) (msg : String) : Errors :=
  { e with msgs := e.msgs.push (Policy.locate e.path pos? msg) }

/-- The selectors of one list of set `set`: each string parsed, every other
element an error. -/
private def parseSelectors (e : Errors) (set : String) (use : Use) (xs : Array Toml.LValue) :
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
        e := e.add x.pos? s!"set '{set}': expected a selector string, found {x.kindName}"
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
      let (e', select) := parseSelectors e name (.setSelect name) xs
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
          let (e', refs) := parseSelectors e name use xs
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

/-- Build the policy from the parsed TOML document at `path`. -/
def Policy.ofToml (path : String) (entries : Array (String × Toml.LValue)) :
    Except (Array String) Policy :=
  Id.run do
    let mut e : Errors := { path }
    let mut sets := #[]
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
      else
        e := e.add v.pos? s!"unknown key '{k}' (known keys: {", ".intercalate knownKeys.toList})"
    let (errs, order) := checkRefs e sets
    if errs.msgs.isEmpty then
      return .ok { path, sets, order }
    return .error errs.msgs

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

end LeanDeny
