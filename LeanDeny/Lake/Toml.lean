import Lake

/-!
# TOML through Lake's parser

lean-deny parses TOML (`lean-deny.toml`, and the test harness's
`fixture.toml`) with Lake's own parser, `Lake.Toml.loadToml`, rather than
carry a TOML library as a dependency. Like the graph loader in
`LeanDeny/Graph/LakeApi.lean`, that parser is internal Lake API, so this module
is the only place that touches it: callers get plain values (`Value`, or
`LValue` with each value's line and column) and error messages already
rendered with their positions, and a toolchain bump that changes `Lake.Toml`
breaks only this file.
-/

open Lean System

namespace LeanDeny.Toml

/-- A TOML value, detached from Lake's syntax-carrying representation. -/
inductive Value where
  | string (s : String)
  | integer (n : Int)
  | float (x : Float)
  | boolean (b : Bool)
  /-- A date or time, kept in its TOML text form. -/
  | dateTime (s : String)
  | array (xs : Array Value)
  /-- A table's entries in source order. -/
  | table (entries : Array (String × Value))
  deriving Inhabited

/-- A key as written (without Lean name escaping). -/
def keyString (k : Name) : String :=
  k.toString (escape := false)

/-- A source position: 1-based line, 0-based column, as Lean and Lake print
them. -/
structure Pos where
  line : Nat
  column : Nat
  deriving BEq, Repr, Inhabited

/-- A TOML value with the position of each value's first character: the
opening `"` of a string, the `[` of an array, the `{` of an inline table, or
the header line (column 0) of a `[table]` or `[[array]]`. The position is
`none` only if Lake gave a synthetic reference. -/
inductive LValue where
  | string (pos? : Option Pos) (s : String)
  | integer (pos? : Option Pos) (n : Int)
  | float (pos? : Option Pos) (x : Float)
  | boolean (pos? : Option Pos) (b : Bool)
  /-- A date or time, kept in its TOML text form. -/
  | dateTime (pos? : Option Pos) (s : String)
  | array (pos? : Option Pos) (xs : Array LValue)
  /-- A table's entries in source order. -/
  | table (pos? : Option Pos) (entries : Array (String × LValue))
  deriving Inhabited

/-- The value's position. -/
def LValue.pos? : LValue → Option Pos
  | .string p _ | .integer p _ | .float p _ | .boolean p _ | .dateTime p _ | .array p _ |
    .table p _ => p

/-- The value's kind with its article, for messages: "a string", "an array". -/
def LValue.kindName : LValue → String
  | .string .. => "a string"
  | .integer .. => "an integer"
  | .float .. => "a float"
  | .boolean .. => "a boolean"
  | .dateTime .. => "a date-time"
  | .array .. => "an array"
  | .table .. => "a table"

/-- Drop the positions. -/
partial def LValue.strip : LValue → Value
  | .string _ s => .string s
  | .integer _ n => .integer n
  | .float _ x => .float x
  | .boolean _ b => .boolean b
  | .dateTime _ s => .dateTime s
  | .array _ xs => .array (xs.map strip)
  | .table _ es => .table (es.map fun (k, v) => (k, strip v))

/-- Convert Lake's value, turning each syntax reference into a position in
`fileMap`. -/
partial def ofLake (fileMap : FileMap) (v : Lake.Toml.Value) : LValue :=
  let pos? :=
    v.ref.getPos?.map fun p =>
      let q := fileMap.toPosition p
      { line := q.line, column := q.column : Pos }
  match v with
  | .string _ s => .string pos? s
  | .integer _ n => .integer pos? n
  | .float _ x => .float pos? x
  | .boolean _ b => .boolean pos? b
  | .dateTime _ dt => .dateTime pos? (toString dt)
  | .array _ xs => .array pos? (xs.map (ofLake fileMap))
  | .table _ t => .table pos? (t.items.map fun (k, v) => (keyString k, ofLake fileMap v))

/-- Parse `input` as a TOML document, keeping each value's position. On
failure, each message is rendered as `<fileName>:<line>:<column>: <text>`;
`fileName` is used only for those positions. -/
def parseLocated (fileName : String) (input : String) :
    IO (Except (Array String) (Array (String × LValue))) := do
  let ictx := Parser.mkInputContext input fileName
  match ← (Lake.Toml.loadToml ictx).toBaseIO with
  | .ok t =>
    return .ok (t.items.map fun (k, v) => (keyString k, ofLake ictx.fileMap v))
  | .error log =>
    let mut msgs := #[]
    for m in log.toList do
      let text := (← m.data.toString).trimAscii.toString
      msgs := msgs.push s!"{m.fileName}:{m.pos.line}:{m.pos.column}: {text}"
    if msgs.isEmpty then
      msgs := msgs.push s!"{fileName}: not a valid TOML document"
    return .error msgs

/-- Parse `input` as a TOML document, without positions: `parseLocated`,
then `LValue.strip`. -/
def parse (fileName : String) (input : String) :
    IO (Except (Array String) (Array (String × Value))) := do
  return (← parseLocated fileName input).map (·.map fun (k, v) => (k, v.strip))

end LeanDeny.Toml
