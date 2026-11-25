import Lake

/-!
# TOML through Lake's parser

lean-deny parses TOML (`lean-deny.toml`, and the test harness's
`fixture.toml`) with Lake's own parser, `Lake.Toml.loadToml`, rather than
carry a TOML library as a dependency. Like the graph loader in
`LeanDeny/Graph/LakeApi.lean`, that parser is internal Lake API, so this module
is the only place that touches it: callers get plain `Value`s and error
messages already rendered with their positions, and a toolchain bump that
changes `Lake.Toml` breaks only this file.
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

/-- Convert Lake's value, dropping the syntax references. -/
partial def ofLake : Lake.Toml.Value → Value
  | .string _ s => .string s
  | .integer _ n => .integer n
  | .float _ x => .float x
  | .boolean _ b => .boolean b
  | .dateTime _ dt => .dateTime (toString dt)
  | .array _ xs => .array (xs.map ofLake)
  | .table _ t => .table (t.items.map fun (k, v) => (keyString k, ofLake v))

/-- Parse `input` as a TOML document. On failure, each message is rendered as
`<fileName>:<line>:<column>: <text>`; `fileName` is used only for those
positions. -/
def parse (fileName : String) (input : String) :
    IO (Except (Array String) (Array (String × Value))) := do
  let ictx := Parser.mkInputContext input fileName
  match ← (Lake.Toml.loadToml ictx).toBaseIO with
  | .ok t => return .ok (t.items.map fun (k, v) => (keyString k, ofLake v))
  | .error log =>
    let mut msgs := #[]
    for m in log.toList do
      let text := (← m.data.toString).trimAscii.toString
      msgs := msgs.push s!"{m.fileName}:{m.pos.line}:{m.pos.column}: {text}"
    if msgs.isEmpty then
      msgs := msgs.push s!"{fileName}: not a valid TOML document"
    return .error msgs

end LeanDeny.Toml
