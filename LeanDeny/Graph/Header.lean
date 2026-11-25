import Lean.Parser.Module
import Lean.Elab.ParseImportsFast
import LeanDeny.Graph.Raw

/-!
# Import lines from Lean's header parser

Lake's header parser (`Lean.parseImports'`) keeps no positions, so the file
and line of each `import` come from Lean's own `Module.header` parser, the
one `lake shake` uses. Only the header is parsed: `Lean.ParseImports.main`
(Lake's fast parser) finds where it ends, and the full parser runs on that
prefix alone, with one empty environment shared by every file. Parsing whole
files, or making an environment per file, cost about ten times as much
(`docs/decisions/graph-source.md`, phase-3 addendum).

This file is one of lean-deny's three toolchain-coupled files: it calls
Lean's parser API (`Module.header.fn`, `Module.updateTokens`,
`getTokenTable`, `mkEmptyEnvironment`, `mkInputContext`, `mkParserState`,
`andthenFn`, `whitespace`, `ParseImports.main`), which is public but not
stable. Nothing else in lean-deny calls it.
-/

open Lean Parser

namespace LeanDeny.Graph

/-- What every header parse shares: an empty environment and its token table
extended with the header's keywords. Build it once per run. -/
structure HeaderParser where
  env : Environment
  tokens : TokenTable

/-- A parser for any number of headers. -/
def HeaderParser.new : IO HeaderParser := do
  let env ← mkEmptyEnvironment
  return { env, tokens := Module.updateTokens (getTokenTable env) }

/-- The imports of one module directive, as written. -/
private def importOf (stx : Syntax) : Option (Name × ImportKind) :=
  match stx with
  | `(Module.import| $[public%$pubTk?]? $[meta%$metaTk?]? import $[all%$allTk?]? $mod) =>
    some (mod.getId, { isPublic := pubTk?.isSome, isMeta := metaTk?.isSome, isAll := allTk?.isSome })
  | _ => none

/-- The explicit `import` directives of the source `text` of `fileName`, in
source order, each with the line it starts on. The implicit `Init` imports
are not included. A header Lean cannot parse is an error naming the file,
line and column. -/
def HeaderParser.parse (p : HeaderParser) (fileName : String) (text : String) :
    Except String (Array HeaderImport) := do
  -- Where the header ends, by Lake's fast parser.
  let s := ParseImports.main text (ParseImports.whitespace text {})
  if let some err := s.error? then
    let pos := text.toFileMap.toPosition s.pos
    throw s!"{fileName}:{pos.line}:{pos.column}: {err}"
  let ictx := mkInputContext (String.Pos.Raw.extract text 0 s.pos) fileName
  let fn := andthenFn whitespace Module.header.fn
  let st := fn.run ictx { env := p.env, options := {} } p.tokens (mkParserState ictx.inputString)
  if let some (pos, _, err) := st.allErrors[0]? then
    let pos := ictx.fileMap.toPosition pos
    throw s!"{fileName}:{pos.line}:{pos.column}: {err}"
  if st.stxStack.isEmpty then throw s!"{fileName}: no header syntax"
  let stx : Syntax := st.stxStack.back
  -- `Module.header`: optional `module`, optional `prelude`, the imports.
  let dirs := stx[2].getArgs
  dirs.mapM fun d => do
    let some (module, kind) := importOf d
      | throw s!"{fileName}: unexpected import syntax {d}"
    let some pos := d.getPos?
      | throw s!"{fileName}: an import of {module} has no position"
    return { module, kind, line := (ictx.fileMap.toPosition pos).line }

end LeanDeny.Graph
