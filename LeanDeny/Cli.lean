import LeanDeny.Graph.Render
import LeanDeny.Graph.View
import LeanDeny.Policy.Selector
import LeanDeny.Report
import LeanDeny.Version

/-!
# Command line

A hand-written, pure argument parser: no CLI library, since every workspace
that `require`s lean-deny would have to fetch it.
-/

open System

namespace LeanDeny

/-- Options of `lean-deny check`. -/
structure CheckOpts where
  /-- The Lake workspace to check. -/
  workspace : FilePath := "."
  /-- The policy file; `none` means `<workspace>/lean-deny.toml`. An explicit
  path is relative to the working directory. -/
  config? : Option FilePath := none
  /-- How to print the report. -/
  format : CheckFormat := .text
  deriving BEq, Repr, Inhabited

/-- Options of `lean-deny graph`. -/
structure GraphOpts where
  /-- The Lake workspace to read. -/
  workspace : FilePath := "."
  /-- The policy file, read only for its `[[root]]` tables; `none` means
  `<workspace>/lean-deny.toml`. -/
  config? : Option FilePath := none
  format : Graph.Format := .text
  level : Graph.Level := .module
  deriving BEq, Repr, Inhabited

/-- Options of `lean-deny explain`. -/
structure ExplainOpts where
  /-- The Lake workspace to read. -/
  workspace : FilePath := "."
  /-- The policy file, read for its `[[root]]` tables, and in full for a
  `set:` selector; `none` means `<workspace>/lean-deny.toml`. -/
  config? : Option FilePath := none
  /-- The selector as written. -/
  text : String
  selector : Selector
  deriving BEq, Repr, Inhabited

/-- What the command line asks for. -/
inductive Command where
  | help
  | version
  | check (opts : CheckOpts)
  | graph (opts : GraphOpts)
  | explain (opts : ExplainOpts)
  deriving BEq, Repr, Inhabited

/-- A bad command line. -/
structure UsageError where
  msg : String
  deriving BEq, Repr, Inhabited

/-- The `--help` text. -/
def usage : String :=
  s!"lean-deny {version}: dependency policy checks for Lean 4 / Lake workspaces

Usage:
  lean-deny check [--workspace <dir>] [--config <file>]
                  [--format text|json|github]
  lean-deny graph [--workspace <dir>] [--config <file>]
                  [--format text|json|dot] [--level module|lib|package]
  lean-deny explain [--workspace <dir>] [--config <file>] <selector>
  lean-deny --help | --version

Commands:
  check    Check the workspace's module graph against its policy
  graph    Print the workspace's module graph
  explain  List the modules a selector matches, one per line

Options for check:
  --workspace <dir>   The Lake workspace to check (default: .)
  --config <file>     The policy file (default: <dir>/lean-deny.toml)
  --format <fmt>      text, json or github (default: text); the exit
                      code is the same in every format

Options for graph:
  --workspace <dir>   The Lake workspace to read (default: .)
  --config <file>     The policy file, read only for its [[root]] tables
                      (default: <dir>/lean-deny.toml)
  --format <fmt>      text, json or dot (default: text)
  --level <level>     module, lib or package (default: module)

Options for explain:
  --workspace <dir>   The Lake workspace to read (default: .)
  --config <file>     The policy file, read for its [[root]] tables, and
                      in full for a set: selector
                      (default: <dir>/lean-deny.toml)

Selectors:
  pkg:<name>          every module of a package
  lib:<lib>           every module of a lean_lib (lib:<pkg>/<lib> if
                      several packages have one by that name)
  mod:<Prefix>        that module and every module under it
  mod:<Module>!       that module alone
                      (mod: also matches the policy's declared roots)
  keyword:<kw>        every module of every package with that keyword
  external:<Prefix>   modules from outside the workspace that it imports
  set:<name>          a set from the policy's [sets] table

Loading the workspace elaborates its and its dependencies' lakefile.lean
files, so check, graph and explain run their code, as lake does
(lakefile.toml is not run). Do not point them at a workspace you would not
run `lake build` in.

Global options:
  -h, --help          Print this help
  -V, --version       Print the version

Exit codes:
  0  every rule holds (check), or the graph or the matches were printed
  1  at least one rule is broken
  2  the command line, the policy or the workspace is bad, a selector
     matches nothing, or a wrapper, except or allow entry has no effect
"

private def isHelp (a : String) : Bool :=
  a == "-h" || a == "--help"

private def isVersion (a : String) : Bool :=
  a == "-V" || a == "--version"

/-- Split `--name=value` into the name and the value. -/
private def splitEq (a : String) : String × Option String :=
  match a.splitOn "=" with
  | n :: v :: vs => (n, some ("=".intercalate (v :: vs)))
  | _ => (a, none)

/-- One option of a command: its name (`--workspace`) and how its value
updates the command's options. -/
private abbrev OptSpec (σ : Type) :=
  String × (σ → String → Except UsageError σ)

/-- Parse a command's arguments: `--name value` or `--name=value` for each
option in `specs`, each at most once. A non-option argument goes to
`positional?`; with none, it is an error. `none` means `--help`/`-h` was
given. -/
private partial def parseOpts {σ : Type} (cmd : String) (specs : List (OptSpec σ))
    (positional? : Option (σ → String → Except UsageError σ)) (seen : List String) (st : σ) :
    List String → Except UsageError (Option σ)
  | [] => .ok (some st)
  | a :: rest => do
    if isHelp a then
      return none
    let (name, inline?) := splitEq a
    let some (_, set) := specs.find? (·.1 == name) |
      do
        if a.startsWith "-" then
          throw ⟨s!"unknown option '{name}' for '{cmd}'"⟩
        match positional? with
        | some add =>
          parseOpts cmd specs positional? seen (← add st a) rest
        | none =>
          throw ⟨s!"unexpected argument '{a}'"⟩
    let (val, rest) ←
      match inline?, rest with
      | some v, rest =>
        pure (v, rest)
      | none, v :: rest =>
        if v.startsWith "-" then
          pure ("", v :: rest)
        else
          pure (v, rest)
      | none, [] =>
        pure ("", [])
    if val.isEmpty then
      throw ⟨s!"option '{name}' requires a value"⟩
    if seen.contains name then
      throw ⟨s!"option '{name}' given more than once"⟩
    parseOpts cmd specs positional? (name :: seen) (← set st val) rest

/-- `check`'s options. -/
private def checkSpecs : List (OptSpec CheckOpts) :=
  [("--workspace", fun o v => .ok { o with workspace := v }),
    ("--config", fun o v => .ok { o with config? := some v }),
    ("--format", fun o v =>
      match CheckFormat.parse? v with
      | some f => .ok { o with format := f }
      | none =>
        .error ⟨s!"invalid value '{v}' for option '--format' (expected text, json or github)"⟩)]

/-- Parse the arguments after `check`. -/
private def parseCheck (args : List String) : Except UsageError Command := do
  match ← parseOpts "check" checkSpecs none [] {} args with
  | none =>
    return .help
  | some o =>
    return .check o

/-- `graph`'s options. -/
private def graphSpecs : List (OptSpec GraphOpts) :=
  [("--workspace", fun o v => .ok { o with workspace := v }),
    ("--config", fun o v => .ok { o with config? := some v }),
    ("--format", fun o v =>
      match Graph.Format.parse? v with
      | some f => .ok { o with format := f }
      | none =>
        .error ⟨s!"invalid value '{v}' for option '--format' (expected text, json or dot)"⟩),
    ("--level", fun o v =>
      match Graph.Level.parse? v with
      | some l => .ok { o with level := l }
      | none =>
        .error ⟨s!"invalid value '{v}' for option '--level' (expected module, lib or package)"⟩)]

/-- Parse the arguments after `graph`. -/
private def parseGraph (args : List String) : Except UsageError Command := do
  match ← parseOpts "graph" graphSpecs none [] {} args with
  | none =>
    return .help
  | some o =>
    return .graph o

/-- `explain`'s options while parsing: the selector is positional, so it
may be missing. -/
private structure ExplainBuilder where
  workspace : FilePath := "."
  config? : Option FilePath := none
  /-- The selector as written, and parsed. -/
  selector? : Option (String × Selector) := none

/-- `explain`'s options. -/
private def explainSpecs : List (OptSpec ExplainBuilder) :=
  [("--workspace", fun o v => .ok { o with workspace := v }),
    ("--config", fun o v => .ok { o with config? := some v })]

/-- `explain`'s one positional argument: the selector. -/
private def explainSelector (o : ExplainBuilder) (a : String) : Except UsageError ExplainBuilder :=
  if o.selector?.isSome then .error ⟨s!"unexpected argument '{a}'"⟩
  else
    match Selector.parse a with
    | .ok sel => .ok { o with selector? := some (a, sel) }
    | .error reason => .error ⟨s!"invalid selector '{a}': {reason}"⟩

/-- Parse the arguments after `explain`. -/
private def parseExplain (args : List String) : Except UsageError Command := do
  match ← parseOpts "explain" explainSpecs (some explainSelector) [] {} args with
  | none =>
    return .help
  | some o =>
    let some (text, selector) :=
      o.selector? | throw ⟨"explain needs a selector, such as 'mod:Editor.Api'"⟩
    return .explain { workspace := o.workspace, config? := o.config?, text, selector }

/-- Parse lean-deny's command line (without the program name). -/
def parseArgs : List String → Except UsageError Command
  | [] => .error ⟨"no command given"⟩
  | a :: rest =>
    if isHelp a || isVersion a then
      match rest with
      | [] => .ok (if isHelp a then .help else .version)
      | b :: _ => .error ⟨s!"unexpected argument '{b}'"⟩
    else
      if a == "check" then parseCheck rest
      else
        if a == "graph" then parseGraph rest
        else
          if a == "explain" then parseExplain rest
          else
            if a.startsWith "-" then .error ⟨s!"unknown option '{(splitEq a).1}'"⟩
            else .error ⟨s!"unknown command '{a}'"⟩

end LeanDeny
