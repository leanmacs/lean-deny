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
  deriving BEq, Repr, Inhabited

/-- What the command line asks for. -/
inductive Command where
  | help
  | version
  | check (opts : CheckOpts)
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
  lean-deny --help | --version

Commands:
  check    Check the workspace's module graph against its policy

Options for check:
  --workspace <dir>   The Lake workspace to check (default: .)
  --config <file>     The policy file (default: <dir>/lean-deny.toml)

Loading the workspace elaborates its and its dependencies' lakefile.lean
files, so check runs their code, as lake does (lakefile.toml is not run).
Do not point it at a workspace you would not run `lake build` in.

Global options:
  -h, --help          Print this help
  -V, --version       Print the version

Exit codes:
  0  every rule holds
  1  at least one rule is broken
  2  the command line, the policy or the workspace is bad
"

private def isHelp (a : String) : Bool := a == "-h" || a == "--help"
private def isVersion (a : String) : Bool := a == "-V" || a == "--version"

/-- Split `--name=value` into the name and the value. -/
private def splitEq (a : String) : String × Option String :=
  match a.splitOn "=" with
  | n :: v :: vs => (n, some ("=".intercalate (v :: vs)))
  | _ => (a, none)

/-- One option of a command: its name (`--workspace`) and how its value
updates the command's options. -/
private abbrev OptSpec (σ : Type) := String × (σ → String → Except UsageError σ)

/-- Parse a command's arguments: `--name value` or `--name=value` for each
option in `specs`, each at most once, no positional arguments. `none` means
`--help`/`-h` was given. -/
private partial def parseOpts {σ : Type} (cmd : String) (specs : List (OptSpec σ))
    (seen : List String) (st : σ) : List String → Except UsageError (Option σ)
  | [] => .ok (some st)
  | a :: rest => do
    if isHelp a then return none
    let (name, inline?) := splitEq a
    let some (_, set) := specs.find? (·.1 == name) | do
      if a.startsWith "-" then throw ⟨s!"unknown option '{name}' for '{cmd}'"⟩
      throw ⟨s!"unexpected argument '{a}'"⟩
    let (val, rest) ← match inline?, rest with
      | some v, rest => pure (v, rest)
      | none, v :: rest => if v.startsWith "-" then pure ("", v :: rest) else pure (v, rest)
      | none, [] => pure ("", [])
    if val.isEmpty then throw ⟨s!"option '{name}' requires a value"⟩
    if seen.contains name then throw ⟨s!"option '{name}' given more than once"⟩
    parseOpts cmd specs (name :: seen) (← set st val) rest

/-- `check`'s options. -/
private def checkSpecs : List (OptSpec CheckOpts) := [
  ("--workspace", fun o v => .ok { o with workspace := v }),
  ("--config", fun o v => .ok { o with config? := some v })
]

/-- Parse the arguments after `check`. -/
private def parseCheck (args : List String) : Except UsageError Command := do
  match ← parseOpts "check" checkSpecs [] {} args with
  | none => return .help
  | some o => return .check o

/-- Parse lean-deny's command line (without the program name). -/
def parseArgs : List String → Except UsageError Command
  | [] => .error ⟨"no command given"⟩
  | a :: rest =>
    if isHelp a || isVersion a then
      match rest with
      | [] => .ok (if isHelp a then .help else .version)
      | b :: _ => .error ⟨s!"unexpected argument '{b}'"⟩
    else if a == "check" then parseCheck rest
    else if a.startsWith "-" then .error ⟨s!"unknown option '{(splitEq a).1}'"⟩
    else .error ⟨s!"unknown command '{a}'"⟩

end LeanDeny
