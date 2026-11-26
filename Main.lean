import LeanDeny

/-!
`lean-deny`: dependency policy checks for Lean 4 / Lake workspaces.
See `LeanDeny.usage` for the command line and exit codes.
-/

open LeanDeny

def run (args : List String) : IO Outcome := do
  match parseArgs args with
  | .error e =>
    printError e.msg
    IO.eprintln "Run 'lean-deny --help' for usage."
    return .error
  | .ok .help =>
    IO.print usage
    return .holds
  | .ok .version =>
    IO.println s!"lean-deny {version}"
    return .holds
  | .ok (.check opts) =>
    runCheck opts
  | .ok (.graph opts) =>
    runGraph opts
  | .ok (.explain opts) =>
    runExplain opts

def main (args : List String) : IO UInt32 := do
  -- Any uncaught exception exits 2: Lean's default (1) would read as a
  -- rule violation.
  try
    return (← run args).toExitCode
  catch e =>
    printError (toString e)
    return Outcome.error.toExitCode
