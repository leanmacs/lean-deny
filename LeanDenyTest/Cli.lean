import LeanDeny

/-!
Table-driven tests of `LeanDeny.parseArgs`.
-/

open LeanDeny

namespace LeanDenyTest.Cli

/-- What a case expects: a command, or a usage error with this message. -/
abbrev Expect :=
  Except String Command

def check (ws : System.FilePath := ".") (config? : Option System.FilePath := none) : Expect :=
  .ok (.check { workspace := ws, config? })

def graph (ws : System.FilePath := ".") (format : LeanDeny.Graph.Format := .text)
    (level : LeanDeny.Graph.Level := .module) : Expect :=
  .ok (.graph { workspace := ws, format, level })

/-- `graph`'s cases. -/
def graphCases : Array (List String × Expect) :=
  #[(["graph"], graph), (["graph", "--help"], .ok .help), (["graph", "-h"], .ok .help),
    (["graph", "--format", "json", "-h"], .ok .help), (["graph", "--workspace", "w"], graph "w"),
    (["graph", "--workspace=w"], graph "w"), (["graph", "--format", "text"], graph),
    (["graph", "--format", "json"], graph "." .json), (["graph", "--format=json"], graph "." .json),
    (["graph", "--format", "dot"], graph "." .dot), (["graph", "--format=dot"], graph "." .dot),
    (["graph", "--level", "module"], graph), (["graph", "--level", "lib"], graph "." .text .lib),
    (["graph", "--level=lib"], graph "." .text .lib),
    (["graph", "--level", "package"], graph "." .text .package),
    (["graph", "--level=package"], graph "." .text .package),
    (["graph", "--level", "lib", "--format", "dot", "--workspace", "w"], graph "w" .dot .lib),
    (["graph", "--format", "xml"],
      .error "invalid value 'xml' for option '--format' (expected text, json or dot)"),
    (["graph", "--format=JSON"],
      .error "invalid value 'JSON' for option '--format' (expected text, json or dot)"),
    (["graph", "--level", "crate"],
      .error "invalid value 'crate' for option '--level' (expected module, lib or package)"),
    (["graph", "--format", "json", "--format", "dot"],
      .error "option '--format' given more than once"),
    (["graph", "--level=lib", "--level", "lib"], .error "option '--level' given more than once"),
    (["graph", "--workspace", "a", "--workspace=b"],
      .error "option '--workspace' given more than once"),
    (["graph", "--format"], .error "option '--format' requires a value"),
    (["graph", "--level="], .error "option '--level' requires a value"),
    (["graph", "--level", "--format", "json"], .error "option '--level' requires a value"),
    (["graph", "--config", "p.toml"], .error "unknown option '--config' for 'graph'"),
    (["graph", "--frob"], .error "unknown option '--frob' for 'graph'"),
    (["graph", "x"], .error "unexpected argument 'x'"),
    (["check", "--format", "json"], .error "unknown option '--format' for 'check'")]

def cases : Array (List String × Expect) :=
  #[([], .error "no command given"), (["-h"], .ok .help), (["--help"], .ok .help),
    (["-V"], .ok .version), (["--version"], .ok .version),
    (["--help", "x"], .error "unexpected argument 'x'"),
    (["--version", "check"], .error "unexpected argument 'check'"),
    (["frobnicate"], .error "unknown command 'frobnicate'"),
    (["--frob"], .error "unknown option '--frob'"),
    (["--frob=1"], .error "unknown option '--frob'"), (["check"], check),
    (["check", "--help"], .ok .help), (["check", "-h"], .ok .help),
    (["check", "--workspace", "w", "--help"], .ok .help),
    (["check", "--workspace", "w"], check "w"), (["check", "--workspace=w"], check "w"),
    (["check", "--workspace=a=b"], check "a=b"),
    (["check", "--config", "p.toml"], check "." (some "p.toml")),
    (["check", "--config=p.toml"], check "." (some "p.toml")),
    (["check", "--config", "p.toml", "--workspace", "w"], check "w" (some "p.toml")),
    (["check", "--workspace"], .error "option '--workspace' requires a value"),
    (["check", "--workspace="], .error "option '--workspace' requires a value"),
    (["check", "--workspace", "--config", "p"], .error "option '--workspace' requires a value"),
    (["check", "--config"], .error "option '--config' requires a value"),
    (["check", "--workspace", "a", "--workspace", "b"],
      .error "option '--workspace' given more than once"),
    (["check", "--config=a", "--config", "b"], .error "option '--config' given more than once"),
    (["check", "extra"], .error "unexpected argument 'extra'"),
    (["check", "--frob"], .error "unknown option '--frob' for 'check'"),
    (["check", "-x=1"], .error "unknown option '-x' for 'check'")]

def render : Except UsageError Command → String
  | .ok c => s!"ok {repr c}"
  | .error e => s!"usage error {repr e.msg}"

def renderExpect : Expect → String
  | .ok c => s!"ok {repr c}"
  | .error m => s!"usage error {repr m}"

/-- The failing cases, described. -/
def failures : Array String :=
  Id.run do
    let mut fs := #[]
    for (args, want) in cases ++ graphCases do
      let got := parseArgs args
      let same :=
        match got, want with
        | .ok c, .ok c' => c == c'
        | .error e, .error m => e.msg == m
        | _, _ => false
      unless same do
        fs := fs.push s!"parseArgs {args}: expected {renderExpect want}, got {render got}"
    return fs

end LeanDenyTest.Cli
