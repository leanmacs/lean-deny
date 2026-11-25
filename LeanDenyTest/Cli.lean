import LeanDeny

/-!
Table-driven tests of `LeanDeny.parseArgs`.
-/

open LeanDeny

namespace LeanDenyTest.Cli

/-- What a case expects: a command, or a usage error with this message. -/
abbrev Expect := Except String Command

def check (ws : System.FilePath := ".") (config? : Option System.FilePath := none) : Expect :=
  .ok (.check { workspace := ws, config? })

def cases : Array (List String × Expect) := #[
  ([], .error "no command given"),
  (["-h"], .ok .help),
  (["--help"], .ok .help),
  (["-V"], .ok .version),
  (["--version"], .ok .version),
  (["--help", "x"], .error "unexpected argument 'x'"),
  (["--version", "check"], .error "unexpected argument 'check'"),
  (["frobnicate"], .error "unknown command 'frobnicate'"),
  (["--frob"], .error "unknown option '--frob'"),
  (["--frob=1"], .error "unknown option '--frob'"),
  (["check"], check),
  (["check", "--help"], .ok .help),
  (["check", "-h"], .ok .help),
  (["check", "--workspace", "w", "--help"], .ok .help),
  (["check", "--workspace", "w"], check "w"),
  (["check", "--workspace=w"], check "w"),
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
  (["check", "-x=1"], .error "unknown option '-x' for 'check'")
]

def render : Except UsageError Command → String
  | .ok c => s!"ok {repr c}"
  | .error e => s!"usage error {repr e.msg}"

def renderExpect : Expect → String
  | .ok c => s!"ok {repr c}"
  | .error m => s!"usage error {repr m}"

/-- The failing cases, described. -/
def failures : Array String := Id.run do
  let mut fs := #[]
  for (args, want) in cases do
    let got := parseArgs args
    let same := match got, want with
      | .ok c, .ok c' => c == c'
      | .error e, .error m => e.msg == m
      | _, _ => false
    unless same do
      fs := fs.push s!"parseArgs {args}: expected {renderExpect want}, got {render got}"
  return fs

end LeanDenyTest.Cli
