import Lean.Data.Json
import LeanDeny.Exit
import LeanDeny.Graph.Render
import LeanDeny.Rules.Common

/-!
# The report of `check`

The three renderings of a `check` run. `text` is for people, and its exact
shape is unchanged from before `--format` existed. `json` follows
`docs/check-json.md`. `github` prints GitHub workflow commands, one
annotation per violation or error. Each rendering is stdout's whole content;
the diagnostics go to stderr in every format. Pure.

Paths are taken to use `/` separators, as `Graph.relPath` does.
-/

open Lean LeanDeny.Graph

namespace LeanDeny

/-- How `check` prints its report. -/
inductive CheckFormat where
  | text
  | json
  | github
  deriving BEq, Repr, Inhabited, DecidableEq

def CheckFormat.toString : CheckFormat → String
  | .text => "text"
  | .json => "json"
  | .github => "github"

instance : ToString CheckFormat :=
  ⟨CheckFormat.toString⟩

/-- The format a command line names (`text`, `json` or `github`), exactly. -/
def CheckFormat.parse? : String → Option CheckFormat
  | "text" => some .text
  | "json" => some .json
  | "github" => some .github
  | _ => none

/-- The line `check` prints when every rule holds: "lean-deny: ok (2 rules)". -/
def okLine (rules : Nat) : String :=
  s!"lean-deny: ok ({Graph.plural rules "rule"})"

/-- The last line of a report with violations:
"lean-deny: 3 violations in 1 of 2 rules". -/
def summaryLine (violations broken rules : Nat) : String :=
  s!"lean-deny: {Graph.plural violations "violation"} in {broken} of {Graph.plural rules "rule"}"

/-- The last line of a report that stopped at errors: "lean-deny: 1 error",
"lean-deny: 4 errors". -/
def errorSummaryLine (errors : Nat) : String :=
  s!"lean-deny: {Graph.plural errors "error"}"

/-- The number of rules with at least one violation in `vs`. -/
def brokenRules (vs : Array Violation) : Nat :=
  (vs.map (·.rule)).toList.eraseDups.length

/-- What `check` prints on stdout for the rules' result `vs`: the ok line, or
every violation's block followed by the summary line. -/
def checkReport (g : Graph) (p : Policy) (vs : Array Violation) : Array String :=
  if vs.isEmpty then #[okLine p.ruleCount]
  else vs.flatMap (·.render g p.path) |>.push (summaryLine vs.size (brokenRules vs) p.ruleCount)

/-- The schema version of `check --format json` (`docs/check-json.md`). -/
def checkJsonSchemaVersion : Nat :=
  1

/-- One diagnostic, with its location if it has one in the policy file. -/
structure Diagnostic where
  file? : Option String := none
  pos? : Option Toml.Pos := none
  /-- Without the location prefix. -/
  message : String
  deriving BEq, Repr, Inhabited

/-- A non-empty run of ASCII digits at the start of `cs`, and what follows. -/
private def digits? (cs : List Char) : Option (Nat × List Char) :=
  let (ds, rest) := cs.span Char.isDigit
  if ds.isEmpty then none else some ((String.ofList ds).toNat!, rest)

/-- Split a diagnostic built by `Policy.locate` or `Toml.parseLocated` for
the policy at `policyPath`:
- "<policyPath>:<L>:<C>: <m>", with L and C non-empty runs of ASCII digits,
  gives the file, position ⟨L, C⟩ and message m;
- "<policyPath>: <m>" gives the file only;
- anything else is unlocated, with the whole text as its message. -/
def Diagnostic.ofMessage (policyPath : String) (msg : String) : Diagnostic :=
  let unlocated : Diagnostic := { message := msg }
  match msg.dropPrefix? (policyPath ++ ":") with
  | none => unlocated
  | some rest =>
    match rest.toString.toList with
    | ' ' :: m => { file? := some policyPath, message := String.ofList m }
    | cs =>
      match digits? cs with
      | some (line, ':' :: cs') =>
        match digits? cs' with
        | some (column, ':' :: ' ' :: m) =>
          { file? := some policyPath, pos? := some ⟨line, column⟩, message := String.ofList m }
        | _ => unlocated
      | _ => unlocated

/-- The non-empty components of a `/`-separated path. -/
private def components (p : String) : List String :=
  (p.splitOn "/").filter (!·.isEmpty)

/-- `path` relative to the directory `base`, both absolute with `/`
separators: the shared leading components dropped, one `..` per remaining
component of `base`; `.` when they are equal. A `path` that is not absolute
is returned as is. Empty components (`//`, a trailing `/`) are ignored.
(Windows paths are out of scope.) -/
def relativePath (base path : String) : String :=
  if !path.startsWith "/" then path
  else
    let rec common : List String → List String → List String × List String
      | b :: bs, p :: ps => if b == p then common bs ps else (b :: bs, p :: ps)
      | bs, ps => (bs, ps)
    let (up, down) := common (components base) (components path)
    let parts := up.map (fun _ => "..") ++ down
    if parts.isEmpty then "." else "/".intercalate parts

/-- A path for an annotation, relative to the working directory `cwd`: an
absolute path through `relativePath cwd`; a relative one as is, with
leading `./` components dropped. -/
def githubFile (cwd : String) (path : String) : String :=
  if path.startsWith "/" then relativePath cwd path
  else
    let rec strip (cs : List Char) (fuel : Nat) : List Char :=
      match fuel, cs with
      | n + 1, '.' :: '/' :: rest => strip rest n
      | _, cs => cs
    String.ofList (strip path.toList path.length)

/-- GitHub workflow-command escaping of a message: `%` → `%25`, CR → `%0D`,
LF → `%0A`, in that order. -/
def escapeData (s : String) : String :=
  (s.replace "%" "%25").replace "\r" "%0D" |>.replace "\n" "%0A"

/-- GitHub workflow-command escaping of a property value: `escapeData`, then
`:` → `%3A` and `,` → `%2C`. -/
def escapeProperty (s : String) : String :=
  ((escapeData s).replace ":" "%3A").replace "," "%2C"

/-- "::<cmd> k1=v1,k2=v2::<message>" ("::<cmd>::<message>" with no
properties), each value through `escapeProperty`, the message through
`escapeData`. -/
def githubCommand (cmd : String) (props : List (String × String)) (message : String) : String :=
  let ps := props.map fun (k, v) => s!"{k}={escapeProperty v}"
  let head := if ps.isEmpty then cmd else s!"{cmd} {",".intercalate ps}"
  s!"::{head}::{escapeData message}"

/-- What a `check` run produced. -/
inductive CheckResult where
  /-- Stopped at `errors` (exit 2); `rules?` is the policy's rule count when
  it loaded. -/
  | failed (rules? : Option Nat) (errors : Array String)
  /-- Every rule of `p` was checked over `g`. -/
  | checked (g : Graph) (p : Policy) (violations : Array Violation)

/-- How the run ends: `error` when it failed, `holds` with no violation,
`violation` otherwise. -/
def CheckResult.outcome : CheckResult → Outcome
  | .failed .. => .error
  | .checked _ _ vs => if vs.isEmpty then .holds else .violation

/-- The report's last line, in every format. -/
def CheckResult.summary : CheckResult → String
  | .failed _ es => errorSummaryLine es.size
  | .checked _ p vs =>
    if vs.isEmpty then okLine p.ruleCount else summaryLine vs.size (brokenRules vs) p.ruleCount

/-- What the renderings need besides the result. -/
structure ReportCtx where
  /-- The policy path as given (`--config`, or the workspace's default). -/
  policyPath : String
  /-- The real working directory, for github paths. -/
  cwd : String
  deriving BEq, Repr, Inhabited

private def outcomeName : Outcome → String
  | .holds => "holds"
  | .violation => "violation"
  | .error => "error"

private def jOptNat (n? : Option Nat) : Json :=
  (n?.map toJson).getD .null

private def jOptStr (s? : Option String) : Json :=
  (s?.map Json.str).getD .null

/-- A violation's module (the module a reachable rule does not reach, or a
co-reach rule's root), or one of a co-reach violation's missing modules: its
name and file (relative to the workspace root when under it, otherwise as
is); `null` for none. -/
private def moduleJson (g : Graph) : Option NodeId → Json
  | none => .null
  | some m =>
    Json.mkObj
      [("name", Json.str (nodeName g m)),
        ("file", jOptStr ((g.nodes[m]? >>= (·.file?)).map g.relPath))]

/-- A target-config violation's target: its package, kind (`lib`, `exe`),
name, package lakefile (relative to the workspace root when under it,
otherwise as is) and effective plugins; `null` for the other kinds. -/
private def targetJson (g : Graph) : Option TargetRef → Json
  | none => .null
  | some t =>
    Json.mkObj
      [("package", Json.str (plainName t.pkg)), ("kind", Json.str (toString t.kind)),
        ("name", Json.str (plainName t.name)), ("file", Json.str (g.relPath t.configFile)),
        ("plugins", Json.arr (t.plugins.map (Json.str ·.text)))]

/-- A require-backed violation's package dependency: the importing package,
the imported package, the importing package's lakefile (relative to the
workspace root when under it, otherwise as is) and its direct requires, as
written; `null` for the other kinds. -/
private def requireJson (g : Graph) : Option RequireGap → Json
  | none => .null
  | some r =>
    Json.mkObj
      [("package", Json.str (plainName r.pkg)), ("imported", Json.str (plainName r.imported)),
        ("file", Json.str (g.relPath r.configFile)),
        ("requires", Json.arr (r.requires.map (Json.str ∘ plainName)))]

/-- A doc-modules violation's name: whether it is missing or extra, the
name, the Markdown file (relative to the workspace root when under it,
otherwise as is), the section and the line (the heading's for a missing
name, the first listing's for an extra one); `null` for the other kinds. -/
private def docJson (g : Graph) : Option DocGap → Json
  | none => .null
  | some d =>
    Json.mkObj
      [("kind", Json.str (toString d.kind)), ("name", Json.str d.name),
        ("file", Json.str (g.relPath d.file)), ("section", Json.str d.heading),
        ("line", toJson d.line)]

private def violationJson (g : Graph) (p : Policy) (v : Violation) : Json :=
  Json.mkObj
    [("rule",
        Json.mkObj
          [("kind", Json.str v.rule.kind.toString), ("index", toJson v.rule.index),
            ("label", Json.str v.label), ("file", Json.str p.path),
            ("line", jOptNat (v.pos?.map (·.line))), ("column", jOptNat (v.pos?.map (·.column))),
            ("reason", jOptStr v.reason?)]),
      ("message", Json.str v.message), ("detail", jOptStr v.detail?),
      ("chain", Json.arr (v.chain.map (importJson g))), ("module", moduleJson g v.module?),
      ("missing", Json.arr (v.missing.map (moduleJson g ∘ some))),
      ("target", targetJson g v.target?), ("require", requireJson g v.require?),
      ("doc", docJson g v.doc?)]

private def diagnosticJson (d : Diagnostic) : Json :=
  Json.mkObj
    [("file", jOptStr d.file?), ("line", jOptNat (d.pos?.map (·.line))),
      ("column", jOptNat (d.pos?.map (·.column))), ("message", Json.str d.message)]

/-- The result as a JSON value (schema version `checkJsonSchemaVersion`,
`docs/check-json.md`). -/
def toJsonCheck (ctx : ReportCtx) (r : CheckResult) : Json :=
  let (rules, broken, violations, errors) :=
    match r with
    | .failed rules? es =>
      (jOptNat rules?, 0, #[],
        es.map fun m => diagnosticJson (Diagnostic.ofMessage ctx.policyPath m))
    | .checked g p vs => (toJson p.ruleCount, brokenRules vs, vs.map (violationJson g p), #[])
  let outcome := r.outcome
  Json.mkObj
    [("schemaVersion", toJson checkJsonSchemaVersion), ("ok", toJson (outcome == .holds)),
      ("outcome", Json.str (outcomeName outcome)), ("policy", Json.str ctx.policyPath),
      ("rules", rules), ("brokenRules", toJson broken), ("violations", Json.arr violations),
      ("errors", Json.arr errors), ("summary", Json.str r.summary)]

/-- The result as GitHub workflow commands: one `::error` annotation per
violation, on the import that starts its chain (when the chain is empty, as
for a reachable rule or a co-reach rule whose root is itself in
`if-reaches`, on the file of the violation's module, with no line; for a
target-config rule, on the target's package lakefile, with no line; a
require-backed violation's chain is its one unbacked import; a doc-modules
violation, on its Markdown file at the section's heading for a missing
module or at the name's first listing for an extra name), or per error;
then the summary line.
Ends in one newline. -/
def renderGithub (ctx : ReportCtx) (r : CheckResult) : String :=
  let rel (f : System.FilePath) : String := githubFile ctx.cwd f.toString
  let cmds : Array String :=
    match r with
    | .checked g p vs =>
      vs.map fun (v : Violation) =>
        let e? := v.chain[0]?
        let file? :=
          match v.doc?, e? with
          | some d, _ => some d.file
          | none, some e => some e.file
          | none, none =>
            match v.target? with
            | some t => some t.configFile
            | none => v.module? >>= fun m => g.nodes[m]? >>= (·.file?)
        let line? :=
          match v.doc? with
          | some d => some d.line
          | none => e? >>= (·.line?)
        let props :=
          (file?.map fun f => ("file", rel f)).toList ++
            (line?.map fun l => ("line", toString l)).toList ++
            [("title", s!"lean-deny: {v.label}")]
        githubCommand "error" props ("\n".intercalate (v.render g p.path rel).toList)
    | .failed _ es =>
      es.map fun (m : String) =>
        let d := Diagnostic.ofMessage ctx.policyPath m
        let props :=
          (d.file?.map fun f => ("file", githubFile ctx.cwd f)).toList ++
            (d.pos?.map fun p => ("line", toString p.line)).toList ++
            (d.pos?.map fun p => ("col", toString (p.column + 1))).toList ++
            [("title", "lean-deny: error")]
        githubCommand "error" props d.message
  String.join ((cmds.push r.summary).toList.map (· ++ "\n"))

/-- stdout's whole content in format `f`: for text, nothing for `.failed`
(its errors go to stderr) and otherwise `checkReport`'s lines, each ending
in a newline; for json, the pretty-printed document and a newline; for
github, `renderGithub`. -/
def renderCheck (f : CheckFormat) (ctx : ReportCtx) (r : CheckResult) : String :=
  match f with
  | .text =>
    match r with
    | .failed .. => ""
    | .checked g p vs => String.join ((checkReport g p vs).toList.map (· ++ "\n"))
  | .json => (toJsonCheck ctx r).pretty ++ "\n"
  | .github => renderGithub ctx r

end LeanDeny
