import LeanDeny.DocSection
import LeanDeny.Graph.View
import LeanDeny.Rules.Common
import LeanDeny.Rules.Layers
import LeanDeny.Rules.RequireBacked

/-!
# `[[doc-packages]]` rules

A doc-packages rule says a Markdown table has one row per package
`packages` matches, giving the package's `[layers]` layer and its direct
requires. The table is the first top-level table in section `section` of
Markdown file `file` (relative to the workspace directory) whose header has
the columns `package-column`, `layer-column` and `requires-column`; every
other column is ignored. What counts as a heading, a section and a table is
`LeanDeny.DocSection`'s. Pure: the file is read by `LeanDeny.Check` and
handed in as a `DocPackagesRead`.

- A row's **package** is the first code span in its package cell. Its
  **layer** is its layer cell, trimmed, or the content of a cell that is
  exactly one code span. Its **requires** are every code span in its
  requires cell, in order, or none for a cell that is exactly `none`.
- The **packages** are the whole packages `packages` matches (as a
  require-backed rule's); each one's layer comes from `[layers]`, and its
  direct requires from its lakefile (`LeanDeny.Graph.PackageInfo.requires`),
  less the packages `requires-except` names. Names are compared as users
  write them (`plainName`).
- Each package with no row is one **missing** violation, by name. Then each
  row, in document order: a row naming no selected package is one **extra**
  violation; otherwise a layer cell other than the package's layer is one
  **layer** violation, then requires that differ as sets from the
  package's are one **requires** violation. Row order and duplicate rows
  are not checked: every row naming a selected package is checked on its
  own.

A rule's selectors are resolved against the graph first. The errors, in
order: the selectors' (`resolvePackageRefs`), then each `requires-except`
name the workspace has no package of, then the file's: no file, a read
failure, no heading or a heading appearing more than once, no top-level
table, no top-level table with every named column, or a row whose package,
layer or requires cell cannot be read. A `[layers]` that does not resolve
leaves the rule unevaluated (`[layers]` reports its own errors). A rule with
an error is not evaluated, and any error anywhere means no violation is
reported.
-/

open Lean LeanDeny.Graph

namespace LeanDeny

/-- One row of a package table: its 1-based line, the package it names,
its layer cell and its requires cell's names. -/
structure PackageRow where
  line : Nat
  pkg : String
  layer : String
  requires : Array String
  deriving BEq, Repr, Inhabited

/-- A rule's package table: its heading's and header row's 1-based lines,
and its rows in document order. -/
structure PackageTable where
  headingLine : Nat
  tableLine : Nat
  rows : Array PackageRow
  deriving BEq, Repr, Inhabited

/-- A rule's package table, or the located diagnostic for why it cannot be
read. -/
abbrev DocPackagesRead :=
  Except String PackageTable

/-- The cell `c` is exactly one code span: its content. -/
private def soleSpan? (c : String) : Option String :=
  match codeSpans c with
  | #[s] => if c.startsWith "`" && c.endsWith "`" then some s else none
  | _ => none

/-- Rule `r`'s package table, from its file's contents: `none` for no file
(or a directory), `some (.error e)` for a read failure, `some (.ok text)`
for the text. -/
def DocPackagesRule.readResult (p : Policy) (r : DocPackagesRule)
    (contents : Option (Except String String)) : DocPackagesRead :=
  Id.run do
    let loc := Policy.locate p.path r.pos?
    let text ←
      match contents with
      | none =>
        return .error <|
            loc
              s!"{r.label}: no file '{r.file}' in the workspace (looking for heading '{r.heading}')"
      | some (.error e) =>
        return .error <|
            loc s!"{r.label}: cannot read '{r.file}' (looking for heading '{r.heading}'): {e}"
      | some (.ok text) =>
        pure text
    let (headingLine, tables) ←
      match sectionTables text r.heading with
      | .ok x =>
        pure x
      | .error .notFound =>
        return .error <| loc s!"{r.label}: no heading '{r.heading}' in '{r.file}'"
      | .error (.ambiguous lines) =>
        return .error <|
            loc <|
            s!"{r.label}: heading '{r.heading}' appears {lines.size} times in '{r.file}' \
                (lines {proseList (lines.map toString)})"
    let some first := tables[0]?
      | return .error <| loc s!"{r.label}: section '{r.heading}' of '{r.file}' has no top-level table"
    let names := #[r.packageColumn, r.layerColumn, r.requiresColumn]
    let hasAll (t : DocTable) : Bool := names.all t.header.contains
    let some t := tables.find? hasAll
      |
      let absent := names.filter (!first.header.contains ·)
      return .error <|
          loc <|
          s!"{r.label}: no top-level table in section '{r.heading}' of '{r.file}' has the \
                columns {proseList (names.map (s!"'{·}'"))} (the first, at line {first.line}, has \
                no {proseList (absent.map (s!"'{·}'"))})"
    let col (n : String) : Nat := (t.header.findIdx? (· == n)).getD 0
    let (pc, lc, rc) := (col r.packageColumn, col r.layerColumn, col r.requiresColumn)
    let mut rows := #[]
    for row in t.rows do
      let at_ := s!"{r.label}: '{r.file}':{row.line}:"
      let cell (i : Nat) : String := row.cells[i]?.getD ""
      let some pkg := (codeSpans (cell pc))[0]?
        | return .error <| loc s!"{at_} the '{r.packageColumn}' cell names no package in backticks"
      let layer := (soleSpan? (cell lc)).getD (cell lc)
      if layer.isEmpty then
        return .error <| loc s!"{at_} the '{r.layerColumn}' cell is empty"
      let requires := if cell rc == "none" then #[] else codeSpans (cell rc)
      if requires.isEmpty && cell rc != "none" then
        return .error <|
            loc
              s!"{at_} the '{r.requiresColumn}' cell is neither 'none' nor package names in \
                backticks"
      rows := rows.push { line := row.line, pkg, layer, requires }
    return .ok { headingLine, tableLine := t.line, rows }

/-- A doc-packages rule with its selectors and `[layers]` resolved. -/
structure DocPackagesResolved where
  rule : DocPackagesRule
  /-- The whole packages `packages` matches, sorted by `plainName`. -/
  packages : Array Name
  layers : LayersResolved
  deriving Inhabited

/-- Resolve rule `r`'s selectors and `requires-except` in `g`, with the
policy's sets resolved in `sets`; `none` when `[layers]` is missing or does
not resolve (its own errors are `[layers]`'s). The errors are in the module
doc's order. -/
def resolveDocPackages (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId))
    (r : DocPackagesRule) : Except (Array String) (Option DocPackagesResolved) := do
  let packages ← resolvePackageRefs g p sets r.label r.pos? r.refs
  let known := g.packages.map (plainName ·.name)
  let unknown := r.requiresExcept.filter fun (n, _) => !known.contains n
  unless unknown.isEmpty do
    throw <|
        unknown.map fun (n, pos?) =>
          Policy.locate p.path pos?
            s!"{r.label}: 'requires-except' names package '{n}', which the workspace does not have"
  let some lr := p.layers? | return none
  match resolveLayers g p sets lr with
  | .ok layers =>
    return some { rule := r, packages, layers }
  | .error _ =>
    return none

/-- Names as prose after "requires": `none` for none, else comma-separated. -/
private def namesText (ns : Array String) (empty : String) : String :=
  if ns.isEmpty then empty else ", ".intercalate ns.toList

/-- The names of `xs`, each once, in order. -/
private def dedup (xs : Array String) : Array String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

/-- Evaluate a resolved rule against its table `t`: the missing packages by
name, then each row in document order (an extra row; or a layer, then a
requires violation). -/
def evalDocPackages (g : Graph) (d : DocPackagesResolved) (t : PackageTable) : Array Violation :=
  Id.run do
    let r := d.rule
    let file := g.root / r.file
    let rel := g.relPath file
    let sect := s!"section '{r.heading}' of {rel}"
    let base : Violation :=
      { rule := r.ref, pos? := r.pos?, reason? := some r.reason, chain := #[] }
    let gap (kind : PackageRowKind) (pkg : String) (line : Nat) : PackageRowGap :=
      { kind, pkg, file, heading := r.heading, line }
    let except := r.requiresExcept.map (·.1)
    let mut vs := #[]
    for pk in d.packages do
      let name := plainName pk
      unless t.rows.any (·.pkg == name) do
        vs :=
          vs.push
            { base with
              detail? := some s!"package {name} has no row in {sect}"
              packageRow? := some (gap .missingRow name t.headingLine) }
    for row in t.rows do
      let some pk := d.packages.find? (plainName · == row.pkg)
        |
        vs :=
          vs.push
            { base with
              detail? := some s!"{sect} has a row for {row.pkg}, which 'packages' does not match"
              packageRow? := some (gap .extraRow row.pkg row.line) }
        continue
      let layer := (d.layers.layerOf.get? pk >>= (d.layers.layers[·]?)).getD "?"
      if row.layer != layer then
        vs :=
          vs.push
            { base with
              detail? :=
                some s!"{sect} gives {row.pkg} layer {row.layer}, but [layers] puts it in {layer}"
              packageRow? :=
                some
                  { gap .layerDiffers row.pkg
                      row.line with
                    documentedLayer? := some row.layer
                    layer? := some layer } }
      let direct := dedup ((requiresOf g pk).2.map plainName) |>.filter (!except.contains ·)
      let given := dedup row.requires
      let missing := direct.filter (!given.contains ·)
      let extra := given.filter (!direct.contains ·)
      unless missing.isEmpty && extra.isEmpty do
        let parts :=
          (if missing.isEmpty then [] else [s!"missing {", ".intercalate missing.toList}"]) ++
            if extra.isEmpty then [] else [s!"extra {", ".intercalate extra.toList}"]
        vs :=
          vs.push
            { base with
              detail? :=
                some
                  s!"{sect} gives {row.pkg} requires {namesText given "none"}, but {row.pkg} \
                    requires {namesText direct "nothing"} directly: {"; ".intercalate parts}"
              packageRow? :=
                some
                  { gap .requiresDiffer row.pkg
                      row.line with
                    missingRequires := missing
                    extraRequires := extra } }
    return vs

/-- Every doc-packages rule of `p`, with the policy's sets resolved in
`sets` and rule `i`'s table read in `docs[i]`: the violations in rule
order, or every rule's errors in rule order (a rule's selector and
`requires-except` errors, then its file's error). -/
def checkDocPackages (g : Graph) (p : Policy) (sets : Std.HashMap String (Array NodeId))
    (docs : Array DocPackagesRead) : Except (Array String) (Array Violation) :=
  Id.run do
    let mut errs := #[]
    let mut vs := #[]
    for (r, i) in p.docPackages.zipIdx do
      let resolved := resolveDocPackages g p sets r
      let doc : DocPackagesRead :=
        docs[i]?.getD
          (.error
            (Policy.locate p.path r.pos? s!"{r.label}: internal error: its file was not read"))
      if let .error es := resolved then
        errs := errs ++ es
      if let .error e := doc then
        errs := errs.push e
      if let .ok (some d) := resolved then
        if let .ok t := doc then
          vs := vs ++ evalDocPackages g d t
    if errs.isEmpty then
      return .ok vs
    return .error errs

end LeanDeny
