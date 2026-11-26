import LeanDeny

/-!
Tests of the Markdown reading behind `[[doc-modules]]`
(`LeanDeny.DocSection`) on strings: ATX headings and what is not one, where
a section ends, fenced code blocks, code spans, CRLF and line numbers, a
heading missing or appearing twice, and which spans are module names.
-/

open LeanDeny

namespace LeanDenyTest.DocSection

/-- A section as `h<line> name@line …`, or the error. -/
def render : Except SectionError DocSection → String
  | .ok s =>
    s!"h{s.headingLine}" ++ String.join (s.names.toList.map fun n => s!" {n.name}@{n.line}")
  | .error .notFound => "not found"
  | .error (.ambiguous ls) => s!"ambiguous {ls}"

/-- `(case, text, heading, expected rendering)`. -/
def cases : Array (String × String × String × String) :=
  #[ -- Headings.
    ("a level-2 heading", "# T\n## S\n`A.B`\n", "S", "h2 A.B@3"),
    ("every level from 1 to 6", "###### S\n`A`\n", "S", "h1 A@2"),
    ("seven # is not a heading", "####### S\n", "S", "not found"),
    ("a closing # run is dropped", "## S ##\n`A`\n", "S", "h1 A@2"),
    ("a # with no blank before it is text", "## S#\n`A`\n", "S#", "h1 A@2"),
    ("up to 3 spaces of indent", "   ## S\n`A`\n", "S", "h1 A@2"),
    ("4 spaces of indent is not a heading", "    ## S\n", "S", "not found"),
    ("#x is not a heading", "#S\n", "S", "not found"),
    ("the heading is matched trimmed", "##   S  \n`A`\n", "  S ", "h1 A@2"),
    ("backticks are part of a heading's text", "## `S`\n`A`\n", "`S`", "h1 A@2"),
    ("a setext heading is not recognised", "S\n===\n", "S", "not found"),
    -- Where a section ends.
    ("ends at the same level", "## S\n`A`\n## T\n`B`\n", "S", "h1 A@2"),
    ("ends at a higher level", "## S\n`A`\n# T\n`B`\n", "S", "h1 A@2"),
    ("includes deeper levels, their headings too", "## S\n`A`\n### `C`\n`B`\n## T\n`D`\n", "S",
      "h1 A@2 C@3 B@4"),
    ("runs to the end of the file", "# T\n## S\n`A`\n\n`B`", "S", "h2 A@3 B@5"),
    -- Fences.
    ("a backtick fence is skipped", "## S\n```\n`X`\n```\n`A`\n", "S", "h1 A@5"),
    ("a tilde fence is skipped", "## S\n~~~lean\n`X`\n~~~\n`A`\n", "S", "h1 A@5"),
    ("a longer closer closes", "## S\n```\n`X`\n`````\n`A`\n", "S", "h1 A@5"),
    ("a shorter run does not close", "## S\n````\n```\n`X`\n````\n`A`\n", "S", "h1 A@6"),
    ("a # inside a fence is not a heading", "## S\n```\n## T\n```\n`A`\n", "S", "h1 A@5"),
    ("a heading inside a fence is not found", "```\n## S\n```\n", "S", "not found"),
    ("an unclosed fence runs to the end", "## S\n`A`\n```\n`X`\n## T\n", "S", "h1 A@2"),
    -- Code spans.
    ("several spans on a line", "## S\n| `A` | `B` | x `C` |\n", "S", "h1 A@2 B@2 C@2"),
    ("double backticks around a single one", "## S\n``A`B`` ``C``\n", "S", "h1 C@2"),
    ("one space stripped from each end", "## S\n`` A `` ` B `\n", "S", "h1 A@2 B@2"),
    ("an unmatched run is literal", "## S\n``A `B` `C`\n", "S", "h1 B@2 C@2"),
    ("spans do not cross lines", "## S\n`A\nB`\n", "S", "h1"),
    -- Lines.
    ("CRLF", "## S\r\n`A`\r\n## T\r\n", "S", "h1 A@2"),
    ("duplicates are kept", "## S\n`A` `A`\n`A`\n", "S", "h1 A@2 A@2 A@3"),
    ("not found", "## S\n", "T", "not found"),
    ("ambiguous, with every line", "## S\n\n### S\n## S\n", "S", "ambiguous #[1, 3, 4]")]

/-- `(text, is a module name)`. -/
def nameCases : Array (String × Bool) :=
  #[("A", true), ("A.B", true), ("Editor.Core.Buffer", true), ("a_b'.c2", true), ("_x", true),
    ("a/b", false), ("A..B", false), (".A", false), ("A.", false), ("1A", false), ("A.1b", false),
    ("A B", false), ("", false), ("A-B", false), ("«A»", false), ("A.lean/", false)]

def run : Array String :=
  (cases.filterMap fun (name, text, h, want) =>
      let got := render (findSection text h)
      if got == want then none else some s!"{name}: expected {repr want}, got {repr got}") ++
    nameCases.filterMap fun (s, want) =>
      if isModuleName s == want then none else some s!"isModuleName {repr s}: expected {want}"

end LeanDenyTest.DocSection
