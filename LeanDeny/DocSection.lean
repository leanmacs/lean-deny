/-!
# Reading a Markdown section's module names

What a `[[doc-modules]]` rule reads from its Markdown file: the section
under one heading, and the backticked module names in it. A small,
documented subset of CommonMark, enough for tables and lists. Pure.

- Lines are split on `\n`, a trailing `\r` dropped; line numbers are
  1-based.
- **Fenced code blocks**: a line with at most 3 spaces of indent and then 3
  or more `` ` `` or `~` opens one; a line of the same character, at least
  as long (and nothing after it but blanks), closes it. Lines from the
  opener to the closer are never headings and give no names. An unclosed
  fence runs to the end of the file.
- **ATX headings only**: at most 3 spaces of indent, 1 to 6 `#`, then a
  space, a tab or the end of the line. The text is the rest, an optional
  closing run of `#` (preceded by a blank) removed, then trimmed. Setext
  headings (a line underlined with `=` or `-`) are not recognised.
- A heading matches when its text equals the wanted heading, trimmed, byte
  for byte (backticks in a heading are part of its text). Its **section** is
  the lines after it, up to the next heading of the same or a higher level
  (as many `#` or fewer), or the end of the file: deeper subsections,
  their heading lines included, are part of it.
- **Code spans** are found within one line: a run of n backticks opens a
  span, closed by the next run of exactly n backticks; an unmatched run is
  literal. When the content begins and ends with a space and is not all
  spaces, one space is stripped from each end. A span never crosses a line
  and backslash escapes are not interpreted.
- A **name** is a span whose content is one or more `.`-separated
  components, each non-empty, of ASCII letters, digits, `_` and `'`, not
  starting with a digit (`isModuleName`). `«»`-escaped names are not
  recognised.
-/

namespace LeanDeny

/-- A candidate module name in a section, and its 1-based line. -/
structure DocName where
  name : String
  line : Nat
  deriving BEq, Repr, Inhabited

/-- A section: its heading's 1-based line, and every candidate name in it,
in document order, duplicates kept. -/
structure DocSection where
  headingLine : Nat
  names : Array DocName
  deriving BEq, Repr, Inhabited

/-- Why a section cannot be read. -/
inductive SectionError where
  /-- No heading has the text. -/
  | notFound
  /-- More than one heading has the text: their 1-based lines. -/
  | ambiguous (lines : Array Nat)
  deriving BEq, Repr, Inhabited

/-- What a line is, once fences are known. -/
private inductive LineKind where
  /-- Inside a fenced code block, its opener and closer included. -/
  | code
  /-- An ATX heading: its level and text. -/
  | heading (level : Nat) (text : String)
  | text
  deriving Inhabited

private def isBlank (c : Char) : Bool :=
  c == ' ' || c == '\t'

/-- The number of leading spaces and the rest of the line. -/
private def leadingSpaces (cs : List Char) : Nat × List Char :=
  let sp := cs.takeWhile (· == ' ')
  (sp.length, cs.drop sp.length)

/-- The fence a line opens: its character and length. -/
private def fenceOpen? (cs : List Char) : Option (Char × Nat) :=
  let (n, rest) := leadingSpaces cs
  match rest with
  | c :: _ =>
    let k := (rest.takeWhile (· == c)).length
    if n ≤ 3 && (c == '`' || c == '~') && k ≥ 3 then some (c, k) else none
  | [] => none

/-- The line closes a fence of `k` characters `c`. -/
private def closesFence (c : Char) (k : Nat) (cs : List Char) : Bool :=
  let (n, rest) := leadingSpaces cs
  let run := rest.takeWhile (· == c)
  n ≤ 3 && run.length ≥ k && (rest.drop run.length).all isBlank

/-- Blanks dropped from both ends. -/
private def trimBlanks (cs : List Char) : List Char :=
  ((cs.dropWhile isBlank).reverse.dropWhile isBlank).reverse

/-- The level and text of an ATX heading line. -/
private def heading? (cs : List Char) : Option (Nat × String) :=
  let (n, rest) := leadingSpaces cs
  let hashes := (rest.takeWhile (· == '#')).length
  let after := rest.drop hashes
  let opens :=
    match after with
    | [] => true
    | c :: _ => isBlank c
  if n ≤ 3 && 1 ≤ hashes && hashes ≤ 6 && opens then
    let t := trimBlanks after
    -- An optional closing run of `#`, preceded by a blank (or alone).
    let r := t.reverse
    let closing := (r.takeWhile (· == '#')).length
    let before := r.drop closing
    let t :=
      if closing > 0 && (before.isEmpty || before.head?.any isBlank) then trimBlanks before.reverse
      else t
    some (hashes, String.ofList t)
  else none

/-- The length of the run of backticks at `i`. -/
private def runAt (cs : Array Char) (i : Nat) : Nat :=
  Id.run do
    let mut j := i
    while j < cs.size && cs[j]! == '`' do
      j := j + 1
    return j - i

/-- A span's content: one space stripped from each end when it begins and
ends with one and is not all spaces. -/
private def spanContent (cs : Array Char) : String :=
  let l := cs.toList
  if l.length ≥ 2 && l.head? == some ' ' && l.getLast? == some ' ' && !l.all (· == ' ') then
    String.ofList ((l.drop 1).dropLast)
  else String.ofList l

/-- The contents of the code spans in one line, in order. -/
def codeSpans (line : String) : Array String :=
  Id.run do
    let cs := line.toList.toArray
    let mut out := #[]
    let mut i := 0
    while i < cs.size do
      if cs[i]! == '`' then
        let n := runAt cs i
        let mut j := i + n
        let mut close? : Option Nat := none
        while j < cs.size && close?.isNone do
          if cs[j]! == '`' then
            let m := runAt cs j
            if m == n then
              close? := some j
            else
              j := j + m
          else
            j := j + 1
        match close? with
        | some c =>
          out := out.push (spanContent (cs.extract (i + n) c))
          i := c + n
        | none =>
          i := i + n
      else
        i := i + 1
    return out

/-- One or more `.`-separated components, each non-empty, of ASCII letters,
digits, `_` and `'`, not starting with a digit. -/
def isModuleName (s : String) : Bool :=
  let ok (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''
  (s.splitOn ".").all fun comp =>
    match comp.toList with
    | [] => false
    | c :: cs => !c.isDigit && ok c && cs.all ok

/-- Each line of `text` with its kind. -/
private def classify (lines : Array (List Char)) : Array LineKind :=
  Id.run do
    let mut kinds := #[]
    let mut fence : Option (Char × Nat) := none
    for l in lines do
      match fence with
      | some (c, k) =>
        kinds := kinds.push .code
        if closesFence c k l then
          fence := none
      | none =>
        match fenceOpen? l with
        | some f =>
          fence := some f
          kinds := kinds.push .code
        | none =>
          match heading? l with
          | some (lv, t) =>
            kinds := kinds.push (.heading lv t)
          | none =>
            kinds := kinds.push .text
    return kinds

/-- The section of `text` under the heading whose text is `heading`
(trimmed), with its candidate names; the module doc gives the rules. -/
def findSection (text heading : String) : Except SectionError DocSection :=
  Id.run do
    let lines : Array (List Char) :=
      (text.splitOn "\n").toArray.map fun l =>
        let cs := l.toList
        if cs.getLast? == some '\r' then cs.dropLast else cs
    let kinds := classify lines
    let want := heading.trimAscii.toString
    let mut found : Array (Nat × Nat) := #[]
    for (k, i) in kinds.zipIdx do
      if let .heading lv t := k then
        if t == want then
          found := found.push (i, lv)
    let some (h, level) := found[0]?
      | return .error .notFound
    if found.size > 1 then
      return .error (.ambiguous (found.map (·.1 + 1)))
    let mut names := #[]
    let mut i := h + 1
    let mut stop := false
    while i < lines.size && !stop do
      match kinds[i]! with
      | .heading lv _ =>
        if lv ≤ level then
          stop := true
      | _ =>
        pure ()
      match kinds[i]! with
      | .code =>
        pure ()
      | _ =>
        if !stop then
          for s in codeSpans (String.ofList lines[i]!) do
            if isModuleName s then
              names := names.push { name := s, line := i + 1 }
      i := i + 1
    return .ok { headingLine := h + 1, names }

end LeanDeny
