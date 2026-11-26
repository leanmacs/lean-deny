import LeanDeny

/-!
Table-driven tests of `LeanDeny.Selector.parse` and `Selector.toString`:
every kind, every rejection reason, and the round trip.
-/

open Lean LeanDeny

namespace LeanDenyTest.Selector

/-- `(input, expected)`: the selector, or the reason it is rejected. -/
def cases : Array (String × Except String Selector) :=
  #[("pkg:core", .ok (.pkg "core")), ("pkg:graph-ws", .ok (.pkg "graph-ws")),
    ("lib:Core", .ok (.lib none "Core")), ("lib:core/Core", .ok (.lib (some "core") "Core")),
    ("mod:Core.Api", .ok (.mod `Core.Api false)), ("mod:Core.Api!", .ok (.mod `Core.Api true)),
    ("mod:«my-mod».X", .ok (.mod (Name.mkStr (Name.mkStr .anonymous "my-mod") "X") false)),
    ("mod:App", .ok (.mod `App false)), ("keyword:kernel", .ok (.keyword "kernel")),
    ("keyword:editor-feature", .ok (.keyword "editor-feature")),
    ("external:Lean", .ok (.external `Lean)),
    ("external:Lean.Data.Json", .ok (.external `Lean.Data.Json)), ("set:core", .ok (.set "core")),
    ("set:core_api-2", .ok (.set "core_api-2")), ("imports:mod:A!", .ok (.imports (.mod `A true))),
    ("imports:mod:Core", .ok (.imports (.mod `Core false))),
    ("imports:set:x", .ok (.imports (.set "x"))),
    ("imports:imports:pkg:p", .ok (.imports (.imports (.pkg "p")))),
    ("imports:external:Lean", .ok (.imports (.external `Lean))),
    ("imports:lib:core/Core", .ok (.imports (.lib (some "core") "Core"))),
    -- `imports:` shapes: the inner selector's own reasons, unchanged.
    ("imports:", .error "nothing after 'imports:'"),
    ("imports:imports:", .error "nothing after 'imports:'"),
    ("imports:mod:", .error "nothing after 'mod:'"),
    ("imports:pkg:core!",
      .error "'!' (this module alone) is only valid at the end of a mod: selector"),
    ("imports:Core", .error "expected '<kind>:<value>', such as 'mod:Editor.Api'"),
    ("imports", .error "expected '<kind>:<value>', such as 'mod:Editor.Api'"),
    ("imports:crate:x",
      .error "unknown kind 'crate' (expected pkg, lib, mod, keyword, external, set or imports)"),
    ("imports: mod:A", .error "contains whitespace"),
    -- No `:`.
    ("Core.Api", .error "expected '<kind>:<value>', such as 'mod:Editor.Api'"),
    ("", .error "expected '<kind>:<value>', such as 'mod:Editor.Api'"),
    -- Unknown kind.
    ("crate:core",
      .error "unknown kind 'crate' (expected pkg, lib, mod, keyword, external, set or imports)"),
    (":core", .error "unknown kind '' (expected pkg, lib, mod, keyword, external, set or imports)"),
    ("Mod:A",
      .error "unknown kind 'Mod' (expected pkg, lib, mod, keyword, external, set or imports)"),
    -- Empty value.
    ("pkg:", .error "nothing after 'pkg:'"), ("lib:", .error "nothing after 'lib:'"),
    ("mod:", .error "nothing after 'mod:'"), ("keyword:", .error "nothing after 'keyword:'"),
    ("external:", .error "nothing after 'external:'"), ("set:", .error "nothing after 'set:'"),
    -- Whitespace, anywhere.
    ("pkg:a b", .error "contains whitespace"), (" pkg:core", .error "contains whitespace"),
    ("pkg:core ", .error "contains whitespace"), ("mod:A\t", .error "contains whitespace"),
    -- `!` anywhere but the end of `mod:`.
    ("pkg:core!", .error "'!' (this module alone) is only valid at the end of a mod: selector"),
    ("external:Lean!",
      .error "'!' (this module alone) is only valid at the end of a mod: selector"),
    ("mod:A!.B", .error "'!' (this module alone) is only valid at the end of a mod: selector"),
    ("mod:A!!", .error "'!' (this module alone) is only valid at the end of a mod: selector"),
    ("lib:Core!", .error "'!' (this module alone) is only valid at the end of a mod: selector"),
    -- `lib:` shapes.
    ("lib:a/b/c", .error "expected 'lib:<lib>' or 'lib:<package>/<lib>'"),
    ("lib:/b", .error "expected 'lib:<lib>' or 'lib:<package>/<lib>'"),
    ("lib:a/", .error "expected 'lib:<lib>' or 'lib:<package>/<lib>'"),
    ("pkg:a/b", .error "a package name has no '/' (for a library, use 'lib:<package>/<lib>')"),
    -- Module names.
    ("mod:Core..Api", .error "'Core..Api' is not a module name"),
    ("mod:.Core", .error "'.Core' is not a module name"),
    ("mod:Core.", .error "'Core.' is not a module name"),
    ("mod:Foo.1", .error "'Foo.1' is not a module name"),
    ("mod:lean-deny", .error "'lean-deny' is not a module name"),
    ("mod:!", .error "'!' is not a module name"),
    ("external:Lean..Data", .error "'Lean..Data' is not a module name"),
    ("mod:A:B", .error "'A:B' is not a module name"),
    -- Set names.
    ("set:a.b", .error "'a.b' is not a set name (use letters, digits, '-' and '_')"),
    ("set:a/b", .error "'a/b' is not a set name (use letters, digits, '-' and '_')")]

def render : Except String Selector → String
  | .ok s => s!"ok {repr s}"
  | .error e => s!"error {repr e}"

/-- The failing cases, described. -/
def failures : Array String :=
  Id.run do
    let mut fs := #[]
    for (input, want) in cases do
      let got := Selector.parse input
      let same :=
        match got, want with
        | .ok a, .ok b => a == b
        | .error a, .error b => a == b
        | _, _ => false
      unless same do
        fs := fs.push s!"parse {repr input}: expected {render want}, got {render got}"
      -- The canonical text parses back to the same selector.
      if let .ok s := want then
        match Selector.parse s.toString with
        | .ok s' =>
          unless s' == s do
            fs := fs.push s!"round trip of {repr input} via {repr s.toString}: got {repr s'}"
        | .error e =>
          fs := fs.push s!"round trip of {repr input} via {repr s.toString}: error {repr e}"
    for (s, want) in
      [("core", true), ("core_api-2", true), ("A9", true), ("", false), ("a.b", false),
        ("core api", false), ("é", false)] do
      unless isSetName s == want do
        fs := fs.push s!"isSetName {repr s}: expected {want}"
    return fs

end LeanDenyTest.Selector
