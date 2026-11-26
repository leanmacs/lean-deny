import LeanDenyTest.Query

/-!
Tests of `LeanDeny.matchSelector`, `resolveSets` and `resolveRef` on a
hand-written graph: what each selector kind matches and why it matches
nothing, ambiguous libraries, executables' roots, externals, sets with
`except`, the errors a set can give, their order, and resolving one set's
closure only.
-/

open Lean LeanDeny LeanDeny.Graph LeanDenyTest.Query

namespace LeanDenyTest.Resolve

/-- Package `ws`: libraries `App` (`App`, `App.Shared`) and `AppTest`
(`App.Shared`, `AppTest`) sharing `App.Shared`, and an executable `app`
with root `Main`. Package `core` (keyword `kernel`): libraries `Core` and
`Util`. Package `other`: a second library `Util` and an empty library
`Empty`. Package `bare` (keyword `lonely`) has no modules. Externals:
`Init` and `Lean.Data.Json`. -/
def modules : Array M :=
  let json := #[plain `Lean.Data.Json]
  #[{ name := `App, pkg := `ws, target := `App },
    { name := `App.Shared, pkg := `ws, target := `App, imports := json },
    { name := `App.Shared, pkg := `ws, target := `AppTest, imports := json },
    { name := `AppTest, pkg := `ws, target := `AppTest },
    { name := `Main, pkg := `ws, kind := .exe, target := `app },
    { name := `Core.Api, pkg := `core, target := `Core },
    { name := `Core.Impl, pkg := `core, target := `Core },
    { name := `Core.Util, pkg := `core, target := `Util },
    { name := `Side, pkg := `other, target := `Util }]

def pkg (n : Name) (keywords : Array String) (libs : Array Name) (exes : Array (Name × Name)) :
    PackageInfo :=
  { name := n, dir := s!"/ws/{n}", configFile := s!"/ws/{n}/lakefile.toml", keywords
    remoteUrl? := none, requires := #[], isRoot := n == `ws
    libs := libs.map fun l => { name := l, roots := #[l], globs := #[] }
    exes := exes.map fun (x, r) => { name := x, root := r } }

def packages : Array PackageInfo :=
  #[pkg `ws #[] #[`App, `AppTest] #[(`app, `Main)],
    pkg `core #["kernel", "api"] #[`Core, `Util] #[], pkg `other #[] #[`Util, `Empty] #[],
    pkg `bare #["lonely"] #[] #[]]

def graph : Except String Graph :=
  (mkGraph modules).map fun g => { g with packages }

def names (g : Graph) (ns : Array NodeId) : String :=
  ", ".intercalate (ns.map fun i => (g.nodes[i]?.map (·.name.toString)).getD "?").toList

def renderMatch (g : Graph) : MatchResult → String
  | .ok ns => s!"ok [{names g ns}]"
  | .nothing r => s!"nothing: {r}"
  | .ambiguous d => s!"ambiguous: {d}"

/-- `(selector, expected rendering)`, in `NodeId` (`Name.cmp`) order. -/
def matchCases : Array (String × String) :=
  #[ -- pkg: includes the executable's root, never externals.
    ("pkg:ws", "ok [App, AppTest, Main, App.Shared]"),
    ("pkg:core", "ok [Core.Api, Core.Impl, Core.Util]"),
    ("pkg:nope", "nothing: no package named 'nope' (packages: ws, core, other, bare)"),
    ("pkg:bare", "nothing: package 'bare' has no modules"),
    -- lib: counts a shared module in both libraries, never an executable's root.
    ("lib:App", "ok [App, App.Shared]"), ("lib:AppTest", "ok [AppTest, App.Shared]"),
    ("lib:ws/App", "ok [App, App.Shared]"), ("lib:Core", "ok [Core.Api, Core.Impl]"),
    ("lib:Util",
      "ambiguous: lean_lib 'Util' is in packages core, other; write 'lib:<package>/Util'"),
    ("lib:core/Util", "ok [Core.Util]"), ("lib:other/Util", "ok [Side]"),
    ("lib:Empty", "nothing: lean_lib 'other/Empty' has no modules"),
    ("lib:other/Empty", "nothing: lean_lib 'other/Empty' has no modules"),
    ("lib:Nope", "nothing: no package has a lean_lib named 'Nope'"),
    ("lib:app", "nothing: no package has a lean_lib named 'app'"),
    ("lib:nope/Util", "nothing: no package named 'nope' (packages: ws, core, other, bare)"),
    ("lib:core/Nope", "nothing: package 'core' has no lean_lib named 'Nope'"),
    ("lib:ws/app", "nothing: package 'ws' has no lean_lib named 'app'"),
    -- mod: by name component.
    ("mod:App", "ok [App, App.Shared]"), ("mod:App!", "ok [App]"),
    ("mod:App.Shared", "ok [App.Shared]"), ("mod:Core", "ok [Core.Api, Core.Impl, Core.Util]"),
    ("mod:Main!", "ok [Main]"), ("mod:Ap", "nothing: no workspace module is or is under 'Ap'"),
    ("mod:Core!", "nothing: no workspace module named 'Core'"),
    ("mod:Lean.Data",
      "nothing: no workspace module is or is under 'Lean.Data'; 'external:Lean.Data' \
      matches modules outside the workspace"),
    ("mod:Init!",
      "nothing: no workspace module named 'Init'; 'external:Init' matches modules outside \
      the workspace"),
    -- keyword: every module of the packages, never externals.
    ("keyword:kernel", "ok [Core.Api, Core.Impl, Core.Util]"),
    ("keyword:api", "ok [Core.Api, Core.Impl, Core.Util]"),
    ("keyword:Kernel", "nothing: no package declares keyword 'Kernel'"),
    ("keyword:lonely", "nothing: the packages with keyword 'lonely' (bare) have no modules"),
    -- external: externals only.
    ("external:Lean", "ok [Lean.Data.Json]"), ("external:Init", "ok [Init]"),
    ("external:Lean.Data.Json", "ok [Lean.Data.Json]"),
    ("external:Std",
      "nothing: no external module is or is under 'Std' (the graph holds only the external \
      modules the workspace imports directly)"),
    ("external:App",
      "nothing: no external module is or is under 'App' (the graph holds only the external \
      modules the workspace imports directly)")]

/-- A selector of a set written on line `line`, at column `col`. -/
def sref (use : Use) (line col : Nat) (text : String) : SelectorRef :=
  { text, sel := (Selector.parse text).toOption.getD default, pos? := some { line, column := col }
    use }

/-- A set on line `line` (its value at column 0): `select` from column 10,
`except` from column 30, one column per selector. -/
def mkSet (name : String) (line : Nat) (select : List String) (except : List String := []) :
    SetDef :=
  { name, pos? := some { line, column := 0 }
    select := select.toArray.zipIdx.map fun (t, i) => sref (.setSelect name) line (10 + i) t
    except := except.toArray.zipIdx.map fun (t, i) => sref (.setExcept name) line (30 + i) t }

/-- A policy of `sets`, resolved in `order` (default: as written). -/
def mkPolicy (sets : Array SetDef) (order? : Option (Array Nat) := none) : LeanDeny.Policy :=
  { path := "p.toml", sets, order := order?.getD (Array.range sets.size) }

/-- Each resolved set as `name: [modules]`, by name; or the errors. -/
def renderSets (g : Graph) :
    Except (Array String) (Std.HashMap String (Array NodeId)) → Array String
  | .ok m => (m.toArray.qsort (·.1 < ·.1)).map fun (n, ns) => s!"{n}: [{names g ns}]"
  | .error es => es.map ("error: " ++ ·)

/-- `(case, policy, only?, expected)`. -/
def setCases : Array (String × LeanDeny.Policy × Option String × Array String) :=
  #[("union, a set reference and an exception",
      mkPolicy
        #[mkSet "app" 1 ["pkg:ws"], mkSet "api" 2 ["set:app", "mod:Core.Api!"] ["lib:AppTest"],
          mkSet "tests" 3 ["lib:AppTest"], mkSet "surf" 4 ["set:app"] ["set:tests"],
          mkSet "dup" 5 ["mod:App!", "mod:App", "pkg:ws"]],
      none,
      #["api: [App, Main, Core.Api]", "app: [App, AppTest, Main, App.Shared]",
        "dup: [App, AppTest, Main, App.Shared]", "surf: [App, Main]",
        "tests: [AppTest, App.Shared]"]),
    ("an except entry that removes nothing",
      mkPolicy #[mkSet "core" 1 ["pkg:core"] ["mod:Core.Api!", "mod:App!"]], none,
      #["error: p.toml:1:31: selector 'mod:App!' in the except list of set 'core' removes no \
          module from it"]),
    ("an except entry that matches nothing", mkPolicy #[mkSet "core" 1 ["pkg:core"] ["mod:Nope"]],
      none,
      #["error: p.toml:1:30: selector 'mod:Nope' in the except list of set 'core' matches no \
          module: no workspace module is or is under 'Nope'"]),
    ("a set its except list empties",
      mkPolicy #[mkSet "t" 1 ["lib:AppTest"] ["mod:AppTest!", "mod:App.Shared!"]], none,
      #["error: p.toml:1:0: set 't' matches no module: its except list removes every module it \
          selects"]),
    ("a failed select selector adds no 'removes no module' error",
      mkPolicy #[mkSet "core" 1 ["mod:Core.Apii"] ["mod:Core.Api!"]], none,
      #["error: p.toml:1:10: selector 'mod:Core.Apii' in set 'core' matches no module: no \
          workspace module is or is under 'Core.Apii'"]),
    ("a select-side set: naming a failed set adds no 'removes no module' error",
      mkPolicy
        #[mkSet "bad" 1 ["mod:Apps", "mod:App!"],
          mkSet "s" 2 ["set:bad", "pkg:core"] ["mod:App.Shared!"]],
      none,
      #["error: p.toml:1:10: selector 'mod:Apps' in set 'bad' matches no module: no workspace \
          module is or is under 'Apps'"]),
    ("an ambiguous lib in a set", mkPolicy #[mkSet "util" 1 ["lib:Util"]], none,
      #["error: p.toml:1:10: selector 'lib:Util' in set 'util' is ambiguous: lean_lib 'Util' is \
          in packages core, other; write 'lib:<package>/Util'"]),
    ("a set that refers to a failed set: one error",
      mkPolicy
        #[mkSet "bad" 1 ["mod:Nope"], mkSet "uses" 2 ["set:bad", "pkg:core"],
          mkSet "excl" 3 ["pkg:ws"] ["set:bad"]],
      none,
      #["error: p.toml:1:10: selector 'mod:Nope' in set 'bad' matches no module: no workspace \
          module is or is under 'Nope'"]),
    ("errors by set in source order, then by selector",
      mkPolicy
        #[mkSet "z" 1 ["mod:Z1", "pkg:core", "mod:Z2"], mkSet "y" 2 ["mod:Y1"],
          mkSet "x" 3 ["set:y", "set:z"]]
        (some #[1, 0, 2]),
      none,
      #["error: p.toml:1:10: selector 'mod:Z1' in set 'z' matches no module: no workspace \
          module is or is under 'Z1'",
        "error: p.toml:1:12: selector 'mod:Z2' in set 'z' matches no module: no workspace \
          module is or is under 'Z2'",
        "error: p.toml:2:10: selector 'mod:Y1' in set 'y' matches no module: no workspace \
          module is or is under 'Y1'"]),
    ("only? resolves the closure and ignores a broken unrelated set",
      mkPolicy
        #[mkSet "ok" 1 ["pkg:core"], mkSet "broken" 2 ["mod:Nope"], mkSet "top" 3 ["set:ok"],
          mkSet "aside" 4 ["pkg:other"]],
      some "top",
      #["ok: [Core.Api, Core.Impl, Core.Util]", "top: [Core.Api, Core.Impl, Core.Util]"]),
    ("only? still reports an error in the closure",
      mkPolicy #[mkSet "broken" 1 ["mod:Nope", "pkg:core"], mkSet "top" 2 ["set:broken"]],
      some "top",
      #["error: p.toml:1:10: selector 'mod:Nope' in set 'broken' matches no module: no \
          workspace module is or is under 'Nope'"]),
    ("only? walks a diamond of set: references to the end",
      mkPolicy
        #[mkSet "b" 1 ["mod:App!"], mkSet "c" 2 ["mod:Core.Api!"], mkSet "l" 3 ["set:b"],
          mkSet "r" 4 ["set:b"], mkSet "m" 5 ["set:b"],
          mkSet "top" 6 ["set:c", "set:l", "set:r", "set:m"]],
      some "top",
      #["b: [App]", "c: [Core.Api]", "l: [App]", "m: [App]", "r: [App]", "top: [App, Core.Api]"]),
    ("only? with repeated set: references",
      mkPolicy
        #[mkSet "b" 1 ["mod:App!"], mkSet "c" 2 ["mod:Core.Api!"],
          mkSet "a" 3 ["set:b", "set:c", "set:c", "set:c"]],
      some "a", #["a: [App, Core.Api]", "b: [App]", "c: [Core.Api]"])]

/-- A command-line selector. -/
def cli (text : String) : SelectorRef :=
  { text, sel := (Selector.parse text).toOption.getD default, pos? := none, use := .commandLine }

def renderRef (g : Graph) : Except (Array String) (Array NodeId) → String
  | .ok ns => s!"ok [{names g ns}]"
  | .error es => s!"error {es}"

/-- `(selector, policy, expected)`: `resolveRef` on the command line. -/
def refCases : Array (String × Option LeanDeny.Policy × String) :=
  let p :=
    mkPolicy
      #[mkSet "app" 1 ["pkg:ws"], mkSet "api" 2 ["set:app"] ["lib:AppTest"],
        mkSet "broken" 3 ["mod:Nope"]]
  #[("pkg:other", none, "ok [Side]"),
    ("mod:Nope", none,
      "error #[selector 'mod:Nope' matches no module: no workspace module is or is under 'Nope']"),
    ("lib:Util", none,
      "error #[selector 'lib:Util' is ambiguous: lean_lib 'Util' is in packages core, other; \
      write 'lib:<package>/Util']"),
    ("set:api", some p, "ok [App, Main]"),
    ("set:nope", some p, "error #[unknown set 'nope' in 'p.toml' (defined: app, api, broken)]"),
    ("set:nope", some (mkPolicy #[]),
      "error #[unknown set 'nope' in 'p.toml' (it defines no sets)]"),
    ("set:broken", some p,
      "error #[p.toml:3:10: selector 'mod:Nope' in set 'broken' matches no module: no \
      workspace module is or is under 'Nope']")]

def failuresOn (g : Graph) : Array String :=
  Id.run do
    let mut fs := #[]
    for (sel, want) in matchCases do
      let got :=
        match Selector.parse sel with
        | .ok s => renderMatch g (matchSelector g s)
        | .error e => s!"parse error {e}"
      unless got == want do
        fs := fs.push s!"match {sel}: expected {repr want}, got {repr got}"
    for (name, p, only?, want) in setCases do
      let got := renderSets g (resolveSets g p only?)
      unless got == want do
        fs := fs.push s!"{name}: expected {repr want}, got {repr got}"
    for (sel, p?, want) in refCases do
      let got := renderRef g (resolveRef g p? (cli sel))
      unless got == want do
        fs := fs.push s!"resolveRef {sel}: expected {repr want}, got {repr got}"
    return fs

def run : Array String :=
  match graph with
  | .ok g => failuresOn g
  | .error e => #[s!"building the test graph failed: {e}"]

end LeanDenyTest.Resolve
