import LeanDeny

/-!
`lean-deny-spike <workspace-dir> [--parse-only]`: print the module graph Lake
resolves for a workspace as TSV, plus package metadata, with stage timings on
stderr. `--parse-only` lists the modules through Lake, then parses each header
directly with `Lean.parseImports'` (the cost of header parsing alone).
-/

open Lake Lean System LeanDeny.Graph.LakeApi

def nameStr (n : Name) : String := n.toString (escape := false)

def flagsStr (e : Edge) : String :=
  let fs := (if e.isExported then #["exported"] else #[])
    ++ (if e.isMeta then #["meta"] else #[])
    ++ (if e.importAll then #["all"] else #[])
  if fs.isEmpty then "-" else ",".intercalate fs.toList

def printRows (rows : Array Row) : IO Unit := do
  let out ← IO.getStdout
  for r in rows do
    let pre := s!"{nameStr r.pkg}\t{nameStr r.lib}\t{nameStr r.module}\t{r.isModule}"
    if r.edges.isEmpty then
      out.putStrLn s!"{pre}\t-\t-\t-"
    for e in r.edges do
      let pkg := (e.targetPkg?.map nameStr).getD "-"
      out.putStrLn s!"{pre}\t{nameStr e.target}\t{pkg}\t{flagsStr e}"

def printMeta (ws : Workspace) : IO Unit := do
  let out ← IO.getStdout
  for m in pkgMeta ws do
    let reqs := if m.requires.isEmpty then "-" else " ".intercalate (m.requires.map nameStr).toList
    let kws := if m.keywords.isEmpty then "-" else " ".intercalate m.keywords.toList
    let lang := m.configFile.extension.getD "?"
    let url := if m.remoteUrl.isEmpty then "-" else m.remoteUrl
    out.putStrLn s!"#pkg\t{nameStr m.name}\t{m.dir}\t{lang}\tkeywords={kws}\trequires={reqs}\tremote={url}"
    for (lib, roots, globs) in m.libs do
      out.putStrLn s!"#lib\t{nameStr m.name}\t{nameStr lib}\troots={" ".intercalate (roots.map nameStr).toList}\tglobs={" ".intercalate globs.toList}"

def runFull (dir : FilePath) : IO Unit := do
  let (ws, rows, t) ← graph dir
  printMeta ws
  printRows rows
  let edges := rows.foldl (· + ·.edges.size) 0
  let internal := rows.foldl (fun n r => n + (r.edges.filter (·.targetPkg?.isSome)).size) 0
  let libs := ws.packages.foldl (· + ·.leanLibs.size) 0
  IO.eprintln s!"stages_ms env={t.env} load={t.load} fetch={t.fetch}"
  IO.eprintln s!"counts packages={ws.packages.size} libs={libs} modules={rows.size} \
    imports={edges} workspace_edges={internal}"

def runParseOnly (dir : FilePath) : IO Unit := do
  let (env, tEnv) ← timed computeEnv
  let (ws, tLoad) ← timed (loadWs env dir)
  let (libs, tMods) ← timed (modulesOf ws)
  let ((nMods, nImports), tParse) ← timed do
    let mut nMods := 0
    let mut nImports := 0
    for (_, _, mods) in libs do
      for mod in mods do
        let path := mod.leanFile
        let header ← Lean.parseImports' (← IO.FS.readFile path) path.toString
        nMods := nMods + 1
        nImports := nImports + header.imports.size
    return (nMods, nImports)
  IO.eprintln s!"stages_ms env={tEnv} load={tLoad} modules={tMods} parse={tParse}"
  IO.eprintln s!"counts packages={ws.packages.size} libs={libs.size} modules={nMods} imports={nImports}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [dir] => runFull dir; return 0
  | [dir, "--parse-only"] => runParseOnly dir; return 0
  | _ =>
    IO.eprintln "usage: lean-deny-spike <workspace-dir> [--parse-only]"
    return 2
