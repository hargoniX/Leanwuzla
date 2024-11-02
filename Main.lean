import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide
import Lean.Language.Lean

import Leanwuzla.Parser

open Lean

private partial def getIntrosSize (e : Expr) : Nat :=
  go 0 e
where
  go (size : Nat) : Expr → Nat
    | .forallE _ _ b _ => go (size + 1) b
    | .mdata _ b       => go size b
    | e                =>
      if let some (_, _, _, b) := e.letFun? then
        go (size + 1) b
      else
        size

/--
Introduce as many binders as possible without unfolding definitions and preserve names.
-/
def _root_.Lean.MVarId.introsP (mvarId : MVarId) : MetaM (Array FVarId × MVarId) := do
  let type ← mvarId.getType
  let type ← instantiateMVars type
  let n := getIntrosSize type
  if n == 0 then
    return (#[], mvarId)
  else
    mvarId.introNP n

open Elab in
def decide (type : Expr) : MetaM Unit := do
  let mv ← Meta.mkFreshExprMVar type
  let (_, mv') ← mv.mvarId!.introsP
  trace[debug] "{mv'}"
  try
    mv'.withContext $ IO.FS.withTempFile fun _ lratFile => do
      let startTime ← IO.monoMsNow
      let cfg ← (Tactic.BVDecide.Frontend.TacticContext.new lratFile).run' { declName? := `lrat }
      discard <| Tactic.BVDecide.Frontend.bvDecide mv' cfg
      let endTime ← IO.monoMsNow
      logInfo m!"bv_decide took {endTime - startTime}ms"
  catch e =>
    if (← e.toMessageData.toString).startsWith "The prover found a counterexample" then
      IO.println "sat"
      return
    else
      throwError e.toMessageData
  let value ← instantiateExprMVars mv
  let r := (← getEnv).addDecl (← getOptions) (.thmDecl { name := ← Lean.mkAuxName `thm 1, levelParams := [], type, value })
  match r with
  | .error e =>
    throwError m!"Error: {e.toMessageData (← getOptions)}"
  | .ok env =>
    setEnv env
    IO.println "unsat"

def parseSmt2File (path : System.FilePath) : MetaM Expr := do
  let query ← IO.FS.readFile path
  ofExcept (Parser.parseSmt2Query query)

def parseAndDecideSmt2File (path : System.FilePath) : MetaM Unit := do
  let type ← parseSmt2File path
  decide type

open Elab Command in
def elabParseSmt2File (path : System.FilePath) : CommandElabM Unit := do
  runTermElabM fun _ => do
  let e ← parseSmt2File path
  trace[debug] "{e}"

open Elab Command in
def elabParseAndDecideSmt2File (path : System.FilePath) : CommandElabM Unit := do
  runTermElabM fun _ => parseAndDecideSmt2File path

def parseOptions (args : List String) : IO (Options × List String) := do
  let (opts, args) := go {} args
  return (← Language.Lean.reparseOptions opts, args)
where
  go (opts : Options) : List String → (Options × List String)
    | "-D" :: arg :: args =>
      if let [name, value] := arg.splitOn "=" then
        let opts := opts.set name.toName value
        go opts args
      else
        (opts, args)
    | args => (opts, args)

unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let (opts, args) ← parseOptions args
  let [path] := args
    | throw (.userError "usage: lake exe leanwuzla [-D name=value] /path/to/file.smt2")
  withImportModules #[`Std.Tactic.BVDecide] {} 0 fun env => do
    _ ← Meta.MetaM.toIO (parseAndDecideSmt2File path)
      { fileName := "leanwuzla", fileMap := default, options := opts } { env := env }
