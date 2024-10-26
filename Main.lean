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
  mv'.withContext $ IO.FS.withTempFile fun _ lratFile => do
    let startTime ← IO.monoMsNow
    let cfg ← (Tactic.BVDecide.Frontend.TacticContext.new lratFile).run' { declName? := `lrat }
    discard <| Tactic.BVDecide.Frontend.bvDecide mv' cfg
    let endTime ← IO.monoMsNow
    logInfo m!"bv_decide took {endTime - startTime}ms"
  let value ← instantiateExprMVars mv
  let r := (← getEnv).addDecl (← getOptions) (.thmDecl { name := ← Lean.mkAuxName `thm 1, levelParams := [], type, value })
  match r with
  | .error e =>
    throwError m!"Error: {e.toMessageData (← getOptions)}"
  | .ok env =>
    modifyEnv fun _ => env

def parseSmt2File (path : System.FilePath) : MetaM Expr := do
  let query ← IO.FS.readFile path
  Parser.parseSmt2Query query

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

unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let some (path : String) := args[0]?
    | throw (.userError "usage: lake exe leanwuzla /path/to/file.smt2")
  withImportModules #[`Std.Tactic.BVDecide] Options.empty 0 fun env => do
    _ ← Meta.MetaM.toIO (parseAndDecideSmt2File path)
      { fileName := "leanwuzla", fileMap := default, options := Options.empty } { env := env }
