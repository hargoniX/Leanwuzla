import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide
import Lean.Language.Lean
import Cli

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

def parseSmt2File (path : System.FilePath) : MetaM Expr := do
  let query ← IO.FS.readFile path
  ofExcept (Parser.parseSmt2Query query)

structure Context where
  acNf : Bool
  parseOnly : Bool
  timeout : Nat
  input : String
  maxSteps : Nat

abbrev SolverM := ReaderT Context MetaM

namespace SolverM

def getAcNf : SolverM Bool := return (← read).acNf
def getParseOnly : SolverM Bool := return (← read).parseOnly
def getTimeout : SolverM Nat := return (← read).timeout
def getInput : SolverM String := return (← read).input
def getMaxSteps : SolverM Nat := return (← read).maxSteps

def run (x : SolverM α) (ctx : Context) (coreContext : Core.Context) (coreState : Core.State) :
    IO α := do
  let (res, _, _) ← ReaderT.run x ctx |> (Meta.MetaM.toIO · coreContext coreState)
  return res

end SolverM

open Elab in
def decideSmt (type : Expr) : SolverM UInt32 := do
  let mv ← Meta.mkFreshExprMVar type
  let (_, mv') ← mv.mvarId!.introsP
  trace[Meta.Tactic.bv] m!"Working on goal: {mv'}"
  try
    mv'.withContext $ IO.FS.withTempFile fun _ lratFile => do
      let cfg := {
        timeout := ← SolverM.getTimeout
        acNf := ← SolverM.getAcNf
        maxSteps := ← SolverM.getMaxSteps
      }
      let ctx ← (Tactic.BVDecide.Frontend.TacticContext.new lratFile cfg).run' { declName? := `lrat }
      discard <| Tactic.BVDecide.Frontend.bvDecide mv' ctx
  catch e =>
    -- TODO: improve handling of sat cases. This is a temporary workaround.
    let message ← e.toMessageData.toString
    if message.startsWith "The prover found a counterexample" ||
       message.startsWith "None of the hypotheses are in the supported BitVec fragment" then
      -- We fully support SMT-LIB v2.6. Getting the above error message means
      -- the goal was reduced to `False` with only `True` as an assumption.
      logInfo "sat"
      return (0 : UInt32)
    else
      logError m!"Error: {e.toMessageData}"
      return (1 : UInt32)
  let value ← instantiateExprMVars mv
  let r := (← getEnv).addDecl (← getOptions) (.thmDecl { name := ← Lean.mkAuxName `thm 1, levelParams := [], type, value })
  match r with
  | .error e =>
    logError m!"Error: {e.toMessageData (← getOptions)}"
    return 1
  | .ok env =>
    setEnv env
    logInfo "unsat"
    return 0

def typeCheck (e : Expr) : SolverM UInt32 := do
  let defn := .defnDecl {
    name := ← Lean.mkAuxName `def 1
    levelParams := []
    type := .sort .zero
    value := e
    hints := .regular 0
    safety := .safe
  }
  let r := (← getEnv).addDecl (← getOptions) defn
  let .error e := r | return 0
  logError m!"Error: {e.toMessageData (← getOptions)}"
  return 1

def parseAndDecideSmt2File : SolverM UInt32 := do
  try
    let goalType ← parseSmt2File (← SolverM.getInput)
    if ← SolverM.getParseOnly then
      typeCheck goalType
    else
      decideSmt goalType
  finally
    printTraces
    Lean.Language.reportMessages (← Core.getMessageLog) (← getOptions)

section Cli

open Cli

unsafe def runLeanwuzlaCmd (p : Parsed) : IO UInt32 := do
  let options := argsToOpts p
  let context := argsToContext p
  Lean.initSearchPath (← Lean.findSysroot)
  withImportModules #[`Std.Tactic.BVDecide, `Leanwuzla.Aux] {} 0 fun env => do
    let coreContext := { fileName := "leanwuzla", fileMap := default, options }
    let coreState := { env }
    SolverM.run parseAndDecideSmt2File context coreContext coreState
where
  argsToOpts (p : Parsed) : Options := Id.run do
    let mut opts := Options.empty

    if p.hasFlag "verbose" then
      opts :=
        opts
          |>.setBool `trace.Meta.Tactic.bv true
          |>.setBool `trace.Meta.Tactic.sat true
          |>.setBool `trace.profiler true

    if p.hasFlag "vsimp" then
      opts :=
        opts
          |>.setBool `trace.Meta.Tactic.simp true

    opts := opts.setNat `maxHeartbeats <| p.flag! "maxHeartbeats" |>.as! Nat
    opts := opts.setNat `maxRecDepth <| p.flag! "maxRecDepth" |>.as! Nat
    opts := opts.setNat `trace.profiler.threshold <| p.flag! "pthreshold" |>.as! Nat

    return opts

  argsToContext (p : Parsed) : Context :=
    {
      acNf := p.hasFlag "acNf"
      parseOnly := p.hasFlag "parseOnly"
      timeout := p.flag! "timeout" |>.as! Nat
      input := p.positionalArg! "input" |>.as! String
      maxSteps := p.flag! "maxSteps" |>.as! Nat
    }

unsafe def leanwuzlaCmd : Cmd := `[Cli|
  leanwuzla VIA runLeanwuzlaCmd; ["0.1.0"]
  "Run LeanSAT as an SMT solver on an SMTLIB2 file."

  FLAGS:
    v, verbose; "Print profiler trace output from LeanSAT."
    acnf; "Activate the normalisation pass up to commutatitvity."
    parseOnly; "Only parse and exit right away."
    timeout : Nat; "Set the SAT solver timeout in seconds."

    maxHeartbeats : Nat; "Set the maxHeartbeats."
    maxRecDepth : Nat; "Set the maxRecDepth."
    pthreshold : Nat; "The timing threshold for profiler output."
    maxSteps : Nat; "Set the maximum number of simplification steps."
    vsimp; "Print the profiler trace output from simp."

  ARGS:
    input : String; "Path to the smt2 file to work on"

  EXTENSIONS:
    defaultValues! #[
      ("timeout", "10"),
      ("maxHeartbeats", toString maxHeartbeats.defValue),
      ("maxRecDepth", toString maxRecDepth.defValue),
      ("pthreshold", toString trace.profiler.threshold.defValue),
      ("maxSteps", toString Lean.Meta.Simp.defaultMaxSteps)
    ]
]

end Cli

unsafe def main (args : List String) : IO UInt32 := do
  leanwuzlaCmd.validate args
