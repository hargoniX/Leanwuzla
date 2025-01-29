import Cli

import Leanwuzla.Parser
import Leanwuzla.Basic
import Leanwuzla.NoKernel

open Lean

def parseSmt2File (path : System.FilePath) : MetaM Expr := do
  let query ← IO.FS.readFile path
  ofExcept (Parser.parseSmt2Query query)


open Elab in
def decideSmt (type : Expr) : SolverM UInt32 := do
  let mv ← Meta.mkFreshExprMVar type
  let (_, mv') ← mv.mvarId!.introsP
  trace[Meta.Tactic.bv] m!"Working on goal: {mv'}"
  try
    mv'.withContext $ IO.FS.withTempFile fun _ lratFile => do
      let cfg ← SolverM.getBVDecideConfig
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
  try
    Lean.addDecl (.thmDecl { name := ← Lean.mkAuxName `thm 1, levelParams := [], type, value })
    logInfo "unsat"
    return 0
  catch e =>
    logError m!"Error: {e.toMessageData}"
    return 1

def typeCheck (e : Expr) : SolverM UInt32 := do
  try
    let defn := .defnDecl {
      name := ← Lean.mkAuxName `def 1
      levelParams := []
      type := .sort .zero
      value := e
      hints := .regular 0
      safety := .safe
    }
    Lean.addDecl defn
    return 0
  catch e =>
    logError m!"Error: {e.toMessageData}"
    return 1

def parseAndDecideSmt2File : SolverM UInt32 := do
  try
    let goalType ← parseSmt2File (← SolverM.getInput)
    if ← SolverM.getParseOnly then
      logInfo m!"Goal:\n{goalType}"
      typeCheck goalType
    else
      if ← SolverM.getKernelDisabled then
        decideSmtNoKernel goalType
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
          --|>.setBool `trace.profiler true

    if p.hasFlag "vsimp" then
      opts :=
        opts
          |>.setBool `trace.Meta.Tactic.simp true

    if p.hasFlag "disableKernel" then
      opts :=
        opts
          |>.setBool `debug.skipKernelTC true

    if p.hasFlag "parseOnly" then
       opts :=
        opts
          |>.setNat `pp.maxSteps 10000000000
          |>.setNat `pp.deepTerms.threshold 100

    opts := opts.setNat `maxHeartbeats <| p.flag! "maxHeartbeats" |>.as! Nat
    opts := opts.setNat `maxRecDepth <| p.flag! "maxRecDepth" |>.as! Nat
    opts := opts.setNat `trace.profiler.threshold <| p.flag! "pthreshold" |>.as! Nat
    opts := opts.setNat `exponentiation.threshold <| p.flag! "expthreshold" |>.as! Nat

    return opts

  argsToContext (p : Parsed) : Context :=
    {
      acNf := p.hasFlag "acNf"
      parseOnly := p.hasFlag "parseOnly"
      timeout := p.flag! "timeout" |>.as! Nat
      input := p.positionalArg! "input" |>.as! String
      maxSteps := p.flag! "maxSteps" |>.as! Nat
      disableAndFlatten := p.hasFlag "disableAndFlatten"
      disableEmbeddedConstraintSubst := p.hasFlag "disableEmbeddedConstraintSubst"
      disableKernel := p.hasFlag "disableKernel"
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
    expthreshold : Nat; "The threshold for maximum exponents. Useful to limit runaway computation."
    maxSteps : Nat; "Set the maximum number of simplification steps."
    pthreshold : Nat; "The timing threshold for profiler output."
    vsimp; "Print the profiler trace output from simp."
    disableAndFlatten; "Disable the and flattening pass."
    disableEmbeddedConstraintSubst; "Disable the embedded constraints substitution pass."
    disableKernel; "Disable the Lean kernel, that is only verify the LRAT cert, no reflection proof"

  ARGS:
    input : String; "Path to the smt2 file to work on"

  EXTENSIONS:
    defaultValues! #[
      ("timeout", "10"),
      ("maxHeartbeats", toString maxHeartbeats.defValue),
      ("maxRecDepth", toString maxRecDepth.defValue),
      ("pthreshold", toString trace.profiler.threshold.defValue),
      ("maxSteps", toString Lean.Meta.Simp.defaultMaxSteps),
      ("expthreshold", toString exponentiation.threshold.defValue)
    ]
]

end Cli

unsafe def main (args : List String) : IO UInt32 := do
  leanwuzlaCmd.validate args
