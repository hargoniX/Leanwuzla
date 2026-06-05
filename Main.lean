import Cli

import Leanwuzla.Parser
import Leanwuzla.Basic
import Leanwuzla.NoKernel

open Lean

def parseSmt2File (path : System.FilePath) : MetaM (Expr × Bool) := do
  let query ← IO.FS.readFile path
  ofExcept (Parser.parseSmt2Query query)


open Meta in
open Elab in
def decideSmt (type : Expr) (getModel : Bool) : SolverM UInt8 := do
  let mv ← Meta.mkFreshExprMVar type
  let (fvars, mv') ← mv.mvarId!.introsP
  trace[Meta.Tactic.bv] m!"Working on goal: {mv'}"
  try
    mv'.withContext $ IO.FS.withTempFile fun _ lratFile => do
      let cfg ← SolverM.getBVDecideConfig
      let ctx ← (Tactic.BVDecide.TacticContext.new lratFile cfg).run' { declName? := `lrat }
      match ← Tactic.BVDecide.bvDecide' mv' ctx with
      | .error counterExample =>
        reportCounterExample fvars getModel counterExample
      | .ok _ =>
        let value ← instantiateExprMVars mv
        Lean.addDecl (.thmDecl { name := ← Lean.mkAuxDeclName, levelParams := [], type, value })
        logInfo "unsat"
        return (0 : UInt8)
  catch e =>
    -- TODO: improve handling of sat cases. This is a temporary workaround.
    let message ← e.toMessageData.toString
    if message.startsWith "None of the hypotheses are in the supported BitVec fragment" then
      -- We fully support SMT-LIB v2.6. Getting the above error message means the
      -- goal was reduced to `False` with only `True` as an assumption. Every
      -- declared constant is then unconstrained, so the model completed entirely
      -- with default values is a valid one.
      logInfo "sat"
      if getModel then
        mv'.withContext do printModel fvars #[]
      return (0 : UInt8)
    else
      logError m!"Error: {e.toMessageData}"
      return (1 : UInt8)

def typeCheck (e : Expr) : SolverM UInt8 := do
  try
    let defn := .defnDecl {
      name := ← Lean.mkAuxDeclName
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

/--
Reports messages on stdout and returns the new total number of errors reported.
If `json` is true, prints messages as JSON (one per line).
If a message's kind is in `severityOverrides`, it will be reported with
the specified severity.
-/
private def reportMessages (msgLog : MessageLog) (opts : Options)
    (json : Bool) (severityOverrides : NameMap MessageSeverity) (numErrors : Nat) : IO Nat := do
  let includeEndPos := Lean.Language.printMessageEndPos.get opts
  msgLog.unreported.foldlM (init := numErrors) fun numErrors msg => do
    let numErrors := numErrors + (if msg.severity matches .error then 1 else 0)
    let maxErrorsReached := Lean.Language.maxErrors.get opts != 0 && numErrors > Lean.Language.maxErrors.get opts
    let msg : Message :=
      if maxErrorsReached then { msg with
        data := s!"maximum number of errors ({Lean.Language.maxErrors.get opts}; from option `maxErrors`) reached, exiting"
        severity := .error
      } else if let some severity := severityOverrides.find? msg.kind then
        {msg with severity}
      else
        msg
    unless msg.isSilent do
      if json then
        let j ← msg.toJson
        IO.println j.compress
      else
        let s ← msg.toString includeEndPos
        IO.print s
    if maxErrorsReached then
      IO.Process.exit 1
    return numErrors

def parseAndDecideSmt2File : SolverM UInt8 := do
  try
    let (goalType, getModel) ← parseSmt2File (← SolverM.getInput)
    if ← SolverM.getParseOnly then
      logInfo m!"Goal:\n{goalType}"
      typeCheck goalType
    else
      if ← SolverM.getKernelDisabled then
        decideSmtNoKernel goalType getModel
      else
        decideSmt goalType getModel
  finally
    printTraces
    reportMessages (← Core.getMessageLog) (← getOptions) false {} 0

section Cli

open Cli

open Elab.Tactic.BVDecide.Frontend

deriving instance Inhabited for Elab.Tactic.BVDecide.SolverMode

instance : ToString Elab.Tactic.BVDecide.SolverMode where
  toString
  | .proof          => "proof"
  | .counterexample => "counterexample"
  | .default        => "default"

instance : ParseableType Elab.Tactic.BVDecide.SolverMode where
  name := "SolverMode"
  parse?
  | "proof"           => some .proof
  | "counterexample"  => some .counterexample
  | "default"         => some .default
  | _                 => none

unsafe def runLeanwuzlaCmd (p : Parsed) : IO UInt32 := do
  let options := argsToOpts p
  let context := argsToContext p
  Lean.initSearchPath (← Lean.findSysroot)
  enableInitializersExecution
  let env ← importModules #[`Std.Tactic.BVDecide, `Leanwuzla.Auxiliary] {} 0 (loadExts := true)
  let coreContext := { fileName := "leanwuzla", fileMap := default, options }
  let coreState := { env }
  let code ← SolverM.run parseAndDecideSmt2File context coreContext coreState
  IO.Process.exit code
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
          |>.set `pp.maxSteps 100000000000000000
          |>.set `pp.deepTerms.threshold 100000000

    opts := opts.set `maxHeartbeats <| p.flag! "maxHeartbeats" |>.as! Nat
    opts := opts.set `maxRecDepth <| p.flag! "maxRecDepth" |>.as! Nat
    opts := opts.set `trace.profiler.threshold <| p.flag! "pthreshold" |>.as! Nat
    opts := opts.set `exponentiation.threshold <| p.flag! "expthreshold" |>.as! Nat

    return opts

  argsToContext (p : Parsed) : Context :=
    {
      acNf := p.hasFlag "acnf"
      parseOnly := p.hasFlag "parseOnly"
      timeout := p.flag! "timeout" |>.as! Nat
      input := p.positionalArg! "input" |>.as! String
      maxSteps := p.flag! "maxSteps" |>.as! Nat
      disableAndFlatten := p.hasFlag "disableAndFlatten"
      disableEmbeddedConstraintSubst := p.hasFlag "disableEmbeddedConstraintSubst"
      disableKernel := p.hasFlag "disableKernel"
      solverMode := p.flag! "solverMode" |>.as! Elab.Tactic.BVDecide.SolverMode
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
    solverMode : Elab.Tactic.BVDecide.SolverMode; "Select the SAT solver configuration to use (`proof`, `counterexample`, `default`)."

  ARGS:
    input : String; "Path to the smt2 file to work on"

  EXTENSIONS:
    defaultValues! #[
      ("timeout", "10"),
      ("maxHeartbeats", toString maxHeartbeats.defValue),
      ("maxRecDepth", toString maxRecDepth.defValue),
      ("pthreshold", toString trace.profiler.threshold.defValue),
      ("maxSteps", toString Lean.Meta.Simp.defaultMaxSteps),
      ("expthreshold", toString exponentiation.threshold.defValue),
      ("solverMode", toString Lean.Elab.Tactic.BVDecide.SolverMode.proof)
    ]
]

end Cli

unsafe def main (args : List String) : IO UInt32 := do
  leanwuzlaCmd.validate args
