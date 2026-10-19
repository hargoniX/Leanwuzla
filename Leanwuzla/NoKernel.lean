module

public import Leanwuzla.Basic
import all Lean.Meta.Tactic.BVDecide


open Lean Std.Sat Std.Tactic.BVDecide
open Meta.Tactic.BVDecide

def runSolver (cnf : CNF Nat) (solver : System.FilePath) (lratPath : System.FilePath)
    (trimProofs : Bool) (timeout : Nat) (binaryProofs : Bool) (solverMode : Elab.Tactic.BVDecide.SolverMode) :
    CoreM (Except (Array (Bool × Nat)) (Array LRAT.IntAction)) := do
  IO.FS.withTempFile fun cnfHandle cnfPath => do
    withTraceNode `sat (fun _ => return "Serializing SAT problem to DIMACS file") do
      -- lazyPure to prevent compiler lifting
      cnfHandle.putStr  (← IO.lazyPure (fun _ => cnf.dimacs))
      cnfHandle.flush

    let res ←
      withTraceNode `sat (fun _ => return "Running SAT solver") do
        External.satQuery solver cnfPath lratPath timeout binaryProofs solverMode
    if let .sat assignment := res then
      return .error assignment

    let lratProof ←
      withTraceNode `sat (fun _ => return "Obtaining LRAT certificate") do
        LratCert.load lratPath trimProofs

    return .ok lratProof

public def decideSmtNoKernel (type : Expr) (getModel : Bool) : SolverM UInt8 := do
  let solver ← determineSolver
  let g := (← Meta.mkFreshExprMVar type).mvarId!
  let (fvars, g) ← g.introsP
  trace[Meta.Tactic.bv] m!"Working on goal: {g}"
  let cfg ← SolverM.getBVDecideConfig
  try
    SolverM.runGrind <| Normalize.PreProcessM.run' (.new (.solve (some #[])) cfg) (.mvarIdTarget g) do
    g.withContext $ IO.FS.withTempFile fun _ lratPath => do
      if ← Normalize.bvNormalize then
        logInfo "unsat"
        return (0 : UInt8)
      let g ← Normalize.PreProcessM.getTargetMVarId
      let hypotheses ← Normalize.PreProcessM.getHyps
      -- Reflect the goal and, at the same time, record the atom assignment so
      -- that we can reconstruct a model if the query turns out to be sat.
      let (bvExpr, atomsAssignment, unusedHypotheses) ← ReifyM.run (hypotheses := hypotheses) (cfg := cfg) do
        let reflectionResult ← reflectBV g
        let atomsAssignment ← ReifyM.atomsAssignmentMap
        return (reflectionResult.satExpr.bvExpr, atomsAssignment, reflectionResult.unusedHypotheses)

      let entry ←
        withTraceNode `bv (fun _ => return "Bitblasting BVLogicalExpr to AIG") do
          -- lazyPure to prevent compiler lifting
          IO.lazyPure (fun _ => bvExpr.bitblast)
      let aigSize := entry.aig.decls.size
      trace[Meta.Tactic.bv] s!"AIG has {aigSize} nodes."

      let cnf ←
        withTraceNode `sat (fun _ => return "Converting AIG to CNF") do
          -- lazyPure to prevent compiler lifting
          IO.lazyPure (fun _ => Std.Sat.AIG.toCNF entry)

      let res ←
        withTraceNode `sat (fun _ => return "Obtaining external proof certificate") do
          runSolver cnf solver lratPath cfg.trimProofs cfg.timeout cfg.binaryProofs cfg.solverMode

      match res with
      | .ok cert =>
        let certFine ←
          withTraceNode `sat (fun _ => return "Verifying LRAT certificate") do
            -- lazyPure to prevent compiler lifting
            IO.lazyPure (fun _ => LRAT.check cert cnf)
        if certFine then
          logInfo "unsat"
          return (0 : UInt8)
        else
          logInfo "Error: Failed to check LRAT cert"
          return (1 : UInt8)
      | .error assignment =>
        let equations := reconstructCounterExample entry.aig assignment atomsAssignment
        let equations := equations.filterMap fun (lhs, synth, rhs) =>
          if synth then none else some (lhs, rhs)
        reportCounterExample fvars getModel { goal := g, unusedHypotheses, equations, functionAtoms := #[] }
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
        g.withContext do printModel fvars #[]
      return (0 : UInt8)
    else
      logError m!"Error: {e.toMessageData}"
      return (1 : UInt8)
where
  determineSolver : CoreM System.FilePath := do
    let opts ← getOptions
    let option := sat.solver.get opts
    if option == "" then
      let cadicalPath := (← IO.appPath).parent.get! / "cadical" |>.withExtension System.FilePath.exeExtension
      if ← cadicalPath.pathExists then
        return cadicalPath
      else
        return "cadical"
    else
      return option
