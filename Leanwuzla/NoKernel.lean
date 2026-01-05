import Leanwuzla.Basic

open Lean Std.Sat Std.Tactic.BVDecide
open Elab.Tactic.BVDecide
open Elab.Tactic.BVDecide.Frontend

def runSolver (cnf : CNF Nat) (solver : System.FilePath) (lratPath : System.FilePath)
    (trimProofs : Bool) (timeout : Nat) (binaryProofs : Bool) (solverMode : SolverMode) :
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

def decideSmtNoKernel (type : Expr) : SolverM UInt8 := do
  let solver ← determineSolver
  let g := (← Meta.mkFreshExprMVar type).mvarId!
  let (_, g) ← g.introsP
  trace[Meta.Tactic.bv] m!"Working on goal: {g}"
  try
    g.withContext $ IO.FS.withTempFile fun _ lratPath => do
      let cfg ← SolverM.getBVDecideConfig
      match ← Normalize.bvNormalize g cfg with
      | some g =>
        let bvExpr := (← M.run <| reflectBV g).bvExpr

        let entry ←
          withTraceNode `bv (fun _ => return "Bitblasting BVLogicalExpr to AIG") do
            -- lazyPure to prevent compiler lifting
            IO.lazyPure (fun _ => bvExpr.bitblast)
        let aigSize := entry.aig.decls.size
        trace[Meta.Tactic.bv] s!"AIG has {aigSize} nodes."

        let (cnf, _) ←
          withTraceNode `sat (fun _ => return "Converting AIG to CNF") do
            -- lazyPure to prevent compiler lifting
            IO.lazyPure (fun _ =>
              let (entry, map) := entry.relabelNat'
              let cnf := Std.Sat.AIG.toCNF entry
              (cnf, map)
            )

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
        | .error .. =>
          logInfo "sat"
          return (0 : UInt8)
      | none =>
        logInfo "unsat"
        return (0 : UInt8)
  catch e =>
    -- TODO: improve handling of sat cases. This is a temporary workaround.
    let message ← e.toMessageData.toString
    if message.startsWith "None of the hypotheses are in the supported BitVec fragment" then
      -- We fully support SMT-LIB v2.6. Getting the above error message means
      -- the goal was reduced to `False` with only `True` as an assumption.
      logInfo "sat"
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
