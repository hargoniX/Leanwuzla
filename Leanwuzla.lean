/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

/--
Invoke Bitwuzla on an SMT-fied version of a bitvector goal to see if it holds or not.
Does not generate a proof term.
-/
syntax (name := bvBitwuzla) "bv_bitwuzla" (str)? : tactic

/--
Compare the performance of `bv_decide` and `bv_bitwuzla`.
-/
syntax (name := bvCompare) "bv_compare" (str)? : tactic

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend

open Std.Sat
open Std.Tactic.BVDecide
open Std.Tactic.BVDecide.Reflect
open Lean.Meta


partial def toSMT (expr : BVLogicalExpr) (atomsAssignment : Std.HashMap Nat (Nat × Expr)) : String :=
  let (_, buffer) := StateT.run (go expr atomsAssignment) ""
  buffer
where
  @[inline]
  push (str : String) : StateM String Unit := modify fun buf => buf ++ str

  @[specialize]
  withParens (arg : StateM String Unit) : StateM String Unit := do
    push "("
    arg
    push ")"

  @[inline]
  pushUnaryOp (opName : String) (arg : StateM String Unit) : StateM String Unit := do
    withParens do
      push s!"{opName} "
      arg

  @[inline]
  pushBinaryOp (opName : String) (lhs rhs : StateM String Unit) : StateM String Unit := do
    withParens do
      push s!"{opName} "
      lhs
      push " "
      rhs

  @[inline]
  pushIteOp (c e1 e2 : StateM String Unit) : StateM String Unit := do
    withParens do
      push s!"ite "
      c
      push " "
      e1
      push " "
      e2

  go (expr : BVLogicalExpr) (atomsAssignment : Std.HashMap Nat (Nat × Expr)) : StateM String Unit := do
    push "(set-logic QF_BV)\n"
    declareConsts atomsAssignment
    pushUnaryOp "assert" (goBVLogical expr)
    push "\n"
    push "(check-sat)\n"
    push "(exit)\n"

  declareConsts (atomsAssignment : Std.HashMap Nat (Nat × Expr)) : StateM String Unit := do
    for (atom, (width, _)) in atomsAssignment do
      push s!"(declare-const x_{atom} (_ BitVec {width}))\n"

  goBVLogical (expr : BVLogicalExpr) : StateM String Unit := do
    match expr with
    | .literal pred => goBVPred pred
    | .const b =>
      match b with
      | true => push "true"
      | false => push "false"
    | .not expr => pushUnaryOp "not" (goBVLogical expr)
    | .ite c e1 e2 => pushIteOp (goBVLogical c) (goBVLogical e1) (goBVLogical e2)
    | .gate gate lhs rhs =>
      let gateStr :=
        match gate with
        | .and => "and"
        | .xor => "xor"
        | .beq => "="
        | .imp => "=>"
      pushBinaryOp gateStr (goBVLogical lhs) (goBVLogical rhs)

  goBVPred (pred : BVPred) : StateM String Unit := do
   match pred with
   | .bin lhs op rhs =>
     let opStr :=
       match op with
       | .eq => "="
       | .ult => "bvult"
     pushBinaryOp opStr (goBVExpr lhs) (goBVExpr rhs)
   | .getLsbD expr idx =>
     push s!"(= #b1 ((_ extract {idx} {idx}) "
     goBVExpr expr
     push "))"

  goBVExpr {w : Nat} (expr : BVExpr w) : StateM String Unit := do
    match expr with
    | .var idx => push s!"x_{idx}"
    | .const val =>
      let s := (Nat.toDigits 2 val.toNat).asString
      let t := (List.replicate (w - s.length) '0').asString
      let binStr := t ++ s
      push "#b"
      push binStr
    | .extract start len expr => pushUnaryOp s!"(_ extract {len - 1 + start} {start})" (goBVExpr expr)
    | .bin lhs op rhs =>
      let lhs := goBVExpr lhs
      let rhs := goBVExpr rhs
      match op with
      | .and => pushBinaryOp "bvand" lhs rhs
      | .or =>  pushBinaryOp "bvor" lhs rhs
      | .xor => pushBinaryOp "bvxor" lhs rhs
      | .add => pushBinaryOp "bvadd" lhs rhs
      | .mul => pushBinaryOp "bvmul" lhs rhs
      | .udiv =>
        let zero := goBVExpr <| .const (w := w) 0
        withParens do
          push "ite "
          pushBinaryOp "=" zero rhs
          push " "
          zero
          push " "
          pushBinaryOp "bvudiv" lhs rhs
      | .umod =>
        let zero := goBVExpr <| .const (w := w) 0
        withParens do
          push "ite "
          pushBinaryOp "=" zero rhs
          push " "
          zero
          push " "
          pushBinaryOp "bvurem" lhs rhs
    | .un op operand =>
      match op with
      | .not => pushUnaryOp "bvnot" (goBVExpr operand)
      | .shiftLeftConst n => pushBinaryOp "bvshl" (goBVExpr operand) (goBVExpr (bvConst w n))
      | .shiftRightConst n => pushBinaryOp "bvlshr" (goBVExpr operand) (goBVExpr (bvConst w n))
      | .rotateLeft n => pushUnaryOp s!"(_ rotate_left {n})" (goBVExpr operand)
      | .rotateRight n => pushUnaryOp s!"(_ rotate_right {n})" (goBVExpr operand)
      | .arithShiftRightConst n => pushBinaryOp s!"bvashr" (goBVExpr operand) (goBVExpr (bvConst w n))
    | .append lhs rhs => pushBinaryOp "concat" (goBVExpr lhs) (goBVExpr rhs)
    | .replicate n expr => pushUnaryOp s!"(_ repeat {n})" (goBVExpr expr)
    | .zeroExtend (w := w) v expr =>
      if v ≤ w then
        emitTruncate expr v
      else
        pushUnaryOp s!"(_ zero_extend {v - w})" (goBVExpr expr)
    | .signExtend (w := w) v expr =>
      if v ≤ w then
        emitTruncate expr v
      else
        pushUnaryOp s!"(_ sign_extend {v - w})" (goBVExpr expr)
    | .shiftLeft lhs rhs => pushBinaryOp "bvshl" (goBVExpr lhs) (goBVExpr rhs)
    | .shiftRight lhs rhs => pushBinaryOp "bvlshr" (goBVExpr lhs) (goBVExpr rhs)

  emitTruncate {w : Nat} (expr : BVExpr w) (targetWidth : Nat) : StateM String Unit := do
    pushUnaryOp s!"(_ extract {targetWidth - 1} 0)" (goBVExpr expr)

  @[inline]
  bvConst (w : Nat) (n : Nat) : BVExpr w := .const (BitVec.ofNat w n)

def smtQuery (solverPath : System.FilePath) (problemPath : System.FilePath) (timeout : Nat) :
    CoreM External.SolverResult := do
  let cmd := solverPath.toString
  let opts ← getOptions
  let verbose := diagnostics.get opts
  let mut args := #[
    problemPath.toString,
    "-v=1"
  ]

  if verbose then
    args := args.push "-p"

  let out? ← External.runInterruptible timeout { cmd, args, stdin := .piped, stdout := .piped, stderr := .null }
  match out? with
  | .timeout =>
    throwError "The SMT solver timed out while solving the problem."
  | .success { exitCode := exitCode, stdout := stdout, stderr := stderr} =>
    if exitCode == 255 then
      throwError s!"Failed to execute external prover:\n{stderr}"
    else
      let stdoutLines := stdout.splitOn "\n"
      let solvingLine := stdoutLines[stdoutLines.length - 2]!
      assert! solvingLine.startsWith "solving_context::time_solve:"
      trace[Meta.Tactic.bv] solvingLine
      if stdoutLines.contains "sat" then
        return .sat #[]
      else if stdoutLines.contains "unsat" then
        return .unsat
      else
        throwError s!"The external prover produced unexpected output, stdout:\n{stdout}stderr:\n{stderr}"



axiom bitwuzlaCorrect (expr : BVLogicalExpr) : expr.Unsat

def bitwuzlaCounterExample : String := "Bitwuzla found a counter example"
def bitwuzlaSuccess : String := "Bitwuzla thinks it's right but can't trust the wuzla!"

def bitwuzla (g : MVarId) (reflectionResult : ReflectionResult) (atomsAssignment : Std.HashMap Nat (Nat × Expr))
    (solverPath : System.FilePath) :
    MetaM (Except CounterExample UnsatProver.Result) := do
  let smt := toSMT reflectionResult.bvExpr atomsAssignment
  trace[Meta.Tactic.bv] s!"Encoded as SMT: {smt}"
  let res ←
    IO.FS.withTempFile fun handle path => do
      handle.putStr smt
      handle.flush
      withTraceNode `bv (fun _ => return "Proving with bitwuzla") do
        let opts ← getOptions
        let timeout := sat.timeout.get opts
        smtQuery solverPath path timeout
  match res with
  | .sat .. => return .error ⟨g, {}, #[]⟩
  | .unsat => return .ok ⟨mkApp (mkConst ``bitwuzlaCorrect) (toExpr reflectionResult.bvExpr), ""⟩

def bvBitwuzla (g : MVarId) (solverPath : System.FilePath) : MetaM (Except CounterExample Unit) := do
  let some g ← Normalize.bvNormalize g | return .ok ()
  let unsatProver : UnsatProver := fun g reflectionResult atomsAssignment => do
    withTraceNode `bv (fun _ => return "Preparing LRAT reflection term") do
      bitwuzla g reflectionResult atomsAssignment solverPath
  match ← closeWithBVReflection g unsatProver with
  | .ok .. => return .ok ()
  | .error err => return .error err


@[tactic bvBitwuzla]
def evalBvBitwuzla : Tactic := fun
  | `(tactic| bv_bitwuzla $solverPath:str) => do
    liftMetaFinishingTactic fun g => do
      match ← bvBitwuzla g solverPath.getString with
      | .ok .. => throwError bitwuzlaSuccess
      | .error .. => throwError bitwuzlaCounterExample
  | `(tactic| bv_bitwuzla) => do
    liftMetaFinishingTactic fun g => do
      match ← bvBitwuzla g "bitwuzla" with
      | .ok .. => throwError bitwuzlaSuccess
      | .error .. => throwError bitwuzlaCounterExample
  | _ => throwUnsupportedSyntax

structure BitwuzlaPerf where
  success : Bool
  overallTime : Float
  solvingContextTime : Float

structure LeansatSuccessTimings where
  timeRewrite: Float
  timeBitBlasting : Float
  timeSatSolving : Float
  timeLratTrimming : Float
  timeLratChecking : Float

structure LeansatFailureTimings where
  timeRewrite : Float
  timeSatSolving : Float

inductive LeansatPerf where
| success (overallTime : Float) (timings : LeansatSuccessTimings)
| failure (overallTime : Float) (timings : LeansatFailureTimings)

structure Comparision where
  bitwuzlaPerf : BitwuzlaPerf
  leansatPerf : LeansatPerf

def BitwuzlaPerf.toString (perf : BitwuzlaPerf) : String :=
  if perf.success then
    s!"Bitwuzla proved the goal after {perf.overallTime}ms, solving context: {perf.solvingContextTime}ms"
  else
    s!"Bitwuzla provided a counter example after {perf.overallTime}ms, solving context: {perf.solvingContextTime}ms"

instance : ToString BitwuzlaPerf where
  toString := BitwuzlaPerf.toString

def LeansatSuccessTimings.toString (timings : LeansatSuccessTimings) : String :=
  let { timeRewrite, timeBitBlasting, timeSatSolving, timeLratTrimming, timeLratChecking } := timings
  s!"rewriting {timeRewrite}ms, bitblasting {timeBitBlasting}ms, SAT solving {timeSatSolving}ms, LRAT trimming {timeLratTrimming}ms, LRAT checking {timeLratChecking}ms"

instance : ToString LeansatSuccessTimings where
  toString := LeansatSuccessTimings.toString

def LeansatFailureTimings.toString (timings : LeansatFailureTimings) : String :=
  let { timeRewrite, timeSatSolving } := timings
  s!"rewriting {timeRewrite} SAT solving {timeSatSolving}ms"

instance : ToString LeansatFailureTimings where
  toString := LeansatFailureTimings.toString

def LeansatPerf.toString (perf : LeansatPerf) : String :=
  match perf with
  | .success overallTime timings =>
    s!"LeanSAT proved the goal after {overallTime}ms: {timings}"
  | .failure overallTime timings =>
    s!"LeanSAT provided a counter example after {overallTime}ms: {timings}"

instance : ToString LeansatPerf where
  toString := LeansatPerf.toString

def Comparision.toString (comp : Comparision) : String :=
  comp.bitwuzlaPerf.toString ++ "\n" ++ comp.leansatPerf.toString

instance : ToString Comparision where
  toString := Comparision.toString

def TraceData.durationMs (data : TraceData) : Float := (data.stopTime - data.startTime) * 1000.0

partial def parseSuccessTrace (traces : PersistentArray TraceElem) : IO LeansatSuccessTimings := do
  let traces := traces.toArray.map TraceElem.msg
  let (_, time) ← go traces |>.run {
    timeRewrite := 0,
    timeBitBlasting := 0,
    timeSatSolving := 0,
    timeLratTrimming := 0,
    timeLratChecking := 0,
  }
  return time
where
  go (msgs : Array MessageData) : StateT LeansatSuccessTimings IO Unit := do
    for msg in msgs do
      match msg with
      | .trace data msg children =>
        let msg ← msg.toString
        match msg with
        | "Normalizing goal" =>
          modify fun s => { s with timeRewrite := TraceData.durationMs data }
        | "Bitblasting BVLogicalExpr to AIG" =>
          modify fun s => { s with timeBitBlasting := TraceData.durationMs data }
        | "Running SAT solver" =>
          modify fun s => { s with timeSatSolving := TraceData.durationMs data }
        | "Obtaining LRAT certificate" =>
          modify fun s => { s with timeLratTrimming := TraceData.durationMs data }
        | "Verifying LRAT certificate" =>
          modify fun s => { s with timeLratChecking := TraceData.durationMs data }
        | _ => pure ()
        go children
      | .withContext _ msg => go #[msg]
      | _ => continue

partial def parseFailureTrace (traces : PersistentArray TraceElem) : IO LeansatFailureTimings := do
  let traces := traces.toArray.map TraceElem.msg
  let (_, time) ← go traces |>.run { timeRewrite := 0.0, timeSatSolving := 0.0 }
  return time
where
  go (msgs : Array MessageData) : StateT LeansatFailureTimings IO Unit := do
    for msg in msgs do
      match msg with
      | .trace data msg children =>
        let msg ← msg.toString
        match msg with
        | "Normalizing goal" =>
          modify fun s => { s with timeRewrite := TraceData.durationMs data }
        | "Running SAT solver" =>
          modify fun s => { s with timeSatSolving := TraceData.durationMs data }
        | _ => pure ()
        go children
      | .withContext _ msg => go #[msg]
      | _ => continue

partial def evalBitwuzla (g : MVarId) (solverPath : System.FilePath) : MetaM BitwuzlaPerf := do
  let t1 ← IO.monoNanosNow
  let res ← bvBitwuzla g solverPath
  let t2 ← IO.monoNanosNow
  let overallTime := (Float.ofNat <| t2 - t1) / 1000000.0
  let (_, solvingContextTime) ← parseBitwuzlaTrace ((← getTraces).toArray.map TraceElem.msg) |>.run 0
  return { success := res.isOk, overallTime, solvingContextTime }
where
  parseBitwuzlaTrace (msgs : Array MessageData) : StateT Float IO Unit := do
    for msg in msgs do
      match msg with
      | .trace _ msg children =>
        let msg ← msg.toString
        let pref := "solving_context::time_solve: "
        if msg.startsWith pref then
          let msg := (msg.splitOn " ")[1]!.dropRight 2
          set <| Float.ofInt msg.toNat!
        parseBitwuzlaTrace children
      | .withContext _ msg => parseBitwuzlaTrace #[msg]
      | _ => continue

def evalLeanSat (g : MVarId) (cfg : TacticContext) : MetaM LeansatPerf := do
  let t1 ← IO.monoNanosNow
  let result ← bvDecide' g cfg
  let t2 ← IO.monoNanosNow
  let overallTime := (Float.ofNat <| t2 - t1) / 1000000.0

  let traces ← getTraces
  match result with
  | .ok _ =>
    return .success overallTime (← parseSuccessTrace traces)
  | .error _ =>
    return .failure overallTime (← parseFailureTrace traces)

def bvCompare (g : MVarId) (solverPath : System.FilePath) (cfg : TacticContext) :
    MetaM Comparision := do
  let setTraceOptions (opt : Options) : Options :=
    opt
      |>.setBool `trace.profiler true
      |>.setBool `trace.Meta.Tactic.bv true
      |>.setBool `trace.Meta.Tactic.sat true
  withOptions setTraceOptions do
    let s ← saveState
    resetTraceState
    let g' ← mkFreshExprMVar (← g.getType)
    let bitwuzlaPerf ← evalBitwuzla g'.mvarId! solverPath
    restoreState s
    let leansatPerf ← evalLeanSat g cfg
    resetTraceState
    return { bitwuzlaPerf, leansatPerf }

@[tactic bvCompare]
def evalBvCompare : Tactic := fun
  | `(tactic| bv_compare $solverPath:str) => do
    IO.FS.withTempFile fun _ lratFile => do
      let cfg ← TacticContext.new lratFile
      let g ← getMainGoal
      let res ← bvCompare g solverPath.getString cfg
      logInfo <| toString res
  | `(tactic| bv_compare) => do
    IO.FS.withTempFile fun _ lratFile => do
      let cfg ← TacticContext.new lratFile
      let g ← getMainGoal
      let res ← bvCompare g "bitwuzla" cfg
      logInfo <| toString res
  | _ => throwUnsupportedSyntax

end Frontend
end Lean.Elab.Tactic.BVDecide
