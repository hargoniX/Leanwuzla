/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

syntax (name := bvBitwuzla) "bv_bitwuzla" str : tactic

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

  @[inline]
  pushUnaryOp (opName : String) (arg : StateM String Unit) : StateM String Unit := do
      push s!"({opName} "
      arg
      push ")"

  @[inline]
  pushBinaryOp (opName : String) (lhs rhs : StateM String Unit) : StateM String Unit := do
      push s!"({opName} "
      lhs
      push " "
      rhs
      push ")"

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
    | .gate gate lhs rhs =>
      let gateStr :=
        match gate with
        | .and => "and"
        | .or => "or"
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
      let opStr :=
        match op with
        | .and => "bvand"
        | .or => "bvor"
        | .xor => "bvxor"
        | .add => "bvadd"
        | .mul => "bvmul"
      pushBinaryOp opStr (goBVExpr lhs) (goBVExpr rhs)
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
    | .zeroExtend (w := w) v expr => pushUnaryOp s!"(_ zero_extend {v - w})" (goBVExpr expr)
    | .signExtend (w := w) v expr => pushUnaryOp s!"(_ sign_extend {v - w})" (goBVExpr expr)
    | .shiftLeft lhs rhs => pushBinaryOp "bvshl" (goBVExpr lhs) (goBVExpr rhs)
    | .shiftRight lhs rhs => pushBinaryOp "bvlshr" (goBVExpr lhs) (goBVExpr rhs)

  @[inline]
  bvConst (w : Nat) (n : Nat) : BVExpr w := .const (BitVec.ofNat w n)

def smtQuery (solverPath : System.FilePath) (problemPath : System.FilePath) (timeout : Nat) :
    CoreM External.SolverResult := do
  let cmd := solverPath.toString
  let opts ← getOptions
  let verbose := diagnostics.get opts
  let mut args := #[
    problemPath.toString
  ]

  if verbose then
    args := args.push "-v=1"

  let out? ← External.runInterruptible timeout { cmd, args, stdin := .piped, stdout := .piped, stderr := .null }
  match out? with
  | .timeout =>
    throwError "The SMT solver timed out while solving the problem."
  | .success { exitCode := exitCode, stdout := stdout, stderr := stderr} =>
    if exitCode == 255 then
      throwError s!"Failed to execute external prover:\n{stderr}"
    else
      if stdout.startsWith "sat" then
        return .sat #[]
      else if stdout.startsWith "unsat" then
        return .unsat
      else
        throwError s!"The external prover produced unexpected output, stdout:\n{stdout}stderr:\n{stderr}"

def bitwuzla (reflectionResult : ReflectionResult) (atomsAssignment : Std.HashMap Nat (Nat × Expr))
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
  | .sat .. => throwError "Bitwuzla found a counter example"
  | .unsat => throwError "Bitwuzla thinks it's right but can't trust the wuzla!"

def bvBitwuzla (g : MVarId) (solverPath : System.FilePath) : MetaM Unit := do
  let ⟨g?, _⟩ ← Normalize.bvNormalize g
  let some g := g? | return ()
  let unsatProver : UnsatProver := fun reflectionResult atomsAssignment => do
    withTraceNode `bv (fun _ => return "Preparing LRAT reflection term") do
      bitwuzla reflectionResult atomsAssignment solverPath
  discard <| closeWithBVReflection g unsatProver


@[tactic bvBitwuzla]
def evalBvBitwuzla : Tactic := fun
  | `(tactic| bv_bitwuzla $solverPath:str) => do
    liftMetaFinishingTactic fun g => do
      discard <| bvBitwuzla g solverPath.getString
  | _ => throwUnsupportedSyntax

end Frontend
end Lean.Elab.Tactic.BVDecide
