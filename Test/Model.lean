/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/
import Leanwuzla.Parser
import Leanwuzla.Basic

open Lean Meta Elab Command
open Std.Tactic.BVDecide

/-! ## `smtSymbolToName` / `formatSmtSymbol` round-trip

A model must only mention symbols that occur in the original SMT-LIB input, so
`formatSmtSymbol (smtSymbolToName s)` has to denote the same symbol as `s`
(modulo redundant `|` quotes). -/

private def dequote (s : String) : String :=
  if s.startsWith "|" && s.endsWith "|" then ((s.drop 1).dropEnd 1).toString else s

private def roundTrips (s : String) : Bool :=
  dequote (formatSmtSymbol (Parser.smtSymbolToName s)) == dequote s

private def symbolCases : List String :=
  ["x", "y0", "_foo", "a.b", "a.b.c", "|a.b|", "a+b", "bv5", "|hello world|",
   "a.00", "a.0", "a.01", "T1_6131", "<=", "|x|", "|123|", "$x", "a..b", ".a",
   "a.", "|a b.c|", "select", "foo!bar", "|x'|", "|weird:name|", "|0bad|"]

#guard symbolCases.all roundTrips

-- Explicit checks, including the cases that used to drop leading zeros and the
-- ones that must stay quoted.
#guard formatSmtSymbol (Parser.smtSymbolToName "a.00") == "a.00"
#guard formatSmtSymbol (Parser.smtSymbolToName "a.0") == "a.0"
#guard formatSmtSymbol (Parser.smtSymbolToName "x") == "x"
#guard formatSmtSymbol (Parser.smtSymbolToName "|hello world|") == "|hello world|"
#guard formatSmtSymbol (Parser.smtSymbolToName "|123|") == "|123|"

/-! ## `formatBitVecLiteral` -/

#guard formatBitVecLiteral 5 8 == "#b00000101"
#guard formatBitVecLiteral 0 4 == "#b0000"
#guard formatBitVecLiteral 6 4 == "#b0110"

/-! ## `printModel` -/

private def bvSort (w : Nat) : Expr := .app (.const ``BitVec []) (mkNatLit w)

/-- Bitvectors print their assigned value, booleans `true`/`false`, and constants
absent from the assignment are completed with zeros (`z`) / `false` (`c`). -/
private def runModel : CommandElabM Unit := runTermElabM fun _ => do
  withLocalDeclD `x (bvSort 8) fun x =>
  withLocalDeclD `b (.const ``Bool []) fun b =>
  withLocalDeclD `z (bvSort 4) fun z =>
  withLocalDeclD `c (.const ``Bool []) fun c => do
    let eqs : Array (Expr × BVExpr.PackedBitVec) :=
      #[(x, ⟨5#8⟩), (.app (.const ``BitVec.ofBool []) b, ⟨1#1⟩)]
    printModel #[x.fvarId!, b.fvarId!, z.fvarId!, c.fvarId!] eqs

/--
info: (
  (define-fun x () (_ BitVec 8) #b00000101)
  (define-fun b () Bool true)
  (define-fun z () (_ BitVec 4) #b0000)
  (define-fun c () Bool false)
)
-/
#guard_msgs in
#eval runModel

/-- A `define-sort` alias type is unfolded to the underlying sort. -/
private def runModelAlias : CommandElabM Unit := runTermElabM fun _ => do
  withLetDecl `i32 (.sort 1) (bvSort 32) fun i32 =>
  withLocalDeclD `v i32 fun v => do
    printModel #[v.fvarId!] #[(v, ⟨7#32⟩)]

/--
info: (
  (define-fun v () (_ BitVec 32) #b00000000000000000000000000000111)
)
-/
#guard_msgs in
#eval runModelAlias

/-! ## `introsP` selects declared (not defined) symbols -/

/-- The user names of the free variables `introsP` introduces for a query. These
should be exactly the `declare-const`/`declare-fun` symbols, excluding any
`define-sort`/`define-const`/`define-fun` symbols. -/
private def declaredNames (cmds : List Sexp) : CommandElabM Unit := runTermElabM fun _ => do
  let e ← ofExcept <| (Parser.parseQuery (Parser.filterCmds cmds)).run' {}
  let mv ← mkFreshExprMVar e
  let (fvars, mv') ← mv.mvarId!.introsP
  mv'.withContext do
    logInfo m!"{(← fvars.mapM fun f => return (← f.getDecl).userName).toList}"

private def mixedQuery : List Sexp :=
sexps!{
(define-sort i8 () (_ BitVec 8))
(declare-const x i8)
(declare-const b Bool)
(define-const k i8 (_ bv7 8))
(define-fun f ((a i8)) i8 (bvadd a k))
}

/-- info: [x, b] -/
#guard_msgs in
#eval declaredNames mixedQuery
