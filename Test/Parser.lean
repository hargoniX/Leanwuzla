/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/
import Lean
import Leanwuzla.Parser

open Lean Elab Command

def parseSexps (cmds : List Sexp) : MetaM Expr := do
  let query := Parser.filterCmds cmds
  ofExcept <| (Parser.parseQuery query).run' {}

def elabSexps (cmds : List Sexp) : CommandElabM Unit := do
  runTermElabM fun _ => do
  let e ← parseSexps cmds
  logInfo m!"{e}"

def query1 : List Sexp :=
sexps!{
(define-sort i32 () (_ BitVec 32))
(define-sort i64 () (_ BitVec 64))
(declare-fun f (i32 i64) Bool)
}

/--
info: let i32 := BitVec 32;
let i64 := BitVec 64;
∀ (f : i32 → i64 → Bool), (!true) = true
-/
#guard_msgs in
#eval elabSexps query1
