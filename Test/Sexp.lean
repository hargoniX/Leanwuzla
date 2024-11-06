/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Leanwuzla
import Leanwuzla.Sexp

open Std.Tactic.BVDecide

def expr1 : BVLogicalExpr := .const true

/-- info: true -/
#guard_msgs in
#eval Sexp.Parser.manySexps! |>.run (Lean.Elab.Tactic.BVDecide.Frontend.toSMT expr1 {}) |>.isOk

def expr2 : BVLogicalExpr := .not (.const true)

/-- info: true -/
#guard_msgs in
#eval Sexp.Parser.manySexps! |>.run (Lean.Elab.Tactic.BVDecide.Frontend.toSMT expr2 {}) |>.isOk

def expr3 : BVLogicalExpr := .gate .and (.const true) (.const false)

/-- info: true -/
#guard_msgs in
#eval Sexp.Parser.manySexps! |>.run (Lean.Elab.Tactic.BVDecide.Frontend.toSMT expr3 {}) |>.isOk

def expr4 : BVLogicalExpr := .literal (.bin (.const 10#32) .eq (.const 11#32))

/-- info: true -/
#guard_msgs in
#eval Sexp.Parser.manySexps! |>.run (Lean.Elab.Tactic.BVDecide.Frontend.toSMT expr4 {}) |>.isOk
