/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Leanwuzla

variable (a b c : Bool)
variable (x y z : BitVec 32)

/-- error: Bitwuzla thinks it's right but can't trust the wuzla! -/
#guard_msgs in
example : x + y = y + x := by
  bv_bitwuzla

/-- error: Bitwuzla thinks it's right but can't trust the wuzla! -/
#guard_msgs in
example : x - 1 ≠ x := by
  bv_bitwuzla

/-- error: Bitwuzla thinks it's right but can't trust the wuzla! -/
#guard_msgs in
example : (-x) + y = y - x:= by
  bv_bitwuzla

/-- error: Bitwuzla thinks it's right but can't trust the wuzla! -/
#guard_msgs in
example : x * y = y * x := by
  bv_bitwuzla

/-- error: Bitwuzla thinks it's right but can't trust the wuzla! -/
#guard_msgs in
example : x / y ≤ x := by
  bv_bitwuzla

/-- error: Bitwuzla thinks it's right but can't trust the wuzla! -/
#guard_msgs in
example (hx : BitVec.slt 0 x) (hy : BitVec.slt 0 y) : x.msb = y.msb := by
  bv_bitwuzla

/-- error: Bitwuzla thinks it's right but can't trust the wuzla! -/
#guard_msgs in
example : (x.zeroExtend 64).msb = false := by
  bv_bitwuzla

/-- error: Bitwuzla thinks it's right but can't trust the wuzla! -/
#guard_msgs in
example (hx : BitVec.slt 0 x) : (x.signExtend 64).msb = false := by
  bv_bitwuzla

/-- error: Bitwuzla thinks it's right but can't trust the wuzla! -/
#guard_msgs in
example : x &&& y = y &&& x := by
  bv_bitwuzla

/-- error: Bitwuzla thinks it's right but can't trust the wuzla! -/
#guard_msgs in
example : x ||| y = y ||| x := by
  bv_bitwuzla

/-- error: Bitwuzla thinks it's right but can't trust the wuzla! -/
#guard_msgs in
example : ~~~(x ||| y) = (~~~y &&& ~~~x) := by
  bv_bitwuzla

/-- error: Bitwuzla thinks it's right but can't trust the wuzla! -/
#guard_msgs in
example : x <<< 32 = 0 := by
  bv_bitwuzla

/-- error: Bitwuzla thinks it's right but can't trust the wuzla! -/
#guard_msgs in
example : x >>> x = 0 := by
  bv_bitwuzla

/-- error: Bitwuzla thinks it's right but can't trust the wuzla! -/
#guard_msgs in
example : (x ++ x).extractLsb' 0 32 = x := by
  bv_bitwuzla

/-- error: Bitwuzla thinks it's right but can't trust the wuzla! -/
#guard_msgs in
example (h : a = c) : (a → b) = (!c || b) := by
  bv_bitwuzla

/-- error: Bitwuzla thinks it's right but can't trust the wuzla! -/
#guard_msgs in
example : ite a b c = ite (!a) c b := by
  bv_bitwuzla

/-- error: Bitwuzla thinks it's right but can't trust the wuzla! -/
#guard_msgs in
example {x y : BitVec 32} (h : BitVec.slt 0 x) : BitVec.sshiftRight' x y = x >>> y := by
  bv_bitwuzla
