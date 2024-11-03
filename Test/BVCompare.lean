/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Leanwuzla

variable (a b c : Bool)
variable (x y z : BitVec 32)

example : x + y = y + x := by
  bv_compare

example : x - 1 ≠ x := by
  bv_compare

example : ∀ (x : BitVec 32), x.and 0#32 = 0#32 := by
  bv_compare

example : ∀ (x x_1 : BitVec 16), BitVec.truncate 8 ((x_1.and 255#16).and x) = BitVec.truncate 8 (x_1.and x) := by
  bv_compare

example : ∀ (x : BitVec 1), BitVec.ofBool (0#1 > x) = 0#1 := by
  bv_compare

theorem extracted_1 (x y : BitVec 8) : x + y = x + x := by
  bv_compare
  sorry
