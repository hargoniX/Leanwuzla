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
  sorry

example : x - 1 ≠ x := by
  bv_compare
  sorry

example : ∀ (x : BitVec 32), x.and 0#32 = 0#32 := by
  bv_compare
  sorry

example : ∀ (x x_1 : BitVec 16), BitVec.truncate 8 ((x_1.and 255#16).and x) = BitVec.truncate 8 (x_1.and x) := by
  bv_compare
  sorry

example : ∀ (x : BitVec 1), BitVec.ofBool (0#1 > x) = 0#1 := by
  bv_compare
  sorry

theorem extracted_1 (x y : BitVec 8) : x + y = x + x := by
  bv_compare
  sorry

set_option sat.timeout 1 in
example (x y : BitVec 64) : x * y = y * x := by
  bv_compare
  sorry

example (a : BitVec 32) (b : a + 4294967295#32 < 32#32) (c : 32#32 < a) : False := by
  bv_decide


set_option sat.timeout 120
example :
    a2 - a1 < b1 - a1 → a2 - a1 < b2 - a1 →
    b2 - b1 < a1 - b1 → b2 - b1 < a2 - b1 →
    b2 - b1 = 18446744073709551615#64 ∨ c2 - b1 ≤ b2 - b1 ∧ c1 - b1 ≤ c2 - b1 →
    ((a2 - a1 < c1 - a1 ∧ a2 - a1 < c2 - a1)
    ∧ c2 - c1 < a1 - c1)
    ∧ c2 - c1 < a2 - c1 := by
  bv_compare
