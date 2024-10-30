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
