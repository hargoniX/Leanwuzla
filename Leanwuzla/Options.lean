/-
This file registers options that can be passed with `-D <option-name>=<value>`,
which are added to the global options environment.

These options are used to configure Leanwuzla behaviour.

Authors: Siddharth Bhat
-/
import Lean
open Lean


register_option bitwuzla.ac_nf : Bool := {
  defValue := false
  descr := "Enable running 'ac_nf' before the goal"
}

register_option bitwuzla.simp_ac : Bool := {
  defValue := false
  descr := "Enable simplifying upto associativity commutativity by running a `simp` set."
}

register_option bitwuzla.admit : Bool := {
  defValue := true
  descr := "Enable admitting the goal without running `bv_decide`"
}


