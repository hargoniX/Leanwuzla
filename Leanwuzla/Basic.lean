import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide

open Lean

private partial def getIntrosSize (e : Expr) : Nat :=
  go 0 e
where
  go (size : Nat) : Expr → Nat
    | .forallE _ _ b _ => go (size + 1) b
    | .mdata _ b       => go size b
    | _                => size

/--
Introduce only forall binders and preserve names.
-/
def _root_.Lean.MVarId.introsP (mvarId : MVarId) : MetaM (Array FVarId × MVarId) := do
  let type ← mvarId.getType
  let type ← instantiateMVars type
  let n := getIntrosSize type
  if n == 0 then
    return (#[], mvarId)
  else
    mvarId.introNP n

open Elab.Tactic.BVDecide.Frontend in
structure Context where
  acNf : Bool
  parseOnly : Bool
  timeout : Nat
  input : String
  maxSteps : Nat
  disableAndFlatten : Bool
  disableEmbeddedConstraintSubst : Bool
  disableKernel : Bool
  solverMode : SolverMode

abbrev SolverM := ReaderT Context MetaM

namespace SolverM

def getParseOnly : SolverM Bool := return (← read).parseOnly
def getInput : SolverM String := return (← read).input
def getKernelDisabled : SolverM Bool := return (← read).disableKernel

def getBVDecideConfig : SolverM Elab.Tactic.BVDecide.Frontend.BVDecideConfig := do
  let ctx ← read
  return {
    timeout := ctx.timeout
    acNf := ctx.acNf
    embeddedConstraintSubst := !ctx.disableEmbeddedConstraintSubst
    andFlattening := !ctx.disableAndFlatten
    maxSteps := ctx.maxSteps
    structures := false,
    fixedInt := false,
    enums := false,
    solverMode := ctx.solverMode
  }

def run (x : SolverM α) (ctx : Context) (coreContext : Core.Context) (coreState : Core.State) :
    IO α := do
  let (res, _, _) ← ReaderT.run x ctx |> (Meta.MetaM.toIO · coreContext coreState)
  return res

end SolverM
