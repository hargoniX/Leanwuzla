module

public import Lean.Expr
public import Lean.Meta.Basic
public import Lean.Meta.Tactic.BVDecide.Counterexample
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public import Std.Tactic.BVDecide.Syntax
import all Lean.Meta.Tactic.BVDecide.Counterexample
import Lean.Meta.ReduceEval


open Lean
open Std.Tactic.BVDecide

/--
Render a `width`-bit bitvector with the given numeric `value` as an SMT-LIB
binary literal (e.g. `#b00000001`).
-/
public def formatBitVecLiteral (value : Nat) (width : Nat) : String := Id.run do
  let mut s := "#b"
  for i in [0:width] do
    let bit := (value >>> (width - 1 - i)) &&& 1
    s := s.push (if bit == 1 then '1' else '0')
  return s

/--
Render a Lean `Name` as an SMT-LIB symbol, quoting it with `|...|` if it is not
a valid simple symbol.
-/
public def formatSmtSymbol (n : Name) : String :=
  -- `smtSymbolToName` builds every symbol as a single-component name holding the
  -- exact string, so we read it back directly rather than relying on
  -- `Name.toString`'s escaping/pseudo-syntax handling.
  let s := match n with
    | .mkSimple s => s
    | _           => n.toString (escape := false)
  let isSimpleChar c := Char.isAlphanum c || "~!@$%^&*_-+=<>.?/".contains c
  let needsQuote :=
    match s.toList with
    | [] => true
    | c :: cs => c.isDigit || !(c :: cs).all isSimpleChar
  if needsQuote then "|" ++ s ++ "|" else s

/--
Unfold a chain of `let`-bound sort aliases (introduced by `define-sort`) to the
underlying sort.
-/
private partial def resolveSortAlias (e : Expr) : MetaM Expr := do
  match e with
  | .fvar fvarId =>
    match ← fvarId.getDecl with
    | .ldecl (value := v) .. => resolveSortAlias v
    | _ => return e
  | _ => return e

/--
Print a model for a satisfiable query following SMT-LIB `get-model` semantics.

`fvars` are the free variables corresponding to the SMT-LIB declared constants
(in declaration order) and `equations` is the (possibly partial) assignment
found by `bv_decide`. Booleans are reflected as one-bit bitvectors, so a boolean
constant `b` shows up in `equations` as `BitVec.ofBool b`. Since `bv_decide`'s
counterexample is not guaranteed to assign every declared constant, any constant
missing from `equations` is completed with all-zeros for bitvectors and `false`
for booleans.

Must be run in a context in which `fvars` are valid (e.g. inside the goal's
`withContext`).
-/
public def printModel (fvars : Array FVarId) (equations : Array (Expr × BVExpr.PackedBitVec)) :
    MetaM Unit := do
  -- Index the values found by `bv_decide` by the free variable they assign.
  -- Bitvector constants appear directly as free variables, whereas boolean
  -- constants `b` appear wrapped as `BitVec.ofBool b` with a one-bit value.
  let mut values : Std.HashMap FVarId Nat := {}
  for (e, pv) in equations do
    if e.isFVar then
      values := values.insert e.fvarId! pv.bv.toNat
    else if let .app (.const ``BitVec.ofBool []) x := e then
      if x.isFVar then
        values := values.insert x.fvarId! pv.bv.toNat
  let mut lines : Array String := #[]
  for fvar in fvars do
    let decl ← fvar.getDecl
    let sym := formatSmtSymbol decl.userName
    -- A declared constant may have a `define-sort` alias as its type, in which
    -- case it is a `let`-bound free variable that we unfold to its definition.
    match ← resolveSortAlias decl.type with
    | .const ``Bool [] =>
      -- A missing assignment is completed with `false`.
      let value := values.getD fvar 0 == 1
      lines := lines.push s!"  (define-fun {sym} () Bool {value})"
    | .app (.const ``BitVec []) we =>
      let some w := we.nat? | continue
      let value := values.getD fvar 0
      lines := lines.push
        s!"  (define-fun {sym} () (_ BitVec {w}) {formatBitVecLiteral value w})"
    | _ =>
      -- Skip declarations outside the supported QF_BV fragment (e.g. functions
      -- with arguments), which cannot appear in a counterexample anyway.
      continue
  let model :=
    if lines.isEmpty then "(\n)"
    else "(\n" ++ String.intercalate "\n" lines.toList ++ "\n)"
  logInfo model

/--
Count the leading `let` binders (introduced by `define-sort`) followed by the
`forall` binders (introduced by `declare-fun`/`declare-const`) of `e`. Traversal
stops at the first `let` following the foralls, which corresponds to the
`define-fun`/`define-const` bindings of the body. Returns the number of leading
`let`s and the number of following `forall`s, respectively.
-/
private partial def getIntrosSize (e : Expr) : Nat × Nat :=
  goLets 0 e
where
  goLets (lets : Nat) : Expr → Nat × Nat
    | .letE _ _ _ b _ => goLets (lets + 1) b
    | .mdata _ b      => goLets lets b
    | e               => (lets, goForalls 0 e)
  goForalls (foralls : Nat) : Expr → Nat
    | .forallE _ _ b _ => goForalls (foralls + 1) b
    | .mdata _ b       => goForalls foralls b
    | _                => foralls

/--
Introduce the leading `define-sort` `let` binders together with the
`declare-fun`/`declare-const` `forall` binders, preserving names. Returns the
free variables corresponding to the declared symbols, i.e. those coming from the
`forall` binders only (the introduced sort definitions are excluded).
-/
public def _root_.Lean.MVarId.introsP (mvarId : MVarId) : MetaM (Array FVarId × MVarId) := do
  let type ← mvarId.getType
  let type ← instantiateMVars type
  let (numLets, numForalls) := getIntrosSize type
  if numLets + numForalls == 0 then
    return (#[], mvarId)
  else
    let (fvars, mvarId) ← mvarId.introNP (numLets + numForalls)
    -- Drop the leading sort definitions; keep only the declared symbols.
    return (fvars.extract numLets fvars.size, mvarId)

namespace Solver

open Lean.Meta.Tactic.BVDecide

/--
Result of a single solver invocation. The driver uses this to transition its
SMT-LIB mode (`Assert → Sat | Unsat`); `error` aborts the driver loop.
-/
public inductive Result where
  | sat
  | unsat
  | error
deriving DecidableEq, Inhabited, Repr

/--
Value of an expression in a model. We only support Booleans and bitvectors, so this is a simple sum type.
-/
public inductive Value where
  | bool (b : Bool)
  | bitvec (n : Nat) (v : BitVec n)
deriving DecidableEq, Inhabited, Repr

/--
SMT-LIB solver mode, per the state machine in the SMT-LIB v2.7 reference.
Transitions in this driver:
* `start → assert` on `(set-logic …)`
* `assert → sat | unsat` on `(check-sat)` (based on `Result`)
* `sat | unsat` stay put on further queries (e.g. `(get-unsat-core)`)
-/
public inductive Mode where
  | start
  | assert
  | sat
  | unsat
deriving DecidableEq, Inhabited, Repr

/--
Everything needed to answer `(get-model)` later: the (possibly partial)
counterexample found by `bv_decide` together with the free variables of the
declared constants (in declaration order), valid in the counterexample goal's
local context.
-/
public structure Model where
  /-- Free variables of the `declare-const`/`declare-fun` symbols. -/
  fvars : Array FVarId
  /-- `bv_decide`'s counterexample. `counterExample.goal` provides the local
      context in which `fvars` and `counterExample.equations` make sense. -/
  counterExample : CounterExample

/--
  `SolverM` monad state.
-/
public structure State where
  mode : Mode := .start
  /-- Unsatisfiable core, if known. -/
  unsatCore : Option (Array Name) := none
  /-- Counterexample model, if known. -/
  model : Option Model := none

public structure Context where
  acNf : Bool
  parseOnly : Bool
  timeout : Nat
  input : String
  maxSteps : Nat
  disableAndFlatten : Bool
  disableEmbeddedConstraintSubst : Bool
  disableKernel : Bool
  solverMode : Elab.Tactic.BVDecide.SolverMode

public abbrev SolverM := ReaderT Context $ StateRefT State MetaM

public def getParseOnly : SolverM Bool := return (← read).parseOnly
public def getInput : SolverM String := return (← read).input
public def getKernelDisabled : SolverM Bool := return (← read).disableKernel

public def getBVDecideConfig : SolverM Elab.Tactic.BVDecide.BVDecideConfig := do
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

public def getMode : SolverM Mode := return (← get).mode

public def setMode (mode : Mode) : SolverM Unit :=
  modify fun state => { state with mode := mode }

public def setModel (model : Model) : SolverM Unit :=
  modify fun state => { state with model := some model }

public def setModeUnsat (unsatCore : Array Name) : SolverM Unit := do
  set { mode := .unsat, unsatCore := .some unsatCore, model := .none : State }

public def getUnsatCore : SolverM (Array Name) := do
  let state ← get
  let .unsat := state.mode | throwError m!"Error: (get-unsat-core) requires unsat mode (current: {repr state.mode})"
  let .some uc := state.unsatCore | throwError "Error: unsat core not available"
  return uc

public def getModel : SolverM Model := do
  let state ← get
  let .sat := state.mode | throwError m!"Error: (get-model) requires sat mode (current: {repr state.mode})"
  let .some model := state.model | throwError "Error: model not available"
  return model

public def getValue (e : Expr) : SolverM Value := do
  let model ← getModel
  let (fvs, vs) := model.counterExample.equations.unzip
  let ev := e.replaceFVars fvs (vs.map (toExpr ·.bv))
  let t ← Meta.inferType e
  match t with
  | .const ``Bool _ => return .bool (← Meta.reduceEval ev)
  | .app (.const ``BitVec _) n =>
    let n ← Meta.reduceEval n
    return .bitvec n (← Meta.reduceEval ev)
  | _ => throwError m!"Error: value {e} has unsupported type {t}"

public def getValues (es : List Expr) : SolverM (List Value) := do
  es.mapM getValue

/--
Report the outcome of a satisfiable query from a `bv_decide` counterexample.

If the counterexample is genuine, print `sat`, store the model in the solver
state — so a later `(get-model)` can print it — and report `Result.sat`. If it
is *spurious* — i.e. `bv_decide` abstracted an unsupported subterm as an opaque
variable, or did not use a relevant hypothesis, so the assignment may not
actually satisfy the problem — report it as an error, mirroring `bvDecide`.

`fvars` are the free variables of the declared constants (in declaration
order), used to answer a later `(get-model)`.
-/
public def reportSat (fvars : Array FVarId) (counterExample : CounterExample) :
    SolverM Result := do
  let diagnosis ← DiagnosisM.run DiagnosisM.diagnose counterExample
  if diagnosis.uninterpretedSymbols.isEmpty && diagnosis.unusedRelevantHypotheses.isEmpty then
    logInfo "sat"
    setModel { fvars, counterExample }
    return .sat
  else
    logError (← addMessageContextFull (← explainCounterExampleQuality counterExample))
    return .error

namespace SolverM

public def run (x : SolverM α) (ctx : Context) (coreContext : Core.Context) (coreState : Core.State) :
    IO α := do
  let y : MetaM α := ReaderT.run x ctx |>.run' {}
  let (res, _, _) ← y |> (Meta.MetaM.toIO · coreContext coreState)
  return res

end SolverM

end Solver
