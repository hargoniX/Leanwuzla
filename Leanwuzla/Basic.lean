module

public import Lean.Expr
public import Lean.Meta.Basic
public import Lean.Meta.Tactic.BVDecide.Counterexample
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
public import Std.Tactic.BVDecide.Syntax
import all Lean.Meta.Tactic.BVDecide.Counterexample


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

open Lean.Meta.Tactic.BVDecide in
/--
Report the outcome of a satisfiable query from a `bv_decide` counterexample.

If the counterexample is genuine, print `sat` (and, when `getModel` is set, the
model) and return exit code `0`. If it is *spurious* -- i.e. `bv_decide`
abstracted an unsupported subterm as an opaque variable, or did not use a
relevant hypothesis, so the assignment may not actually satisfy the problem --
report it as an error and return exit code `1`, mirroring `bvDecide`.
-/
public def reportCounterExample (fvars : Array FVarId) (getModel : Bool)
    (counterExample : CounterExample) : MetaM UInt8 := do
  let diagnosis ← DiagnosisM.run DiagnosisM.diagnose counterExample
  if diagnosis.uninterpretedSymbols.isEmpty && diagnosis.unusedRelevantHypotheses.isEmpty then
    logInfo "sat"
    if getModel then
      printModel fvars counterExample.equations
    return (0 : UInt8)
  else
    logError (← addMessageContextFull (← explainCounterExampleQuality counterExample))
    return (1 : UInt8)

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

open Meta.Tactic.BVDecide in
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

public abbrev SolverM := ReaderT Context MetaM

namespace SolverM

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

public def run (x : SolverM α) (ctx : Context) (coreContext : Core.Context) (coreState : Core.State) :
    IO α := do
  let (res, _, _) ← ReaderT.run x ctx |> (Meta.MetaM.toIO · coreContext coreState)
  return res

end SolverM
