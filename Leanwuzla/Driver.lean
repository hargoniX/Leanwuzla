import Leanwuzla.Basic
import Leanwuzla.NoKernel
import Leanwuzla.ParserLCtx

open Lean
open Solver

namespace Driver

/--
The driver lives in its own monad which is rich enough to perform IO (via
`SolverM ≤ MetaM ≤ IO`). It threads the pure parser state through successive
`parseCommand` calls and dispatches control-flow commands.
-/
abbrev DriverM := StateT Parser.State SolverM

/--
Run a pure parser action against the driver's current parser state.

The parser mints `FVarId`s for the `LocalContext` it builds, so its name
generator is seeded from `MetaM`'s before the action runs and synced back
afterwards. This maintains `MetaM`'s freshness invariant: every `FVarId`
reachable from the metavariable context is unique, and nothing `MetaM` mints
later can collide with an id the parser created.
-/
def runParser (x : ParserM α) : DriverM α := do
  let ps := { (← get) with ngen := (← getNGen) }
  match x.run ps with
  | .error e    => throwError e
  | .ok (a, ps) => set ps; setNGen ps.ngen; return a

end Driver

open Meta in
open Elab in
/--
Decide the goal `mv`, which is `False` inside the local context accumulated by
the parser. If the goal is proven, the proof of `False` is closed over the
local context (`∀`s for declarations and assertions, `let`s for definitions)
to obtain a self-contained theorem for the kernel to check. If a
counterexample is found instead, it is diagnosed and stored for a later
`(get-model)`; `consts` are the free variables of the declared constants.
-/
def decideSmt (mv : MVarId) (consts : Array FVarId) : SolverM Solver.Result := do
  trace[Meta.Tactic.bv] m!"Working on goal: {mv}"
  try
    mv.withContext $ IO.FS.withTempFile fun _ lratFile => do
      let cfg ← Solver.getBVDecideConfig
      let ctx ← (Tactic.BVDecide.TacticContext.new lratFile cfg).run' { declName? := `lrat }
      match ← Tactic.BVDecide.bvDecide' mv ctx with
      | .error counterExample =>
        Solver.reportSat consts counterExample
      | .ok _ =>
        let lctx ← getLCtx
        let fvars := lctx.getFVars
        let type := lctx.mkForall fvars (.const ``False []) (usedLetOnly := false)
        let value := lctx.mkLambda fvars (← instantiateMVars (.mvar mv)) (usedLetOnly := false)
        Lean.addDecl (.thmDecl { name := ← Lean.mkAuxDeclName, levelParams := [], type, value })
        logInfo "unsat"
        return .unsat
  catch e =>
    -- TODO: improve handling of sat cases. This is a temporary workaround.
    let message ← e.toMessageData.toString
    if message.startsWith "None of the hypotheses are in the supported BitVec fragment" then
      -- We fully support SMT-LIB v2.6. Getting the above error message means the
      -- goal was reduced to `False` with only `True` as an assumption. Every
      -- declared constant is then unconstrained, so the model completed entirely
      -- with default values is a valid one.
      logInfo "sat"
      Solver.setModel { fvars := consts, counterExample := { goal := mv, unusedHypotheses := {}, equations := #[] } }
      return .sat
    else
      logError m!"Error: {e.toMessageData}"
      return .error

/--
Type-check the goal expression (used in `--parseOnly` mode). On success we
report `.unsat` so the driver's mode tracker has a consistent transition to
work with; on failure we report `.error`.
-/
def typeCheck (e : Expr) : SolverM Solver.Result := do
  try
    let defn := .defnDecl {
      name := ← Lean.mkAuxDeclName
      levelParams := []
      type := .sort .zero
      value := e
      hints := .regular 0
      safety := .safe
    }
    Lean.addDecl defn
    return .unsat
  catch e =>
    logError m!"Error: {e.toMessageData}"
    return .error

namespace Driver

/--
Run the appropriate backend on the goal accumulated in the parser's
`LocalContext` and report a `Solver.Result`.

The parser's `LocalContext` is installed in `MetaM` directly — the goal is
just `False` inside it — instead of folding the context into a `∀`/`let`
telescope and re-introducing the binders on the other side. The context
contains no type-class instances (only `Bool`/`BitVec` constants, sort
aliases, definitions, and assertion hypotheses), so the set of local
instances is empty.
-/
def solveGoal : DriverM Solver.Result := do
  if ← Solver.getParseOnly then
    let type ← runParser Parser.getGoalType
    logInfo m!"Goal:\n{type}"
    typeCheck type
  else
    let ps ← get
    Meta.withLCtx ps.lctx #[] do
      let mv ← Meta.mkFreshExprMVar (Expr.const ``False [])
      if ← Solver.getKernelDisabled then
        decideSmtNoKernel mv.mvarId! ps.consts
      else
        decideSmt mv.mvarId! ps.consts

/--
Top-level driver loop: read the SMT-LIB file into the parser, then repeatedly
ask the parser for the next command. The parser owns both s-expression and
command parsing; the driver only reacts to `set-logic`, `check-sat`,
`get-model`, `get-unsat-core`, `exit`, and end-of-input. Returns the process
exit code.
-/
partial def run : DriverM UInt8 := do
  let path ← Solver.getInput
  let query ← IO.FS.readFile path
  runParser (Parser.setInput query)
  loop
where
  loop : DriverM UInt8 := do
    match ← runParser Parser.nextCommand with
    | none => return 0
    | some .noop => loop
    | some .declOrAssert =>
      if (← Solver.getMode) == .start then
        throwError "Error: expected (set-logic …) before declaration/assertion commands"
      Solver.setMode .assert
      loop
    | some (.setLogic logic) =>
      if (← Solver.getMode) != .start then
        throwError "Error: expected (set-logic …) before declaration/assertion commands"
      if logic != "QF_BV" then
        throwError m!"Error: unsupported logic {logic}"
      Solver.setMode .assert
      loop
    | some .checkSat =>
      let r ← solveGoal
      if r == .error then return 1
      if r == .sat then Solver.setMode .sat
      if r == .unsat then Solver.setMode .unsat
      loop
    | some .getUnsatCore =>
      let uc ← Solver.getUnsatCore
      logInfo ("(" ++ " ".intercalate (uc.toList.map formatSmtSymbol) ++ ")")
      loop
    | some .getModel =>
      let model ← Solver.getModel
      model.counterExample.goal.withContext do
        printModel model.fvars model.counterExample.equations
      loop
    | some .exit => return 0

end Driver

/--
Entry point used from `Main.lean`. Runs the driver and discards the final
parser state. Returns the process exit code.
-/
def Driver.runSmt2File : SolverM UInt8 :=
  Driver.run.run' {}
