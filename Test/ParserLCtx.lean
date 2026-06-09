/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/
import Lean
import Leanwuzla.ParserLCtx

open Lean Meta Elab Command

/--
Run the streaming parser over `cmds` and return the final parser state. The
parser's name generator is seeded from `MetaM`'s (and synced back) so the
`FVarId`s in the generated `LocalContext` are globally fresh and the context
can be installed in `MetaM` directly.
-/
def runParserCmds (cmds : List Sexp) : MetaM Parser.State := do
  let go : ParserM Unit := do
    for s in cmds do
      discard <| Parser.parseCommand s
  match go.run { ngen := ← getNGen } with
  | .error e => throwError e
  | .ok (_, ps) => setNGen ps.ngen; return ps

def parseSexps (cmds : List Sexp) : MetaM Expr := do
  let ps ← runParserCmds cmds
  ofExcept <| Parser.getGoalType.run' ps

def elabSexps (cmds : List Sexp) : CommandElabM Unit := do
  runTermElabM fun _ => do
  let e ← parseSexps cmds
  logInfo m!"{e}"

/--
Install the parser's `LocalContext` in `MetaM` and check that it satisfies
`MetaM`'s invariants: every declaration's type (and value, for `let`-bound
declarations) type-checks inside the context, and the goal type it denotes
type-checks in the empty context.
-/
def checkSexps (cmds : List Sexp) : CommandElabM Unit := do
  runTermElabM fun _ => do
  let ps ← runParserCmds cmds
  withLCtx ps.lctx #[] do
    for decl in ps.lctx do
      check decl.type
      if let some v := decl.value? then
        check v
  check (← ofExcept <| Parser.getGoalType.run' ps)
  logInfo "ok"

def query1 : List Sexp :=
sexps!{
(define-sort i32 () (_ BitVec 32))
(define-sort i64 () (_ BitVec 64))
(declare-fun f (i32 i64) Bool)
}

/--
info: let i32 := BitVec 32;
let i64 := BitVec 64;
∀ (f : i32 → i64 → Bool), False
-/
#guard_msgs in
#eval elabSexps query1

/-- info: ok -/
#guard_msgs in
#eval checkSexps query1

def query2 : List Sexp :=
sexps!{
(define-sort i8 () (_ BitVec 8))
(declare-const x i8)
(declare-const b Bool)
(define-const k i8 (_ bv7 8))
(define-fun f ((a i8)) i8 (bvadd a k))
(assert (= (f x) (_ bv9 8)))
(assert (! b :named bIsTrue))
}

/--
info: let i8 := BitVec 8;
∀ (x : i8) (b : Bool),
  let k := 7#8;
  let f := fun a => a + k;
  (f x == 9#8) = true → b = true → False
-/
#guard_msgs in
#eval elabSexps query2

/-- info: ok -/
#guard_msgs in
#eval checkSexps query2
