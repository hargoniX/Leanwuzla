import Leanwuzla.Auxiliary
import Leanwuzla.Sexp

open Lean

structure Parser.State where
  /-- Current de Bruijn level for bound variables introduced by function/sort
      parameters and term-level `let` expressions. Top-level declarations and
      assertions do not bump this level — they live in `lctx`. -/
  level : Nat := 0
  /-- Name generator used to mint fresh `FVarId`s for top-level declarations
      and assertions. `MetaM` maintains the invariant that every `FVarId` in
      scope descends from its name generator, so callers that intend to use
      the generated `lctx` inside `MetaM` must seed this from `MetaM`'s name
      generator before parsing and write it back afterwards (see
      `Driver.runParser`). -/
  ngen : NameGenerator := {}
  /-- A mapping from SMT-LIB symbol names to (canonical type, de Bruijn level)
      for **bound** variables only — function and sort parameters and
      term-level `let`-bindings. The corresponding de Bruijn index at a use
      site is `state.level - level - 1`. Free variables are not stored here;
      they are resolved via `fvars` and `lctx`. -/
  bvars : Std.HashMap Name (Expr × Nat) := {}
  /-- A mapping from SMT-LIB symbol names introduced by top-level declarations
      and definitions to (canonical type, `FVarId`). The canonical type is
      used for type-class resolution; the user-facing type (the one that
      should appear in the goal) is stored as the corresponding decl's type
      in `lctx`, along with any value, binder info, etc. -/
  fvars : Std.HashMap Name (Expr × FVarId) := {}
  /-- A mapping from user-defined types (i.e., aliases) to their corresponding
      canonical types. We need this mapping to provide correct type-class
      instances for user-defined types. -/
  uvars : Std.HashMap Name Expr := {}
  /-- The local context accumulated for top-level declarations and assertions
      in source order. Folded by `getGoalType` via `LocalContext.mkForall` to
      produce the final goal. -/
  lctx : LocalContext := {}
  /-- `FVarId`s of top-level `declare-const`/`declare-fun` symbols in
      declaration order. `(get-model)` prints a `define-fun` for exactly
      these. -/
  consts : Array FVarId := #[]
  /-- Remaining input. Initialised by the driver from the SMT-LIB file
      contents; the parser advances it one s-expression at a time. -/
  input : Sigma String.Pos := ⟨"", "".startPos⟩

abbrev ParserM := StateT Parser.State (Except MessageData)

namespace Parser

/-- Install `input` as the source from which subsequent commands are parsed. -/
def setInput (input : String) : ParserM Unit :=
  modify fun s => { s with input := ⟨input, input.startPos⟩ }

/-- Run a Parsec parser against the stored input position, advancing the
    position on success and throwing on failure. -/
private def runParsec (p : Std.Internal.Parsec.String.Parser α) : ParserM α := do
  let state ← get
  match p state.input with
  | .success pos a =>
    set { state with input := pos }
    return a
  | .error _ err =>
    throw m!"Error: parse error: {err}"

/-- Generate a fresh `FVarId` from the state's `NameGenerator`. As long as the
    generator was seeded from `MetaM`'s (and is synced back), the id is
    globally fresh: it can collide neither with existing `FVarId`s nor with
    ones `MetaM` mints later. -/
private def mkFreshFVarId : ParserM FVarId := do
  let state ← get
  set { state with ngen := state.ngen.next }
  return ⟨state.ngen.curr⟩

/--
Push a `cdecl` (forall-style binder) onto `lctx`. If `canonicalType?` is
`some ct`, the symbol is registered in `fvars` (paired with `ct`) so that
subsequent references can resolve it and type-class lookups use `ct`; if
`none` — as for assertions — the symbol is not name-resolvable but its decl
still contributes to the goal.
-/
private def pushCDecl
    (userName : Name) (userType : Expr) (canonicalType? : Option Expr := none)
    (bi : BinderInfo := .default) : ParserM FVarId := do
  let fvarId ← mkFreshFVarId
  modify fun s => { s with
    lctx := s.lctx.mkLocalDecl fvarId userName userType bi
    fvars := match canonicalType? with
      | some ct => s.fvars.insert userName (ct, fvarId)
      | none    => s.fvars }
  return fvarId

/--
Push an `ldecl` (let-style binder) onto `lctx` and register its name in
`fvars` with the supplied canonical type.
-/
private def pushLDecl
    (userName : Name) (userType : Expr) (canonicalType : Expr)
    (value : Expr) (nonDep : Bool) : ParserM FVarId := do
  let fvarId ← mkFreshFVarId
  modify fun s => { s with
    lctx := s.lctx.mkLetDecl fvarId userName userType value nonDep
    fvars := s.fvars.insert userName (canonicalType, fvarId) }
  return fvarId

private def mkBool : Expr :=
  .const ``Bool []

private def mkBitVec (w : Nat) : Expr :=
  .app (.const ``BitVec []) (mkNatLit w)

private def getBitVecWidth (α : Expr) : ParserM Nat := do
  match α with
  | .app (.const ``BitVec []) w => return w.nat?.get!
  | _ => throw m!"Error: expected BitVec type, got {α}"

private def mkInstBEqBool : Expr :=
  mkApp2 (.const ``instBEqOfDecidableEq [0]) mkBool
         (.const ``instDecidableEqBool [])

private def mkInstBEqBitVec (w : Nat) : Expr :=
  mkApp2 (.const ``instBEqOfDecidableEq [0]) (mkBitVec w)
         (.app (.const ``instDecidableEqBitVec []) (mkNatLit w))

private def mkBitVecAppend (w v : Nat) : Expr :=
  mkApp4 (.const ``HAppend.hAppend [0, 0, 0])
         (mkBitVec w) (mkBitVec v) (mkBitVec (w + v))
         (mkApp2 (.const ``BitVec.instHAppendHAddNat []) (mkNatLit w) (mkNatLit v))

private def mkBitVecAnd (w : Nat) : Expr :=
  mkApp4 (.const ``HAnd.hAnd [0, 0, 0])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``instHAndOfAndOp [0]) (mkBitVec w)
                 (.app (.const ``BitVec.instAndOp []) (mkNatLit w)))

private def mkBitVecOr (w : Nat) : Expr :=
  mkApp4 (.const ``HOr.hOr [0, 0, 0])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``instHOrOfOrOp [0]) (mkBitVec w)
                 (.app (.const ``BitVec.instOrOp []) (mkNatLit w)))

private def mkBitVecXor (w : Nat) : Expr :=
  mkApp4 (.const ``HXor.hXor [0, 0, 0])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``instHXorOfXorOp [0]) (mkBitVec w)
                 (.app (.const ``BitVec.instXorOp []) (mkNatLit w)))

private def mkBitVecNot (w : Nat) : Expr :=
  mkApp2 (.const ``Complement.complement [0])
         (mkBitVec w)
         (.app (.const ``BitVec.instComplement []) (mkNatLit w))

private def mkBitVecNeg (w : Nat) : Expr :=
  mkApp2 (.const ``Neg.neg [0])
         (mkBitVec w)
         (.app (.const ``BitVec.instNeg []) (mkNatLit w))

private def mkBitVecAdd (w : Nat) : Expr :=
  mkApp4 (.const ``HAdd.hAdd [0, 0, 0])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``instHAdd [0]) (mkBitVec w)
                 (.app (.const ``BitVec.instAdd []) (mkNatLit w)))

private def mkBitVecSub (w : Nat) : Expr :=
  mkApp4 (.const ``HSub.hSub [0, 0, 0])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``instHSub [0]) (mkBitVec w)
                 (.app (.const ``BitVec.instSub []) (mkNatLit w)))

private def mkBitVecMul (w : Nat) : Expr :=
  mkApp4 (.const ``HMul.hMul [0, 0, 0])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``instHMul [0]) (mkBitVec w)
                 (.app (.const ``BitVec.instMul []) (mkNatLit w)))

private def mkBitVecMod (w : Nat) : Expr :=
  mkApp4 (.const ``HMod.hMod [0, 0, 0])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``instHMod [0]) (mkBitVec w)
                 (.app (.const ``BitVec.instMod []) (mkNatLit w)))

private def mkBitVecShiftLeft (w : Nat) : Expr :=
  mkApp4 (.const ``HShiftLeft.hShiftLeft [0, 0, 0])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``BitVec.instHShiftLeft []) (mkNatLit w) (mkNatLit w))

private def mkBitVecShiftRight (w : Nat) : Expr :=
  mkApp4 (.const ``HShiftRight.hShiftRight [0, 0, 0])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``BitVec.instHShiftRight []) (mkNatLit w) (mkNatLit w))

def smtSymbolToName (s : String) : Name :=
  let s := if s.startsWith "|" && s.endsWith "|" then String.Pos.Raw.extract s (s.rawStartPos + '|') (s.rawEndPos - '|') else s
  -- SMT-LIB symbols are flat (non-hierarchical) strings, so we always build a
  -- single-component name rather than splitting on `.`. This keeps the exact
  -- symbol intact -- so it can be printed back faithfully (e.g. in models, see
  -- `formatSmtSymbol`) -- and avoids conflating distinct symbols that only
  -- differ in a way `String.toName` normalizes away, such as `a.0` and `a.00`.
  Name.mkSimple s

/-- Parse a numeral atom (e.g. a bitvector width or the index of an indexed
    operator). Throws instead of panicking on malformed input — in compiled
    code a panic does not abort, so `toNat!` would silently continue with `0`. -/
private def parseNumeral (s : Sexp) : ParserM Nat := do
  let .atom n := s | throw m!"Error: expected a numeral, got {s}"
  let some v := n.toNat? | throw m!"Error: expected a numeral, got {s}"
  return v

/-- Returns two types: the first is the canonical type (used for type-class
    resolution) and the second is the user-provided one (which appears in the
    goal). They differ when user-defined sort aliases are involved. -/
def parseSort (s  : Sexp) : ParserM (Expr × Expr) := do
  match s with
  | sexp!{Bool} =>
    return (mkBool, mkBool)
  | sexp!{(_ BitVec {w})} =>
    let w ← parseNumeral w
    return (mkBitVec w, mkBitVec w)
  | sexp!{({sc} ⦃as⦄)} =>
    let (bsc, sc) ← parseSort sc
    let as ← as.mapM parseSort
    let (bas, as) := as.unzip
    -- The canonical head of a parameterized sort alias is a lambda, so the
    -- application is a beta redex; reduce it so that e.g. `getBitVecWidth`
    -- sees the underlying sort.
    return ((mkAppN bsc bas.toArray).headBeta, mkAppN sc as.toArray)
  | .atom n =>
    let n := smtSymbolToName n
    let state ← get
    -- A bare sort atom must resolve to something of canonical type `Sort 1`.
    -- Bound vars get a `.bvar`; free vars (top-level `define-sort` aliases)
    -- get a `.fvar` so the alias is preserved in the goal.
    let ut : Expr ←
      if let some (t, i) := state.bvars[n]? then do
        unless t == .sort 1 do throw m!"Error: unexpected sort {s}"
        pure (.bvar (state.level - i - 1))
      else if let some (t, fvarId) := state.fvars[n]? then do
        unless t == .sort 1 do throw m!"Error: unexpected sort {s}"
        pure (.fvar fvarId)
      else
        throw m!"Error: unexpected sort {s}"
    let ct := match state.uvars[n]? with
      | some ct => ct
      | none    => ut
    return (ct, ut)
  | _ => throw m!"Error: unsupported sort {s}"

partial def parseTerm (s : Sexp) : ParserM (Expr × Expr) := do
  try
    go s
  catch e =>
    -- `e` already starts with `Error:`; just extend the term trace.
    throw m!"{e}\nfailed to parse term {s}"
where
  go (e : Sexp) : ParserM (Expr × Expr) := do
    if let sexp!{(let (⦃_⦄) {_})} := e then
      -- SMT-LIB supports nesting of parallel let expressions. Both can be
      -- very long. So, we use tail-call recursion to avoid stack overflows.
      let state ← get
      let (bindings, b) := getNestedLetBindingsAndBody [] e
      let bindings ← parseNestedBindings bindings
      let (tb, b) ← parseTerm b
      set state
      let e := bindings.foldr (fun (n, t, v) b => .letE n t v b true) b
      return (tb, e)
    if let sexp!{true} := e then
      return (mkBool, .const ``true [])
    if let sexp!{false} := e then
      return (mkBool, .const ``false [])
    if let sexp!{(not {p})} := e then
      let (_, p) ← parseTerm p
      return (mkBool, .app (.const ``not []) p)
    if let sexp!{(=> ⦃ps⦄)} := e then
      if ps.isEmpty then
        throw m!"Error: expected at least two arguments for `=>`"
      let ps ← ps.mapM (fun p => return (← parseTerm p).snd)
      let p := ps.dropLast.foldr (mkApp2 (.const ``implies [])) ps.getLast!
      return (mkBool, p)
    if let sexp!{(and ⦃ps⦄)} := e then
      return ← leftAssocOpBool (.const ``and []) ps
    if let sexp!{(or ⦃ps⦄)} := e then
      return ← leftAssocOpBool (.const ``or []) ps
    if let sexp!{(xor ⦃ps⦄)} := e then
      return ← leftAssocOpBool (.const ``xor []) ps
    if let sexp!{(= ⦃xs⦄)} := e then
      return ← chainableEq xs
    if let sexp!{(distinct ⦃xs⦄)} := e then
      return ← pairwiseDistinct xs
    if let sexp!{(ite {c} {t} {e})} := e then
      let (_, c) ← parseTerm c
      let (α, t) ← parseTerm t
      let (_, e) ← parseTerm e
      return (α, mkApp4 (mkConst ``cond [1]) α c t e)
    if let sexp!{(concat ⦃xs⦄)} := e then
      if xs.isEmpty then
        throw m!"Error: expected at least one argument for `concat`"
      let (α, acc) ← parseTerm xs.head!
      let w ← getBitVecWidth α
      let f := fun (w, acc) x => do
        let (β, x) ← parseTerm x
        let v ← getBitVecWidth β
        return (w + v, mkApp2 (mkBitVecAppend w v) acc x)
      let (w, acc) ← xs.tail.foldlM f (w, acc)
      return (mkBitVec w, acc)
    if let sexp!{(bvand ⦃xs⦄)} := e then
      return ← leftAssocOpBitVec mkBitVecAnd xs
    if let sexp!{(bvor ⦃xs⦄)} := e then
      return ← leftAssocOpBitVec mkBitVecOr xs
    if let sexp!{(bvxor ⦃xs⦄)} := e then
      return ← leftAssocOpBitVec mkBitVecXor xs
    if let sexp!{(bvnot {x})} := e then
      let (α, x) ← parseTerm x
      let w ← getBitVecWidth α
      return (α, .app (mkBitVecNot w) x)
    if let sexp!{(bvnand {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.nand []) (mkNatLit w) x y)
    if let sexp!{(bvnor {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.nor []) (mkNatLit w) x y)
    if let sexp!{(bvxnor {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.xnor []) (mkNatLit w) x y)
    if let sexp!{(bvcomp {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (mkBitVec 1, mkApp3 (.const ``BitVec.compare []) (mkNatLit w) x y)
    if let sexp!{(bvmul ⦃xs⦄)} := e then
      return ← leftAssocOpBitVec mkBitVecMul xs
    if let sexp!{(bvadd ⦃xs⦄)} := e then
      return ← leftAssocOpBitVec mkBitVecAdd xs
    if let sexp!{(bvsub ⦃xs⦄)} := e then
      return ← leftAssocOpBitVec mkBitVecSub xs
    if let sexp!{(bvneg {x})} := e then
      let (α, x) ← parseTerm x
      let w ← getBitVecWidth α
      return (α, .app (mkBitVecNeg w) x)
    if let sexp!{(bvudiv {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.smtUDiv []) (mkNatLit w) x y)
    if let sexp!{(bvurem {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (α, mkApp2 (mkBitVecMod w) x y)
    if let sexp!{(bvsdiv {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.smtSDiv []) (mkNatLit w) x y)
    if let sexp!{(bvsrem {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.srem []) (mkNatLit w) x y)
    if let sexp!{(bvsmod {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.smod []) (mkNatLit w) x y)
    if let sexp!{(bvshl {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (α, mkApp2 (mkBitVecShiftLeft w) x y)
    if let sexp!{(bvlshr {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (α, mkApp2 (mkBitVecShiftRight w) x y)
    if let sexp!{(bvashr {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (α, mkApp4 (.const ``BitVec.sshiftRight' []) (mkNatLit w) (mkNatLit w) x y)
    if let sexp!{(bvult {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.ult []) (mkNatLit w) x y)
    if let sexp!{(bvule {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.ule []) (mkNatLit w) x y)
    if let sexp!{(bvugt {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.ugt []) (mkNatLit w) x y)
    if let sexp!{(bvuge {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.uge []) (mkNatLit w) x y)
    if let sexp!{(bvslt {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.slt []) (mkNatLit w) x y)
    if let sexp!{(bvsle {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.sle []) (mkNatLit w) x y)
    if let sexp!{(bvsgt {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.sgt []) (mkNatLit w) x y)
    if let sexp!{(bvsge {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.sge []) (mkNatLit w) x y)
    if let sexp!{((_ extract {i} {j}) {x})} := e then
      let i ← parseNumeral i
      let j ← parseNumeral j
      let (α, x) ← parseTerm x
      let w ← getBitVecWidth α
      let start := j
      let len := i - j + 1
      return (mkBitVec (i - j + 1), mkApp4 (.const ``BitVec.extractLsb' []) (mkNatLit w) (mkNatLit start) (mkNatLit len) x)
    if let sexp!{((_ repeat {i}) {x})} := e then
      let i ← parseNumeral i
      let (α, x) ← parseTerm x
      let w ← getBitVecWidth α
      return (mkBitVec (w * i), mkApp3 (.const ``BitVec.replicate []) (mkNatLit w) (mkNatLit i) x)
    if let sexp!{((_ zero_extend {i}) {x})} := e then
      let i ← parseNumeral i
      let (α, x) ← parseTerm x
      let w ← getBitVecWidth α
      return (mkBitVec (w + i), mkApp3 (.const ``BitVec.setWidth []) (mkNatLit w) (mkNatLit (w + i)) x)
    if let sexp!{((_ sign_extend {i}) {x})} := e then
      let i ← parseNumeral i
      let (α, x) ← parseTerm x
      let w ← getBitVecWidth α
      return (mkBitVec (w + i), mkApp3 (.const ``BitVec.signExtend []) (mkNatLit w) (mkNatLit (w + i)) x)
    if let sexp!{((_ rotate_left {i}) {x})} := e then
      let i ← parseNumeral i
      let (α, x) ← parseTerm x
      let w ← getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.rotateLeft []) (mkNatLit w) x (mkNatLit i))
    if let sexp!{((_ rotate_right {i}) {x})} := e then
      let i ← parseNumeral i
      let (α, x) ← parseTerm x
      let w ← getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.rotateRight []) (mkNatLit w) x (mkNatLit i))
    if let sexp!{(bvnego {x})} := e then
      let (α, x) ← parseTerm x
      let w ← getBitVecWidth α
      return (mkBool, mkApp2 (.const ``BitVec.negOverflow []) (mkNatLit w) x)
    if let sexp!{(bvuaddo {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.uaddOverflow []) (mkNatLit w) x y)
    if let sexp!{(bvsaddo {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.saddOverflow []) (mkNatLit w) x y)
    if let sexp!{(bvumulo {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.umulOverflow []) (mkNatLit w) x y)
    if let sexp!{(bvsmulo {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.smulOverflow []) (mkNatLit w) x y)
    if let sexp!{(bvusubo {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.usubOverflow []) (mkNatLit w) x y)
    if let sexp!{(bvssubo {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.ssubOverflow []) (mkNatLit w) x y)
    if let sexp!{(bvsdivo {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w ← getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.sdivOverflow []) (mkNatLit w) x y)
    if let some r ← parseVar? e then
      return r
    if let some ⟨w, x⟩ := parseBVLiteral? e then
      return (mkBitVec w, toExpr x)
    if let sexp!{({f} ⦃as⦄)} := e then
      let (α, f) ← parseTerm f
      let as ← as.mapM (fun a => return (← parseTerm a).snd)
      return (retType α, mkAppN f as.toArray)
    throw m!"Error: unsupported term {e}"
  retType : Expr → Expr
    | .forallE _ _ b _ => retType b
    | e                => e
  parseVar? (s : Sexp) : ParserM (Option (Expr × Expr)) := do
    let .atom n := s | return none
    let state ← get
    let n := smtSymbolToName n
    -- Bound variables (function/sort parameters, term-level `let` bindings)
    -- live in `bvars` with their canonical type and de Bruijn level.
    if let some (t, i) := state.bvars[n]? then
      return some (t, .bvar (state.level - i - 1))
    -- Free variables (top-level declarations and definitions): `fvars` gives
    -- us the canonical type for callers (e.g. for picking a `BEq` instance);
    -- the `FVarId` references the decl in `lctx` whose `userType` will appear
    -- in the goal.
    if let some (t, fvarId) := state.fvars[n]? then
      return some (t, .fvar fvarId)
    return none
  parseBVLiteral? (s : Sexp) : Option ((w : Nat) × BitVec w) :=
    -- Malformed literals must yield `none` (falling through to the
    -- "unsupported term" error) rather than panicking: in compiled code a
    -- panic does not abort, so `toNat!` would silently continue with `0`.
    match s with
    | sexp!{(_ {.atom v} {.atom w})} =>
      if v.startsWith "bv" then do
        let w ← w.toNat?
        let v ← (v.drop 2).toNat?
        some ⟨w, BitVec.ofNat w v⟩
      else
        none
    | sexp!{{.atom s}} =>
      if s.startsWith "#b" then
        let s := s.drop 2
        if s.isEmpty || !s.all (fun c => c == '0' || c == '1') then
          none
        else
          let w := s.length
          let v := s.foldl (fun v c => v <<< 1 + (if c == '1' then 1 else 0)) 0
          some ⟨w, BitVec.ofNat w v⟩
      else if s.startsWith "#x" then
        let s := (s.drop 2).copy.toUpper
        if s.isEmpty || !s.all Char.isHexDigit then
          none
        else
          let w := 4 * s.length
          let f v c :=
            let d := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'A'.toNat + 10
            v <<< 4 + d
          let v := s.foldl f 0
          some ⟨w, BitVec.ofNat w v⟩
      else
        none
    | _ =>
      none
  leftAssocOpBool (op : Expr) (as : List Sexp) : ParserM (Expr × Expr) := do
    if as.isEmpty then
      throw m!"Error: expected at least one argument"
    let as ← as.mapM (fun a => return (← parseTerm a).snd)
    return (mkBool, as.tail.foldl (mkApp2 op) as.head!)
  leftAssocOpBitVec (op : Nat → Expr) (as : List Sexp) : ParserM (Expr × Expr) := do
    if as.isEmpty then
      throw m!"Error: expected at least one argument"
    let (α, a) ← parseTerm as.head!
    let op := op (← getBitVecWidth α)
    -- Do not reparse a!
    let as ← as.tail.mapM (fun a => return (← parseTerm a).snd)
    return (α, as.foldl (mkApp2 op) a)
  chainableEq (as : List Sexp) : ParserM (Expr × Expr) := do
    if as.length < 2 then
      throw m!"Error: expected at least two arguments for `=`"
    -- Parse each argument exactly once; `=` is chainable: `(= a b c)`
    -- abbreviates `(and (= a b) (= b c))`.
    let (α, x0) ← parseTerm as.head!
    let xs := (x0 :: (← as.tail.mapM (fun a => return (← parseTerm a).snd))).toArray
    let hα ← if α == mkBool
      then pure mkInstBEqBool
      else if α.isAppOfArity ``BitVec 1 then pure (mkInstBEqBitVec (← getBitVecWidth α))
      else throw m!"Error: unsupported type for equality: {α}"
    let mut acc : Expr := mkApp4 (.const ``BEq.beq [0]) α hα xs[0]! xs[1]!
    for i in [1:xs.size - 1] do
      acc := mkApp2 (.const ``and []) acc (mkApp4 (.const ``BEq.beq [0]) α hα xs[i]! xs[i + 1]!)
    return (mkBool, acc)
  pairwiseDistinct (as : List Sexp) : ParserM (Expr × Expr) := do
    if as.length < 2 then
      throw m!"Error: expected at least two arguments for `distinct`"
    -- Parse each argument exactly once; `distinct` denotes the conjunction of
    -- all pairwise disequalities.
    let (α, x0) ← parseTerm as.head!
    let xs := (x0 :: (← as.tail.mapM (fun a => return (← parseTerm a).snd))).toArray
    let hα ← if α == mkBool
      then pure mkInstBEqBool
      else if α.isAppOfArity ``BitVec 1 then pure (mkInstBEqBitVec (← getBitVecWidth α))
      else throw m!"Error: unsupported type for `distinct`: {α}"
    let mut acc : Expr := mkApp4 (.const ``bne [0]) α hα xs[0]! xs[1]!
    for i in [0:xs.size] do
      for j in [i + 1:xs.size] do
        unless i == 0 && j == 1 do
          acc := mkApp2 (.const ``and []) acc (mkApp4 (.const ``bne [0]) α hα xs[i]! xs[j]!)
    return (mkBool, acc)
  parseNestedBindings (bindings : List (List Sexp)) : ParserM (List (Name × Expr × Expr)) := do
    let bindings ← bindings.mapM parseParallelBindings
    return bindings.flatten
  parseParallelBindings (bindings : List Sexp) : ParserM (List (Name × Expr × Expr)) := do
    -- Note: bindings in a parallel let expression use the same context. In
    -- particular, variable shadowing only applies after all the bindings are
    -- parsed.
    let state ← get
    let bindings ← bindings.mapM parseBinding
    let (level, bvars) := bindings.foldl (fun (lvl, bvs) (n, t, _) => (lvl + 1, bvs.insert n (t, lvl))) (state.level, state.bvars)
    set { state with bvars, level }
    return bindings
  parseBinding (binding : Sexp) : ParserM (Name × Expr × Expr) := do
    match binding with
    | sexp!{({n} {v})} =>
      let n := smtSymbolToName n.serialize
      let (t, v) ← parseTerm v
      modify fun state => { state with level := state.level + 1 }
      return (n, t, v)
    | _ =>
      throw m!"Error: unsupported binding {binding}"
  getNestedLetBindingsAndBody (bindings : List (List Sexp)) : Sexp → (List (List Sexp) × Sexp)
    | sexp!{(let (⦃bs⦄) {b})} => getNestedLetBindingsAndBody (bs :: bindings) b
    | b => (bindings.reverse, b)

/--
The subset of SMT-LIB commands the driver reacts to. Commands are named after
the state-machine categories from the SMT-LIB spec:
* `setLogic` / `checkSat` / `exit` drive the Start/Assert/Sat/Unsat transitions
  tracked by `Driver.Mode`.
* `getUnsat` covers `get-proof` and the `get-unsat-*` family — all of which
  are only valid in `unsat` mode.
* Declarations, definitions, and assertions are absorbed by the parser and
  reported as `declOrAssert` so the driver can track the assertion-stack mode.
* Everything else (options, info, comments) is reported as `noop`.
-/
inductive Command where
  /-- `(set-logic L)`. Transitions `Start → Assert`. -/
  | setLogic (logic : String)
  /-- `(check-sat)`. Transitions `Assert → Sat | Unsat` based
      on the solver's answer. -/
  | checkSat
  /-- `(get-unsat-core)`. Only valid in `unsat` mode. -/
  | getUnsatCore
  /-- `(get-model)`. Only valid in `sat` mode. -/
  | getModel
  /-- `(exit)`. Terminates the driver loop. -/
  | exit
  /-- Any command that modifies the assertion stack (a declaration, definition,
      or assertion). Only valid after `(set-logic …)`. -/
  | declOrAssert
  /-- Any command the driver does not need to act on (`set-info`,
      `set-option`, …). -/
  | noop

private def parseTypeDef : Sexp → ParserM Unit
  | sexp!{(define-sort {n} (⦃ps⦄) {b})} => do
    let savedState ← get
    let ps ← ps.mapM parseParam
    let rt := .sort 1
    let (cb, ub) ← parseSort b
    let n := smtSymbolToName n.serialize
    let t := ps.foldr (fun (pn, pt) acc => Expr.forallE pn pt acc .default) rt
    let bv := ps.foldr (fun (pn, pt) acc => Expr.lam pn pt acc .default) cb
    let nv := ps.foldr (fun (pn, pt) acc => Expr.lam pn pt acc .default) ub
    -- Discard the parameter bvars/level introduced for body parsing.
    set savedState
    modify fun s => { s with uvars := s.uvars.insert n bv }
    -- Non-dependent let unfolding is disabled for user-defined types to keep
    -- type-class resolution happy.
    let _ ← pushLDecl n t t nv false
  | defn =>
    throw m!"Error: unsupported type def {defn}"
where
  parseParam (p : Sexp) : ParserM (Name × Expr) := do
    match p with
    | .atom n =>
      let n := smtSymbolToName n
      let t := .sort 1
      modify fun s => { s with level := s.level + 1, bvars := s.bvars.insert n (t, s.level) }
      return (n, t)
    | _ =>
      throw m!"Error: unsupported type param {p}"

private def parseFunDecl : Sexp → ParserM Unit
  | sexp!{(declare-fun {n} (⦃ps⦄) {s})} => do
    let ps ← ps.mapM parseSort
    let (crt, urt) ← parseSort s
    let n := smtSymbolToName n.serialize
    let (ct, ut) := ps.foldr
      (fun (cb, ub) (ct, ut) =>
        (Expr.forallE n cb ct .default, Expr.forallE n ub ut .default))
      (crt, urt)
    let fvarId ← pushCDecl n ut (canonicalType? := some ct)
    -- Record declared constants in declaration order for `(get-model)`.
    modify fun s => { s with consts := s.consts.push fvarId }
  | decl =>
    throw m!"Error: unsupported fun decl {decl}"

private def parseFunDef : Sexp → ParserM Unit
  | sexp!{(define-fun {n} (⦃ps⦄) {s} {b})} => do
    let savedState ← get
    let ps ← ps.mapM parseParam
    let (crt, urt) ← parseSort s
    let (_, b) ← parseTerm b
    let n := smtSymbolToName n.serialize
    let (ct, ut) := ps.foldr
      (fun (pn, cb, ub) (ct, ut) =>
        (Expr.forallE pn cb ct .default, Expr.forallE pn ub ut .default))
      (crt, urt)
    -- The body was parsed using canonical types in `bvars`; wrap it in
    -- lambdas whose binder types are user-facing so the goal shows aliases.
    let v := ps.foldr (fun (pn, _, ub) acc => Expr.lam pn ub acc .default) b
    -- Discard the parameter bvars/level introduced for body parsing.
    set savedState
    -- The decl must be a dependent `let` (`nonDep := false`): a non-dependent
    -- `ldecl` is semantically a `have`, whose value `MetaM` treats as opaque —
    -- `bv_decide`'s `zetaDelta` preprocessing would then leave the defined
    -- symbol as a free atom in the assertions, relaxing the problem.
    let _ ← pushLDecl n ut ct v false
  | defn =>
    throw m!"Error: unsupported fun def {defn}"
where
  parseParam (p : Sexp) : ParserM (Name × Expr × Expr) := do
    match p with
    | sexp!{({n} {s})} =>
      let n := smtSymbolToName n.serialize
      let (ct, ut) ← parseSort s
      modify fun s => { s with level := s.level + 1, bvars := s.bvars.insert n (ct, s.level) }
      return (n, ct, ut)
    | _ =>
      throw m!"Error: unsupported fun param {p}"

private def parseAssert : Sexp → ParserM Unit
  | sexp!{(assert {body})} => do
    let (n?, term) := stripNamedAnnotation body
    let (_, p) ← parseTerm term
    let ann := mkApp3 (.const ``Eq [1]) (.const ``Bool []) p (.const ``true [])
    -- Assertions get a fresh fvar in `lctx` but are not name-resolvable
    -- (they cannot be referenced from later terms). Leave `canonicalType?`
    -- defaulted to `none` so the symbol is not registered in `fvars`.
    -- `MetaM` does not expect `.anonymous` user names in a local context (the
    -- pretty printer, user-name lookups, etc. assume proper names), so an
    -- unnamed assertion gets a reserved, unique `_a.<i>` name instead. The
    -- two-component name cannot collide with SMT-LIB symbols, which are
    -- always single-component (`Name.mkSimple`).
    let fallback := Name.num (Name.mkSimple "_a") (← get).lctx.decls.size
    let _ ← pushCDecl (n?.getD fallback) ann
  | s =>
    throw m!"Error: unsupported assert {s}"
where
  /-- If `body` is `(! t :named f)`, return `(some f, t)`; otherwise return
      `(none, body)`. Other annotation attributes are ignored. -/
  stripNamedAnnotation : Sexp → Option Name × Sexp
    | sexp!{(! {term} ⦃attrs⦄)} => (findLabel attrs, term)
    | s => (none, s)
  findLabel : List Sexp → Option Name
    | sexps!{:named {.atom n} ⦃_⦄} => some (smtSymbolToName n)
    | sexps!{{_} {_} ⦃rest⦄} => findLabel rest
    | _ => none

/--
Parse a single SMT-LIB command. Any declaration, definition, or assertion is
folded into the parser state (including the accumulated `LocalContext`);
`check-sat` and `exit` are surfaced so the driver can react.
-/
def parseCommand : Sexp → ParserM Command
  | sexp!{(define-sort {n} {ps} {b})} => do
    parseTypeDef sexp!{(define-sort {n} {ps} {b})}
    return .declOrAssert
  | sexp!{(declare-const {n} {s})} => do
    parseFunDecl sexp!{(declare-fun {n} () {s})}
    return .declOrAssert
  | sexp!{(declare-fun {n} {ps} {s})} => do
    parseFunDecl sexp!{(declare-fun {n} {ps} {s})}
    return .declOrAssert
  | sexp!{(define-const {n} {s} {b})} => do
    parseFunDef sexp!{(define-fun {n} () {s} {b})}
    return .declOrAssert
  | sexp!{(define-fun {n} {ps} {s} {b})} => do
    parseFunDef sexp!{(define-fun {n} {ps} {s} {b})}
    return .declOrAssert
  | sexp!{(assert {p})} => do
    parseAssert sexp!{(assert {p})}
    return .declOrAssert
  | sexp!{(check-sat)} => return .checkSat
  | sexp!{(get-unsat-core)} => return .getUnsatCore
  | sexp!{(get-model)} => return .getModel
  | sexp!{(set-logic {.atom logic})} => return .setLogic logic
  | sexp!{(exit)} => return .exit
  | sexp!{({.atom cmd} ⦃_⦄)} => do
    -- Commands we do not implement and that cannot be skipped: ignoring them
    -- would silently change the meaning of the query (`push`/`pop`/`reset`
    -- alter the assertion stack) or misreport results (the `get-*` queries
    -- would go unanswered).
    let unsupported := [
      "push", "pop", "reset", "reset-assertions", "check-sat-assuming",
      "get-value", "get-assignment", "get-proof", "get-unsat-assumptions"
    ]
    if unsupported.contains cmd then
      throw m!"Error: unsupported command {cmd}"
    -- Everything else (`set-info`, `set-option`, `get-info`, `echo`, …) does
    -- not affect the assertion stack and is ignored.
    return .noop
  | _ => return .noop

/--
Parse the next SMT-LIB command from the input stream, or return `none` if the
input has been fully consumed. Whitespace and comments between commands are
skipped. On a parse failure the parser throws.
-/
def nextCommand : ParserM (Option Command) := do
  let isEof ← runParsec (Sexp.Parser.misc *> Std.Internal.Parsec.isEof)
  match isEof with
  | false =>
    let s ← runParsec Sexp.Parser.sexp
    let c ← parseCommand s
    return some c
  | true => return none

/--
Build the current goal type by abstracting all top-level declarations and
assertions accumulated in `lctx` around `False`. `usedLetOnly := false`
preserves unused let-bindings (e.g. `define-fun`s never referenced by an
assertion) so the resulting goal mirrors the source file's structure.
-/
def getGoalType : ParserM Expr := do
  let state ← get
  return state.lctx.mkForall state.lctx.getFVars (.const ``False []) (usedLetOnly := false)

end Parser
