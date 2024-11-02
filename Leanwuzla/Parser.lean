import Leanwuzla.Sexp

open Lean

@[bv_normalize] def implies (a b : Bool) : Bool :=
  !a || b

@[bv_normalize] def BitVec.nand {n : Nat} (x y : BitVec n) : BitVec n :=
  ~~~(x &&& y)

@[bv_normalize] def BitVec.nor {n : Nat} (x y : BitVec n) : BitVec n :=
  ~~~(x ||| y)

@[bv_normalize] def BitVec.xnor {n : Nat} (x y : BitVec n) : BitVec n :=
  ~~~(x ^^^ y)

@[bv_normalize] def BitVec.compare (x y : BitVec n) : BitVec 1 :=
  bif x == y then 1#1 else 0#1

@[bv_normalize] def BitVec.sgt {n : Nat} (x y : BitVec n) : Bool :=
  BitVec.slt y x

@[bv_normalize] def BitVec.sge {n : Nat} (x y : BitVec n) : Bool :=
  BitVec.sle y x

/- Avoids stack-overflow in deeply nested s-expressions. -/
private def Parser.sexpTopLevelHash : Sexp → UInt64
  | .atom s  => hash s
  | .expr ss => hash (ss.filter Sexp.isAtom)

private instance : Hashable Sexp := ⟨Parser.sexpTopLevelHash⟩

structure Parser.State where
  /-- A mapping from variable names to their corresponding type and de Bruijn
      level (not index). So, the variables are indexed from the bottom of the
      stack rather than from the top (i.e., the order in which the symbols are
      introduced in the SMT-LIB file). The expressions created by this parser
      are not valid Lean expressions until the indices are reversed. We follow
      this approach to simplify parsing and preserve the cache. -/
  bvars : Std.HashMap Name (Expr × Nat) := {}
  /-- A mapping from SMT-LIB term to its corresponding Lean type and expression
      (modulo bound variable indexing). -/
  cache : Std.HashMap Sexp (Expr × Expr) := {}
  /-- Current binder level. -/
  level : Nat := 0
deriving Repr

abbrev ParserM := StateT Parser.State (Except MessageData)

namespace Parser

private def mkBool : Expr :=
  .const ``Bool []

private def mkBitVec (w : Nat) : Expr :=
  .app (.const ``BitVec []) (mkNatLit w)

private def getBitVecWidth (α : Expr) :=
  match_expr α with
  | BitVec w => w.nat?.get!
  | _ => panic! "expected BitVec type"

private def mkInstBEqBool : Expr :=
  mkApp2 (.const ``instBEqOfDecidableEq [levelZero]) mkBool
         (.const ``instDecidableEqBool [])

private def mkInstBEqBitVec (w : Nat) : Expr :=
  mkApp2 (.const ``instBEqOfDecidableEq [levelZero]) (mkBitVec w)
         (.app (.const ``instDecidableEqBitVec []) (mkNatLit w))

private def mkBitVecAppend (w v : Nat) : Expr :=
  mkApp4 (.const ``HAppend.hAppend [levelZero, levelZero, levelZero])
         (mkBitVec w) (mkBitVec v) (mkBitVec (w + v))
         (mkApp2 (.const ``BitVec.instHAppendHAddNat []) (mkNatLit w) (mkNatLit v))

private def mkBitVecAnd (w : Nat) : Expr :=
  mkApp4 (.const ``HAnd.hAnd [levelZero, levelZero, levelZero])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``instHAndOfAndOp [levelZero]) (mkBitVec w)
                 (.app (.const ``BitVec.instAndOp []) (mkNatLit w)))

private def mkBitVecOr (w : Nat) : Expr :=
  mkApp4 (.const ``HOr.hOr [levelZero, levelZero, levelZero])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``instHOrOfOrOp [levelZero]) (mkBitVec w)
                 (.app (.const ``BitVec.instOrOp []) (mkNatLit w)))

private def mkBitVecXor (w : Nat) : Expr :=
  mkApp4 (.const ``HXor.hXor [levelZero, levelZero, levelZero])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``instHXorOfXor [levelZero]) (mkBitVec w)
                 (.app (.const ``BitVec.instXor []) (mkNatLit w)))

private def mkBitVecNot (w : Nat) : Expr :=
  mkApp2 (.const ``Complement.complement [levelZero])
         (mkBitVec w)
         (.app (.const ``BitVec.instComplement []) (mkNatLit w))

private def mkBitVecNeg (w : Nat) : Expr :=
  mkApp2 (.const ``Neg.neg [levelZero])
         (mkBitVec w)
         (.app (.const ``BitVec.instNeg []) (mkNatLit w))

private def mkBitVecAdd (w : Nat) : Expr :=
  mkApp4 (.const ``HAdd.hAdd [levelZero, levelZero, levelZero])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``instHAdd [levelZero]) (mkBitVec w)
                 (.app (.const ``BitVec.instAdd []) (mkNatLit w)))

private def mkBitVecSub (w : Nat) : Expr :=
  mkApp4 (.const ``HSub.hSub [levelZero, levelZero, levelZero])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``instHSub [levelZero]) (mkBitVec w)
                 (.app (.const ``BitVec.instSub []) (mkNatLit w)))

private def mkBitVecMul (w : Nat) : Expr :=
  mkApp4 (.const ``HMul.hMul [levelZero, levelZero, levelZero])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``instHMul [levelZero]) (mkBitVec w)
                 (.app (.const ``BitVec.instMul []) (mkNatLit w)))

private def mkBitVecMod (w : Nat) : Expr :=
  mkApp4 (.const ``HMod.hMod [levelZero, levelZero, levelZero])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``instHMod [levelZero]) (mkBitVec w)
                 (.app (.const ``BitVec.instMod []) (mkNatLit w)))

private def mkBitVecShiftLeft (w : Nat) : Expr :=
  mkApp4 (.const ``HShiftLeft.hShiftLeft [levelZero, levelZero, levelZero])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``BitVec.instHShiftLeft []) (mkNatLit w) (mkNatLit w))

private def mkBitVecShiftRight (w : Nat) : Expr :=
  mkApp4 (.const ``HShiftRight.hShiftRight [levelZero, levelZero, levelZero])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``BitVec.instHShiftRight []) (mkNatLit w) (mkNatLit w))

def smtSymbolToName (s : String) : Name :=
  let s := if s.startsWith "|" && s.endsWith "|" then s.extract ⟨1⟩ (s.endPos - ⟨1⟩) else s
  -- Quote the string if a natural translation to Name fails
  if s.toName == .anonymous then
    Name.mkSimple s
  else
    s.toName

partial def parseSort : Sexp → ParserM Expr
  | sexp!{Bool} =>
    return mkBool
  | sexp!{(_ BitVec {w})} =>
    let w := w.serialize.toNat!
    return (mkBitVec w)
  | s => throw m!"Error: unsupported sort {s}"

partial def parseTerm (s : Sexp) : ParserM (Expr × Expr) := do
  try
    if let some r := (← get).cache[s]? then
      return r
    else
      let r ← go s
      modify fun state => { state with cache := state.cache.insert s r }
      return r
  catch e =>
    throw m!"Error: {e}\nfailed to parse term {s}"
where
  go (e : Sexp) : ParserM (Expr × Expr) := do
    match e with
    | sexp!{(let (...{_}) {_})} =>
      -- SMT-LIB supports nesting of parallel let expressions. Both can be
      -- very long. So, we use tail-call recursion to avoid stack overflows.
      let state ← get
      let (bindings, b) := getNestedLetBindingsAndBody [] e
      let bindings ← parseNestedBindings bindings
      let (t, b) ← parseTerm b
      set state
      let e := bindings.foldr (fun (_, n, t, v) b => .letE n t v b true) b
      return (t, e)
    | sexp!{true} =>
      return (mkBool, .const ``true [])
    | sexp!{false} =>
      return (mkBool, .const ``false [])
    | sexp!{(not {p})} =>
      let (_, p) ← parseTerm p
      return (mkBool, .app (.const ``not []) p)
    | sexp!{(=> ...{ps})} =>
      let ps ← ps.mapM (fun p => return (← parseTerm p).snd)
      let p := ps.dropLast.foldr (mkApp2 (.const ``implies [])) ps.getLast!
      return (mkBool, p)
    | sexp!{(and ...{ps})} =>
      return (mkBool, ← leftAssocOp (.const ``and []) ps)
    | sexp!{(or ...{ps})} =>
      return (mkBool, ← leftAssocOp (.const ``or []) ps)
    | sexp!{(xor ...{ps})} =>
      return (mkBool, ← leftAssocOp (.const ``xor []) ps)
    | sexp!{(= {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let hα := if α == mkBool then mkInstBEqBool else mkInstBEqBitVec (getBitVecWidth α)
      return (mkBool, mkApp4 (.const ``BEq.beq [levelZero]) α hα x y)
    | sexp!{(distinct ...{xs})} =>
      let (α, _) ← parseTerm xs.head!
      let hα := if α == mkBool then mkInstBEqBool else mkInstBEqBitVec (getBitVecWidth α)
      return (mkBool, ← pairwiseDistinct α hα xs)
    | sexp!{(ite {c} {t} {e})} =>
      let (_, c) ← parseTerm c
      let (α, t) ← parseTerm t
      let (_, e) ← parseTerm e
      return (α, mkApp4 (.const ``cond [levelZero]) α c t e)
    | sexp!{(concat ...{xs})} =>
      let (α, acc) ← parseTerm xs.head!
      let w := getBitVecWidth α
      let f := fun (w, acc) x => do
        let (v, x) ← parseTerm x
        let v := getBitVecWidth v
        return (w + v, mkApp2 (mkBitVecAppend w v) acc x)
      let (w, acc) ← xs.tail.foldlM f (w, acc)
      return (mkBitVec w, acc)
    | sexp!{(bvand ...{ps})} =>
      let (α, _) ← parseTerm ps.head!
      let w := getBitVecWidth α
      return (α, ← leftAssocOp (mkBitVecAnd w) ps)
    | sexp!{(bvor ...{ps})} =>
      let (α, _) ← parseTerm ps.head!
      let w := getBitVecWidth α
      return (α, ← leftAssocOp (mkBitVecOr w) ps)
    | sexp!{(bvxor ...{ps})} =>
      let (α, _) ← parseTerm ps.head!
      let w := getBitVecWidth α
      return (α, ← leftAssocOp (mkBitVecXor w) ps)
    | sexp!{(bvnot {x})} =>
      let (α, x) ← parseTerm x
      let w := getBitVecWidth α
      return (α, .app (mkBitVecNot w) x)
    | sexp!{(bvnand {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.nand []) (mkNatLit w) x y)
    | sexp!{(bvnor {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.nor []) (mkNatLit w) x y)
    | sexp!{(bvxnor {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.xnor []) (mkNatLit w) x y)
    | sexp!{(bvcomp {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBitVec 1, mkApp3 (.const ``BitVec.compare []) (mkNatLit w) x y)
    | sexp!{(bvmul ...{ps})} =>
      let (α, _) ← parseTerm ps.head!
      let w := getBitVecWidth α
      return (α, ← leftAssocOp (mkBitVecMul w) ps)
    | sexp!{(bvadd ...{ps})} =>
      let (α, _) ← parseTerm ps.head!
      let w := getBitVecWidth α
      return (α, ← leftAssocOp (mkBitVecAdd w) ps)
    | sexp!{(bvsub ...{ps})} =>
      let (α, _) ← parseTerm ps.head!
      let w := getBitVecWidth α
      return (α, ← leftAssocOp (mkBitVecSub w) ps)
    | sexp!{(bvneg {x})} =>
      let (α, x) ← parseTerm x
      let w := getBitVecWidth α
      return (α, .app (mkBitVecNeg w) x)
    | sexp!{(bvudiv {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.smtUDiv []) (mkNatLit w) x y)
    | sexp!{(bvurem {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp2 (mkBitVecMod w) x y)
    | sexp!{(bvsdiv {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.smtSDiv []) (mkNatLit w) x y)
    | sexp!{(bvsrem {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.srem []) (mkNatLit w) x y)
    | sexp!{(bvsmod {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.smod []) (mkNatLit w) x y)
    | sexp!{(bvshl {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp2 (mkBitVecShiftLeft w) x y)
    | sexp!{(bvlshr {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp2 (mkBitVecShiftRight w) x y)
    | sexp!{(bvashr {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp4 (.const ``BitVec.sshiftRight' []) (mkNatLit w) (mkNatLit w) x y)
    | sexp!{(bvult {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.ult []) (mkNatLit w) x y)
    | sexp!{(bvule {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.ule []) (mkNatLit w) x y)
    | sexp!{(bvugt {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.ult []) (mkNatLit w) x y)
    | sexp!{(bvuge {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.ule []) (mkNatLit w) x y)
    | sexp!{(bvslt {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.slt []) (mkNatLit w) x y)
    | sexp!{(bvsle {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.sle []) (mkNatLit w) x y)
    | sexp!{(bvsgt {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.sgt []) (mkNatLit w) x y)
    | sexp!{(bvsge {x} {y})} =>
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.sge []) (mkNatLit w) x y)
    | sexp!{((_ extract {i} {j}) {x})} =>
      let i := i.serialize.toNat!
      let j := j.serialize.toNat!
      let (α, x) ← parseTerm x
      let w := getBitVecWidth α
      return (mkBitVec (i - j + 1), mkApp4 (.const ``BitVec.extractLsb []) (mkNatLit w) (mkNatLit i) (mkNatLit j) x)
    | sexp!{((_ repeat {i}) {x})} =>
      let i := i.serialize.toNat!
      let (α, x) ← parseTerm x
      let w := getBitVecWidth α
      return (mkBitVec (w * i), mkApp3 (.const ``BitVec.replicate []) (mkNatLit w) (mkNatLit i) x)
    | sexp!{((_ zero_extend {i}) {x})} =>
      let i := i.serialize.toNat!
      let (α, x) ← parseTerm x
      let w := getBitVecWidth α
      return (mkBitVec (w + i), mkApp3 (.const ``BitVec.zeroExtend []) (mkNatLit w) (mkNatLit (w + i)) x)
    | sexp!{((_ sign_extend {i}) {x})} =>
      let i := i.serialize.toNat!
      let (α, x) ← parseTerm x
      let w := getBitVecWidth α
      return (mkBitVec (w + i), mkApp3 (.const ``BitVec.signExtend []) (mkNatLit w) (mkNatLit (w + i)) x)
    | sexp!{((_ rotate_left {i}) {x})} =>
      let i := i.serialize.toNat!
      let (α, x) ← parseTerm x
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.rotateLeft []) (mkNatLit w) x (mkNatLit i))
    | sexp!{((_ rotate_right {i}) {x})} =>
      let i := i.serialize.toNat!
      let (α, x) ← parseTerm x
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.rotateRight []) (mkNatLit w) x (mkNatLit i))
    | _ =>
      if let some r ← parseVar? e then
        return r
      else
      if let some r := parseBVLiteral? s then
        return r
      else if let sexp!{({f} ...{as})} := s then
        let (α, f) ← parseTerm f
        let as ← as.mapM (fun a => return (← parseTerm a).snd)
        return (retType α, mkAppN f as.toArray)
      else
        throw m!"Error: unsupported term {e}"
  retType : Expr → Expr
    | .forallE _ _ b _ => retType b
    | e                => e
  parseVar? (s : Sexp) : ParserM (Option (Expr × Expr)) := do
    if let .atom n := s then
      let n := smtSymbolToName n
      if let some (t, n) := (← get).bvars[n]? then
        return some (t, .bvar n)
      else
        return none
    else
      return none
  parseBVLiteral? (s : Sexp) : Option (Expr × Expr) :=
    match s with
    | sexp!{(_ {.atom v} {.atom w})} =>
      if v.startsWith "bv" then
        let v := v.drop 2
        let w := w.toNat!
        let v := v.toNat!
        some (mkBitVec w, mkApp2 (.const ``BitVec.ofNat []) (mkNatLit w) (mkNatLit v))
      else
        none
    | sexp!{{.atom s}} =>
      if s.startsWith "#b" then
        let s := s.drop 2
        let w := s.length
        let v := s.foldl (fun v c => v <<< 1 + (if c == '1' then 1 else 0)) 0
        some (mkBitVec w, mkApp2 (.const ``BitVec.ofNat []) (mkNatLit w) (mkNatLit v))
      else if s.startsWith "#x" then
        let s := (s.drop 2).toUpper
        let w := 4 * s.length
        let f v c :=
          let d := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'A'.toNat + 10
          v <<< 4 + d
        let v := s.foldl f 0
        some (mkBitVec w, mkApp2 (.const ``BitVec.ofNat []) (mkNatLit w) (mkNatLit v))
      else
        none
    | _ =>
      none
  leftAssocOp (op : Expr) (as : List Sexp) : ParserM Expr := do
    let as ← as.mapM (fun a => return (← parseTerm a).snd)
    return as.tail.foldl (mkApp2 op) as.head!
  pairwiseDistinct (α : Expr) (hα : Expr) (as : List Sexp) : ParserM Expr := do
    if h : as.length < 2 then
      throw m!"Error: expected at least two arguments for `distinct`"
    else
      let (_, as0) ← parseTerm as[0]
      let (_, as1) ← parseTerm as[1]
      let mut acc : Expr := mkApp4 (.const ``bne [levelZero]) α hα as0 as1
      for hi : i in [2:as.length] do
        let (_, asi) ← parseTerm as[i]
        acc := mkApp2 (.const ``and []) acc (mkApp4 (.const ``bne [levelZero]) α hα as0 asi)
      for hi : i in [1:as.length] do
        for hj : j in [i + 1:as.length] do
          let (_, asi) ← parseTerm as[i]
          let (_, asj) ← parseTerm as[j]
          acc :=  mkApp2 (.const ``and []) acc (mkApp4 (.const ``bne [levelZero]) α hα asi asj)
      return acc
  parseNestedBindings (bindings : List (List Sexp)) : ParserM (List (Sexp × Name × Expr × Expr)) := do
    let bindings ← bindings.mapM parseParallelBindings
    return bindings.flatten
  parseParallelBindings (bindings : List Sexp) : ParserM (List (Sexp × Name × Expr × Expr)) := do
    -- Note: bindings in a parallel let expression use the same context. In
    -- particular, variable shadowing only applies after all the bindings are
    -- parsed.
    let state ← get
    let bindings ← bindings.mapM parseBinding
    -- clear the cache if there's variable shadowing
    let clearCache := bindings.any fun (_, n, _) => state.bvars.contains n
    let (level, bvars) := bindings.foldl (fun (lvl, bvs) (_, n, t, _) => (lvl + 1, bvs.insert n (t, lvl))) (state.level, state.bvars)
    let cache := if clearCache then {} else state.cache
    set { bvars, cache, level : Parser.State }
    return bindings
  parseBinding (binding : Sexp) : ParserM (Sexp × Name × Expr × Expr) := do
    match binding with
    | sexp!{({n} {v})} =>
      let (t, v) ← parseTerm v
      return (n, smtSymbolToName n.serialize, t, v)
    | _ =>
      throw m!"Error: unsupported bindings {binding}"
  getNestedLetBindingsAndBody (bindings : List (List Sexp)) : Sexp → (List (List Sexp) × Sexp)
    | sexp!{(let (...{bs}) {b})} => getNestedLetBindingsAndBody (bs :: bindings) b
    | b => (bindings.reverse, b)

private def mkArrow (α β : Expr) : Expr :=
  Lean.mkForall .anonymous BinderInfo.default α β

def withDecls (decls : List Sexp) (k : ParserM Expr) : ParserM Expr := do
  let state ← get
  let mut decls ← decls.mapM parseDecl
  -- clear the cache if there's variable shadowing
  let clearCache := decls.any fun (_, n, _) => state.bvars.contains n
  let (level, bvars) := decls.foldl (fun (lvl, bvs) (_, n, t) => (lvl + 1, bvs.insert n (t, lvl))) (state.level, state.bvars)
  let cache := if clearCache then {} else state.cache
  set { bvars, cache, level : Parser.State }
  let b ← k
  set state
  return decls.foldr (fun (_, n, t) b => .forallE n t b .default) b
where
  parseDecl (decl : Sexp) : ParserM (Sexp × Name × Expr) := do
    match decl with
    | sexp!{(declare-fun {n} (...{ps}) {s})} =>
      let ss ← ps.mapM parseSort
      return (n, smtSymbolToName n.serialize, ss.foldr mkArrow (← parseSort s))
    | sexp!{(declare-const {n} {s})} =>
      return (n, smtSymbolToName n.serialize, ← parseSort s)
    | _ =>
      throw m!"Error: unsupported decl {decl}"

def withDefs (defs : List Sexp) (k : ParserM Expr) : ParserM Expr := do
  let state ← get
  -- it's common for SMT-LIB queries to be "letified" using define-fun to
  -- minimize their size. We don't recurse on each definition to avoid stack
  -- overflows.
  let defs ← defs.mapM parseDef
  let b ← k
  set state
  return defs.foldr (fun (_, n, t, v) b => .letE n t v b true) b
where
  parseDef (defn : Sexp) : ParserM (Sexp × Name × Expr × Expr) := do
    match defn with
    | sexp!{(define-fun {n} (...{ps}) {s} {b})} =>
      let state ← get
      let ps ← ps.mapM parseParam
      -- clear the cache if there's variable shadowing
      let clearCache := ps.any fun (_, n, _) => state.bvars.contains n
      let (level, bvars) := ps.foldl (fun (lvl, bvs) (_, n, t) => (lvl + 1, bvs.insert n (t, lvl))) (state.level, state.bvars)
      let cache := if clearCache then {} else state.cache
      set { bvars, cache, level : Parser.State }
      let s ← parseSort s
      let (_, b) ← parseTerm b
      let nn := smtSymbolToName n.serialize
      let clearCache := state.bvars.contains nn
      let bvars := state.bvars.insert nn (s, state.level)
      let cache := if clearCache then {} else state.cache
      let level := state.level + 1
      set { bvars, cache, level : Parser.State }
      let t := ps.foldr (fun (_, n, t) b => .forallE n t b .default) s
      let v := ps.foldr (fun (_, n, t) b => .lam n t b .default) b
      return (n, nn, t, v)
    | _ =>
      throw m!"Error: unsupported def {defs}"
  parseParam (p : Sexp) : ParserM (Sexp × Name × Expr) := do
    match p with
    | sexp!{({n} {s})} =>
      return (n, smtSymbolToName n.serialize, ← parseSort s)
    | _ =>
      throw m!"Error: unsupported param {p}"

def parseAssert : Sexp → ParserM Expr
  | sexp!{(assert {p})} =>
    return (← parseTerm p).snd
  | s =>
    throw m!"Error: unsupported assert {s}"

/-- A single pass to reverse the indices of bound variables. This is done to
    replace de Bruijn levels used by the parser with de Bruijn indices
    understood by Lean. Note: The Lean expression produced by the parser could
    be deeply nested. So, we flatten nested applications of the same constructor
    to avoid stack overflows.
-/
partial def reverseIndices (e : Expr) : Expr :=
  go 0 e
where
  go (scope : Nat) (e : Expr) : Expr :=
    if e.isApp then
      let (op, as) := getLeftAssocOpAndArgs #[] e
      if as.isEmpty then
        let (f, as) := getAppFnAndArgs #[] e
        mkAppN (go scope f) (as.map (go scope))
      else
        let op := go scope op
        let as := as.map (go scope)
        as[1:].foldl (mkApp2 op) as[0]!
    else if e.isLambda then
      let (bs, b) := getLamBindersAndBody #[] e
      bs.foldr (fun (n, t, d) b => .lam n t b d) (go (scope + bs.size) b)
    else if e.isForall then
      let (bs, b) := getForallBindersAndBody #[] e
      bs.foldr (fun (n, t, d) b => .forallE n t b d) (go (scope + bs.size) b)
    else if e.isLet then
      let (bs, b) := getLetBindersAndBody #[] e
      let bs := bs.mapIdx fun i (n, t, v) => (n, t, go (scope + i) v)
      bs.foldr (fun (n, t, v) b => .letE n t v b true) (go (scope + bs.size) b)
    else if let .bvar i := e then
      .bvar (scope - i - 1)
    else
      e
  getAppFnAndArgs (as : Array Expr) : Expr → Expr × Array Expr
    | .app f a => getAppFnAndArgs (as.push a) f
    | e        => (e, as.reverse)
  getLeftAssocOpAndArgs (as : Array Expr) : Expr → Expr × Array Expr
    | .app (.app f₁ (.app (.app f₂ a₁) a₂)) a₃ =>
      if f₁ == f₂ then
        getLeftAssocOpAndArgs (as.push a₃) (.app (.app f₂ a₁) a₂)
      else
        let as := (as.push a₃).push (.app (.app f₂ a₁) a₂)
        (f₁, as.reverse)
    | .app (.app f e) a =>
      let as := (as.push a).push e
      (f, as.reverse)
    | e        => (e, as.reverse)
  getLamBindersAndBody (as : Array (Name × Expr × BinderInfo)) : Expr → Array (Name × Expr × BinderInfo) × Expr
    | .lam n t b d => getLamBindersAndBody (as.push (n, t, d)) b
    | e            => (as, e)
  getForallBindersAndBody (as : Array (Name × Expr × BinderInfo)) : Expr → Array (Name × Expr × BinderInfo) × Expr
    | .forallE n t b d => getForallBindersAndBody (as.push (n, t, d)) b
    | e                => (as, e)
  getLetBindersAndBody (as : Array (Name × Expr × Expr)) : Expr → Array (Name × Expr × Expr) × Expr
    | .letE n t v b _ => getLetBindersAndBody (as.push (n, t, v)) b
    | e               => (as, e)

structure Query where
  decls : List Sexp := []
  defs : List Sexp := []
  asserts : List Sexp := []

def parseQuery (query : Query) : ParserM Expr := do
  let e ← withDecls query.decls <| withDefs query.defs do
    try
      let conjs ← query.asserts.mapM parseAssert
      let p := conjs.tail.foldl (mkApp2 (.const ``and [])) conjs.head!
      return mkApp3 (.const ``Eq [levelOne]) (.const ``Bool []) (.app (.const ``not []) p) (.const ``true [])
    catch e =>
      throw m!"Error: {e}\nfailed to parse query {repr (← get)}"
  return reverseIndices e

def filterCmds (sexps : List Sexp) : Query :=
  go {} sexps
where
  go (query : Query) : List Sexp → Query
    | sexp!{(declare-const {n} {s})} :: cmds =>
      go { query with decls := sexp!{(declare-const {n} {s})} :: query.decls } cmds
    | sexp!{(declare-fun {n} {ps} {s})} :: cmds =>
      go { query with decls := sexp!{(declare-fun {n} {ps} {s})} :: query.decls } cmds
    | sexp!{(define-fun {n} {ps} {s} {e})} :: cmds =>
      go { query with defs := sexp!{(define-fun {n} {ps} {s} {e})} :: query.defs } cmds
    | sexp!{(assert {p})} :: cmds =>
      go { query with asserts := sexp!{(assert {p})} :: query.asserts } cmds
    | _ :: cmds =>
      go query cmds
    | [] =>
      { decls := query.decls.reverse
        defs := query.defs.reverse
        asserts := query.asserts.reverse }

def parseSmt2Query (query : String) : Except MessageData Expr :=
  match Sexp.parseMany query with
  | Except.error e =>
    .error s!"{e}"
  | Except.ok cmds =>
    let query := filterCmds cmds
    (parseQuery query).run' {}

end Parser
