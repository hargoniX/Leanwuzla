import Leanwuzla.Aux
import Leanwuzla.Sexp

open Lean

structure Parser.State where
  /-- Current de Bruijn level. -/
  level : Nat := 0
  /-- A mapping from variable names to their corresponding type and de Bruijn
      level (not index). So, the variables are indexed from the bottom of the
      stack rather than from the top (i.e., the order in which the symbols are
      introduced in the SMT-LIB file). To compute the de Bruijn index, we
      subtract the variable's level from the current level. -/
  bvars : Std.HashMap Name (Expr × Nat) := {}
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
         (mkApp2 (.const ``instHXorOfXor [0]) (mkBitVec w)
                 (.app (.const ``BitVec.instXor []) (mkNatLit w)))

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
  let s := if s.startsWith "|" && s.endsWith "|" then s.extract ⟨1⟩ (s.endPos - ⟨1⟩) else s
  -- Quote the string if a natural translation to Name fails
  if s.toName == .anonymous then
    Name.mkSimple s
  else
    s.toName

def parseSort : Sexp → ParserM Expr
  | sexp!{Bool} =>
    return mkBool
  | sexp!{(_ BitVec {w})} =>
    let w := w.serialize.toNat!
    return (mkBitVec w)
  | s => throw m!"Error: unsupported sort {s}"

partial def parseTerm (s : Sexp) : ParserM (Expr × Expr) := do
  try
    go s
  catch e =>
    throw m!"Error: {e}\nfailed to parse term {s}"
where
  go (e : Sexp) : ParserM (Expr × Expr) := do
    if let sexp!{(let (...{_}) {_})} := e then
      -- SMT-LIB supports nesting of parallel let expressions. Both can be
      -- very long. So, we use tail-call recursion to avoid stack overflows.
      let state ← get
      let (bindings, b) := getNestedLetBindingsAndBody [] e
      let bindings ← parseNestedBindings bindings
      let (tb, b) ← parseTerm b
      set state
      let e := bindings.foldr (fun (_, n, t, v) b => .letE n t v b true) b
      return (tb, e)
    if let sexp!{true} := e then
      return (mkBool, .const ``true [])
    if let sexp!{false} := e then
      return (mkBool, .const ``false [])
    if let sexp!{(not {p})} := e then
      let (_, p) ← parseTerm p
      return (mkBool, .app (.const ``not []) p)
    if let sexp!{(=> ...{ps})} := e then
      let ps ← ps.mapM (fun p => return (← parseTerm p).snd)
      let p := ps.dropLast.foldr (mkApp2 (.const ``implies [])) ps.getLast!
      return (mkBool, p)
    if let sexp!{(and ...{ps})} := e then
      return ← leftAssocOpBool (.const ``and []) ps
    if let sexp!{(or ...{ps})} := e then
      return ← leftAssocOpBool (.const ``or []) ps
    if let sexp!{(xor ...{ps})} := e then
      return ← leftAssocOpBool (.const ``xor []) ps
    if let sexp!{(= {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let hα := if α == mkBool then mkInstBEqBool else mkInstBEqBitVec (getBitVecWidth α)
      return (mkBool, mkApp4 (.const ``BEq.beq [0]) α hα x y)
    if let sexp!{(distinct ...{xs})} := e then
      return ← pairwiseDistinct xs
    if let sexp!{(ite {c} {t} {e})} := e then
      let (_, c) ← parseTerm c
      let (α, t) ← parseTerm t
      let (_, e) ← parseTerm e
      return (α, mkApp4 (mkConst ``cond [1]) α c t e)
    if let sexp!{(concat ...{xs})} := e then
      let (α, acc) ← parseTerm xs.head!
      let w := getBitVecWidth α
      let f := fun (w, acc) x => do
        let (v, x) ← parseTerm x
        let v := getBitVecWidth v
        return (w + v, mkApp2 (mkBitVecAppend w v) acc x)
      let (w, acc) ← xs.tail.foldlM f (w, acc)
      return (mkBitVec w, acc)
    if let sexp!{(bvand ...{xs})} := e then
      return ← leftAssocOpBitVec mkBitVecAnd xs
    if let sexp!{(bvor ...{xs})} := e then
      return ← leftAssocOpBitVec mkBitVecOr xs
    if let sexp!{(bvxor ...{xs})} := e then
      return ← leftAssocOpBitVec mkBitVecXor xs
    if let sexp!{(bvnot {x})} := e then
      let (α, x) ← parseTerm x
      let w := getBitVecWidth α
      return (α, .app (mkBitVecNot w) x)
    if let sexp!{(bvnand {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.nand []) (mkNatLit w) x y)
    if let sexp!{(bvnor {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.nor []) (mkNatLit w) x y)
    if let sexp!{(bvxnor {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.xnor []) (mkNatLit w) x y)
    if let sexp!{(bvcomp {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBitVec 1, mkApp3 (.const ``BitVec.compare []) (mkNatLit w) x y)
    if let sexp!{(bvmul ...{xs})} := e then
      return ← leftAssocOpBitVec mkBitVecMul xs
    if let sexp!{(bvadd ...{xs})} := e then
      return ← leftAssocOpBitVec mkBitVecAdd xs
    if let sexp!{(bvsub ...{xs})} := e then
      return ← leftAssocOpBitVec mkBitVecSub xs
    if let sexp!{(bvneg {x})} := e then
      let (α, x) ← parseTerm x
      let w := getBitVecWidth α
      return (α, .app (mkBitVecNeg w) x)
    if let sexp!{(bvudiv {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.smtUDiv []) (mkNatLit w) x y)
    if let sexp!{(bvurem {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp2 (mkBitVecMod w) x y)
    if let sexp!{(bvsdiv {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.smtSDiv []) (mkNatLit w) x y)
    if let sexp!{(bvsrem {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.srem []) (mkNatLit w) x y)
    if let sexp!{(bvsmod {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.smod []) (mkNatLit w) x y)
    if let sexp!{(bvshl {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp2 (mkBitVecShiftLeft w) x y)
    if let sexp!{(bvlshr {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp2 (mkBitVecShiftRight w) x y)
    if let sexp!{(bvashr {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (α, mkApp4 (.const ``BitVec.sshiftRight' []) (mkNatLit w) (mkNatLit w) x y)
    if let sexp!{(bvult {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.ult []) (mkNatLit w) x y)
    if let sexp!{(bvule {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.ule []) (mkNatLit w) x y)
    if let sexp!{(bvugt {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.ugt []) (mkNatLit w) x y)
    if let sexp!{(bvuge {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.uge []) (mkNatLit w) x y)
    if let sexp!{(bvslt {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.slt []) (mkNatLit w) x y)
    if let sexp!{(bvsle {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.sle []) (mkNatLit w) x y)
    if let sexp!{(bvsgt {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.sgt []) (mkNatLit w) x y)
    if let sexp!{(bvsge {x} {y})} := e then
      let (α, x) ← parseTerm x
      let (_, y) ← parseTerm y
      let w := getBitVecWidth α
      return (mkBool, mkApp3 (.const ``BitVec.sge []) (mkNatLit w) x y)
    if let sexp!{((_ extract {i} {j}) {x})} := e then
      let i := i.serialize.toNat!
      let j := j.serialize.toNat!
      let (α, x) ← parseTerm x
      let w := getBitVecWidth α
      let start := j
      let len := i - j + 1
      return (mkBitVec (i - j + 1), mkApp4 (.const ``BitVec.extractLsb' []) (mkNatLit w) (mkNatLit start) (mkNatLit len) x)
    if let sexp!{((_ repeat {i}) {x})} := e then
      let i := i.serialize.toNat!
      let (α, x) ← parseTerm x
      let w := getBitVecWidth α
      return (mkBitVec (w * i), mkApp3 (.const ``BitVec.replicate []) (mkNatLit w) (mkNatLit i) x)
    if let sexp!{((_ zero_extend {i}) {x})} := e then
      let i := i.serialize.toNat!
      let (α, x) ← parseTerm x
      let w := getBitVecWidth α
      return (mkBitVec (w + i), mkApp3 (.const ``BitVec.setWidth []) (mkNatLit w) (mkNatLit (w + i)) x)
    if let sexp!{((_ sign_extend {i}) {x})} := e then
      let i := i.serialize.toNat!
      let (α, x) ← parseTerm x
      let w := getBitVecWidth α
      return (mkBitVec (w + i), mkApp3 (.const ``BitVec.signExtend []) (mkNatLit w) (mkNatLit (w + i)) x)
    if let sexp!{((_ rotate_left {i}) {x})} := e then
      let i := i.serialize.toNat!
      let (α, x) ← parseTerm x
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.rotateLeft []) (mkNatLit w) x (mkNatLit i))
    if let sexp!{((_ rotate_right {i}) {x})} := e then
      let i := i.serialize.toNat!
      let (α, x) ← parseTerm x
      let w := getBitVecWidth α
      return (α, mkApp3 (.const ``BitVec.rotateRight []) (mkNatLit w) x (mkNatLit i))
    if let some r ← parseVar? e then
      return r
    if let some r := parseBVLiteral? s then
      return r
    if let sexp!{({f} ...{as})} := s then
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
    let some (t, i) := state.bvars[n]? | return none
    return some (t, .bvar (state.level - i - 1))
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
  leftAssocOpBool (op : Expr) (as : List Sexp) : ParserM (Expr × Expr) := do
    let as ← as.mapM (fun a => return (← parseTerm a).snd)
    return (mkBool, as.tail.foldl (mkApp2 op) as.head!)
  leftAssocOpBitVec (op : Nat → Expr) (as : List Sexp) : ParserM (Expr × Expr) := do
    let (α, a) ← parseTerm as.head!
    let op := op (getBitVecWidth α)
    -- Do not reparse a!
    let as ← as.tail.mapM (fun a => return (← parseTerm a).snd)
    return (α, as.foldl (mkApp2 op) a)
  pairwiseDistinct (as : List Sexp) : ParserM (Expr × Expr) := do
    if h : as.length < 2 then
      throw m!"Error: expected at least two arguments for `distinct`"
    else
      let (α, as0) ← parseTerm as[0]
      let (_, as1) ← parseTerm as[1]
      let hα := if α == mkBool then mkInstBEqBool else mkInstBEqBitVec (getBitVecWidth α)
      let mut acc : Expr := mkApp4 (.const ``bne [0]) α hα as0 as1
      for hi : i in [2:as.length] do
        let (_, asi) ← parseTerm as[i]
        acc := mkApp2 (.const ``and []) acc (mkApp4 (.const ``bne [0]) α hα as0 asi)
      for hi : i in [1:as.length] do
        for hj : j in [i + 1:as.length] do
          let (_, asi) ← parseTerm as[i]
          let (_, asj) ← parseTerm as[j]
          acc :=  mkApp2 (.const ``and []) acc (mkApp4 (.const ``bne [0]) α hα asi asj)
      return (mkBool, acc)
  parseNestedBindings (bindings : List (List Sexp)) : ParserM (List (Sexp × Name × Expr × Expr)) := do
    let bindings ← bindings.mapM parseParallelBindings
    return bindings.flatten
  parseParallelBindings (bindings : List Sexp) : ParserM (List (Sexp × Name × Expr × Expr)) := do
    -- Note: bindings in a parallel let expression use the same context. In
    -- particular, variable shadowing only applies after all the bindings are
    -- parsed.
    let state ← get
    let bindings ← bindings.mapM parseBinding
    let (level, bvars) := bindings.foldl (fun (lvl, bvs) (_, n, t, _) => (lvl + 1, bvs.insert n (t, lvl))) (state.level, state.bvars)
    set { bvars, level : Parser.State }
    return bindings
  parseBinding (binding : Sexp) : ParserM (Sexp × Name × Expr × Expr) := do
    match binding with
    | sexp!{({n} {v})} =>
      let (t, v) ← parseTerm v
      modify fun state => { state with level := state.level + 1 }
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
  let (level, bvars) := decls.foldl (fun (lvl, bvs) (_, n, t) => (lvl + 1, bvs.insert n (t, lvl))) (state.level, state.bvars)
  set { bvars, level : Parser.State }
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
      let (level, bvars) := ps.foldl (fun (lvl, bvs) (_, n, t) => (lvl + 1, bvs.insert n (t, lvl))) (state.level, state.bvars)
      set { bvars, level : Parser.State }
      let s ← parseSort s
      let (_, b) ← parseTerm b
      let nn := smtSymbolToName n.serialize
      let bvars := state.bvars.insert nn (s, state.level)
      let level := state.level + 1
      set { bvars, level : Parser.State }
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

structure Query where
  decls : List Sexp := []
  defs : List Sexp := []
  asserts : List Sexp := []

def parseQuery (query : Query) : ParserM Expr := do
  try
    withDecls query.decls <| withDefs query.defs do
      let conjs ← query.asserts.mapM parseAssert
      let p := if h : 0 < conjs.length
        then conjs.tail.foldl (mkApp2 (.const ``and [])) conjs[0]
        else .const ``true []
      return mkApp3 (.const ``Eq [1]) (.const ``Bool []) (.app (.const ``not []) p) (.const ``true [])
  catch e =>
    throw m!"Error: {e}\nfailed to parse query {repr (← get)}"

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
  match Sexp.Parser.manySexps!.run query with
  | Except.error e =>
    .error s!"{e}"
  | Except.ok cmds =>
    let query := filterCmds cmds
    (parseQuery query).run' {}

end Parser
