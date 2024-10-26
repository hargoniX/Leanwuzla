import Qq

import Leanwuzla.Sexp

open Lean

@[bv_normalize] def BitVec.compare (x y : BitVec n) : BitVec 1 :=
  bif x == y then 1#1 else 0#1

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
deriving Repr

abbrev ParserM := StateRefT Parser.State CoreM

namespace Parser

open Qq

def smtSymbolToName (s : String) : Name :=
  -- Quote the string if a natural translation to Name fails
  if s.toName == .anonymous then
    Name.mkSimple s
  else
    s.toName

partial def parseSort : Sexp → ParserM Expr
  | sexp!{Bool} =>
    return q(Bool)
  | sexp!{(_ BitVec {w})} =>
    let w : Nat := w.serialize.toNat!
    return q(BitVec $w)
  | s => throwError m!"unsupported sort: {s}"

partial def parseTerm (s : Sexp) : ParserM (Expr × Expr) := do
  try
    if let some r := (← get).cache[s]? then
      return r
    else
      let r ← go s
      modify fun state => { state with cache := state.cache.insert s r }
      return r
  catch e =>
    throwError m!"{e.toMessageData}\nfailed to parse term: {s}"
where
  go (e : Sexp) : ParserM (Expr × Expr) := do
    match e with
    | sexp!{(let (...{bindings}) {b})} =>
      let state ← get
      let bindings ← bindings.mapM parseBinding
      -- clear the cache if there's variable shadowing
      let clearCache := bindings.any fun (_, n, _) => state.bvars.contains n
      let bvars := bindings.foldl (fun bvs (_, n, t, _) => bvs.insert n (t, bvs.size)) state.bvars
      let cache := if clearCache then {} else state.cache
      set { bvars, cache : Parser.State }
      let (t, b) ← parseTerm b
      set state
      let e := bindings.foldr (fun (_, n, t, v) b => .letE n t v b true) b
      return (t, e)
    | sexp!{(concat ...{xs})} =>
      let w : Q(Nat) ← parseTerm xs.head! >>= (pure ·.fst.appArg!)
      let acc : Q(BitVec $w) ← parseTerm xs.head! >>= (pure ·.snd)
      let f := fun ⟨w, acc⟩ x => do
        let v : Q(Nat) ← parseTerm x >>= (pure ·.fst.appArg!)
        let x : Q(BitVec $v) ← parseTerm x >>= (pure ·.snd)
        return ⟨q($w + $v), q($acc ++ $x)⟩
      let ⟨w, acc⟩ ← xs.tail.foldlM f (⟨w, acc⟩ : (w : Q(Nat)) × Q(BitVec $w))
      return (q(BitVec $w), acc)
    | sexp!{true} =>
      return (q(Bool), q(true))
    | sexp!{false} =>
      return (q(Bool), q(false))
    | sexp!{(not {p})} =>
      let (_, (p : Q(Bool))) ← parseTerm p
      return (q(Bool), q(!$p))
    | sexp!{(=> ...{ps})} =>
      return (q(Bool), ← rightAssocOp q(mkArrow) ps)
    | sexp!{(and ...{ps})} =>
      return (q(Bool), ← leftAssocOp q(and) ps)
    | sexp!{(or ...{ps})} =>
      return (q(Bool), ← leftAssocOp q(or) ps)
    | sexp!{(xor ...{ps})} =>
      return (q(Bool), ← leftAssocOp q(xor) ps)
    | sexp!{(= {x} {y})} =>
      let α := (← parseTerm x).fst
      if α == q(Bool) then
        let (_, (x : Q(Bool))) ← parseTerm x
        let (_, (y : Q(Bool))) ← parseTerm y
          return (q(Bool), q($x == $y))
      else
        let w : Q(Nat) ← pure α.appArg!
        let (_, (x : Q(BitVec $w))) ← parseTerm x
        let (_, (y : Q(BitVec $w))) ← parseTerm y
        return (q(Bool), q(@BEq.beq (BitVec $w) _ $x $y))
    | sexp!{(distinct {x} {y})} =>
      let α := (← parseTerm x).fst
      if α == q(Bool) then
        let (_, (x : Q(Bool))) ← parseTerm x
        let (_, (y : Q(Bool))) ← parseTerm y
          return (q(Bool), q($x != $y))
      else
        let w : Q(Nat) ← pure α.appArg!
        let (_, (x : Q(BitVec $w))) ← parseTerm x
        let (_, (y : Q(BitVec $w))) ← parseTerm y
        return (q(Bool), q(@bne (BitVec $w) _ $x $y))
    | sexp!{(ite {c} {t} {e})} =>
      let (_, (c : Q(Bool))) ← parseTerm c
      let ((α : Q(Type)), (t : Q($α))) ← parseTerm t
      let (_, (e : Q($α))) ← parseTerm e
      return (q($α), q(bif $c then $t else $e))
    | sexp!{(bvand ...{ps})} =>
      let w : Q(Nat) := (← parseTerm ps.head!).fst.appArg!
      return (q(BitVec $w), ← leftAssocOp q(@HAnd.hAnd (BitVec $w) (BitVec $w) (BitVec $w) _) ps)
    | sexp!{(bvor ...{ps})} =>
      let w : Q(Nat) := (← parseTerm ps.head!).fst.appArg!
      return (q(BitVec $w), ← leftAssocOp q(@HOr.hOr (BitVec $w) (BitVec $w) (BitVec $w) _) ps)
    | sexp!{(bvxor ...{ps})} =>
      let w : Q(Nat) := (← parseTerm ps.head!).fst.appArg!
      return (q(BitVec $w), ← leftAssocOp q(@HXor.hXor (BitVec $w) (BitVec $w) (BitVec $w) _) ps)
    | sexp!{(bvnot {x})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      return (q(BitVec $w), q(~~~$x))
    | sexp!{(bvcomp {x} {y})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      let (_, (y : Q(BitVec $w))) ← parseTerm y
      return (q(BitVec 1), q(@BitVec.compare $w $x $y))
    | sexp!{(bvmul ...{ps})} =>
      let w : Q(Nat) := (← parseTerm ps.head!).fst.appArg!
      return (q(BitVec $w), ← leftAssocOp q(@HMul.hMul (BitVec $w) (BitVec $w) (BitVec $w) _) ps)
    | sexp!{(bvadd ...{ps})} =>
      let w : Q(Nat) := (← parseTerm ps.head!).fst.appArg!
      return (q(BitVec $w), ← leftAssocOp q(@HAdd.hAdd (BitVec $w) (BitVec $w) (BitVec $w) _) ps)
    | sexp!{(bvsub ...{ps})} =>
      let w : Q(Nat) := (← parseTerm ps.head!).fst.appArg!
      return (q(BitVec $w), ← leftAssocOp q(@HSub.hSub (BitVec $w) (BitVec $w) (BitVec $w) _) ps)
    | sexp!{(bvneg {x})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      return (q(BitVec $w), q(-$x))
    | sexp!{(bvudiv {x} {y})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      let (_, (y : Q(BitVec $w))) ← parseTerm y
      return (q(BitVec $w), q(BitVec.smtUDiv $x $y))
    | sexp!{(bvurem {x} {y})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      let (_, (y : Q(BitVec $w))) ← parseTerm y
      return (q(BitVec $w), q($x % $y))
    | sexp!{(bvsdiv {x} {y})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      let (_, (y : Q(BitVec $w))) ← parseTerm y
      return (q(BitVec $w), q(BitVec.smtSDiv $x $y))
    | sexp!{(bvsrem {x} {y})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      let (_, (y : Q(BitVec $w))) ← parseTerm y
      return (q(BitVec $w), q(BitVec.srem $x $y))
    | sexp!{(bvsmod {x} {y})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      let (_, (y : Q(BitVec $w))) ← parseTerm y
      return (q(BitVec $w), q(BitVec.smod $x $y))
    | sexp!{(bvshl {x} {y})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      let (_, (y : Q(BitVec $w))) ← parseTerm y
      return (q(BitVec $w), q($x <<< $y))
    | sexp!{(bvlshr {x} {y})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      let (_, (y : Q(BitVec $w))) ← parseTerm y
      return (q(BitVec $w), q($x >>> $y))
    | sexp!{(bvult {x} {y})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      let (_, (y : Q(BitVec $w))) ← parseTerm y
      return (q(Bool), q(@BitVec.ult $w $x $y))
    | sexp!{(bvule {x} {y})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      let (_, (y : Q(BitVec $w))) ← parseTerm y
      return (q(Bool), q(@BitVec.ule $w $x $y))
    | sexp!{(bvugt {x} {y})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      let (_, (y : Q(BitVec $w))) ← parseTerm y
      return (q(Bool), q(@BitVec.ult $w $y $x))
    | sexp!{(bvuge {x} {y})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      let (_, (y : Q(BitVec $w))) ← parseTerm y
      return (q(Bool), q(@BitVec.ule $w $y $x))
    | sexp!{(bvslt {x} {y})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      let (_, (y : Q(BitVec $w))) ← parseTerm y
      return (q(Bool), q(@BitVec.slt $w $x $y))
    | sexp!{(bvsle {x} {y})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      let (_, (y : Q(BitVec $w))) ← parseTerm y
      return (q(Bool), q(@BitVec.sle $w $x $y))
    | sexp!{((_ extract {i} {j}) {x})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let i : Nat := i.serialize.toNat!
      let j : Nat := j.serialize.toNat!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      return (q(BitVec $w), q(«$x».extractLsb $i $j))
    | sexp!{((_ repeat {n}) {x})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let n : Nat := n.serialize.toNat!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      return (q(BitVec $w), q(«$x».replicate $n))
    | sexp!{((_ zero_extend {n}) {x})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let n : Nat := n.serialize.toNat!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      return (q(BitVec ($w + $n)), q(«$x».zeroExtend ($w + $n)))
    | sexp!{((_ sign_extend {n}) {x})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let n : Nat := n.serialize.toNat!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      return (q(BitVec ($w + $n)), q(«$x».signExtend ($w + $n)))
    | sexp!{((_ rotate_left {n}) {x})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let n : Nat := n.serialize.toNat!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      return (q(BitVec $w), q(«$x».rotateLeft $n))
    | sexp!{((_ rotate_right {n}) {x})} =>
      have w : Q(Nat) := (← parseTerm x).fst.appArg!
      let n : Nat := n.serialize.toNat!
      let (_, (x : Q(BitVec $w))) ← parseTerm x
      return (q(BitVec $w), q(«$x».rotateRight $n))
    | _ =>
      if let some r ← parseVar? e then
        return r
      else
      if let some r := parseBVLiteral? s then
        return r
      else if let sexp!{({f} ...{as})} := s then
        let (_, f) ← parseTerm f
        let as ← as.mapM (parseTerm · >>= pure ∘ Prod.snd)
        return (f, mkAppN f as.toArray)
      else
        throwError m!"unsupported term: {e}"
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
        let w : Nat := w.toNat!
        let v : Nat := v.toNat!
        some (q(BitVec $w), q(BitVec.ofNat $w $v))
      else
        none
    | sexp!{{.atom s}} =>
      if s.startsWith "#b" then
        let s := s.drop 2
        let w : Nat := s.length
        let v : Nat := s.foldl (fun v c => v <<< 1 + (if c == '1' then 1 else 0)) 0
        some (q(BitVec $w), q(BitVec.ofNat $w $v))
      else if s.startsWith "#x" then
        let s := s.drop 2
        let w : Nat := 4 * s.length
        let v : Nat := s.foldl (fun v c => v <<< 4 + c.toNat - '0'.toNat) 0
        some (q(BitVec $w), q(BitVec.ofNat $w $v))
      else
        none
    | _ =>
      none
  leftAssocOp (op : Expr) (as : List Sexp) : ParserM Expr := do
    let as ← as.mapM (parseTerm · >>= pure ∘ Prod.snd)
    return as.tail.foldl (mkApp2 op) as.head!
  rightAssocOp (op : Expr) (as : List Sexp) : ParserM Expr := do
    let as ← as.mapM (parseTerm · >>= pure ∘ Prod.snd)
    return as.dropLast.foldr (mkApp2 op) as.getLast!
  parseBinding (binding : Sexp) : ParserM (Sexp × Name × Expr × Expr) := do
    match binding with
    | sexp!{({n} {v})} =>
      let (t, v) ← parseTerm v
      return (n, smtSymbolToName n.serialize, t, v)
    | _ =>
      throwError m!"unsupported binding: {binding}"

def mkArrow (α β : Expr) : Expr :=
  Lean.mkForall .anonymous BinderInfo.default α β

def withDecls (decls : List Sexp) (k : ParserM Expr) : ParserM Expr := do
  let state ← get
  let mut decls ← decls.mapM parseDecl
  -- clear the cache if there's variable shadowing
  let clearCache := decls.any fun (_, n, _) => state.bvars.contains n
  let bvars := decls.foldl (fun bvs (_, n, t) => bvs.insert n (t, bvs.size)) state.bvars
  let cache := if clearCache then {} else state.cache
  set { bvars, cache : Parser.State }
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
      throwError m!"unsupported decl: {decl}"

def withDefs (defs : List Sexp) (k : ParserM Expr) : ParserM Expr := do
  let state ← get
  -- it's common for SMT-LIB queries to be "letified" using define-fun to
  -- minimize their size. We don't recurse on each definition to avoid stack
  -- overflows.
  let mut defs ← defs.mapM parseDef
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
      let bvars := ps.foldl (fun bvs (_, n, t) => bvs.insert n (t, bvs.size)) state.bvars
      let cache := if clearCache then {} else state.cache
      set { bvars, cache : Parser.State }
      let s ← parseSort s
      let (_, b) ← parseTerm b
      let nn := smtSymbolToName n.serialize
      let bvars := state.bvars.insert nn (s, state.bvars.size)
      let cache := if state.bvars.contains nn then {} else state.cache
      set { bvars, cache : Parser.State }
      let t := ps.foldr (fun (_, n, t) b => .forallE n t b .default) s
      let v := ps.foldr (fun (_, n, t) b => .lam n t b .default) b
      return (n, nn, t, v)
    | _ =>
      throwError m!"unsupported def: {defs}"
  parseParam (p : Sexp) : ParserM (Sexp × Name × Expr) := do
    match p with
    | sexp!{({n} {s})} =>
      return (n, smtSymbolToName n.serialize, ← parseSort s)
    | _ => throwError m!"unsupported param: {p}"

def parseAssert : Sexp → ParserM Expr
  | sexp!{(assert {p})} =>
    parseTerm p >>= pure ∘ Prod.snd
  | s =>
    throwError m!"unsupported assert: {s}"

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
      let (f, as) := getAppFnAndArgs #[] e
      mkAppN (go scope f) (as.map (go scope))
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
      let p : Q(Bool) := conjs.tail.foldl (mkApp2 q(and)) conjs.head!
      return q((!$p) = true)
    catch e =>
      throwError "{e.toMessageData}\nfailed to parse query {repr (← get)}"
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

def parseSmt2Query (query : String) : MetaM Expr := do
  match Sexp.parseMany query with
  | Except.error e =>
    throwError s!"{e}"
  | Except.ok cmds =>
    let query := filterCmds cmds
    (parseQuery query).run' {}

end Parser
