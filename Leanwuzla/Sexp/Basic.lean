/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
Source: https://github.com/ufmg-smite/lean-smt/blob/main/Smt/Data/Sexp.lean
-/

import Std.Internal.Parsec.String

/-- The type of S-expressions. -/
inductive Sexp where
  | atom : String → Sexp
  | expr : List Sexp → Sexp
deriving Repr, BEq, Inhabited, Hashable

class ToSexp (α : Type u) where
  toSexp : α → Sexp

namespace Sexp

def isAtom : Sexp → Bool
  | atom _ => true
  | _      => false

def isExpr : Sexp → Bool
  | expr _ => true
  | _      => false

partial def serialize : Sexp → String
  | atom s  => s
  | expr ss => "(" ++ (" ".intercalate <| ss.map serialize) ++ ")"

def serializeMany (ss : List Sexp) : String :=
  ss.map serialize |> "\n".intercalate

instance : ToString Sexp :=
  ⟨serialize⟩

inductive ParseError where
  | /-- Incomplete input, for example missing a closing parenthesis. -/
    incomplete (msg : String)
  | /-- Malformed input, for example having too many closing parentheses. -/
    malformed (msg : String)

instance : ToString ParseError where
  toString
    | .incomplete msg => s!"incomplete input: {msg}"
    | .malformed msg  => s!"malformed input: {msg}"

/-- Tokenize `s` with the s-expression grammar. Supported token kinds are more or less as in
https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf:
- parentheses `(`/`)`
- symbols `abc`
- quoted symbols `|abc|`
- string literals `"abc"` -/
partial def tokenize (s : Substring) : Except ParseError (Array Substring) :=
  go #[] s
where go (stk : Array Substring) (s : Substring) :=
  -- Note: not written using `do` notation to ensure tail-call recursion
  if s.isEmpty then .ok stk
  else
    let c := s.front
    if c == '"' || c == '|' then
      let s1 := s.drop 1 |>.takeWhile (· ≠ c)
      if s1.stopPos = s.stopPos then
        throw <| .incomplete s!"ending {c} missing after {s1}"
      else
        let s1 := ⟨s.str, s.startPos, s.next s1.stopPos⟩
        let s2 := ⟨s.str, s1.stopPos, s.stopPos⟩
        go (stk.push s1) s2
    else if c == ';' then
      go stk (s.dropWhile (· ≠ '\n'))
    else if c == ')' || c == '(' then
      go (stk.push <| s.take 1) (s.drop 1)
    else if c.isWhitespace then
      go stk (s.drop 1)
    else
      let tk := s.takeWhile fun c =>
        !c.isWhitespace && c != '(' && c != ')' && c != '|' && c != '"' && c != ';'
      -- assertion: tk.bsize > 0 as otherwise we would have gone into one of the branches above
      go (stk.push tk) (s.extract ⟨tk.bsize⟩ ⟨s.bsize⟩)

def parseManyAux (tks : Array Substring) : Except ParseError (List Sexp) := do
  let mut stack : List (List Sexp) := []
  let mut curr := []
  for tk in tks do
    if tk.front == '(' then
      stack := curr :: stack
      curr := []
    else if tk.front == ')' then
      match stack with
      | [] => throw <| .malformed "unexpected ')'"
      | sexp :: sexps =>
        curr := expr curr.reverse :: sexp
        stack := sexps
    else
      curr := atom tk.toString :: curr
  if !stack.isEmpty then
    throw <| .incomplete "expected ')'"
  return curr.reverse

def parseOneAux (tks : Array Substring) : Except ParseError Sexp := do
  if h : tks.size = 0 then
    throw <| .incomplete "expected a token, got none"
  else if tks.size = 1 then
    if tks[0].front == '(' then
      throw <| .incomplete "expected ')'"
    if tks[0].front == ')' then
      throw <| .malformed "unexpected ')'"
    return atom tks[0].toString
  else
    if tks[0].front != '(' then
      throw <| .malformed "expected '('"
    if tks[tks.size - 1].front != ')' then
      throw <| .incomplete "expected ')'"
    return expr (← parseManyAux tks[1:tks.size - 1])

/-- Parse all the s-expressions in the given string. For example, `"(abc) (def)"` contains two. -/
def parseMany (s : String) : Except ParseError (List Sexp) := do
  let tks ← tokenize s.toSubstring
  let sexps ← parseManyAux tks
  return sexps

/-- Parse a single s-expression. Note that the string may contain extra data, but parsing will
succeed as soon as the single s-exp is complete. -/
def parseOne (s : String) : Except ParseError Sexp := do
  let tks ← tokenize s.toSubstring
  let sexp ← parseOneAux tks
  return sexp

end Sexp
