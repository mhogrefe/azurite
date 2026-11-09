/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/
import Azurite.Oracle.AzNatExtra
import Azurite.AzVector.Operations
import Azurite.AzVector.Dot
import Azurite.AzVector.Cross
import Azurite.AzVector.Basis
import Azurite.AzVector.Parse
import Azurite.AzInt.Instances
import Azurite.AzInt.ParsableElement

/-!
# Checks for Malachite's `IntegerVector`

The `IntegerVector` functions that `AzVector AzInt n` computes: the entrywise sum, difference, and
negation, multiplication by a scalar, the dot product, the squared length, the cross product, the
zero and standard basis vectors, indexing, and the string forms, which the two libraries share.
Each check reads a vector of Malachite's demo output, builds the `AzVector` of its dimension, and
compares Azurite's result, rendered by its own `toString`, with the line Malachite printed.
(`dotSign` has its check in `Azurite.Oracle.AzNatExtra`.)
-/

namespace Azurite.Oracle

open Azurite

/-- A vector of integers as Malachite prints it, possibly borrowed: `(a, b, …)`, `&(a, b, …)`, or
`(&(a, b, …))`. -/
def parseIntVector (s : String) : Option (List AzInt) := do
  let t := trim s
  let t := if t.startsWith "(&" && t.endsWith ")" then dropRightChars (dropChars t 2) 1 else t
  let t := trim (if t.startsWith "&" then dropChars t 1 else t)
  guard (isWrapped t '(' ')')
  parseIntVectorBody (dropRightChars (dropChars t 1) 1)

/-- Azurite's rendering of the vector with the given elements. -/
def renderIntVector (l : List AzInt) : String :=
  toString (AzVector.ofList l rfl : AzVector AzInt l.length)

/-- The operands and result of an entrywise operation, from the by-value and by-reference forms
`x op y = z` and from the in-place form `v := x; v op= y; v = z`. -/
def vectorBinaryLine (line op : String) : Except Failure (String × String × String) := do
  if line.startsWith "v := " then
    match line.splitOn "; " with
    | [a, b, c] =>
      let pre := s!"v {op}= "
      if !(b.startsWith pre && c.startsWith "v = ") then fail "not an assignment line"
      pure (dropChars a 5, dropChars b pre.length, dropChars c 4)
    | _ => fail "not an assignment line"
  else
    let (lhs, rhs) ← expect s!"an `x {op} y = z` line" (splitEquals line)
    match lhs.splitOn s!" {op} " with
    | [x, y] => pure (x, y, rhs)
    | _ => fail s!"not an `x {op} y` line"

/-- `x op y = z` for an entrywise operation on two vectors of the same dimension. -/
def checkIntVectorEntrywise (op : String)
    (f : (n : Nat) → AzVector AzInt n → AzVector AzInt n → AzVector AzInt n) (line : String) :
    Verdict := do
  let (x, y, z) ← vectorBinaryLine line op
  let xs ← expect "x" (parseIntVector x)
  let ys ← expect "y" (parseIntVector y)
  if h : ys.length = xs.length then
    expectEq op (toString (f xs.length (AzVector.ofList xs rfl) (AzVector.ofList ys h))) (trim z)
  else
    disagree "the vectors have different dimensions"

/-- `IntegerVector`'s `+` and `+=`. -/
def checkIntVectorAdd : String → Verdict := checkIntVectorEntrywise "+" fun _ v w => v + w

/-- `IntegerVector`'s `-` and `-=`. -/
def checkIntVectorSub : String → Verdict := checkIntVectorEntrywise "-" fun _ v w => v - w

/-- `-(x) = z`, `-&(x) = z`, or `v := x; v.neg_assign(); v = z`. -/
def checkIntVectorNeg (line : String) : Verdict := do
  let (x, z) ← if line.startsWith "v := " then
      match line.splitOn "; " with
      | [a, b, c] =>
        if !(b == "v.neg_assign()" && c.startsWith "v = ") then fail "not an assignment line"
        pure (dropChars a 5, dropChars c 4)
      | _ => fail "not an assignment line"
    else do
      let (lhs, rhs) ← expect "a `-(x) = z` line" (splitEquals line)
      if lhs.startsWith "-&(" && lhs.endsWith ")" then
        pure (dropRightChars (dropChars lhs 3) 1, rhs)
      else if lhs.startsWith "-(" && lhs.endsWith ")" then
        pure (dropRightChars (dropChars lhs 2) 1, rhs)
      else fail "not a negation"
  let xs ← expect "x" (parseIntVector x)
  expectEq "neg" (toString (-(AzVector.ofList xs rfl : AzVector AzInt xs.length))) (trim z)

/-- Whether an operand, possibly borrowed, is a vector rather than a scalar. -/
def isVectorOperand (s : String) : Bool :=
  let t := trim s
  (if t.startsWith "&" then dropChars t 1 else t).startsWith "("

/-- `v * c = z`, `c * v = z`, or `v := x; v *= c; v = z`: multiplication by an `Integer`, on
either side, which is `AzVector`'s `SMul`. -/
def checkIntVectorMulScalar (line : String) : Verdict := do
  let (x, y, z) ← vectorBinaryLine line "*"
  let (v, c) := if isVectorOperand x then (x, y) else (y, x)
  let xs ← expect "v" (parseIntVector v)
  let c ← expect "c" (parseAzInt (stripRef c))
  expectEq "mul" (toString (c • (AzVector.ofList xs rfl : AzVector AzInt xs.length))) (trim z)

/-- `v.dot(w) = r`, with either operand borrowed. -/
def checkIntVectorDot (line : String) : Verdict := do
  let (v, args, res) ← expect "a `v.dot(w) = r` line" (methodCall line "dot")
  let w ← match args with
    | [w] => pure w
    | _ => fail "dot takes one argument"
  let vs ← expect "v" (parseIntVectorBody v)
  let ws ← expect "w" (parseIntVectorBody w)
  let r ← expect "r" (parseAzInt res)
  if h : ws.length = vs.length then
    expectEq "dot"
      ((AzVector.ofList vs rfl : AzVector AzInt vs.length).dot (AzVector.ofList ws h)) r
  else
    disagree "the vectors have different dimensions"

/-- `v.abs_squared() = r`, which is `AzVector.normSq`. -/
def checkIntVectorAbsSquared (line : String) : Verdict := do
  let (v, args, res) ← expect "a `v.abs_squared() = r` line" (methodCall line "abs_squared")
  if !args.isEmpty then fail "abs_squared takes no arguments"
  let vs ← expect "v" (parseIntVectorBody v)
  let r ← expect "r" (parseAzInt res)
  expectEq "abs_squared" (AzVector.ofList vs rfl : AzVector AzInt vs.length).normSq r

/-- `v.cross(w) = z`, with either operand borrowed, or `v := x; v.cross_assign(w); v = z`. -/
def checkIntVectorCross (line : String) : Verdict := do
  let (x, y, z) ← if line.startsWith "v := " then
      match line.splitOn "; " with
      | [a, b, c] =>
        let pre := "v.cross_assign("
        if !(b.startsWith pre && b.endsWith ")" && c.startsWith "v = ") then
          fail "not an assignment line"
        pure (dropChars a 5, dropRightChars (dropChars b pre.length) 1, dropChars c 4)
      | _ => fail "not an assignment line"
    else do
      let (v, args, res) ← expect "a `v.cross(w) = z` line" (methodCall line "cross")
      match args with
      | [w] => pure (s!"({v})", s!"({w})", res)
      | _ => fail "cross takes one argument"
  let xs ← expect "x" (parseIntVector x)
  let ys ← expect "y" (parseIntVector y)
  if h : xs.length = 3 ∧ ys.length = 3 then
    let v : AzVector AzInt 3 := AzVector.ofList xs h.1
    let w : AzVector AzInt 3 := AzVector.ofList ys h.2
    expectEq "cross" (toString (v.cross w)) (trim z)
  else
    disagree "the cross product needs two 3-dimensional vectors"

/-- `IntegerVector::zero(d) = z`. -/
def checkIntVectorZero (line : String) : Verdict := do
  let (args, res) ← expect "an `IntegerVector::zero(d) = z` line"
    (functionCall line "IntegerVector::zero")
  let d ← match args with
    | [d] => expect "d" (parseNat d)
    | _ => fail "zero takes one argument"
  expectEq "zero" (toString (0 : AzVector AzInt d)) (trim res)

/-- `IntegerVector::standard_basis_vector(d, i) = z`, which is `AzVector.stdBasis`. -/
def checkIntVectorStandardBasisVector (line : String) : Verdict := do
  let (args, res) ← expect "an `IntegerVector::standard_basis_vector(d, i) = z` line"
    (functionCall line "IntegerVector::standard_basis_vector")
  let (d, i) ← match args with
    | [d, i] => do pure (← expect "d" (parseNat d), ← expect "i" (parseNat i))
    | _ => fail "standard_basis_vector takes two arguments"
  if h : i < d then
    expectEq "standard_basis_vector"
      (toString (AzVector.stdBasis (R := AzInt) (n := d) ⟨i, h⟩)) (trim res)
  else
    disagree "the index is out of range"

/-- `v[i] = x`, which is `AzVector.get`. -/
def checkIntVectorIndex (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `v[i] = x` line" (splitEquals line)
  match lhs.splitOn "[" with
  | [v, rest] =>
    if !rest.endsWith "]" then fail "not an index"
    let i ← expect "i" (parseNat (dropRightChars rest 1))
    let xs ← expect "v" (parseIntVector v)
    let x ← expect "x" (parseAzInt rhs)
    if h : i < xs.length then
      expectEq "index" ((AzVector.ofList xs rfl : AzVector AzInt xs.length).get ⟨i, h⟩) x
    else
      disagree "the index is out of range"
  | _ => fail "not an index line"

/-- A bare vector, as the `to_string` and `Debug` demos print it: Azurite's parser reads it with
the dimension its elements give, and its printer must reproduce it exactly. -/
def checkIntVectorToString (line : String) : Verdict := do
  let t := trim line
  if !isWrapped t '(' ')' then fail "not a vector"
  let body := dropRightChars (dropChars t 1) 1
  let k := if body.isEmpty then 0 else (body.splitOn ", ").length
  let v ← expect "a vector" (AzVector.parseStr (R := AzInt) (n := k) t)
  expectEq "to_string" (toString v) t

/-- The characters of a string written as Rust's `Debug` writes one, without the quotes: the
escapes `\\`, `\"`, `\'`, `\n`, `\r`, `\t`, `\0`, and `\u{…}`. -/
partial def rustUnescapeChars : List Char → Option (List Char)
  | [] => some []
  | '\\' :: 'n' :: r => ('\n' :: ·) <$> rustUnescapeChars r
  | '\\' :: 'r' :: r => ('\r' :: ·) <$> rustUnescapeChars r
  | '\\' :: 't' :: r => ('\t' :: ·) <$> rustUnescapeChars r
  | '\\' :: '0' :: r => (Char.ofNat 0 :: ·) <$> rustUnescapeChars r
  | '\\' :: '\\' :: r => ('\\' :: ·) <$> rustUnescapeChars r
  | '\\' :: '"' :: r => ('"' :: ·) <$> rustUnescapeChars r
  | '\\' :: '\'' :: r => ('\'' :: ·) <$> rustUnescapeChars r
  | '\\' :: 'u' :: '{' :: r =>
    let hex := r.takeWhile (· != '}')
    match r.drop hex.length with
    | '}' :: rest => do
      let digits ← hex.mapM fun c =>
        if c.isDigit then some (c.toNat - '0'.toNat)
        else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
        else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
        else none
      guard (!digits.isEmpty)
      let code := digits.foldl (fun acc d => acc * 16 + d) 0
      (Char.ofNat code :: ·) <$> rustUnescapeChars rest
    | _ => none
  | '\\' :: _ => none
  | c :: r => (c :: ·) <$> rustUnescapeChars r

/-- A string literal as Rust's `Debug` prints it, quotes included. -/
def parseRustString (s : String) : Option String := do
  let t := trim s
  guard (t.length ≥ 2 && t.startsWith "\"" && t.endsWith "\"")
  String.ofList <$> rustUnescapeChars (dropRightChars (dropChars t 1) 1).toList

/-- Malachite's documented `IntegerVector::from_str`: the elements separated by `", "` inside
parentheses, `()` for the 0-dimensional vector, and each element read by `Integer::from_str`. -/
def malachiteParseIntegerVector (s : String) : Option (List AzInt) :=
  if s.length ≥ 2 && s.startsWith "(" && s.endsWith ")" then
    let inner := dropRightChars (dropChars s 1) 1
    if inner.isEmpty then some [] else (inner.splitOn ", ").mapM (malachiteParseInteger 10)
  else none

/-- `IntegerVector::from_str(s) = Ok(v)` or `Err(())`, with `s` printed as a Rust string literal. -/
def checkIntVectorFromStr (line : String) : Verdict := do
  let (lhs, rhs) ← expect "an `IntegerVector::from_str(s) = r` line" (splitEquals line)
  let pre := "IntegerVector::from_str("
  if !(lhs.startsWith pre && lhs.endsWith ")") then fail "not a from_str call"
  let s ← expect "a string literal" (parseRustString (dropRightChars (dropChars lhs pre.length) 1))
  let expected := match malachiteParseIntegerVector s with
    | some l => s!"Ok({renderIntVector l})"
    | none => "Err(())"
  expectEq "from_str" expected (trim rhs)

end Azurite.Oracle
