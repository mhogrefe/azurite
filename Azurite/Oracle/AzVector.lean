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
import Azurite.AzNat.Instances
import Azurite.AzNat.ParsableElement
import Azurite.AzInt.Instances
import Azurite.AzInt.ParsableElement
import Azurite.Oracle.AzZMod
import Azurite.Oracle.AzZModPow2
import Azurite.AzZMod.Instances
import Azurite.AzZMod.ParsableElement
import Azurite.AzZModPow2.Instances
import Azurite.AzZModPow2.ParsableElement

/-!
# Checks for Malachite's `NaturalVector` and `IntegerVector`

The vector functions that `AzVector AzNat n` and `AzVector AzInt n` compute: the entrywise sum,
multiplication by a scalar, the dot product, the squared length, the zero and standard basis
vectors, indexing, and the string forms, which the two libraries share, and, for integer vectors,
the entrywise difference and negation and the cross product. For natural vectors, the modular
operations `mod_*` and `mod_power_of_2_*` are checked against `AzVector (AzZMod m) n` and
`AzVector (AzZModPow2 k) n`: the entrywise sum, difference, and negation, multiplication by a
scalar, the dot product, the squared length, and the cross product. Each check reads the vectors of a
line of Malachite's demo output, builds the `AzVector`s of their dimension, and compares Azurite's
result, rendered by its own `toString`, with what Malachite printed. The checks are generic in the
element type; each takes the parser of the elements' bodies and the elements themselves.
(`dotSign` has its checks in `Azurite.Oracle.AzNatExtra`.)
-/

namespace Azurite.Oracle

open Azurite

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

/-- Whether an operand, possibly borrowed, is a vector rather than a scalar. -/
def isVectorOperand (s : String) : Bool :=
  let t := trim s
  (if t.startsWith "&" then dropChars t 1 else t).startsWith "("

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

section Generic

variable {R : Type} [ParsableElement R]

/-- A vector as Malachite prints it, possibly borrowed: `(a, b, …)`, `&(a, b, …)`, or
`(&(a, b, …))`, read with the parser `body` of the elements between the parentheses. -/
def parseVectorWith (body : String → Option (List R)) (s : String) : Option (List R) := do
  let t := trim s
  let t := if t.startsWith "(&" && t.endsWith ")" then dropRightChars (dropChars t 2) 1 else t
  let t := trim (if t.startsWith "&" then dropChars t 1 else t)
  guard (isWrapped t '(' ')')
  body (dropRightChars (dropChars t 1) 1)

/-- Azurite's rendering of the vector with the given elements. -/
def renderVector (l : List R) : String :=
  toString (AzVector.ofList l rfl : AzVector R l.length)

/-- `x op y = z` for an entrywise operation on two vectors of the same dimension. -/
def checkVectorEntrywise (body : String → Option (List R)) (op : String)
    (f : (n : Nat) → AzVector R n → AzVector R n → AzVector R n) (line : String) : Verdict := do
  let (x, y, z) ← vectorBinaryLine line op
  let xs ← expect "x" (parseVectorWith body x)
  let ys ← expect "y" (parseVectorWith body y)
  if h : ys.length = xs.length then
    expectEq op (toString (f xs.length (AzVector.ofList xs rfl) (AzVector.ofList ys h))) (trim z)
  else
    disagree "the vectors have different dimensions"

/-- `v * c = z`, `c * v = z`, or `v := x; v *= c; v = z`: multiplication by a scalar, on either
side, which is `AzVector`'s `SMul`. -/
def checkVectorMulScalar [SMul R R] (body : String → Option (List R))
    (elem : String → Option R) (line : String) : Verdict := do
  let (x, y, z) ← vectorBinaryLine line "*"
  let (v, c) := if isVectorOperand x then (x, y) else (y, x)
  let xs ← expect "v" (parseVectorWith body v)
  let c ← expect "c" (elem (stripRef c))
  expectEq "mul" (toString (c • (AzVector.ofList xs rfl : AzVector R xs.length))) (trim z)

/-- `v.dot(w) = r`, with either operand borrowed. -/
def checkVectorDot [Mul R] [Add R] [Zero R] [BEq R] [ToString R]
    (body : String → Option (List R)) (elem : String → Option R) (line : String) : Verdict := do
  let (v, args, res) ← expect "a `v.dot(w) = r` line" (methodCall line "dot")
  let w ← match args with
    | [w] => pure w
    | _ => fail "dot takes one argument"
  let vs ← expect "v" (body v)
  let ws ← expect "w" (body w)
  let r ← expect "r" (elem res)
  if h : ws.length = vs.length then
    expectEq "dot" ((AzVector.ofList vs rfl : AzVector R vs.length).dot (AzVector.ofList ws h)) r
  else
    disagree "the vectors have different dimensions"

/-- `v.abs_squared() = r`, which is `AzVector.normSq`. -/
def checkVectorAbsSquared [Mul R] [Add R] [Zero R] [BEq R] [ToString R]
    (body : String → Option (List R)) (elem : String → Option R) (line : String) : Verdict := do
  let (v, args, res) ← expect "a `v.abs_squared() = r` line" (methodCall line "abs_squared")
  if !args.isEmpty then fail "abs_squared takes no arguments"
  let vs ← expect "v" (body v)
  let r ← expect "r" (elem res)
  expectEq "abs_squared" (AzVector.ofList vs rfl : AzVector R vs.length).normSq r

/-- `T::zero(d) = z`, for the type name `T`. -/
def checkVectorZero [Zero R] (typeName : String) (line : String) : Verdict := do
  let (args, res) ← expect s!"a `{typeName}::zero(d) = z` line"
    (functionCall line s!"{typeName}::zero")
  let d ← match args with
    | [d] => expect "d" (parseNat d)
    | _ => fail "zero takes one argument"
  expectEq "zero" (toString (0 : AzVector R d)) (trim res)

/-- `T::standard_basis_vector(d, i) = z`, which is `AzVector.stdBasis`. -/
def checkVectorStandardBasisVector [Zero R] [One R] (typeName : String) (line : String) :
    Verdict := do
  let (args, res) ← expect s!"a `{typeName}::standard_basis_vector(d, i) = z` line"
    (functionCall line s!"{typeName}::standard_basis_vector")
  let (d, i) ← match args with
    | [d, i] => do pure (← expect "d" (parseNat d), ← expect "i" (parseNat i))
    | _ => fail "standard_basis_vector takes two arguments"
  if h : i < d then
    expectEq "standard_basis_vector"
      (toString (AzVector.stdBasis (R := R) (n := d) ⟨i, h⟩)) (trim res)
  else
    disagree "the index is out of range"

/-- `v[i] = x`, which is `AzVector.get`. -/
def checkVectorIndex [BEq R] [ToString R] (body : String → Option (List R))
    (elem : String → Option R) (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `v[i] = x` line" (splitEquals line)
  match lhs.splitOn "[" with
  | [v, rest] =>
    if !rest.endsWith "]" then fail "not an index"
    let i ← expect "i" (parseNat (dropRightChars rest 1))
    let xs ← expect "v" (parseVectorWith body v)
    let x ← expect "x" (elem rhs)
    if h : i < xs.length then
      expectEq "index" ((AzVector.ofList xs rfl : AzVector R xs.length).get ⟨i, h⟩) x
    else
      disagree "the index is out of range"
  | _ => fail "not an index line"

/-- Malachite's documented `from_str` for its vectors: the elements separated by `", "` inside
parentheses, `()` for the 0-dimensional vector, and each element read by the element type's
`from_str` rule `elem`. -/
def malachiteParseVector (elem : String → Option R) (s : String) : Option (List R) :=
  if s.length ≥ 2 && s.startsWith "(" && s.endsWith ")" then
    let inner := dropRightChars (dropChars s 1) 1
    if inner.isEmpty then some [] else (inner.splitOn ", ").mapM elem
  else none

/-- `T::from_str(s) = Ok(v)` or `Err(())`, with `s` printed as a Rust string literal, for the type
name `T` and its element type's `from_str` rule `elem`. -/
def checkVectorFromStr (typeName : String) (elem : String → Option R) (line : String) :
    Verdict := do
  let (lhs, rhs) ← expect s!"a `{typeName}::from_str(s) = r` line" (splitEquals line)
  let pre := s!"{typeName}::from_str("
  if !(lhs.startsWith pre && lhs.endsWith ")") then fail "not a from_str call"
  let s ← expect "a string literal" (parseRustString (dropRightChars (dropChars lhs pre.length) 1))
  let expected := match malachiteParseVector elem s with
    | some l => s!"Ok({renderVector l})"
    | none => "Err(())"
  expectEq "from_str" expected (trim rhs)

end Generic

/-- A bare vector, as the `to_string` and `Debug` demos print it: Azurite's parser reads it with
the dimension its elements give, and its printer must reproduce it exactly. -/
def checkVectorToString (R : Type) [ParsableElement R] (line : String) : Verdict := do
  let t := trim line
  if !isWrapped t '(' ')' then fail "not a vector"
  let body := dropRightChars (dropChars t 1) 1
  let k := if body.isEmpty then 0 else (body.splitOn ", ").length
  let v ← expect "a vector" (AzVector.parseStr (R := R) (n := k) t)
  expectEq "to_string" (toString v) t

/-! ### `NaturalVector` -/

/-- `NaturalVector`'s `+` and `+=`. -/
def checkNatVectorAdd : String → Verdict :=
  checkVectorEntrywise parseNatVectorBody "+" fun _ v w => v + w

/-- `NaturalVector`'s multiplication by a `Natural`. -/
def checkNatVectorMulScalar : String → Verdict :=
  checkVectorMulScalar parseNatVectorBody parseAzNat

def checkNatVectorDot : String → Verdict := checkVectorDot parseNatVectorBody parseAzNat

def checkNatVectorAbsSquared : String → Verdict :=
  checkVectorAbsSquared parseNatVectorBody parseAzNat

def checkNatVectorZero : String → Verdict := checkVectorZero (R := AzNat) "NaturalVector"

def checkNatVectorStandardBasisVector : String → Verdict :=
  checkVectorStandardBasisVector (R := AzNat) "NaturalVector"

def checkNatVectorIndex : String → Verdict := checkVectorIndex parseNatVectorBody parseAzNat

def checkNatVectorToString : String → Verdict := checkVectorToString AzNat

/-- `NaturalVector::from_str`, each element read by `Natural::from_str`'s rule. -/
def checkNatVectorFromStr : String → Verdict :=
  checkVectorFromStr "NaturalVector" (malachiteParseBase 10)

/-! ### `IntegerVector` -/

/-- A vector of integers as Malachite prints it, possibly borrowed. -/
def parseIntVector : String → Option (List AzInt) := parseVectorWith parseIntVectorBody

/-- `IntegerVector`'s `+` and `+=`. -/
def checkIntVectorAdd : String → Verdict :=
  checkVectorEntrywise parseIntVectorBody "+" fun _ v w => v + w

/-- `IntegerVector`'s `-` and `-=`. -/
def checkIntVectorSub : String → Verdict :=
  checkVectorEntrywise parseIntVectorBody "-" fun _ v w => v - w

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

/-- `IntegerVector`'s multiplication by an `Integer`. -/
def checkIntVectorMulScalar : String → Verdict :=
  checkVectorMulScalar parseIntVectorBody parseAzInt

def checkIntVectorDot : String → Verdict := checkVectorDot parseIntVectorBody parseAzInt

def checkIntVectorAbsSquared : String → Verdict :=
  checkVectorAbsSquared parseIntVectorBody parseAzInt

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

def checkIntVectorZero : String → Verdict := checkVectorZero (R := AzInt) "IntegerVector"

def checkIntVectorStandardBasisVector : String → Verdict :=
  checkVectorStandardBasisVector (R := AzInt) "IntegerVector"

def checkIntVectorIndex : String → Verdict := checkVectorIndex parseIntVectorBody parseAzInt

def checkIntVectorToString : String → Verdict := checkVectorToString AzInt

/-- `IntegerVector::from_str`, each element read by `Integer::from_str`'s rule. -/
def checkIntVectorFromStr : String → Verdict :=
  checkVectorFromStr "IntegerVector" (malachiteParseInteger 10)

/-! ### Modular `NaturalVector` operations -/

/-- The modular vector operations Azurite's `AzVector` computes over a residue ring. -/
inductive ModVectorOp
  | add | sub | neg | mul | dot | absSquared | cross

/-- The operation's name in Malachite, after the `mod_` or `mod_power_of_2_` prefix. -/
def ModVectorOp.suffix : ModVectorOp → String
  | .add => "add" | .sub => "sub" | .neg => "neg" | .mul => "mul" | .dot => "dot"
  | .absSquared => "abs_squared" | .cross => "cross"

/-- Takes apart `x.f(a, …) = z`, with the receiver and arguments possibly borrowed, or the
in-place form `v := x; v.f_assign(a, …); v = z`, returning the receiver, the arguments, and the
result. -/
def modVectorCall (line method : String) : Except Failure (String × List String × String) := do
  if line.startsWith "v := " then
    match line.splitOn "; " with
    | [a, b, c] =>
      let pre := s!"v.{method}_assign("
      if !(b.startsWith pre && b.endsWith ")" && c.startsWith "v = ") then
        fail "not an assignment line"
      pure (stripRef (dropChars a 5), splitArgs (dropRightChars (dropChars b pre.length) 1),
        trim (dropChars c 4))
    | _ => fail "not an assignment line"
  else
    expect s!"an `x.{method}(…) = z` line" (methodCall line method)

section Modular

variable (R : Type) [CommRing R] [ParsableElement R]

/-- The elements of a natural vector, possibly borrowed and then wrapped once more (as in
`(&((a, b)))`), as residues read by `res`, which rejects unreduced ones. -/
def vectorResidues (res : String → AzNat → Except Failure R) (what s : String) :
    Except Failure (List R) := do
  let xs ← expect what (parseNatVectorBody (unwrapParens (stripRef s)))
  xs.mapM (res what)

/-- A modular vector operation over the residue ring `R`, whose reduced residues `res` reads and
whose values `val` gives: the receiver `v`, the arguments before the modulus, and the printed
result `z`. -/
def checkModVectorIn (res : String → AzNat → Except Failure R) (val : R → AzNat) (name : String)
    (op : ModVectorOp) (v : String) (args : List String) (z : String) : Verdict := do
  let xs ← vectorResidues R res "v" v
  let x : AzVector R xs.length := AzVector.ofList xs rfl
  let other (w : String) : Except Failure (AzVector R xs.length) := do
    let ys ← vectorResidues R res "w" w
    if h : ys.length = xs.length then pure (AzVector.ofList ys h)
    else disagree "the vectors have different dimensions"
  match op, args with
  | .add, [w] => expectEq name (toString (x + (← other w))) (trim z)
  | .sub, [w] => expectEq name (toString (x - (← other w))) (trim z)
  | .neg, [] => expectEq name (toString (-x)) (trim z)
  | .mul, [c] => do
    let c ← res "c" (← expect "c" (parseAzNat c))
    expectEq name (toString (c • x)) (trim z)
  | .dot, [w] => expectEq name (val (x.dot (← other w))) (← expect "z" (parseAzNat z))
  | .absSquared, [] => expectEq name (val x.normSq) (← expect "z" (parseAzNat z))
  | .cross, [w] => do
    let y ← other w
    if h : xs.length = 3 then
      expectEq name (toString ((h ▸ x : AzVector R 3).cross (h ▸ y))) (trim z)
    else
      disagree "the cross product needs two 3-dimensional vectors"
  | _, _ => fail s!"wrong number of arguments to {name}"

end Modular

/-- `NaturalVector`'s `mod_*` operations (`pow2 = false`), against `AzVector (AzZMod m) n`, and
its `mod_power_of_2_*` operations (`pow2 = true`), against `AzVector (AzZModPow2 k) n`. The
modulus is the last argument; the inputs must be reduced. -/
def checkNatVectorMod (pow2 : Bool) (op : ModVectorOp) (line : String) : Verdict := do
  let name := (if pow2 then "mod_power_of_2_" else "mod_") ++ op.suffix
  let (v, args, z) ← modVectorCall line name
  let (args, modArg) ← match args.reverse with
    | m :: rest => pure (rest.reverse, m)
    | [] => fail "the modulus is missing"
  if pow2 then
    let k ← expect "k" (parseNat modArg)
    checkModVectorIn (AzZModPow2 k) (residue k) AzZModPow2.val name op v args z
  else
    let m ← expect "m" (parseAzNat modArg)
    let hm ← modulus m
    have : NeZero m.toNat := hm.down
    checkModVectorIn (AzZMod m) (residueMod m) AzZMod.val name op v args z

end Azurite.Oracle
