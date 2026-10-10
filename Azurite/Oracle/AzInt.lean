/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Oracle.AzNat
import Azurite.AzInt.Add
import Azurite.AzInt.Sub
import Azurite.AzInt.Mul
import Azurite.AzInt.DivMod
import Azurite.AzInt.DivRound
import Azurite.AzInt.ExactDiv
import Azurite.AzInt.ExtendedGcd
import Azurite.AzInt.NormalizedGcd
import Azurite.AzInt.Pow
import Azurite.AzInt.Pow2
import Azurite.AzInt.LowMask
import Azurite.AzInt.Parity
import Azurite.AzInt.Size
import Azurite.AzInt.TrailingZeros
import Azurite.AzInt.ShiftLeft
import Azurite.AzInt.ShiftRight
import Azurite.AzInt.ShiftRightRound
import Azurite.AzInt.Compare
import Azurite.AzInt.Conversion
import Azurite.AzInt.ToString
import Azurite.AzInt.SumProduct

/-!
# Checks for Malachite's `Integer` against `AzInt`

One check per line shape that an `Integer` demo prints, as `Azurite.Oracle.AzNat` has for the
`Natural` demos. The correspondence between the two libraries' operations, and the conventions
these checks encode (Malachite's truncating `/` against Azurite's Euclidean one, so the Euclidean
and floor families are checked by name; `Exact` rounding; the normalization of Malachite's Bézout
coefficients), are documented on Malachite's "Malachite for Azurite Users: Integers" page.
-/

namespace Azurite.Oracle

open Azurite

/-! ### Operators -/

/-- `x op y = z` for an infix operator on two integers. -/
def checkIntBinaryOp (op : String) (f : AzInt → AzInt → AzInt) (line : String) : Verdict := do
  let (x, y, z) ← expect s!"an `x {op} y = z` line" (binaryOp line op)
  let x ← expect "x" (parseAzInt x)
  let y ← expect "y" (parseAzInt y)
  let z ← expect "z" (parseAzInt z)
  expectEq s!"x {op} y" (f x y) z

/-- `recv.method(arg) = result`, with one integer argument and an integer result. -/
def checkIntMethod (method : String) (f : AzInt → AzInt → AzInt) (line : String) : Verdict := do
  let (x, args, res) ← expect s!"an `x.{method}(y) = z` line" (methodCall line method)
  let y ← match args with
    | [y] => pure y
    | _ => fail s!"{method} takes one argument"
  let x ← expect "x" (parseAzInt x)
  let y ← expect "y" (parseAzInt y)
  let z ← expect "result" (parseAzInt res)
  expectEq method (f x y) z

/-- `recv.method(y) = (a, b)`, with one integer argument and a pair of integers as the result. -/
def checkIntMethodPair (method : String) (f : AzInt → AzInt → AzInt × AzInt) (line : String) :
    Verdict := do
  let (x, args, res) ← expect s!"an `x.{method}(y) = (a, b)` line" (methodCall line method)
  let y ← match args with
    | [y] => pure y
    | _ => fail s!"{method} takes one argument"
  let x ← expect "x" (parseAzInt x)
  let y ← expect "y" (parseAzInt y)
  let (a, b) ← expect "(a, b)" (parseTuple2 res)
  let a ← expect "first component" (parseAzInt a)
  let b ← expect "second component" (parseAzInt b)
  let (fa, fb) := f x y
  expectEq method s!"({fa}, {fb})" s!"({a}, {b})"

def checkIntAdd : String → Verdict := checkIntBinaryOp "+" AzInt.add

def checkIntSub : String → Verdict := checkIntBinaryOp "-" AzInt.sub

def checkIntMul : String → Verdict := checkIntBinaryOp "*" AzInt.mul

/-- `-x = z`, or `-(&x) = z` from the by-reference demo; the printed `x` may itself be negative,
giving `--5 = 5`. -/
def checkIntNeg (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `-x = z` line" (splitEquals line)
  if !lhs.startsWith "-" then fail "not a negation"
  let x ← expect "x" (parseAzInt (stripRef (dropChars lhs 1)))
  let z ← expect "z" (parseAzInt rhs)
  expectEq "neg" (AzInt.neg x) z

/-! ### Division -/

/-- Malachite's Euclidean division is Azurite's `div`/`mod`: the remainder is nonnegative. -/
def checkIntDivEuclidean : String → Verdict := checkIntMethod "div_euclidean" AzInt.ediv

def checkIntModEuclidean : String → Verdict := checkIntMethod "mod_euclidean" AzInt.emod

def checkIntDivModEuclidean : String → Verdict :=
  checkIntMethodPair "div_mod_euclidean" AzInt.edivMod

/-- Malachite's `div_mod` and `mod_op` floor the quotient, as `fdivMod` and `fmod` do. -/
def checkIntDivMod : String → Verdict := checkIntMethodPair "div_mod" AzInt.fdivMod

def checkIntMod : String → Verdict := checkIntMethod "mod_op" AzInt.fmod

/-- `div_exact` assumes the division is exact, as the `ExactDiv` instance does. -/
def checkIntDivExact : String → Verdict :=
  checkIntMethod "div_exact" fun x y => ExactDiv.exactDiv x y

/-- The division `x / y` rounded with `rm`, with its ordering against the exact quotient. Under
`Exact`, Malachite only prints a line when the division is exact. -/
def roundedIntDiv (x y : AzInt) : Rounding → Except Failure (AzInt × Ordering)
  | .mode m => pure (AzInt.divRound x y m)
  | .exact =>
    if AzInt.emod x y == (0 : AzInt) then pure (AzInt.ediv x y, .eq)
    else disagree "Malachite printed an Exact division that is not exact"

def checkIntDivRound (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.div_round(y, rm) = (q, o)` line"
    (methodCall line "div_round")
  let (y, rm) ← match args with
    | [y, rm] => pure (y, rm)
    | _ => fail "div_round takes two arguments"
  let x ← expect "x" (parseAzInt x)
  let y ← expect "y" (parseAzInt y)
  let rm ← expect "rounding mode" (parseRounding rm)
  let (q, o) ← expect "(quotient, ordering)" (parseTuple2 res)
  let q ← expect "quotient" (parseAzInt q)
  let o ← expect "ordering" (parseOrdering o)
  let (aq, ao) ← roundedIntDiv x y rm
  expectEq "div_round" (pairString aq ao) (pairString q o)

/-! ### Shifts -/

/-- `x << sh = z`; a negative `sh` (from the signed demos) shifts right, flooring. -/
def checkIntShl (line : String) : Verdict := do
  let (x, sh, z) ← expect "an `x << sh = z` line" (binaryOp line "<<")
  let x ← expect "x" (parseAzInt x)
  let sh ← expect "shift" (parseInt sh)
  let z ← expect "z" (parseAzInt z)
  let shifted := if sh < 0 then AzInt.shiftRight x (-sh).toNat else AzInt.shiftLeft x sh.toNat
  expectEq "shl" shifted z

/-- `x >> sh = z`, flooring; a negative `sh` shifts left. -/
def checkIntShr (line : String) : Verdict := do
  let (x, sh, z) ← expect "an `x >> sh = z` line" (binaryOp line ">>")
  let x ← expect "x" (parseAzInt x)
  let sh ← expect "shift" (parseInt sh)
  let z ← expect "z" (parseAzInt z)
  let shifted := if sh < 0 then AzInt.shiftLeft x (-sh).toNat else AzInt.shiftRight x sh.toNat
  expectEq "shr" shifted z

/-- The shift `x >> sh` rounded with `rm`. A negative `sh` shifts left, exactly. -/
def roundedIntShr (x : AzInt) (sh : Int) : Rounding → Except Failure (AzInt × Ordering)
  | .mode m =>
    if sh < 0 then pure (AzInt.shiftLeft x (-sh).toNat, .eq)
    else pure (AzInt.shiftRightRound x m sh.toNat)
  | .exact =>
    if sh < 0 then pure (AzInt.shiftLeft x (-sh).toNat, .eq)
    else if AzNat.modPow2 x.abs sh.toNat == (0 : AzNat) then
      pure (AzInt.shiftRight x sh.toNat, .eq)
    else disagree "Malachite printed an Exact shift that is not exact"

def checkIntShrRound (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.shr_round(sh, rm) = (v, o)` line"
    (methodCall line "shr_round")
  let (sh, rm) ← match args with
    | [sh, rm] => pure (sh, rm)
    | _ => fail "shr_round takes two arguments"
  let x ← expect "x" (parseAzInt x)
  let sh ← expect "shift" (parseInt sh)
  let rm ← expect "rounding mode" (parseRounding rm)
  let (v, o) ← expect "(value, ordering)" (parseTuple2 res)
  let v ← expect "value" (parseAzInt v)
  let o ← expect "ordering" (parseOrdering o)
  let (av, ao) ← roundedIntShr x sh rm
  expectEq "shr_round" (pairString av ao) (pairString v o)

/-! ### Powers and GCD -/

def checkIntPow (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.pow(n) = z` line" (methodCall line "pow")
  let n ← match args with
    | [n] => pure n
    | _ => fail "pow takes one argument"
  let x ← expect "x" (parseAzInt x)
  let n ← expect "exponent" (parseNat n)
  let z ← expect "z" (parseAzInt res)
  expectEq "pow" (AzInt.pow x n) z

/-- `gcd` on integers is the nonnegative GCD of the magnitudes, the `NormalizedGcd` instance. -/
def checkIntGcd : String → Verdict := checkIntMethod "gcd" fun x y => NormalizedGcd.ngcd x y

/-- `x.extended_gcd(y) = (g, s, t)` for two naturals. Azurite's `egcd` computes the GCD and a
Bézout pair of its own, so the check is that the GCDs agree, that Malachite's pair satisfies
`s·x + t·y = g` in `AzInt` arithmetic, and that it is the pair Malachite's documentation
specifies: `(0, 0)` for two zeros, `(0, 1)` when `y` divides `x`, `(1, 0)` when `x` divides `y`,
and otherwise one with `|s| ≤ y / g` and `|t| ≤ x / g`. -/
def checkIntExtendedGcd (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.extended_gcd(y) = (g, s, t)` line"
    (methodCall line "extended_gcd")
  let y ← match args with
    | [y] => pure y
    | _ => fail "extended_gcd takes one argument"
  let x ← expect "x" (parseAzNat x)
  let y ← expect "y" (parseAzNat y)
  let (g, s, t) ← expect "(gcd, s, t)" (parseTuple3 res)
  let g ← expect "gcd" (parseAzNat g)
  let s ← expect "s" (parseAzInt s)
  let t ← expect "t" (parseAzInt t)
  let (ag, _, _) := AzInt.egcd x y
  if ag != g then disagree s!"gcd: Azurite computed {ag}, Malachite printed {g}"
  let combination := AzInt.add (AzInt.mul s x.toAzInt) (AzInt.mul t y.toAzInt)
  if combination != g.toAzInt then
    disagree s!"Bézout identity: {s}·{x} + {t}·{y} = {combination}, not {g}"
  let zero : AzNat := 0
  let expected : Option (AzInt × AzInt) :=
    if x == zero && y == zero then some (0, 0)
    else if AzNat.mod x y == zero then some (0, 1)
    else if AzNat.mod y x == zero then some (1, 0)
    else none
  match expected with
  | some (es, et) => expectEq "normalized Bézout pair" s!"({es}, {et})" s!"({s}, {t})"
  | none =>
    if AzNat.compare (AzNat.mul s.abs g) y == .gt || AzNat.compare (AzNat.mul t.abs g) x == .gt
    then disagree s!"the Bézout pair ({s}, {t}) is outside Malachite's bounds for ({x}, {y})"
    else pure ()

/-! ### Bits and predicates -/

def checkIntPowerOf2 (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `2^k = n` line" (splitEquals line)
  if !lhs.startsWith "2^" then fail "not a `2^k` left-hand side"
  let k ← expect "k" (parseNat (dropChars lhs 2))
  let n ← expect "n" (parseAzInt rhs)
  expectEq "power_of_2" (AzInt.pow2 k) n

/-- `Integer::low_mask(k) = n`. -/
def checkIntLowMask (line : String) : Verdict := do
  let (args, res) ← expect "an `Integer::low_mask(k) = n` line"
    (functionCall line "Integer::low_mask")
  let k ← match args with
    | [k] => pure k
    | _ => fail "low_mask takes one argument"
  let k ← expect "k" (parseNat k)
  let n ← expect "n" (parseAzInt res)
  expectEq "low_mask" (AzInt.lowMask k) n

/-- A predicate printed as `n<pos>` or `n<neg>`. -/
def checkIntPredicate (pos neg : String) (f : AzInt → Bool) (line : String) : Verdict := do
  let (n, expected) ←
    if line.endsWith neg then pure (dropRightChars line neg.length, false)
    else if line.endsWith pos then pure (dropRightChars line pos.length, true)
    else fail s!"not an `n{pos}` or `n{neg}` line"
  let n ← expect "n" (parseAzInt n)
  expectEq (trim pos) (f n) expected

def checkIntIsPowerOf2 : String → Verdict :=
  checkIntPredicate " is a power of 2" " is not a power of 2" AzInt.isPowerOfTwo

/-- The `even` and `odd` demos. -/
def checkIntParity (line : String) : Verdict :=
  if line.endsWith " even" then checkIntPredicate " is even" " is not even" AzInt.isEven line
  else checkIntPredicate " is odd" " is not odd" AzInt.isOdd line

/-- `n is negative`, `n is zero`, or `n is positive`. -/
def checkIntSign (line : String) : Verdict := do
  let (n, expected) ←
    if line.endsWith " is negative" then pure (dropRightChars line 12, Ordering.lt)
    else if line.endsWith " is zero" then pure (dropRightChars line 8, Ordering.eq)
    else if line.endsWith " is positive" then pure (dropRightChars line 12, Ordering.gt)
    else fail "not a sign line"
  let n ← expect "n" (parseAzInt n)
  expectEq "sign" (orderingName (AzInt.compare n 0)) (orderingName expected)

/-- `name(z) = result` with an integer argument. -/
def unaryIntFunction (line name : String) : Except Failure (AzInt × String) := do
  let (args, res) ← expect s!"a `{name}(z) = r` line" (functionCall line name)
  let z ← match args with
    | [z] => pure z
    | _ => fail s!"{name} takes one argument"
  let z ← expect "z" (parseAzInt z)
  pure (z, res)

def checkIntSignificantBits (line : String) : Verdict := do
  let (z, res) ← unaryIntFunction line "significant_bits"
  let bits ← expect "bits" (parseNat res)
  expectEq "significant_bits" (AzInt.size z) bits

def checkIntTrailingZeros (line : String) : Verdict := do
  let (z, res) ← unaryIntFunction line "trailing_zeros"
  let zeros ← expect "zeros" (parseOption res)
  let zeros ← match zeros with
    | some k => expect "zeros" ((parseNat k).map some)
    | none => pure none
  expectEq "trailing_zeros" (optionString (AzInt.trailingZeros z)) (optionString zeros)

/-! ### Strings -/

/-- Malachite's `Integer::from_string_base`: an optional single leading `-`, then the natural
rule (which allows a single `+`); `-+1` is rejected, and `-0` is zero. -/
def malachiteParseInteger (base : Nat) (s : String) : Option AzInt :=
  if s.startsWith "-" then
    let rest := dropChars s 1
    if rest.startsWith "+" then none
    else (malachiteParseBase base rest).map fun n => AzInt.neg n.toAzInt
  else (malachiteParseBase base s).map AzNat.toAzInt

/-- The result of an integer parsing demo: `Some(z)`/`None` (`from_string_base`), `Ok(z)`/`Err(())`
(`from_str`), or a bare `z` from the `_targeted` demos, whose inputs always parse. -/
def parsedInteger (rhs : String) : Except Failure (Option AzInt) := do
  let res ← match parseOption rhs, parseResult rhs with
    | some r, _ => pure r
    | _, some r => pure r
    | none, none => pure (some rhs)
  match res with
  | some z => expect "z" ((parseAzInt z).map some)
  | none => pure none

/-- `Integer::from_string_base(b, s) = Some(z)` or `None`. The string is printed bare, so it is
everything after the first comma; it never contains ` = `. -/
def checkIntFromStringBase (line : String) : Verdict := do
  let (lhs, rhs) ← expect "an `Integer::from_string_base(b, s) = r` line" (splitEquals line)
  let prefix_ := "Integer::from_string_base("
  if !(lhs.startsWith prefix_ && lhs.endsWith ")") then fail "not a from_string_base call"
  let inner := dropRightChars (dropChars lhs prefix_.length) 1
  let (b, s) ← match inner.splitOn ", " with
    | b :: rest@(_ :: _) => pure (b, ", ".intercalate rest)
    | _ => fail "from_string_base takes two arguments"
  let b ← expect "base" (parseNat b)
  let res ← parsedInteger rhs
  expectEq "from_string_base" (optionString (malachiteParseInteger b s)) (optionString res)

/-- `Integer::from_str(s) = Ok(z)` or `Err(())`: `from_string_base` in base 10. -/
def checkIntFromStr (line : String) : Verdict := do
  let (lhs, rhs) ← expect "an `Integer::from_str(s) = r` line" (splitEquals line)
  let prefix_ := "Integer::from_str("
  if !(lhs.startsWith prefix_ && lhs.endsWith ")") then fail "not a from_str call"
  let s := dropRightChars (dropChars lhs prefix_.length) 1
  let res ← parsedInteger rhs
  expectEq "from_str" (resultString (malachiteParseInteger 10 s)) (resultString res)

/-- A bare `z`, as the `to_string` demo prints it: the canonical decimal rendering, which
`parseAzInt` accepts and `toString` reproduces. -/
def checkIntToString (line : String) : Verdict := do
  let z ← expect "a decimal integer" (parseAzInt line)
  expectEq "to_string" (toString z) (trim line)

/-! ### Comparison -/

/-- The `x < y`, `x = y`, and `x > y` lines of a comparison demo, as strings. -/
def comparisonLine (line : String) : Except Failure (String × String × Ordering) :=
  match line.splitOn " < ", line.splitOn " > ", line.splitOn " = " with
  | [x, y], _, _ => pure (x, y, .lt)
  | _, [x, y], _ => pure (x, y, .gt)
  | _, _, [x, y] => pure (x, y, .eq)
  | _, _, _ => fail "not a comparison line"

/-- A machine unsigned integer, which fits in a `UInt64`. -/
def parseUInt64 (s : String) : Except Failure UInt64 := do
  let u ← expect "an unsigned integer" (parseNat s)
  if u ≥ 2 ^ 64 then fail "the value does not fit in a UInt64"
  pure (UInt64.ofNat u)

/-- A machine signed integer, which fits in an `Int64`. -/
def parseInt64 (s : String) : Except Failure Int64 := do
  let i ← expect "a signed integer" (parseInt s)
  if i < -(2 ^ 63) || i ≥ 2 ^ 63 then fail "the value does not fit in an Int64"
  pure (Int64.ofInt i)

def checkIntCmp (line : String) : Verdict := do
  let (x, y, o) ← comparisonLine line
  let x ← expect "x" (parseAzInt x)
  let y ← expect "y" (parseAzInt y)
  expectEq "cmp" (orderingName (AzInt.compare x y)) (orderingName o)

/-- An integer compared with a natural. -/
def checkIntCmpNatural (line : String) : Verdict := do
  let (x, y, o) ← comparisonLine line
  let x ← expect "x" (parseAzInt x)
  let y ← expect "y" (parseAzNat y)
  expectEq "partial_cmp" (orderingName (AzInt.compareAzNat x y)) (orderingName o)

/-- An integer compared with an unsigned machine integer. -/
def checkIntCmpUnsigned (line : String) : Verdict := do
  let (x, u, o) ← comparisonLine line
  let x ← expect "x" (parseAzInt x)
  let u ← parseUInt64 u
  expectEq "partial_cmp" (orderingName (AzInt.compareUInt64 x u)) (orderingName o)

/-- An integer compared with a signed machine integer. -/
def checkIntCmpSigned (line : String) : Verdict := do
  let (x, i, o) ← comparisonLine line
  let x ← expect "x" (parseAzInt x)
  let i ← parseInt64 i
  expectEq "partial_cmp" (orderingName (AzInt.compareInt64 x i)) (orderingName o)

/-- The `x = y` and `x ≠ y` lines of an equality demo, as strings. -/
def equalityLine (line : String) : Except Failure (String × String × Bool) :=
  match line.splitOn " ≠ ", line.splitOn " = " with
  | [x, y], _ => pure (x, y, false)
  | _, [x, y] => pure (x, y, true)
  | _, _ => fail "not an equality line"

def checkIntEq (line : String) : Verdict := do
  let (x, y, e) ← equalityLine line
  let x ← expect "x" (parseAzInt x)
  let y ← expect "y" (parseAzInt y)
  expectEq "eq" (x == y) e

def checkIntEqNatural (line : String) : Verdict := do
  let (x, y, e) ← equalityLine line
  let x ← expect "x" (parseAzInt x)
  let y ← expect "y" (parseAzNat y)
  expectEq "partial_eq" (AzInt.beqAzNat x y) e

def checkIntEqUnsigned (line : String) : Verdict := do
  let (x, u, e) ← equalityLine line
  let x ← expect "x" (parseAzInt x)
  let u ← parseUInt64 u
  expectEq "partial_eq" (AzInt.beqUInt64 x u) e

def checkIntEqSigned (line : String) : Verdict := do
  let (x, i, e) ← equalityLine line
  let x ← expect "x" (parseAzInt x)
  let i ← parseInt64 i
  expectEq "partial_eq" (AzInt.beqInt64 x i) e

/-! ### Construction and conversion -/

/-- The argument of `Integer::from(x) = z`, as a string. -/
def integerFromLine (line : String) : Except Failure (String × String) := do
  let (args, res) ← expect "an `Integer::from(x) = z` line" (functionCall line "Integer::from")
  match args with
  | [x] => pure (x, res)
  | _ => fail "Integer::from takes one argument"

/-- `Integer::from(n) = z` for a natural (also printed as `Integer::from(&n)`). -/
def checkIntFromNatural (line : String) : Verdict := do
  let (n, res) ← integerFromLine line
  let n ← expect "n" (parseAzNat n)
  let z ← expect "z" (parseAzInt res)
  expectEq "from" n.toAzInt z

/-- `Integer::from(u) = z` for an unsigned machine integer. -/
def checkIntFromUnsigned (line : String) : Verdict := do
  let (u, res) ← integerFromLine line
  let u ← parseUInt64 u
  let z ← expect "z" (parseAzInt res)
  expectEq "from" u.toAzInt z

/-- `Integer::from(i) = z` for a signed machine integer. -/
def checkIntFromSigned (line : String) : Verdict := do
  let (i, res) ← integerFromLine line
  let i ← parseInt64 i
  let z ← expect "z" (parseAzInt res)
  expectEq "from" i.toAzInt z

/-- `Integer::from_sign_and_abs(sign, abs) = z` (also the `_ref` variant): `mkNorm`. -/
def checkIntFromSignAndAbs (line : String) : Verdict := do
  let (args, res) ← expect "an `Integer::from_sign_and_abs(sign, abs) = z` line"
    ((functionCall line "Integer::from_sign_and_abs").orElse fun _ =>
      functionCall line "Integer::from_sign_and_abs_ref")
  let (sign, abs) ← match args with
    | [sign, abs] => pure (sign, abs)
    | _ => fail "from_sign_and_abs takes two arguments"
  let sign ← expect "sign" (parseBool sign)
  let abs ← expect "abs" (parseAzNat abs)
  let z ← expect "z" (parseAzInt res)
  expectEq "from_sign_and_abs" (AzInt.mkNorm sign abs) z

/-- `unsigned_abs(z) = n` (also `unsigned_abs(&z)`). -/
def checkIntUnsignedAbs (line : String) : Verdict := do
  let (z, res) ← unaryIntFunction line "unsigned_abs"
  let n ← expect "n" (parseAzNat res)
  expectEq "unsigned_abs" (AzInt.natAbs z) n

/-- `T::wrapping_from(&z) = v`, for a machine integer type `T`: the low bits of `z` in two's
complement, reinterpreted for the signed types. -/
def checkIntWrappingFrom (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `T::wrapping_from(&z) = v` line" (splitEquals line)
  let (t, rest) ← match lhs.splitOn "::wrapping_from(" with
    | [t, rest] => pure (t, rest)
    | _ => fail "not a wrapping_from call"
  if !rest.endsWith ")" then fail "not a wrapping_from call"
  let z ← expect "z" (parseAzInt (stripRef (dropRightChars rest 1)))
  let computed ← match t with
    | "u8" => pure (toString z.toUInt8)
    | "u16" => pure (toString z.toUInt16)
    | "u32" => pure (toString z.toUInt32)
    | "u64" => pure (toString z.toUInt64)
    | "usize" => pure (toString z.toUSize)
    | "i8" => pure (toString z.toInt8)
    | "i16" => pure (toString z.toInt16)
    | "i32" => pure (toString z.toInt32)
    | "i64" => pure (toString z.toInt64)
    | "isize" => pure (toString z.toISize)
    | _ => fail s!"no AzInt conversion to {t}"
  expectEq s!"{t}::wrapping_from" computed rhs

/-! ### Sums and products -/

/-- `name([x, …]) = r` for a fold `f` over a list of integers: Malachite's `Integer::sum` and
`Integer::product`, printed with the list they consumed. -/
def checkIntListFold (name : String) (f : List AzInt → AzInt) (line : String) : Verdict := do
  let (args, res) ← expect s!"a `{name}([x, …]) = r` line" (functionCall line name)
  let xs ← match args with
    | [xs] => pure xs
    | _ => fail s!"{name} takes one list"
  let xs ← expect "list" (parseList xs >>= fun l => l.mapM parseAzInt)
  let r ← expect "result" (parseAzInt res)
  expectEq name (f xs) r

def checkIntSum : String → Verdict := checkIntListFold "sum" AzInt.sum

def checkIntProduct : String → Verdict := checkIntListFold "product" AzInt.product

end Azurite.Oracle
