/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Oracle.Parse
import Azurite.AzNat.Add
import Azurite.AzNat.Sub
import Azurite.AzNat.Mul
import Azurite.AzNat.Div
import Azurite.AzNat.DivRound
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.ShiftRightRound
import Azurite.AzNat.Square
import Azurite.AzNat.Pow
import Azurite.AzNat.Gcd
import Azurite.AzNat.SqrtRem
import Azurite.AzNat.RootInt
import Azurite.AzNat.JacobiSym
import Azurite.AzNat.InvMod
import Azurite.AzNat.Garner
import Azurite.AzNat.ModPow2
import Azurite.AzNat.AddModPow2
import Azurite.AzNat.SubModPow2
import Azurite.AzNat.MulModPow2.Dispatch
import Azurite.AzNat.SquareModPow2.Dispatch
import Azurite.AzNat.Pow2
import Azurite.AzNat.IsMultipleOfPow2
import Azurite.AzNat.Size
import Azurite.AzNat.TrailingZeros
import Azurite.AzNat.LowMask
import Azurite.AzNat.Parity
import Azurite.AzNat.OfLimbs
import Azurite.AzNat.ToStringBase
import Azurite.AzNat.LimbDigits
import Azurite.AzNat.Compare
import Azurite.AzNat.NormalizedCompare
import Azurite.AzNat.Conversion

/-!
# Checks for Malachite's `Natural` against `AzNat`

One check per line shape that a `Natural` demo prints. Each takes a line, parses it, recomputes
the operation with `AzNat`, and reports agreement or the two values. The correspondence between
the two libraries' operations, and the conventions that make some of these checks adjust an input
(reduced residues, `Exact` rounding, Malachite's base-62 digits), are documented on Malachite's
"Malachite for Azurite Users: Naturals" page.
-/

namespace Azurite.Oracle

open Azurite

/-! ### Operators -/

/-- `x op y = z` for an infix operator on two naturals. -/
def checkBinaryOp (op : String) (f : AzNat → AzNat → AzNat) (line : String) : Verdict := do
  let (x, y, z) ← expect s!"an `x {op} y = z` line" (binaryOp line op)
  let x ← expect "x" (parseAzNat x)
  let y ← expect "y" (parseAzNat y)
  let z ← expect "z" (parseAzNat z)
  expectEq s!"x {op} y" (f x y) z

/-- `recv.method(arg) = result`, with one natural argument and a natural result. -/
def checkMethod (method : String) (f : AzNat → AzNat → AzNat) (line : String) : Verdict := do
  let (x, args, res) ← expect s!"an `x.{method}(y) = z` line" (methodCall line method)
  let y ← match args with
    | [y] => pure y
    | _ => fail s!"{method} takes one argument"
  let x ← expect "x" (parseAzNat x)
  let y ← expect "y" (parseAzNat y)
  let z ← expect "result" (parseAzNat res)
  expectEq method (f x y) z

/-- `recv.method(k) = result`, with one `Nat` argument and a natural result. -/
def checkMethodNat (method : String) (f : AzNat → Nat → AzNat) (line : String) : Verdict := do
  let (x, args, res) ← expect s!"an `x.{method}(k) = z` line" (methodCall line method)
  let k ← match args with
    | [k] => pure k
    | _ => fail s!"{method} takes one argument"
  let x ← expect "x" (parseAzNat x)
  let k ← expect "k" (parseNat k)
  let z ← expect "result" (parseAzNat res)
  expectEq method (f x k) z

def checkAdd : String → Verdict := checkBinaryOp "+" AzNat.add

/-- Malachite's `-` panics when the difference would be negative, so every printed line is a
difference `AzNat.sub` computes exactly. -/
def checkSub : String → Verdict := checkBinaryOp "-" AzNat.sub

/-- `saturating_sub` is the truncated subtraction `AzNat.sub` always performs. -/
def checkSaturatingSub : String → Verdict := checkMethod "saturating_sub" AzNat.sub

def checkMul : String → Verdict := checkBinaryOp "*" AzNat.mul

def checkDiv : String → Verdict := checkBinaryOp "/" AzNat.div

/-- `%` (the `rem` demos) and `mod_op` (the `mod` demos) coincide on naturals. -/
def checkMod (line : String) : Verdict :=
  match binaryOp line "%" with
  | some _ => checkBinaryOp "%" AzNat.mod line
  | none => checkMethod "mod_op" AzNat.mod line

/-- `x ^ 2 = z`. -/
def checkSquare (line : String) : Verdict := do
  let (x, two, z) ← expect "an `x ^ 2 = z` line" (binaryOp line "^")
  if two != "2" then fail "the exponent is not 2"
  let x ← expect "x" (parseAzNat x)
  let z ← expect "z" (parseAzNat z)
  expectEq "square" (AzNat.square x) z

def checkPow : String → Verdict := checkMethodNat "pow" AzNat.pow

/-! ### Division with remainder and rounding -/

/-- `div_mod` and `div_rem`, which coincide on naturals; the result is a `(quotient, remainder)`
pair. -/
def checkDivMod (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.div_mod(y) = (q, r)` line"
    ((methodCall line "div_mod").orElse fun _ => methodCall line "div_rem")
  let y ← match args with
    | [y] => pure y
    | _ => fail "div_mod takes one argument"
  let x ← expect "x" (parseAzNat x)
  let y ← expect "y" (parseAzNat y)
  let (q, r) ← expect "(quotient, remainder)" (parseTuple2 res)
  let q ← expect "quotient" (parseAzNat q)
  let r ← expect "remainder" (parseAzNat r)
  let (aq, ar) := AzNat.divMod x y
  expectEq "div_mod" s!"({aq}, {ar})" s!"({q}, {r})"

/-- The division `x / y` rounded with `rm`, with its ordering against the exact quotient. Under
`Exact`, Malachite only prints a line when the division is exact. -/
def roundedDiv (x y : AzNat) : Rounding → Except Failure (AzNat × Ordering)
  | .mode m => pure (AzNat.divRound x y m)
  | .exact =>
    if AzNat.mod x y == (0 : AzNat) then pure (AzNat.div x y, .eq)
    else disagree "Malachite printed an Exact division that is not exact"

def checkDivRound (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.div_round(y, rm) = (q, o)` line"
    (methodCall line "div_round")
  let (y, rm) ← match args with
    | [y, rm] => pure (y, rm)
    | _ => fail "div_round takes two arguments"
  let x ← expect "x" (parseAzNat x)
  let y ← expect "y" (parseAzNat y)
  let rm ← expect "rounding mode" (parseRounding rm)
  let (q, o) ← expect "(quotient, ordering)" (parseTuple2 res)
  let q ← expect "quotient" (parseAzNat q)
  let o ← expect "ordering" (parseOrdering o)
  let (aq, ao) ← roundedDiv x y rm
  expectEq "div_round" (pairString aq ao) (pairString q o)

/-- The shift `x >> sh` rounded with `rm`. A negative `sh` (from the signed demos) shifts left,
exactly. -/
def roundedShr (x : AzNat) (sh : Int) : Rounding → Except Failure (AzNat × Ordering)
  | .mode m =>
    if sh < 0 then pure (AzNat.shiftLeft x (-sh).toNat, .eq)
    else pure (AzNat.shiftRightRound x m sh.toNat)
  | .exact =>
    if sh < 0 then pure (AzNat.shiftLeft x (-sh).toNat, .eq)
    else if AzNat.modPow2 x sh.toNat == (0 : AzNat) then pure (AzNat.shiftRight x sh.toNat, .eq)
    else disagree "Malachite printed an Exact shift that is not exact"

def checkShrRound (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.shr_round(sh, rm) = (v, o)` line"
    (methodCall line "shr_round")
  let (sh, rm) ← match args with
    | [sh, rm] => pure (sh, rm)
    | _ => fail "shr_round takes two arguments"
  let x ← expect "x" (parseAzNat x)
  let sh ← expect "shift" (parseInt sh)
  let rm ← expect "rounding mode" (parseRounding rm)
  let (v, o) ← expect "(value, ordering)" (parseTuple2 res)
  let v ← expect "value" (parseAzNat v)
  let o ← expect "ordering" (parseOrdering o)
  let (av, ao) ← roundedShr x sh rm
  expectEq "shr_round" (pairString av ao) (pairString v o)

/-! ### GCD and modular arithmetic -/

def checkGcd : String → Verdict := checkMethod "gcd" AzNat.gcd

/-- A relation printed as `x <pos> y` or `x <neg> y`. -/
def checkRelation (pos neg : String) (f : AzNat → AzNat → Bool) (line : String) : Verdict := do
  let (x, y, expected) ← match line.splitOn neg, line.splitOn pos with
    | [x, y], _ => pure (x, y, false)
    | _, [x, y] => pure (x, y, true)
    | _, _ => fail s!"not an `x{pos}y` or `x{neg}y` line"
  let x ← expect "x" (parseAzNat (stripRef x))
  let y ← expect "y" (parseAzNat (stripRef y))
  expectEq (trim pos) (f x y) expected

def checkCoprimeWith : String → Verdict :=
  checkRelation " is coprime with " " is not coprime with " AzNat.coprime

/-- `n⁻¹ ≡ i mod m`, or `n is not invertible mod m`. Malachite requires `n` reduced modulo `m`,
so `invMod`'s coprimality precondition is the only one to check. -/
def checkModInverse (line : String) : Verdict := do
  match line.splitOn "⁻¹ ≡ " with
  | [n, rest] =>
    let (i, m) ← match rest.splitOn " mod " with
      | [i, m] => pure (i, m)
      | _ => fail "not an `n⁻¹ ≡ i mod m` line"
    let n ← expect "n" (parseAzNat n)
    let i ← expect "inverse" (parseAzNat i)
    let m ← expect "modulus" (parseAzNat m)
    if !AzNat.coprime n m then disagree "Malachite inverted a non-coprime pair"
    expectEq "mod_inverse" (AzNat.invMod n m) i
  | _ =>
    match line.splitOn " is not invertible mod " with
    | [n, m] =>
      let n ← expect "n" (parseAzNat n)
      let m ← expect "modulus" (parseAzNat m)
      expectEq "coprime" (AzNat.coprime n m) false
    | _ => fail "not a mod_inverse line"

/-- `x.jacobi_symbol(n) = s`, for odd `n`. -/
def checkJacobiSymbol (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.jacobi_symbol(n) = s` line" (methodCall line "jacobi_symbol")
  let n ← match args with
    | [n] => pure n
    | _ => fail "jacobi_symbol takes one argument"
  let x ← expect "x" (parseAzNat x)
  let n ← expect "n" (parseAzNat n)
  let s ← expect "symbol" (parseInt res)
  expectEq "jacobi_symbol" (AzNat.jacobi x n) s

/-- Whether every pair of moduli is coprime. -/
def pairwiseCoprime : List AzNat → Bool
  | [] => true
  | m :: ms => ms.all (AzNat.coprime m) && pairwiseCoprime ms

/-- `multi_crt([m, …], [v, …]) = Some(n)` or `None`. Malachite returns `None` when the moduli
are unusable: not pairwise coprime, a residue not reduced, or (as in FLINT's `fmpz_multi_CRT`) a
modulus of 0 or 1 among two or more moduli, a single modulus of 1 being allowed. Garner's
algorithm has no defined answer for the first two; otherwise the two must agree. -/
def checkMultiCrt (line : String) : Verdict := do
  let (args, res) ← expect "a `multi_crt(ms, vs) = r` line" (functionCall line "multi_crt")
  let (ms, vs) ← match args with
    | [ms, vs] => pure (ms, vs)
    | _ => fail "multi_crt takes two arguments"
  let ms ← expect "moduli" (parseList ms >>= parseAzNats)
  let vs ← expect "values" (parseList vs >>= parseAzNats)
  let res ← expect "result" (parseOption res)
  let reduced := ms.length == vs.length && (ms.zip vs).all fun (m, v) => v < m
  let usable :=
    reduced && pairwiseCoprime ms && (ms.length ≤ 1 || ms.all fun m => m ≥ (2 : AzNat))
  match res with
  | some n =>
    let n ← expect "n" (parseAzNat n)
    if !usable then disagree "Malachite combined moduli it documents as unusable"
    expectEq "multi_crt" (AzNat.garner ms vs) n
  | none =>
    if usable then
      disagree s!"multi_crt: Malachite printed None, but Azurite computes {AzNat.garner ms vs}"
    else pure ()

/-! ### Arithmetic modulo a power of 2 -/

/-- `x op y ≡ z mod 2^k`. -/
def checkModPow2Op (op : String) (f : AzNat → AzNat → Nat → AzNat) (line : String) :
    Verdict := do
  let (lhs, rhs) ← match line.splitOn " ≡ " with
    | [lhs, rhs] => pure (lhs, rhs)
    | _ => fail s!"not an `x {op} y ≡ z mod 2^k` line"
  let (x, y) ← match lhs.splitOn s!" {op} " with
    | [x, y] => pure (x, y)
    | _ => fail s!"not an `x {op} y` left-hand side"
  let (z, k) ← match rhs.splitOn " mod 2^" with
    | [z, k] => pure (z, k)
    | _ => fail "not a `z mod 2^k` right-hand side"
  let x ← expect "x" (parseAzNat (stripRef x))
  let y ← expect "y" (parseAzNat (stripRef y))
  let z ← expect "z" (parseAzNat z)
  let k ← expect "k" (parseNat k)
  expectEq s!"{op} mod 2^k" (f x y k) z

def checkModPowerOf2Add : String → Verdict := checkModPow2Op "+" AzNat.addModPow2

def checkModPowerOf2Sub : String → Verdict := checkModPow2Op "-" AzNat.subModPow2

def checkModPowerOf2Mul : String → Verdict := checkModPow2Op "*" AzNat.mulDispatchModPow2

/-- `x.square() ≡ z mod 2^k`. -/
def checkModPowerOf2Square (line : String) : Verdict := do
  let (lhs, rhs) ← match line.splitOn " ≡ " with
    | [lhs, rhs] => pure (lhs, rhs)
    | _ => fail "not an `x.square() ≡ z mod 2^k` line"
  if !lhs.endsWith ".square()" then fail "not an `x.square()` left-hand side"
  let (z, k) ← match rhs.splitOn " mod 2^" with
    | [z, k] => pure (z, k)
    | _ => fail "not a `z mod 2^k` right-hand side"
  let x ← expect "x" (parseAzNat (stripRef (dropRightChars lhs 9)))
  let z ← expect "z" (parseAzNat z)
  let k ← expect "k" (parseNat k)
  expectEq "square mod 2^k" (AzNat.squareDispatchModPow2 x k) z

def checkModPowerOf2 : String → Verdict := checkMethodNat "mod_power_of_2" AzNat.modPow2

/-! ### Powers and roots -/

/-- `x.floor_sqrt() = s`. -/
def checkFloorSqrt (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.floor_sqrt() = s` line" (methodCall line "floor_sqrt")
  if !args.isEmpty then fail "floor_sqrt takes no arguments"
  let x ← expect "x" (parseAzNat x)
  let s ← expect "root" (parseAzNat res)
  expectEq "floor_sqrt" (AzNat.sqrt x) s

/-- `x.sqrt_rem() = (s, r)`. -/
def checkSqrtRem (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.sqrt_rem() = (s, r)` line" (methodCall line "sqrt_rem")
  if !args.isEmpty then fail "sqrt_rem takes no arguments"
  let x ← expect "x" (parseAzNat x)
  let (s, r) ← expect "(root, remainder)" (parseTuple2 res)
  let s ← expect "root" (parseAzNat s)
  let r ← expect "remainder" (parseAzNat r)
  let (as_, ar) := AzNat.sqrtRem x
  expectEq "sqrt_rem" s!"({as_}, {ar})" s!"({s}, {r})"

def checkFloorRoot : String → Verdict := checkMethodNat "floor_root" AzNat.rootInt

/-- `x.checked_root(k) = Some(r)` or `None`: `Some` exactly when `x` is a perfect `k`-th power. -/
def checkCheckedRoot (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.checked_root(k) = r` line" (methodCall line "checked_root")
  let k ← match args with
    | [k] => pure k
    | _ => fail "checked_root takes one argument"
  let x ← expect "x" (parseAzNat x)
  let k ← expect "k" (parseNat k)
  let res ← expect "result" (parseOption res)
  let expected := if AzNat.isPow x k then some (AzNat.rootInt x k) else none
  expectEq "checked_root" (optionString expected) (optionString res)

/-- `2^k = n`. -/
def checkPowerOf2 (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `2^k = n` line" (splitEquals line)
  if !lhs.startsWith "2^" then fail "not a `2^k` left-hand side"
  let k ← expect "k" (parseNat (dropChars lhs 2))
  let n ← expect "n" (parseAzNat rhs)
  expectEq "power_of_2" (AzNat.pow2 k) n

/-! ### Bits and predicates -/

/-- A predicate printed as `n<pos>` or `n<neg>`. -/
def checkPredicate (pos neg : String) (f : AzNat → Bool) (line : String) : Verdict := do
  let (n, expected) ←
    if line.endsWith neg then pure (dropRightChars line neg.length, false)
    else if line.endsWith pos then pure (dropRightChars line pos.length, true)
    else fail s!"not an `n{pos}` or `n{neg}` line"
  let n ← expect "n" (parseAzNat n)
  expectEq (trim pos) (f n) expected

def checkIsPowerOf2 : String → Verdict :=
  checkPredicate " is a power of 2" " is not a power of 2" AzNat.isPowerOfTwo

/-- The `even` and `odd` demos. -/
def checkParity (line : String) : Verdict :=
  if line.endsWith " even" then checkPredicate " is even" " is not even" AzNat.isEven line
  else checkPredicate " is odd" " is not odd" AzNat.isOdd line

/-- `n is divisible by 2^k` or `n is not divisible by 2^k`. -/
def checkDivisibleByPowerOf2 (line : String) : Verdict := do
  let (n, k, expected) ←
    match line.splitOn " is not divisible by 2^", line.splitOn " is divisible by 2^" with
    | [n, k], _ => pure (n, k, false)
    | _, [n, k] => pure (n, k, true)
    | _, _ => fail "not a divisible-by-2^k line"
  let n ← expect "n" (parseAzNat n)
  let k ← expect "k" (parseNat k)
  expectEq "divisible_by_power_of_2" (AzNat.isMultipleOfPow2 n k) expected

/-- `name(n) = result` with a natural argument. -/
def unaryFunction (line name : String) : Except Failure (AzNat × String) := do
  let (args, res) ← expect s!"a `{name}(n) = r` line" (functionCall line name)
  let n ← match args with
    | [n] => pure n
    | _ => fail s!"{name} takes one argument"
  let n ← expect "n" (parseAzNat n)
  pure (n, res)

def checkSignificantBits (line : String) : Verdict := do
  let (n, res) ← unaryFunction line "significant_bits"
  let bits ← expect "bits" (parseNat res)
  expectEq "significant_bits" (AzNat.size n) bits

def checkTrailingZeros (line : String) : Verdict := do
  let (n, res) ← unaryFunction line "trailing_zeros"
  let zeros ← expect "zeros" (parseOption res)
  let zeros ← match zeros with
    | some z => expect "zeros" ((parseNat z).map some)
    | none => pure none
  expectEq "trailing_zeros" (optionString (AzNat.trailingZeros n)) (optionString zeros)

/-- `Natural::low_mask(k) = n`. -/
def checkLowMask (line : String) : Verdict := do
  let (args, res) ← expect "a `Natural::low_mask(k) = n` line"
    (functionCall line "Natural::low_mask")
  let k ← match args with
    | [k] => pure k
    | _ => fail "low_mask takes one argument"
  let k ← expect "k" (parseNat k)
  let n ← expect "n" (parseAzNat res)
  expectEq "low_mask" (AzNat.lowMask k) n

/-! ### Limbs and digits -/

/-- `limbs(n) = [l, …]`, least significant first. -/
def checkLimbs (line : String) : Verdict := do
  let (n, res) ← unaryFunction line "limbs"
  let limbs ← expect "limbs" (parseList res >>= parseLimbs)
  expectEq "limbs" n.limbs limbs

/-- `from_limbs_asc([l, …]) = n`. -/
def checkFromLimbsAsc (line : String) : Verdict := do
  let (args, res) ← expect "a `from_limbs_asc(ls) = n` line" (functionCall line "from_limbs_asc")
  let ls ← match args with
    | [ls] => pure ls
    | _ => fail "from_limbs_asc takes one argument"
  let ls ← expect "limbs" (parseList ls >>= parseLimbs)
  let n ← expect "n" (parseAzNat res)
  expectEq "from_limbs_asc" (AzNat.ofLimbs ls) n

/-- `to_digits_asc(n, b) = [d, …]`, least significant first, for a base below `2^64`. -/
def checkToDigitsAsc (line : String) : Verdict := do
  let (args, res) ← expect "a `to_digits_asc(n, b) = ds` line" (functionCall line "to_digits_asc")
  let (n, b) ← match args with
    | [n, b] => pure (n, b)
    | _ => fail "to_digits_asc takes two arguments"
  let n ← expect "n" (parseAzNat n)
  let b ← expect "base" (parseNat b)
  if b < 2 || b ≥ 2 ^ 64 then fail "the base is outside [2, 2^64)"
  let ds ← expect "digits" (parseList res >>= parseLimbs)
  expectEq "to_digits_asc" (AzNat.limbDigits (UInt64.ofNat b) n) ds

/-! ### Strings -/

/-- The value of a digit character under Malachite's rule for a base up to 62: letters are
case-insensitive up to base 36, and past it `A`–`Z` are 10–35 and `a`–`z` are 36–61. -/
def malachiteDigit (base : Nat) (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 'A'.toNat + 10)
  else if 'a' ≤ c ∧ c ≤ 'z' then
    some (if base ≤ 36 then c.toNat - 'a'.toNat + 10 else c.toNat - 'a'.toNat + 36)
  else none

/-- Malachite's `from_string_base`: an optional single leading `+`, then Horner's rule over the
digits, rejecting an empty digit string or a digit at least the base. Written from Malachite's
documented rule (the `+` from its unit tests) and evaluated with `AzNat` arithmetic; it also covers
the bases above 36 that `AzNat.parseBase` does not accept. -/
def malachiteParseBase (base : Nat) (s : String) : Option AzNat := do
  let s := if s.startsWith "+" then dropChars s 1 else s
  guard (2 ≤ base ∧ base ≤ 62 ∧ !s.isEmpty)
  let b := UInt64.ofNat base
  s.toList.foldlM (init := (0 : AzNat)) fun acc c => do
    let d ← malachiteDigit base c
    guard (d < base)
    pure ((AzNat.mulUInt64 acc b).addUInt64 (UInt64.ofNat d))

/-- The character of a digit under Malachite's rule, lowercase letters up to base 36. -/
def malachiteDigitChar (base d : Nat) : Char :=
  if d < 10 then Char.ofNat ('0'.toNat + d)
  else if d < 36 then
    if base ≤ 36 then Char.ofNat ('a'.toNat + d - 10) else Char.ofNat ('A'.toNat + d - 10)
  else Char.ofNat ('a'.toNat + d - 36)

/-- Malachite's `to_string_base`, from `AzNat`'s base-`b` digits. -/
def malachiteToStringBase (base : Nat) (n : AzNat) : String :=
  let digits := AzNat.limbDigits (UInt64.ofNat base) n
  if digits.isEmpty then "0"
  else String.ofList (digits.toList.reverse.map fun d => malachiteDigitChar base d.toNat)

/-- The result of a parsing demo: `Some(n)`/`None` (`from_string_base`), `Ok(n)`/`Err(())`
(`from_str`), or a bare `n` from the `_targeted` demos, whose inputs always parse. -/
def parsedNatural (rhs : String) : Except Failure (Option AzNat) := do
  let res ← match parseOption rhs, parseResult rhs with
    | some r, _ => pure r
    | _, some r => pure r
    | none, none => pure (some rhs)
  match res with
  | some n => expect "n" ((parseAzNat n).map some)
  | none => pure none

/-- `Natural::from_string_base(b, s) = Some(n)` or `None`. The string is printed bare, so it is
everything after the first comma; it never contains ` = `. -/
def checkFromStringBase (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `Natural::from_string_base(b, s) = r` line" (splitEquals line)
  let prefix_ := "Natural::from_string_base("
  if !(lhs.startsWith prefix_ && lhs.endsWith ")") then fail "not a from_string_base call"
  let inner := dropRightChars (dropChars lhs prefix_.length) 1
  let (b, s) ← match inner.splitOn ", " with
    | b :: rest@(_ :: _) => pure (b, ", ".intercalate rest)
    | _ => fail "from_string_base takes two arguments"
  let b ← expect "base" (parseNat b)
  let res ← parsedNatural rhs
  expectEq "from_string_base" (optionString (malachiteParseBase b s)) (optionString res)

/-- `Natural::from_str(s) = Ok(n)` or `Err(())`: `from_string_base` in base 10. -/
def checkFromStr (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `Natural::from_str(s) = r` line" (splitEquals line)
  let prefix_ := "Natural::from_str("
  if !(lhs.startsWith prefix_ && lhs.endsWith ")") then fail "not a from_str call"
  let s := dropRightChars (dropChars lhs prefix_.length) 1
  let res ← parsedNatural rhs
  expectEq "from_str" (resultString (malachiteParseBase 10 s)) (resultString res)

/-- `n.to_string_base(b) = s`, for any base up to 62. -/
def checkToStringBase (line : String) : Verdict := do
  let (n, args, res) ← expect "an `n.to_string_base(b) = s` line"
    (methodCall line "to_string_base")
  let b ← match args with
    | [b] => pure b
    | _ => fail "to_string_base takes one argument"
  let n ← expect "n" (parseAzNat n)
  let b ← expect "base" (parseNat b)
  if b < 2 || b > 62 then fail "the base is outside [2, 62]"
  expectEq "to_string_base" (malachiteToStringBase b n) res

/-! ### Comparison -/

/-- `x < y`, `x = y`, or `x > y`. -/
def checkCmp (line : String) : Verdict := do
  let (x, y, o) ← match line.splitOn " < ", line.splitOn " > ", line.splitOn " = " with
    | [x, y], _, _ => pure (x, y, Ordering.lt)
    | _, [x, y], _ => pure (x, y, Ordering.gt)
    | _, _, [x, y] => pure (x, y, Ordering.eq)
    | _, _, _ => fail "not a comparison line"
  let x ← expect "x" (parseAzNat x)
  let y ← expect "y" (parseAzNat y)
  expectEq "cmp" (orderingName (AzNat.compare x y)) (orderingName o)

/-- `cmp_normalized(x, y) = o`. -/
def checkCmpNormalized (line : String) : Verdict := do
  let (args, res) ← expect "a `cmp_normalized(x, y) = o` line"
    (functionCall line "cmp_normalized")
  let (x, y) ← match args with
    | [x, y] => pure (x, y)
    | _ => fail "cmp_normalized takes two arguments"
  let x ← expect "x" (parseAzNat x)
  let y ← expect "y" (parseAzNat y)
  let o ← expect "ordering" (parseOrdering res)
  expectEq "cmp_normalized" (orderingName (AzNat.normalizedCompare x y)) (orderingName o)

/-! ### Conversion -/

/-- `Natural::from(u) = n`, for an unsigned machine integer. -/
def checkFromUnsigned (line : String) : Verdict := do
  let (args, res) ← expect "a `Natural::from(u) = n` line" (functionCall line "Natural::from")
  let u ← match args with
    | [u] => pure u
    | _ => fail "Natural::from takes one argument"
  let u ← expect "u" (parseNat u)
  if u ≥ 2 ^ 64 then fail "the input does not fit in a limb"
  let n ← expect "n" (parseAzNat res)
  expectEq "from" (UInt64.ofNat u).toAzNat n

/-- `Natural::saturating_from(i) = n`, for a signed machine integer; a negative input gives 0. -/
def checkSaturatingFromSigned (line : String) : Verdict := do
  let (args, res) ← expect "a `Natural::saturating_from(i) = n` line"
    (functionCall line "Natural::saturating_from")
  let i ← match args with
    | [i] => pure i
    | _ => fail "Natural::saturating_from takes one argument"
  let i ← expect "i" (parseInt i)
  if i < -(2 ^ 63) || i ≥ 2 ^ 63 then fail "the input does not fit in an Int64"
  let n ← expect "n" (parseAzNat res)
  expectEq "saturating_from" (Int64.ofInt i).toAzNatClampNeg n

/-- `T::wrapping_from(&n) = v`, for a machine integer type `T`: the low bits of `n`, reinterpreted
for the signed types. -/
def checkWrappingFrom (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `T::wrapping_from(&n) = v` line" (splitEquals line)
  let (t, rest) ← match lhs.splitOn "::wrapping_from(" with
    | [t, rest] => pure (t, rest)
    | _ => fail "not a wrapping_from call"
  if !rest.endsWith ")" then fail "not a wrapping_from call"
  let n ← expect "n" (parseAzNat (stripRef (dropRightChars rest 1)))
  let computed ← match t with
    | "u8" => pure (toString n.toUInt8)
    | "u16" => pure (toString n.toUInt16)
    | "u32" => pure (toString n.toUInt32)
    | "u64" => pure (toString n.toUInt64)
    | "usize" => pure (toString n.toUSize)
    | "i8" => pure (toString n.toInt8)
    | "i16" => pure (toString n.toInt16)
    | "i32" => pure (toString n.toInt32)
    | "i64" => pure (toString n.toInt64)
    | "isize" => pure (toString n.toISize)
    | _ => fail s!"no AzNat conversion to {t}"
  expectEq s!"{t}::wrapping_from" computed rhs

end Azurite.Oracle
