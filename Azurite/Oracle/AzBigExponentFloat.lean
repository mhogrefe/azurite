/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Oracle.AzFloat

/-!
# Checks for Malachite's `BigExponentFloat` against `AzFloat`

Malachite's `BigExponentFloat` is a binary floating-point number with an unbounded (`Integer`)
exponent, no stored precision, and no negative zero, like FLINT's `arf_t`. Its `_debug` demos print
every value in Malachite's exact hexadecimal format without a precision (`0x1.8`), and their lines
otherwise have the shapes of the `Float` demos'. So the `Float` checks of `Azurite.Oracle.AzFloat`
are reused under the `BigExponentFloat` dialect (`bigExponentFloatDialect`): values are read at
their own precision, their number of significant bits; results are compared by value; and, since
`AzFloat`'s exponent is unbounded too, nothing is clamped. The checks here cover the shapes the
`BigExponentFloat` demos print differently: its `+`, `-`, `*`, `square`, `sum`, and `product` are
exact, and some of its lines name their operations differently.
-/

namespace Azurite.Oracle

open Azurite

local instance (priority := high) : FloatDialect := bigExponentFloatDialect

/-! ### Reading `BigExponentFloat` names

The `BigExponentFloat` demos name some operations differently from the `Float` demos: they always
prefix an associated function with the type (`BigExponentFloat::pi_prec(p)`, where the `Float` demo
prints `pi_prec(p)`), and an operation whose name contains the type says `big_exponent_float` where
the `Float` one says `float` (`agm_big_exponent_float_rational`,
`log_base_big_exponent_float_base`).
`withBigExponentFloatNames` runs a `Float` check on a line as printed and, while the check cannot
read it, on the line with the prefix removed, with the type's name shortened, and with both. A
disagreement is never retried, and a line no reading accepts is reported as the first reading's
failure; the printed values (hexadecimal, decimal, or rational) never contain these names. -/

def withoutTypePrefix (line : String) : String :=
  if line.startsWith "BigExponentFloat::" then dropChars line "BigExponentFloat::".length else line

def withFloatNames (line : String) : String := line.replace "_big_exponent_float" "_float"

def withBigExponentFloatNames (check : String → Verdict) (line : String) : Verdict :=
  let readings := [withoutTypePrefix line, withFloatNames line,
    withFloatNames (withoutTypePrefix line)].filter (· != line)
  match check line with
  | .error (.unreadable msg) =>
    match readings.find? (fun l => !(check l matches .error (.unreadable _))) with
    | some l => check l
    | none => .error (.unreadable msg)
  | v => v

/-! ### Arithmetic -/

/-- `x + y = z` (exact), `(x).add_prec(y, p) = (z, o)`, or
`(x).add_prec_round(y, p, rm) = (z, o)`. -/
def checkBigExponentFloatAdd : String → Verdict := withBigExponentFloatNames checkFloatAdd

def checkBigExponentFloatSub : String → Verdict := withBigExponentFloatNames checkFloatSub

def checkBigExponentFloatMul : String → Verdict := withBigExponentFloatNames checkFloatMul

/-- `(x).div_prec(y, p) = (z, o)` or `(x).div_prec_round(y, p, rm) = (z, o)`. A
`BigExponentFloat` has no signed zero to give a quotient by zero a sign, so Malachite documents
`x / 0` as `NaN` for every `x`, as FLINT's `arf_div` does; Azurite's is `±∞`. -/
def checkBigExponentFloatDiv : String → Verdict := checkFloatBinary "/" "div" fun x y p m =>
  if y.1 matches .zero then (.nan, .eq) else AzFloat.divPrecRound x.1 y.1 p m

/-- `(x).square() = z`, exact, or `(x).square_prec[_round](…)`. -/
def checkBigExponentFloatSquare (line : String) : Verdict := do
  match methodCall line "square" with
  | some (x, [], z) =>
    let x ← expect "x" (parseFloat x)
    let z ← expect "z" (parseFloat z)
    let p := 2 * x.1.precision?.getD 1
    expectFloat "square" (AzFloat.sqrPrecRound x.1 p .Nearest).1 z
  | _ => checkFloatSquare line

def checkBigExponentFloatSqrt : String → Verdict := withBigExponentFloatNames checkFloatSqrt

def checkBigExponentFloatReciprocalSqrt : String → Verdict :=
  withBigExponentFloatNames checkFloatReciprocalSqrt

/-- `(x).reciprocal_prec[_round](…)`. As for division, Malachite documents `1 / 0` as `NaN`. -/
def checkBigExponentFloatReciprocal : String → Verdict :=
  checkFloatUnary "reciprocal" reciprocalLine fun x p m =>
    if x matches .zero then (.nan, .eq) else AzFloat.recipPrecRound x p m

/-- `-x = z`. -/
def checkBigExponentFloatNeg : String → Verdict := withBigExponentFloatNames checkFloatNeg

/-- `(x).abs() = z`. -/
def checkBigExponentFloatAbs (line : String) : Verdict := do
  let (x, args, z) ← expect "an `(x).abs() = z` line" (methodCall line "abs")
  if !args.isEmpty then fail "abs takes no arguments"
  let x ← expect "x" (parseFloat x)
  let z ← expect "z" (parseFloat z)
  expectFloat "abs" (AzFloat.abs x.1) z

def checkBigExponentFloatShl : String → Verdict := withBigExponentFloatNames checkFloatShl

def checkBigExponentFloatShr : String → Verdict := withBigExponentFloatNames checkFloatShr

/-- The precision of an exact sum of the finite elements of `xs`: enough bits to span all their
significant bits, plus one for each element to absorb carries. -/
def exactSumPrecision (xs : List AzFloat) : Nat :=
  let bounds := xs.filterMap fun
    | .finite _ e p _ _ => some (e, e - (AzNat.ofNat p).toAzInt)
    | _ => none
  match bounds with
  | [] => 1
  | (hi, lo) :: rest =>
    let (hi, lo) := rest.foldl (fun (h, l) (h', l') => (max h h', min l l')) (hi, lo)
    (hi - lo).natAbs.toNat + xs.length + 1

/-- The precision of an exact product of the elements of `xs`: the sum of their precisions. -/
def exactProductPrecision (xs : List AzFloat) : Nat :=
  max 1 (xs.foldl (fun p x => p + x.precision?.getD 0) 0)

/-- A fold over a list in one of its three shapes: `name([x, …]) = z`, exact;
`name_prec([x, …], p) = (z, o)`; or `name_prec_round([x, …], p, rm) = (z, o)`. -/
def checkBigExponentFloatListFold (name : String) (exact : List AzFloat → Nat)
    (f : List AzFloat → Nat → RoundingMode → AzFloat × Ordering) (line : String) :
    Verdict := do
  match functionCall line s!"{name}_prec_round", functionCall line s!"{name}_prec" with
  | some ([xs, p, rm], res), _ =>
    let xs ← expect "list" (parseFloatList xs)
    let p ← expect "precision" (parseNat p)
    let rm ← expect "rounding mode" (parseRounding rm)
    let printed ← parseFloatPair res
    let computed ← roundedResult name (f xs p) rm
    expectFloatPair s!"{name}_prec_round" computed printed
  | _, some ([xs, p], res) =>
    let xs ← expect "list" (parseFloatList xs)
    let p ← expect "precision" (parseNat p)
    let printed ← parseFloatPair res
    let computed ← roundedResult name (f xs p) (.mode .Nearest)
    expectFloatPair s!"{name}_prec" computed printed
  | _, _ =>
    let (args, res) ← expect s!"a `{name}([x, …]) = z` line" (functionCall line name)
    let xs ← match args with
      | [xs] => expect "list" (parseFloatList xs)
      | _ => fail s!"{name} takes one list"
    let z ← expect "z" (parseFloat res)
    expectFloat name (f xs (exact xs) .Nearest).1 z

def checkBigExponentFloatSum : String → Verdict :=
  checkBigExponentFloatListFold "sum" exactSumPrecision AzFloat.sumPrecRound

def checkBigExponentFloatProduct : String → Verdict :=
  checkBigExponentFloatListFold "product" exactProductPrecision AzFloat.productPrecRound

/-! ### Logarithms with a `BigExponentFloat` base

Malachite documents a base of `1` as giving `NaN` for every argument: `ln 1 = 0`, and a
`BigExponentFloat` has no signed zero to give the quotient `ln x / ln 1` a sign, so it follows the
rule for division by zero. Azurite, like `Float`, divides the logarithms as IEEE 754 does. -/

/-- `NaN` for the base `1`, and `f` otherwise. -/
def baseOneIsNaN {α : Type} (f : α → AzFloat → Nat → RoundingMode → AzFloat × Ordering)
    (x : α) (b : AzFloat) (p : Nat) (m : RoundingMode) : AzFloat × Ordering :=
  if sameFloatValue b AzFloat.one then (.nan, .eq) else f x b p m

def checkBigExponentFloatLogBaseFloatBase : String → Verdict :=
  withBigExponentFloatNames fun line => checkFloatUnaryArgsWith "log_base_float_base" 1
    parseFloatArg (baseOneIsNaN AzFloat.logBaseFloatPrecRound) line ["log_base"]

def checkBigExponentFloatLogBaseFloatBase1PlusX : String → Verdict :=
  withBigExponentFloatNames fun line => checkFloatUnaryArgsWith "log_base_float_base_1_plus_x" 1
    parseFloatArg (baseOneIsNaN AzFloat.logBaseFloatP1PrecRound) line ["log_base_1_plus_x"]

def checkBigExponentFloatLogBaseRationalFloatBase : String → Verdict :=
  withBigExponentFloatNames <| checkFloatOfRationalArgsWith "log_base_rational_float_base" 1
    parseFloatArg (baseOneIsNaN AzFloat.logBaseRatFloatPrecRound)

/-! ### Checks reused unchanged

These `Float` checks read the `BigExponentFloat` demos' lines as they are, under the
`BigExponentFloat` dialect. -/

def checkBigExponentFloatAddRational : String → Verdict :=
  withBigExponentFloatNames checkFloatAddRational

def checkBigExponentFloatSubRational : String → Verdict :=
  withBigExponentFloatNames checkFloatSubRational

def checkBigExponentFloatMulRational : String → Verdict :=
  withBigExponentFloatNames checkFloatMulRational

/-- `x / q`, `q / x`, and their `_prec` and `_prec_round` forms. As for `div`, Malachite documents a
quotient by zero as `NaN`, whichever operand is the divisor. -/
def checkBigExponentFloatDivRational : String → Verdict :=
  withBigExponentFloatNames <| checkFloatRationalBinary "/" "div_rational"
    (fun x q p m => if q == 0 then (.nan, .eq) else AzFloat.divRatPrecRound x.1 q p m)
    (fun q x p m => if x.1 matches .zero then (.nan, .eq) else AzFloat.ratDivPrecRound q x.1 p m)
    (some "rational_div_float")

def checkBigExponentFloatSqrtRational : String → Verdict :=
  withBigExponentFloatNames checkFloatSqrtRational

def checkBigExponentFloatReciprocalSqrtRational : String → Verdict :=
  withBigExponentFloatNames checkFloatReciprocalSqrtRational

def checkBigExponentFloatAgm : String → Verdict := withBigExponentFloatNames checkFloatAgm

def checkBigExponentFloatAgmRational : String → Verdict :=
  withBigExponentFloatNames checkFloatAgmRational

def checkBigExponentFloatAgmFloatRational : String → Verdict :=
  withBigExponentFloatNames checkFloatAgmFloatRational

def checkBigExponentFloatSqrtAll : String → Verdict := withBigExponentFloatNames checkFloatSqrtAll

def checkBigExponentFloatReciprocalSqrtAll : String → Verdict :=
  withBigExponentFloatNames checkFloatReciprocalSqrtAll

def checkBigExponentFloatSqrtUnsigned : String → Verdict :=
  withBigExponentFloatNames checkFloatSqrtUnsigned

def checkBigExponentFloatLn : String → Verdict := withBigExponentFloatNames checkFloatLn

def checkBigExponentFloatLnRational : String → Verdict :=
  withBigExponentFloatNames checkFloatLnRational

def checkBigExponentFloatLn1PlusX : String → Verdict := withBigExponentFloatNames checkFloatLn1PlusX

def checkBigExponentFloatLogBase2 : String → Verdict := withBigExponentFloatNames checkFloatLogBase2

def checkBigExponentFloatLogBase2Rational : String → Verdict :=
  withBigExponentFloatNames checkFloatLogBase2Rational

def checkBigExponentFloatLogBase21PlusX : String → Verdict :=
  withBigExponentFloatNames checkFloatLogBase21PlusX

def checkBigExponentFloatLogBase10 : String → Verdict :=
  withBigExponentFloatNames checkFloatLogBase10

def checkBigExponentFloatLogBase10Rational : String → Verdict :=
  withBigExponentFloatNames checkFloatLogBase10Rational

def checkBigExponentFloatLogBase101PlusX : String → Verdict :=
  withBigExponentFloatNames checkFloatLogBase101PlusX

def checkBigExponentFloatLogBasePowerOf2 : String → Verdict :=
  withBigExponentFloatNames checkFloatLogBasePowerOf2

def checkBigExponentFloatLogBasePowerOf2Rational : String → Verdict :=
  withBigExponentFloatNames checkFloatLogBasePowerOf2Rational

def checkBigExponentFloatLogBasePowerOf21PlusX : String → Verdict :=
  withBigExponentFloatNames checkFloatLogBasePowerOf21PlusX

def checkBigExponentFloatLogBase : String → Verdict := withBigExponentFloatNames checkFloatLogBase

def checkBigExponentFloatLogBaseRational : String → Verdict :=
  withBigExponentFloatNames checkFloatLogBaseRational

def checkBigExponentFloatLogBase1PlusX : String → Verdict :=
  withBigExponentFloatNames checkFloatLogBase1PlusX




def checkBigExponentFloatLogBaseRationalBase : String → Verdict :=
  withBigExponentFloatNames checkFloatLogBaseRationalBase

def checkBigExponentFloatLogBaseRationalBase1PlusX : String → Verdict :=
  withBigExponentFloatNames checkFloatLogBaseRationalBase1PlusX

def checkBigExponentFloatLogBaseRationalRationalBase : String → Verdict :=
  withBigExponentFloatNames checkFloatLogBaseRationalRationalBase

/-! ### Exponentials and powers
`Float`'s checks replace an input whose result is beyond `Float`'s exponent range by one that
rounds the same way there; a `BigExponentFloat`'s exponent is unbounded, so these call Azurite at
the input itself. -/

def checkBigExponentFloatExp : String → Verdict :=
  withBigExponentFloatNames <| checkFloatUnaryWith "exp" AzFloat.expPrecRound

def checkBigExponentFloatExpRational : String → Verdict :=
  withBigExponentFloatNames checkFloatExpRational

def checkBigExponentFloatExpXMinus1 : String → Verdict :=
  withBigExponentFloatNames <| checkFloatUnaryWith "exp_x_minus_1" AzFloat.expM1PrecRound

def checkBigExponentFloatExpXMinus1Rational : String → Verdict :=
  withBigExponentFloatNames checkFloatExpXMinus1Rational

def checkBigExponentFloatPowerOf2OfFloat : String → Verdict :=
  withBigExponentFloatNames fun line =>
    checkFloatUnaryArgsWith "power_of_2_of_float" 0 (fun _ => some ())
      (fun x _ => AzFloat.pow2PrecRound x) (assocAsMethod line) ["power_of_2", "power_of_2_assign"]

def checkBigExponentFloatPowerOf2Rational : String → Verdict :=
  withBigExponentFloatNames checkFloatPowerOf2Rational

def checkBigExponentFloatPowerOf2XMinus1 : String → Verdict :=
  withBigExponentFloatNames <| checkFloatUnaryWith "power_of_2_x_minus_1" AzFloat.pow2M1PrecRound

def checkBigExponentFloatPowerOf2XMinus1Rational : String → Verdict :=
  withBigExponentFloatNames checkFloatPowerOf2XMinus1Rational

/-- A negative odd integer? -/
def isNegativeOddInteger (q : AzRat) : Bool := !q.sign && q.den == AzNat.ofNat 1 && q.num.isOdd

/-- With no negative zero, `0^y` for a negative odd integer `y`, whose one-sided limits are `∞`
and `-∞`, is `NaN` (documented), where Azurite gives `∞`. -/
def zeroPowIsNaN {α : Type} (toRat : α → Option AzRat)
    (f : UInt64 → α → Nat → RoundingMode → AzFloat × Ordering) (u : UInt64) (y : α) (p : Nat)
    (m : RoundingMode) : AzFloat × Ordering :=
  if u.toNat == 0 && (toRat y).any isNegativeOddInteger then (.nan, .eq) else f u y p m

def checkBigExponentFloatUnsignedPow : String → Verdict :=
  withBigExponentFloatNames <| checkFloatUnsignedPowWith "unsigned_pow"
    (fun s => (parseFloat s).map (·.1)) (zeroPowIsNaN AzFloat.toAzRat? AzFloat.powBasePrecRound)

def checkBigExponentFloatUnsignedPowRational : String → Verdict :=
  withBigExponentFloatNames <| checkFloatUnsignedPowWith "unsigned_pow_rational" parseAzRat
    (zeroPowIsNaN some AzFloat.powBaseRatPrecRound)

def checkBigExponentFloatUnsignedPowUnsigned : String → Verdict :=
  withBigExponentFloatNames <| checkFloatUnsignedPowWith "unsigned_pow_unsigned" parseAzRat
    AzFloat.powBaseRatPrecRound

def checkBigExponentFloatPowerOf10OfFloat : String → Verdict :=
  withBigExponentFloatNames fun line =>
    checkFloatUnaryArgsWith "power_of_10_of_float" 0 (fun _ => some ())
      (fun x _ => AzFloat.pow10PrecRound x) (assocAsMethod line)
      ["power_of_10", "power_of_10_assign"]

def checkBigExponentFloatPowerOf10Rational : String → Verdict :=
  withBigExponentFloatNames <| checkFloatOfRational "power_of_10_rational" AzFloat.pow10RatPrecRound

def checkBigExponentFloatPowerOf10XMinus1 : String → Verdict :=
  withBigExponentFloatNames <|
    checkFloatUnaryWith "power_of_10_x_minus_1" AzFloat.pow10M1PrecRound

def checkBigExponentFloatPowerOf10XMinus1Rational : String → Verdict :=
  withBigExponentFloatNames <|
    checkFloatOfRational "power_of_10_x_minus_1_rational" AzFloat.pow10M1RatPrecRound

/-- `x^n` with BEF's special values: `NaN^0 = 1` (Azurite's `NaN` propagates), and `0^n = NaN`
for a negative odd `n`. -/
def bigExponentFloatPowInt (x : AzFloat) (n : AzInt) (p : Nat) (m : RoundingMode) :
    AzFloat × Ordering :=
  if n = 0 then AzFloat.powIntPrecRound AzFloat.one n p m
  else if (x matches .zero) && !n.sign && n.abs.isOdd then (.nan, .eq)
  else AzFloat.powIntPrecRound x n p m

def checkBigExponentFloatPowInteger : String → Verdict :=
  withBigExponentFloatNames fun line =>
    checkFloatUnaryArgsWith "pow_integer" 1 (fun | [k] => parseAzInt k | _ => none)
      bigExponentFloatPowInt line ["pow"]

def checkBigExponentFloatPowS : String → Verdict :=
  withBigExponentFloatNames fun line =>
    checkFloatUnaryArgsWith "pow_s" 1 (fun | [k] => parseAzInt k | _ => none)
      bigExponentFloatPowInt line ["pow"]

def checkBigExponentFloatPowU : String → Verdict :=
  withBigExponentFloatNames fun line =>
    checkFloatUnaryArgsWith "pow_u" 1 (fun | [k] => parseAzInt k | _ => none)
      bigExponentFloatPowInt line ["pow"]

def checkBigExponentFloatCbrt : String → Verdict := withBigExponentFloatNames checkFloatCbrt

def checkBigExponentFloatCbrtRational : String → Verdict :=
  withBigExponentFloatNames checkFloatCbrtRational

/-- `x^y` with BEF's special values, at Azurite's `x^y` itself (no substitution: the exponent is
unbounded): `x^0 = 1` even for `NaN`, and `0^y = NaN` for a negative odd integer `y`. -/
def bigExponentFloatPowWith {α β : Type} (isZero : α → Bool) (toRat : β → Option AzRat)
    (f : α → β → Nat → RoundingMode → AzFloat × Ordering) (x : α) (y : β) (p : Nat)
    (m : RoundingMode) : AzFloat × Ordering :=
  match toRat y with
  | some q =>
    if q.num == AzNat.ofNat 0 then AzFloat.setPrecRound AzFloat.one p m
    else if isZero x && isNegativeOddInteger q then (.nan, .eq)
    else f x y p m
  | none => f x y p m

/-- `(x).pow(n) = z` for an unsigned `n`: exact. -/
def checkBigExponentFloatPowUnsignedExact (line : String) : Verdict := do
  let (x, args, z) ← expect "an `(x).pow(n) = z` line" (methodCall line "pow")
  let n ← match args with
    | [n] => expect "n" (parseAzNat n)
    | _ => fail "pow takes one argument"
  let x ← expect "x" (parseFloat x)
  let z ← expect "z" (parseFloat z)
  let n := n.toAzInt
  let p := max 1 (x.1.precision?.getD 1 * n.natAbs.toNat)
  expectFloat "pow" (bigExponentFloatPowInt x.1 n p .Nearest).1 z

def checkBigExponentFloatPow : String → Verdict :=
  withBigExponentFloatNames fun line =>
    match methodCall line "pow" with
    | some (_, [n], _) =>
      if (parseAzNat n).isSome then checkBigExponentFloatPowUnsignedExact line
      else checkFloatAgmWith "pow" (fun s => (parseFloat s).map (·.1)) combined
        (bigExponentFloatPowWith AzFloat.isZero AzFloat.toAzRat? AzFloat.powPrecRound)
        (plain := "pow") line
    | _ => checkFloatAgmWith "pow" (fun s => (parseFloat s).map (·.1)) combined
        (bigExponentFloatPowWith AzFloat.isZero AzFloat.toAzRat? AzFloat.powPrecRound)
        (plain := "pow") line

def checkBigExponentFloatPowRational : String → Verdict :=
  withBigExponentFloatNames fun line =>
    checkFloatUnaryArgsWith "pow_rational" 1 (fun | [q] => parseAzRat (stripRef q) | _ => none)
      (bigExponentFloatPowWith AzFloat.isZero some AzFloat.powRatPrecRound) line ["pow"]

def checkBigExponentFloatRationalPow : String → Verdict :=
  withBigExponentFloatNames <| checkFloatOfRationalArgsWith "rational_pow" 1
    (fun | [y] => (parseFloat (stripRef y)).map (·.1) | _ => none)
    (bigExponentFloatPowWith (fun q : AzRat => q.num == AzNat.ofNat 0) AzFloat.toAzRat?
      AzFloat.ratPowPrecRound)

def checkBigExponentFloatRationalPowRational : String → Verdict :=
  withBigExponentFloatNames <| checkFloatOfRationalArgsWith "rational_pow_rational" 1
    (fun | [r] => parseAzRat (stripRef r) | _ => none)
    (bigExponentFloatPowWith (fun q : AzRat => q.num == AzNat.ofNat 0) some
      AzFloat.ratPowRatPrecRound)

def checkBigExponentFloatCos : String → Verdict := withBigExponentFloatNames checkFloatCos

def checkBigExponentFloatCosRational : String → Verdict :=
  withBigExponentFloatNames checkFloatCosRational

def checkBigExponentFloatCosWithPeriod : String → Verdict :=
  withBigExponentFloatNames checkFloatCosWithPeriod

def checkBigExponentFloatCosWithPeriodRational : String → Verdict :=
  withBigExponentFloatNames checkFloatCosWithPeriodRational

def checkBigExponentFloatCosPi : String → Verdict := withBigExponentFloatNames checkFloatCosPi

def checkBigExponentFloatCosPiRational : String → Verdict :=
  withBigExponentFloatNames checkFloatCosPiRational

def checkBigExponentFloatSin : String → Verdict := withBigExponentFloatNames checkFloatSin

def checkBigExponentFloatSinRational : String → Verdict :=
  withBigExponentFloatNames checkFloatSinRational

def checkBigExponentFloatSinWithPeriod : String → Verdict :=
  withBigExponentFloatNames checkFloatSinWithPeriod

def checkBigExponentFloatSinWithPeriodRational : String → Verdict :=
  withBigExponentFloatNames checkFloatSinWithPeriodRational

def checkBigExponentFloatSinPi : String → Verdict := withBigExponentFloatNames checkFloatSinPi

def checkBigExponentFloatSinPiRational : String → Verdict :=
  withBigExponentFloatNames checkFloatSinPiRational

/-- `y·z`, formed exactly. -/
def exactProduct (y z : AzFloat) : AzFloat :=
  (AzFloat.mulPrecRound y z (exactProductPrecision [y, z]) .Nearest).1

/-- The plain `add_mul` and `sub_mul` are exact: a precision that holds `x ± y·z` exactly. -/
def exactFusedPrecision (x y z : AzFloat) : Nat := exactSumPrecision [x, exactProduct y z]

/-- The plain `mul_add_mul` and `mul_sub_mul` are exact: a precision that holds `x·y ± z·w`
exactly. -/
def exactFusedPrecision₄ (x y z w : AzFloat) : Nat :=
  exactSumPrecision [exactProduct x y, exactProduct z w]

def checkBigExponentFloatAddMul : String → Verdict :=
  withBigExponentFloatNames <| checkFloatFusedWith "add_mul" "add_mul"
    (fun s => (parseFloat s).map (·.1)) exactFusedPrecision AzFloat.addMulPrecRound

def checkBigExponentFloatSubMul : String → Verdict :=
  withBigExponentFloatNames <| checkFloatFusedWith "sub_mul" "sub_mul"
    (fun s => (parseFloat s).map (·.1)) exactFusedPrecision AzFloat.subMulPrecRound

def checkBigExponentFloatAddMulRational : String → Verdict :=
  withBigExponentFloatNames checkFloatAddMulRational

def checkBigExponentFloatSubMulRational : String → Verdict :=
  withBigExponentFloatNames checkFloatSubMulRational

def checkBigExponentFloatMulAddMul : String → Verdict :=
  withBigExponentFloatNames <| checkFloatFused4With "mul_add_mul" "mul_add_mul"
    (fun s => (parseFloat s).map (·.1)) exactFusedPrecision₄ AzFloat.mulAddMulPrecRound

def checkBigExponentFloatMulSubMul : String → Verdict :=
  withBigExponentFloatNames <| checkFloatFused4With "mul_sub_mul" "mul_sub_mul"
    (fun s => (parseFloat s).map (·.1)) exactFusedPrecision₄ AzFloat.mulSubMulPrecRound

def checkBigExponentFloatMulAddMulRational : String → Verdict :=
  withBigExponentFloatNames checkFloatMulAddMulRational

def checkBigExponentFloatMulSubMulRational : String → Verdict :=
  withBigExponentFloatNames checkFloatMulSubMulRational

/-- A precision that holds `x % y` exactly. For `|x| < |y|` the remainder is `x`; otherwise `x`'s
exponent is at least `y`'s, the remainder is below `|y|` and a multiple of the lower of the two
operands' last bits, so the span from that bit to `y`'s exponent, at most the sum of the
precisions, suffices. -/
def exactRemPrecision (x y : AzFloat) : Nat :=
  match x, y with
  | .finite _ e p _ _, .finite _ e' p' _ _ =>
    if AzFloat.lt (AzFloat.abs x) (AzFloat.abs y) then p
    else
      let low := min (e - (AzNat.ofNat p).toAzInt) (e' - (AzNat.ofNat p').toAzInt)
      max 1 (e' - low).natAbs.toNat
  | .finite _ _ p _ _, _ => p
  | _, _ => 1

/-- `x % y = z`, exact, else `Float`'s `rem_prec[_round]` forms. -/
def checkBigExponentFloatRem : String → Verdict :=
  withBigExponentFloatNames fun line =>
    match binaryOp line "%" with
    | some (x, y, z) => do
      let x ← expect "x" (parseFloat x)
      let y ← expect "y" (parseFloat y)
      let z ← expect "z" (parseFloat z)
      expectFloat "%" (AzFloat.remPrecRound x.1 y.1 (exactRemPrecision x.1 y.1) .Nearest).1 z
    | none => checkFloatRem line

def checkBigExponentFloatRoundToInteger : String → Verdict :=
  withBigExponentFloatNames checkFloatRoundToInteger

def checkBigExponentFloatRoundToIntegerThen : String → Verdict :=
  withBigExponentFloatNames checkFloatRoundToIntegerThen

def checkBigExponentFloatPowerOf2 : String → Verdict := withBigExponentFloatNames checkFloatPowerOf2

/-- `(x).name() = b`, BEF's form of a predicate. -/
def checkBigExponentFloatPredicate (name : String) (f : AzFloat → Bool) (line : String) :
    Verdict := do
  let (x, args, b) ← expect s!"an `(x).{name}() = b` line" (methodCall line name)
  if !args.isEmpty then fail s!"{name} takes no arguments"
  let x ← expect "x" (parseFloat x)
  let b ← expect "bool" (parseBool b)
  expectEq name (f x.1) b

def checkBigExponentFloatIsNan : String → Verdict :=
  checkBigExponentFloatPredicate "is_nan" fun x => x.isNaN

def checkBigExponentFloatIsFinite : String → Verdict :=
  checkBigExponentFloatPredicate "is_finite" fun x => x.isFinite

def checkBigExponentFloatIsInfinite : String → Verdict :=
  checkBigExponentFloatPredicate "is_infinite" fun x => x.isInfinite

def checkBigExponentFloatIsZero : String → Verdict :=
  checkBigExponentFloatPredicate "is_zero" fun x => x.isZero

def checkBigExponentFloatIsNormal : String → Verdict :=
  checkBigExponentFloatPredicate "is_normal" fun x => x.isNormal

def checkBigExponentFloatIsInteger : String → Verdict :=
  checkBigExponentFloatPredicate "is_integer" fun x => x.isInteger

def checkBigExponentFloatIsPowerOf2 : String → Verdict :=
  withBigExponentFloatNames checkFloatIsPowerOf2

/-- `(x).sign() = Less|Equal|Greater`: with no negative zero, zero's sign is `Equal`. -/
def checkBigExponentFloatSign (line : String) : Verdict := do
  let (x, args, o) ← expect "an `(x).sign() = o` line" (methodCall line "sign")
  if !args.isEmpty then fail "sign takes no arguments"
  let x ← expect "x" (parseFloat x)
  let o ← expect "ordering" (parseOrdering o)
  let computed ← match x.1 with
    | .zero => pure Ordering.eq
    | .nan => fail "NaN has no sign"
    | x => pure (if x.isPositive then Ordering.gt else .lt)
  expectEq "sign" (orderingName computed) (orderingName o)

/-- `(x).name() = Some(n)` or `None`, rewritten as `name(x) = …` for the `Float` check. -/
def asFunctionLine (name line : String) : String :=
  match methodCall line name with
  | some (x, [], r) => s!"{name}({x}) = {r}"
  | _ => line

def checkBigExponentFloatGetExponent : String → Verdict :=
  fun line => checkFloatGetExponent (asFunctionLine "get_exponent" line)

def checkBigExponentFloatGetPrec : String → Verdict :=
  fun line => checkFloatGetPrec (asFunctionLine "get_prec" line)

def checkBigExponentFloatToSignificand : String → Verdict :=
  fun line => checkFloatToSignificand (asFunctionLine "to_significand" line)

def checkBigExponentFloatConstant : String → Verdict := withBigExponentFloatNames checkFloatConstant

def checkBigExponentFloatIrrationalConstant : String → Verdict :=
  withBigExponentFloatNames checkFloatIrrationalConstant

def checkBigExponentFloatPartialCmp : String → Verdict :=
  withBigExponentFloatNames checkFloatPartialCmp

def checkBigExponentFloatComparablePartialCmp : String → Verdict := checkComparableFloatPartialCmp

def checkBigExponentFloatEq : String → Verdict := withBigExponentFloatNames checkFloatEq

def checkBigExponentFloatComparableEq : String → Verdict := checkComparableFloatEq

/-- A float compared with a natural or an integer, which BEF's demos print in decimal. -/
def checkBigExponentFloatPartialCmpInteger (line : String) : Verdict := do
  let (x, y, o) ← floatComparisonLine line
  let x ← expect "x" (parseFloat x)
  let y ← expect "y" (parseAzInt y)
  expectEq "partial_cmp" (partialOrderingName (AzFloat.partialCompare x.1 (AzFloat.ofAzInt y)))
    (partialOrderingName o)

def checkBigExponentFloatPartialEqInteger (line : String) : Verdict := do
  let (x, y, e) ← equalityLine line
  let x ← expect "x" (parseFloat x)
  let y ← expect "y" (parseAzInt y)
  expectEq "partial_eq" (AzFloat.eqIEEE x.1 (AzFloat.ofAzInt y)) e

/-- `BigExponentFloat::from(n) = z`, `n` a decimal integer of any type: exact. -/
def checkBigExponentFloatFromExact (line : String) : Verdict := do
  let (args, res) ← expect "a `BigExponentFloat::from(n) = z` line" (functionCall line (typed "from"))
  let n ← match args with
    | [n] => expect "n" (parseAzInt n)
    | _ => fail "from takes one argument"
  let z ← expect "z" (parseFloat res)
  expectFloat "from" (exactFromInteger n) z

/-- The exact `from` form, else `Float`'s `from_T_prec[_round]` and `try_from` forms. -/
def checkBigExponentFloatFromIntegerWith (typeName : String) (line : String) : Verdict :=
  if (functionCall line (typed "from")).isSome then checkBigExponentFloatFromExact line
  else withBigExponentFloatNames (checkFloatFromInteger typeName) line

def checkBigExponentFloatFromNatural : String → Verdict :=
  checkBigExponentFloatFromIntegerWith "natural"

def checkBigExponentFloatFromInteger : String → Verdict :=
  checkBigExponentFloatFromIntegerWith "integer"

/-- `BigExponentFloat::from(u)`/`const_from_unsigned(u)`, exact, and
`from_unsigned_prec[_round](u, p[, rm]) = (z, o)`, `u` in decimal. -/
def checkBigExponentFloatFromUnsigned (line : String) : Verdict :=
  match functionCall line (typed "const_from_unsigned") with
  | some (args, res) =>
    checkBigExponentFloatFromExact s!"{typed "from"}({", ".intercalate args}) = {res}"
  | none =>
    if (functionCall line (typed "from")).isSome then checkBigExponentFloatFromExact line
    else checkFloatFromInteger "unsigned" line

def checkBigExponentFloatFromRational : String → Verdict :=
  withBigExponentFloatNames checkFloatFromRational

end Azurite.Oracle
