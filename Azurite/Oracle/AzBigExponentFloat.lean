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

def checkBigExponentFloatExp : String → Verdict := withBigExponentFloatNames checkFloatExp

def checkBigExponentFloatExpRational : String → Verdict :=
  withBigExponentFloatNames checkFloatExpRational

def checkBigExponentFloatExpXMinus1 : String → Verdict :=
  withBigExponentFloatNames checkFloatExpXMinus1

def checkBigExponentFloatExpXMinus1Rational : String → Verdict :=
  withBigExponentFloatNames checkFloatExpXMinus1Rational

def checkBigExponentFloatPowerOf2OfFloat : String → Verdict :=
  withBigExponentFloatNames checkFloatPowerOf2OfFloat

def checkBigExponentFloatPowerOf2Rational : String → Verdict :=
  withBigExponentFloatNames checkFloatPowerOf2Rational

def checkBigExponentFloatPowerOf2XMinus1 : String → Verdict :=
  withBigExponentFloatNames checkFloatPowerOf2XMinus1

def checkBigExponentFloatPowerOf2XMinus1Rational : String → Verdict :=
  withBigExponentFloatNames checkFloatPowerOf2XMinus1Rational

def checkBigExponentFloatUnsignedPow : String → Verdict :=
  withBigExponentFloatNames checkFloatUnsignedPow

def checkBigExponentFloatUnsignedPowRational : String → Verdict :=
  withBigExponentFloatNames checkFloatUnsignedPowRational

def checkBigExponentFloatUnsignedPowUnsigned : String → Verdict :=
  withBigExponentFloatNames checkFloatUnsignedPowUnsigned

def checkBigExponentFloatPowerOf10OfFloat : String → Verdict :=
  withBigExponentFloatNames checkFloatPowerOf10OfFloat

def checkBigExponentFloatPowerOf10Rational : String → Verdict :=
  withBigExponentFloatNames checkFloatPowerOf10Rational

def checkBigExponentFloatPowerOf10XMinus1 : String → Verdict :=
  withBigExponentFloatNames checkFloatPowerOf10XMinus1

def checkBigExponentFloatPowerOf10XMinus1Rational : String → Verdict :=
  withBigExponentFloatNames checkFloatPowerOf10XMinus1Rational

def checkBigExponentFloatPowInteger : String → Verdict :=
  withBigExponentFloatNames checkFloatPowInteger

def checkBigExponentFloatPowS : String → Verdict := withBigExponentFloatNames checkFloatPowS

def checkBigExponentFloatPowU : String → Verdict := withBigExponentFloatNames checkFloatPowU

def checkBigExponentFloatCbrt : String → Verdict := withBigExponentFloatNames checkFloatCbrt

def checkBigExponentFloatCbrtRational : String → Verdict :=
  withBigExponentFloatNames checkFloatCbrtRational

def checkBigExponentFloatPow : String → Verdict := withBigExponentFloatNames checkFloatPow

def checkBigExponentFloatPowRational : String → Verdict :=
  withBigExponentFloatNames checkFloatPowRational

def checkBigExponentFloatRationalPow : String → Verdict :=
  withBigExponentFloatNames checkFloatRationalPow

def checkBigExponentFloatRationalPowRational : String → Verdict :=
  withBigExponentFloatNames checkFloatRationalPowRational

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

def checkBigExponentFloatAddMul : String → Verdict := withBigExponentFloatNames checkFloatAddMul

def checkBigExponentFloatSubMul : String → Verdict := withBigExponentFloatNames checkFloatSubMul

def checkBigExponentFloatAddMulRational : String → Verdict :=
  withBigExponentFloatNames checkFloatAddMulRational

def checkBigExponentFloatSubMulRational : String → Verdict :=
  withBigExponentFloatNames checkFloatSubMulRational

def checkBigExponentFloatMulAddMul : String → Verdict :=
  withBigExponentFloatNames checkFloatMulAddMul

def checkBigExponentFloatMulSubMul : String → Verdict :=
  withBigExponentFloatNames checkFloatMulSubMul

def checkBigExponentFloatMulAddMulRational : String → Verdict :=
  withBigExponentFloatNames checkFloatMulAddMulRational

def checkBigExponentFloatMulSubMulRational : String → Verdict :=
  withBigExponentFloatNames checkFloatMulSubMulRational

def checkBigExponentFloatRem : String → Verdict := withBigExponentFloatNames checkFloatRem

def checkBigExponentFloatRoundToInteger : String → Verdict :=
  withBigExponentFloatNames checkFloatRoundToInteger

def checkBigExponentFloatRoundToIntegerThen : String → Verdict :=
  withBigExponentFloatNames checkFloatRoundToIntegerThen

def checkBigExponentFloatPowerOf2 : String → Verdict := withBigExponentFloatNames checkFloatPowerOf2

def checkBigExponentFloatIsNan : String → Verdict := withBigExponentFloatNames checkFloatIsNaN

def checkBigExponentFloatIsFinite : String → Verdict := withBigExponentFloatNames checkFloatIsFinite

def checkBigExponentFloatIsInfinite : String → Verdict :=
  withBigExponentFloatNames checkFloatIsInfinite

def checkBigExponentFloatIsZero : String → Verdict := withBigExponentFloatNames checkFloatIsZero

def checkBigExponentFloatIsNormal : String → Verdict := withBigExponentFloatNames checkFloatIsNormal

def checkBigExponentFloatIsInteger : String → Verdict :=
  withBigExponentFloatNames checkFloatIsInteger

def checkBigExponentFloatIsPowerOf2 : String → Verdict :=
  withBigExponentFloatNames checkFloatIsPowerOf2

def checkBigExponentFloatSign : String → Verdict := withBigExponentFloatNames checkFloatSign

def checkBigExponentFloatGetExponent : String → Verdict :=
  withBigExponentFloatNames checkFloatGetExponent

def checkBigExponentFloatGetPrec : String → Verdict := withBigExponentFloatNames checkFloatGetPrec

def checkBigExponentFloatToSignificand : String → Verdict :=
  withBigExponentFloatNames checkFloatToSignificand

def checkBigExponentFloatConstant : String → Verdict := withBigExponentFloatNames checkFloatConstant

def checkBigExponentFloatIrrationalConstant : String → Verdict :=
  withBigExponentFloatNames checkFloatIrrationalConstant

def checkBigExponentFloatPartialCmp : String → Verdict :=
  withBigExponentFloatNames checkFloatPartialCmp

def checkBigExponentFloatComparablePartialCmp : String → Verdict := checkComparableFloatPartialCmp

def checkBigExponentFloatEq : String → Verdict := withBigExponentFloatNames checkFloatEq

def checkBigExponentFloatComparableEq : String → Verdict := checkComparableFloatEq

def checkBigExponentFloatPartialCmpInteger : String → Verdict :=
  withBigExponentFloatNames checkFloatPartialCmpInteger

def checkBigExponentFloatPartialEqInteger : String → Verdict :=
  withBigExponentFloatNames checkFloatPartialEqInteger

def checkBigExponentFloatFromNatural : String → Verdict :=
  withBigExponentFloatNames checkFloatFromNatural

def checkBigExponentFloatFromInteger : String → Verdict :=
  withBigExponentFloatNames checkFloatFromIntegerValue

def checkBigExponentFloatFromUnsigned : String → Verdict :=
  withBigExponentFloatNames checkFloatFromUnsigned

def checkBigExponentFloatFromRational : String → Verdict :=
  withBigExponentFloatNames checkFloatFromRational

end Azurite.Oracle
