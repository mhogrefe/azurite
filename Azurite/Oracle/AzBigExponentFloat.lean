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

/-! ### Arithmetic -/

/-- `x + y = z` (exact), `(x).add_prec(y, p) = (z, o)`, or
`(x).add_prec_round(y, p, rm) = (z, o)`. -/
def checkBigExponentFloatAdd : String → Verdict := checkFloatAdd

def checkBigExponentFloatSub : String → Verdict := checkFloatSub

def checkBigExponentFloatMul : String → Verdict := checkFloatMul

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

def checkBigExponentFloatSqrt : String → Verdict := checkFloatSqrt

def checkBigExponentFloatReciprocalSqrt : String → Verdict := checkFloatReciprocalSqrt

/-- `(x).reciprocal_prec[_round](…)`. As for division, Malachite documents `1 / 0` as `NaN`. -/
def checkBigExponentFloatReciprocal : String → Verdict :=
  checkFloatUnary "reciprocal" reciprocalLine fun x p m =>
    if x matches .zero then (.nan, .eq) else AzFloat.recipPrecRound x p m

/-- `-x = z`. -/
def checkBigExponentFloatNeg : String → Verdict := checkFloatNeg

/-- `(x).abs() = z`. -/
def checkBigExponentFloatAbs (line : String) : Verdict := do
  let (x, args, z) ← expect "an `(x).abs() = z` line" (methodCall line "abs")
  if !args.isEmpty then fail "abs takes no arguments"
  let x ← expect "x" (parseFloat x)
  let z ← expect "z" (parseFloat z)
  expectFloat "abs" (AzFloat.abs x.1) z

def checkBigExponentFloatShl : String → Verdict := checkFloatShl

def checkBigExponentFloatShr : String → Verdict := checkFloatShr

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

/-! ### Checks reused unchanged

These `Float` checks read the `BigExponentFloat` demos' lines as they are, under the
`BigExponentFloat` dialect. -/

def checkBigExponentFloatAddRational : String → Verdict := checkFloatAddRational

def checkBigExponentFloatSubRational : String → Verdict := checkFloatSubRational

def checkBigExponentFloatMulRational : String → Verdict := checkFloatMulRational

def checkBigExponentFloatDivRational : String → Verdict := checkFloatDivRational

def checkBigExponentFloatSqrtRational : String → Verdict := checkFloatSqrtRational

def checkBigExponentFloatReciprocalSqrtRational : String → Verdict := checkFloatReciprocalSqrtRational

def checkBigExponentFloatAgm : String → Verdict := checkFloatAgm

def checkBigExponentFloatAgmRational : String → Verdict := checkFloatAgmRational

def checkBigExponentFloatAgmFloatRational : String → Verdict := checkFloatAgmFloatRational

def checkBigExponentFloatSqrtAll : String → Verdict := checkFloatSqrtAll

def checkBigExponentFloatReciprocalSqrtAll : String → Verdict := checkFloatReciprocalSqrtAll

def checkBigExponentFloatSqrtUnsigned : String → Verdict := checkFloatSqrtUnsigned

def checkBigExponentFloatLn : String → Verdict := checkFloatLn

def checkBigExponentFloatLnRational : String → Verdict := checkFloatLnRational

def checkBigExponentFloatLn1PlusX : String → Verdict := checkFloatLn1PlusX

def checkBigExponentFloatLogBase2 : String → Verdict := checkFloatLogBase2

def checkBigExponentFloatLogBase2Rational : String → Verdict := checkFloatLogBase2Rational

def checkBigExponentFloatLogBase21PlusX : String → Verdict := checkFloatLogBase21PlusX

def checkBigExponentFloatLogBase10 : String → Verdict := checkFloatLogBase10

def checkBigExponentFloatLogBase10Rational : String → Verdict := checkFloatLogBase10Rational

def checkBigExponentFloatLogBase101PlusX : String → Verdict := checkFloatLogBase101PlusX

def checkBigExponentFloatLogBasePowerOf2 : String → Verdict := checkFloatLogBasePowerOf2

def checkBigExponentFloatLogBasePowerOf2Rational : String → Verdict := checkFloatLogBasePowerOf2Rational

def checkBigExponentFloatLogBasePowerOf21PlusX : String → Verdict := checkFloatLogBasePowerOf21PlusX

def checkBigExponentFloatLogBase : String → Verdict := checkFloatLogBase

def checkBigExponentFloatLogBaseRational : String → Verdict := checkFloatLogBaseRational

def checkBigExponentFloatLogBase1PlusX : String → Verdict := checkFloatLogBase1PlusX

def checkBigExponentFloatLogBaseFloatBase : String → Verdict := checkFloatLogBaseFloatBase

def checkBigExponentFloatLogBaseFloatBase1PlusX : String → Verdict := checkFloatLogBaseFloatBase1PlusX

def checkBigExponentFloatLogBaseRationalFloatBase : String → Verdict := checkFloatLogBaseRationalFloatBase

def checkBigExponentFloatLogBaseRationalBase : String → Verdict := checkFloatLogBaseRationalBase

def checkBigExponentFloatLogBaseRationalBase1PlusX : String → Verdict := checkFloatLogBaseRationalBase1PlusX

def checkBigExponentFloatLogBaseRationalRationalBase : String → Verdict := checkFloatLogBaseRationalRationalBase

def checkBigExponentFloatExp : String → Verdict := checkFloatExp

def checkBigExponentFloatExpRational : String → Verdict := checkFloatExpRational

def checkBigExponentFloatExpXMinus1 : String → Verdict := checkFloatExpXMinus1

def checkBigExponentFloatExpXMinus1Rational : String → Verdict := checkFloatExpXMinus1Rational

def checkBigExponentFloatPowerOf2OfFloat : String → Verdict := checkFloatPowerOf2OfFloat

def checkBigExponentFloatPowerOf2Rational : String → Verdict := checkFloatPowerOf2Rational

def checkBigExponentFloatPowerOf2XMinus1 : String → Verdict := checkFloatPowerOf2XMinus1

def checkBigExponentFloatPowerOf2XMinus1Rational : String → Verdict := checkFloatPowerOf2XMinus1Rational

def checkBigExponentFloatUnsignedPow : String → Verdict := checkFloatUnsignedPow

def checkBigExponentFloatUnsignedPowRational : String → Verdict := checkFloatUnsignedPowRational

def checkBigExponentFloatUnsignedPowUnsigned : String → Verdict := checkFloatUnsignedPowUnsigned

def checkBigExponentFloatPowerOf10OfFloat : String → Verdict := checkFloatPowerOf10OfFloat

def checkBigExponentFloatPowerOf10Rational : String → Verdict := checkFloatPowerOf10Rational

def checkBigExponentFloatPowerOf10XMinus1 : String → Verdict := checkFloatPowerOf10XMinus1

def checkBigExponentFloatPowerOf10XMinus1Rational : String → Verdict := checkFloatPowerOf10XMinus1Rational

def checkBigExponentFloatPowInteger : String → Verdict := checkFloatPowInteger

def checkBigExponentFloatPowS : String → Verdict := checkFloatPowS

def checkBigExponentFloatPowU : String → Verdict := checkFloatPowU

def checkBigExponentFloatCbrt : String → Verdict := checkFloatCbrt

def checkBigExponentFloatCbrtRational : String → Verdict := checkFloatCbrtRational

def checkBigExponentFloatPow : String → Verdict := checkFloatPow

def checkBigExponentFloatPowRational : String → Verdict := checkFloatPowRational

def checkBigExponentFloatRationalPow : String → Verdict := checkFloatRationalPow

def checkBigExponentFloatRationalPowRational : String → Verdict := checkFloatRationalPowRational

def checkBigExponentFloatCos : String → Verdict := checkFloatCos

def checkBigExponentFloatCosRational : String → Verdict := checkFloatCosRational

def checkBigExponentFloatCosWithPeriod : String → Verdict := checkFloatCosWithPeriod

def checkBigExponentFloatCosWithPeriodRational : String → Verdict := checkFloatCosWithPeriodRational

def checkBigExponentFloatCosPi : String → Verdict := checkFloatCosPi

def checkBigExponentFloatCosPiRational : String → Verdict := checkFloatCosPiRational

def checkBigExponentFloatSin : String → Verdict := checkFloatSin

def checkBigExponentFloatSinRational : String → Verdict := checkFloatSinRational

def checkBigExponentFloatSinWithPeriod : String → Verdict := checkFloatSinWithPeriod

def checkBigExponentFloatSinWithPeriodRational : String → Verdict := checkFloatSinWithPeriodRational

def checkBigExponentFloatSinPi : String → Verdict := checkFloatSinPi

def checkBigExponentFloatSinPiRational : String → Verdict := checkFloatSinPiRational

def checkBigExponentFloatAddMul : String → Verdict := checkFloatAddMul

def checkBigExponentFloatSubMul : String → Verdict := checkFloatSubMul

def checkBigExponentFloatAddMulRational : String → Verdict := checkFloatAddMulRational

def checkBigExponentFloatSubMulRational : String → Verdict := checkFloatSubMulRational

def checkBigExponentFloatMulAddMul : String → Verdict := checkFloatMulAddMul

def checkBigExponentFloatMulSubMul : String → Verdict := checkFloatMulSubMul

def checkBigExponentFloatMulAddMulRational : String → Verdict := checkFloatMulAddMulRational

def checkBigExponentFloatMulSubMulRational : String → Verdict := checkFloatMulSubMulRational

def checkBigExponentFloatRem : String → Verdict := checkFloatRem

def checkBigExponentFloatRoundToInteger : String → Verdict := checkFloatRoundToInteger

def checkBigExponentFloatRoundToIntegerThen : String → Verdict := checkFloatRoundToIntegerThen

def checkBigExponentFloatPowerOf2 : String → Verdict := checkFloatPowerOf2

def checkBigExponentFloatIsNan : String → Verdict := checkFloatIsNaN

def checkBigExponentFloatIsFinite : String → Verdict := checkFloatIsFinite

def checkBigExponentFloatIsInfinite : String → Verdict := checkFloatIsInfinite

def checkBigExponentFloatIsZero : String → Verdict := checkFloatIsZero

def checkBigExponentFloatIsNormal : String → Verdict := checkFloatIsNormal

def checkBigExponentFloatIsInteger : String → Verdict := checkFloatIsInteger

def checkBigExponentFloatIsPowerOf2 : String → Verdict := checkFloatIsPowerOf2

def checkBigExponentFloatSign : String → Verdict := checkFloatSign

def checkBigExponentFloatGetExponent : String → Verdict := checkFloatGetExponent

def checkBigExponentFloatGetPrec : String → Verdict := checkFloatGetPrec

def checkBigExponentFloatToSignificand : String → Verdict := checkFloatToSignificand

def checkBigExponentFloatConstant : String → Verdict := checkFloatConstant

def checkBigExponentFloatIrrationalConstant : String → Verdict := checkFloatIrrationalConstant

def checkBigExponentFloatPartialCmp : String → Verdict := checkFloatPartialCmp

def checkBigExponentFloatComparablePartialCmp : String → Verdict := checkComparableFloatPartialCmp

def checkBigExponentFloatEq : String → Verdict := checkFloatEq

def checkBigExponentFloatComparableEq : String → Verdict := checkComparableFloatEq

def checkBigExponentFloatPartialCmpInteger : String → Verdict := checkFloatPartialCmpInteger

def checkBigExponentFloatPartialEqInteger : String → Verdict := checkFloatPartialEqInteger

def checkBigExponentFloatFromNatural : String → Verdict := checkFloatFromNatural

def checkBigExponentFloatFromInteger : String → Verdict := checkFloatFromIntegerValue

def checkBigExponentFloatFromUnsigned : String → Verdict := checkFloatFromUnsigned

def checkBigExponentFloatFromRational : String → Verdict := checkFloatFromRational

end Azurite.Oracle
