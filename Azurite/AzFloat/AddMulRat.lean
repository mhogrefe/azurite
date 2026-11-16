/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Add
import Azurite.AzFloat.AddSubRat
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Float64Emulate
import Azurite.AzFloat.Shift
import Azurite.AzRat.Mul

/-!
# Fused multiply-add and multiply-subtract with a rational factor

`addMulRatPrecRound x y z p mode` is `x + y·z` with a single rounding for floats `x`, `y` and a
rational `z`, and `subMulRatPrecRound` is `x − y·z`.  A finite `y = ±m · 2^k` (`m` its integer
significand) is kept apart from its exponent: `x ± y·z = (x · 2^(−k) ± (±m)·z) · 2^k`, so the
one rounding is the float-plus-rational addition `addRatPrecRound` (or `subRatPrecRound`) of
the shifted `x` and the small rational `±m·z`, and the result is shifted back — both shifts
are exact and cost nothing.  (Converting `y` itself to a rational would build a numerator or
denominator of `|k|` bits, and every later step would pay for it.)  An infinite `y`
gives `±∞` (or `NaN` when `z = 0`), added with `addPrecRound`.  `fusedMulRat` is the common
shape, parameterized by the float–float and float–rational operations.

`addMulRatFloat64`/`subMulRatFloat64` are the correctly rounded `Float` versions.
-/

namespace Azurite.AzFloat

/-- `x ⊕ y·z` for a rational `z`, with the float–float operation `opF` and the float–rational
operation `opR` doing the single rounding: for a finite `y = ±m · 2^k` it is applied to
`x · 2^(−k)` and the exact rational `±m·z`, and the result is shifted by `k`; an infinite `y`
gives an infinity of the product's sign (`NaN` when `z = 0`). -/
def fusedMulRat (opF : AzFloat → AzFloat → Nat → RoundingMode → AzFloat × Ordering)
    (opR : AzFloat → AzRat → Nat → RoundingMode → AzFloat × Ordering)
    (x y : AzFloat) (z : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match y with
  | nan => (nan, .eq)
  | infinity s => if z.num = 0 then (nan, .eq) else opF x (infinity (s == z.sign)) p mode
  | zero => opR x 0 p mode
  | finite s e _ m _ =>
    let k := e - (AzNat.ofNat m.size).toAzInt
    let r := opR (shiftLeft x (-k)) ((AzInt.mkNorm s m).toAzRat * z) p mode
    (shiftLeft r.1 k, r.2)

/-- `x + y·z` rounded once to precision `p` with `mode`, with the comparison against the exact
value. -/
def addMulRatPrecRound (x y : AzFloat) (z : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  fusedMulRat addPrecRound addRatPrecRound x y z p mode

/-- `x − y·z` rounded once to precision `p` with `mode`, with the comparison against the exact
value. -/
def subMulRatPrecRound (x y : AzFloat) (z : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  fusedMulRat subPrecRound subRatPrecRound x y z p mode

/-- `x + y·z` rounded to nearest at the larger of the floats' precisions. -/
def addMulRat (x y : AzFloat) (z : AzRat) : AzFloat :=
  (addMulRatPrecRound x y z (combinedPrecision x y) .Nearest).1

/-- `x − y·z` rounded to nearest at the larger of the floats' precisions. -/
def subMulRat (x y : AzFloat) (z : AzRat) : AzFloat :=
  (subMulRatPrecRound x y z (combinedPrecision x y) .Nearest).1

/-- The correctly rounded `x + y·z` for `Float`s `x`, `y` and a rational `z`. -/
def addMulRatFloat64 (x y : Float) (z : AzRat) : Float := emulate₂Rat addMulRatPrecRound x y z

/-- The correctly rounded `x − y·z` for `Float`s `x`, `y` and a rational `z`. -/
def subMulRatFloat64 (x y : Float) (z : AzRat) : Float := emulate₂Rat subMulRatPrecRound x y z

end Azurite.AzFloat
