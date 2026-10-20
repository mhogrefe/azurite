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
import Azurite.AzRat.Mul

/-!
# Fused multiply-add and multiply-subtract with a rational factor

`addMulRatPrecRound x y z p mode` is `x + y·z` with a single rounding for floats `x`, `y` and a
rational `z`, and `subMulRatPrecRound` is `x − y·z`.  A finite `y` is converted to a rational
exactly (`toAzRat?`), the product `y·z` is formed exactly in `AzRat`, and the one rounding is
the float-plus-rational addition `addRatPrecRound` (or `subRatPrecRound`).  An infinite `y`
gives `±∞` (or `NaN` when `z = 0`), added with `addPrecRound`.  `fusedMulRat` is the common
shape, parameterized by the float–float and float–rational operations.

`addMulRatFloat64`/`subMulRatFloat64` are the correctly rounded `Float` versions.
-/

namespace Azurite.AzFloat

/-- `x ⊕ y·z` for a rational `z`, with the float–float operation `opF` and the float–rational
operation `opR` doing the single rounding: `y·z` is exact in `AzRat` for a finite `y`; an infinite
`y` gives an infinity of the product's sign (`NaN` when `z = 0`). -/
def fusedMulRat (opF : AzFloat → AzFloat → Nat → RoundingMode → AzFloat × Ordering)
    (opR : AzFloat → AzRat → Nat → RoundingMode → AzFloat × Ordering)
    (x y : AzFloat) (z : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match y.toAzRat? with
  | some r => opR x (r * z) p mode
  | none =>
    match y with
    | infinity s => if z.num = 0 then (nan, .eq) else opF x (infinity (s == z.sign)) p mode
    | _ => (nan, .eq)

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
