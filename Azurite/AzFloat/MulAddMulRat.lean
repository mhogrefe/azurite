/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AddMul
import Azurite.AzFloat.AddMulRat

/-!
# A product plus or minus a product with a rational factor

`mulAddMulRatPrecRound x y z w p mode` is `x·y + z·w` with a single rounding for floats `x`,
`y`, `z` and a rational `w`, and `mulSubMulRatPrecRound` is `x·y − z·w`: the product `x·y` is
formed exactly (`exactMul`) and the fused `addMulRatPrecRound`/`subMulRatPrecRound` of
`AddMulRat` adds `z·w` with the one rounding.  Special values follow `Spec.mul` then `Spec.add`.

`mulAddMulRatFloat64`/`mulSubMulRatFloat64` are the correctly rounded `Float` versions.
-/

namespace Azurite.AzFloat

/-- `x·y + z·w` rounded once to precision `p` with `mode`, with the comparison against the exact
value. -/
def mulAddMulRatPrecRound (x y z : AzFloat) (w : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  addMulRatPrecRound (exactMul x y) z w p mode

/-- `x·y − z·w` rounded once to precision `p` with `mode`, with the comparison against the exact
value. -/
def mulSubMulRatPrecRound (x y z : AzFloat) (w : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  subMulRatPrecRound (exactMul x y) z w p mode

/-- `x·y + z·w` rounded to nearest at the largest of the floats' precisions. -/
def mulAddMulRat (x y z : AzFloat) (w : AzRat) : AzFloat :=
  (mulAddMulRatPrecRound x y z w (fusedPrecision x y z) .Nearest).1

/-- `x·y − z·w` rounded to nearest at the largest of the floats' precisions. -/
def mulSubMulRat (x y z : AzFloat) (w : AzRat) : AzFloat :=
  (mulSubMulRatPrecRound x y z w (fusedPrecision x y z) .Nearest).1

/-- The correctly rounded `x·y + z·w` for `Float`s `x`, `y`, `z` and a rational `w`. -/
def mulAddMulRatFloat64 (x y z : Float) (w : AzRat) : Float :=
  emulate₃Rat mulAddMulRatPrecRound x y z w

/-- The correctly rounded `x·y − z·w` for `Float`s `x`, `y`, `z` and a rational `w`. -/
def mulSubMulRatFloat64 (x y z : Float) (w : AzRat) : Float :=
  emulate₃Rat mulSubMulRatPrecRound x y z w

end Azurite.AzFloat
