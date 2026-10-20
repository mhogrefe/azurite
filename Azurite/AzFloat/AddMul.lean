/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Add
import Azurite.AzFloat.Mul
import Azurite.AzFloat.Float64Emulate

/-!
# Fused multiply-add and multiply-subtract

`addMulPrecRound x y z p mode` is `x + y·z` with a single rounding, and `subMulPrecRound` is
`x − y·z`.  The product of two floats of precisions `q₁` and `q₂` is exact at precision
`q₁ + q₂` (`exactMul`, a `mulPrecRound` that loses nothing, `Equiv/AddMul.lean`), so the fused
operations are an exact product followed by one correctly rounded addition or subtraction.
Special values follow `Spec.mul` then `Spec.add`: a `NaN` anywhere, `0 · (±∞)`, or `∞ − ∞`
give `NaN`.

`addMulFloat64`/`subMulFloat64` are the correctly rounded `Float` versions (IEEE `fma`).
-/

namespace Azurite.AzFloat

/-- The precision at which the product of two floats is exact: the sum of their precisions. -/
def exactProductPrec (y z : AzFloat) : Nat := y.precision?.getD 1 + z.precision?.getD 1

/-- `y · z` exactly (special values as for `mulPrecRound`). -/
def exactMul (y z : AzFloat) : AzFloat := (mulPrecRound y z (exactProductPrec y z) .Floor).1

/-- `x + y·z` rounded once to precision `p` with `mode`, with the comparison against the exact
value. -/
def addMulPrecRound (x y z : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  addPrecRound x (exactMul y z) p mode

/-- `x − y·z` rounded once to precision `p` with `mode`, with the comparison against the exact
value. -/
def subMulPrecRound (x y z : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  subPrecRound x (exactMul y z) p mode

/-- The precision for `addMul`/`subMul`: the largest of the operands'. -/
def fusedPrecision (x y z : AzFloat) : Nat :=
  max (combinedPrecision x y) (z.precision?.getD 1)

/-- `x + y·z` rounded to nearest at the largest of the operands' precisions. -/
def addMul (x y z : AzFloat) : AzFloat :=
  (addMulPrecRound x y z (fusedPrecision x y z) .Nearest).1

/-- `x − y·z` rounded to nearest at the largest of the operands' precisions. -/
def subMul (x y z : AzFloat) : AzFloat :=
  (subMulPrecRound x y z (fusedPrecision x y z) .Nearest).1

/-- The correctly rounded `x + y·z` on `Float`s (IEEE `fma`): one rounding of the exact value. -/
def addMulFloat64 (x y z : Float) : Float := emulate₃ addMulPrecRound x y z

/-- The correctly rounded `x − y·z` on `Float`s: one rounding of the exact value. -/
def subMulFloat64 (x y z : Float) : Float := emulate₃ subMulPrecRound x y z

end Azurite.AzFloat
