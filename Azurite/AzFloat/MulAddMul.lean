/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AddMul

/-!
# Sums and differences of two products

`mulAddMulPrecRound x y z w p mode` is `x·y + z·w` with a single rounding, and
`mulSubMulPrecRound` is `x·y − z·w`: both products are formed exactly (`exactMul`) and one
correctly rounded addition or subtraction follows.  Special values follow `Spec.mul` then
`Spec.add`: a `NaN` anywhere, `0 · (±∞)`, or `∞ − ∞` give `NaN`.

`mulAddMulFloat64`/`mulSubMulFloat64` are the correctly rounded `Float` versions.
-/

namespace Azurite.AzFloat

/-- `x·y + z·w` rounded once to precision `p` with `mode`, with the comparison against the exact
value. -/
def mulAddMulPrecRound (x y z w : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  addPrecRound (exactMul x y) (exactMul z w) p mode

/-- `x·y − z·w` rounded once to precision `p` with `mode`, with the comparison against the exact
value. -/
def mulSubMulPrecRound (x y z w : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  subPrecRound (exactMul x y) (exactMul z w) p mode

/-- The precision for `mulAddMul`/`mulSubMul`: the largest of the operands'. -/
def fusedPrecision₄ (x y z w : AzFloat) : Nat :=
  max (combinedPrecision x y) (combinedPrecision z w)

/-- `x·y + z·w` rounded to nearest at the largest of the operands' precisions. -/
def mulAddMul (x y z w : AzFloat) : AzFloat :=
  (mulAddMulPrecRound x y z w (fusedPrecision₄ x y z w) .Nearest).1

/-- `x·y − z·w` rounded to nearest at the largest of the operands' precisions. -/
def mulSubMul (x y z w : AzFloat) : AzFloat :=
  (mulSubMulPrecRound x y z w (fusedPrecision₄ x y z w) .Nearest).1

/-- The correctly rounded `x·y + z·w` on `Float`s: one rounding of the exact value. -/
def mulAddMulFloat64 (x y z w : Float) : Float := emulate₄ mulAddMulPrecRound x y z w

/-- The correctly rounded `x·y − z·w` on `Float`s: one rounding of the exact value. -/
def mulSubMulFloat64 (x y z w : Float) : Float := emulate₄ mulSubMulPrecRound x y z w

end Azurite.AzFloat
