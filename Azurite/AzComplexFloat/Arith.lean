/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzComplexFloat.Basic
import Azurite.AzFloat.MulAddMul
import Azurite.AzFloat.Div
import Azurite.AzFloat.Sum
import Azurite.AzFloat.Shift
import Azurite.AzFloat.SinCos

/-!
# Rounded arithmetic on `AzComplexFloat`

Every function rounds the real part to precision `pRe` with the mode `mRe` and the imaginary
part to precision `pIm` with the mode `mIm` (pairs of precisions and modes, as in MPC and
rug), and returns the two comparisons (real
part, imaginary part) with the exact value.

* `addPrecRound`, `subPrecRound`, `mulPrecRound`, `sqrPrecRound`, `mulFloatPrecRound`,
  `divFloatPrecRound`: each component is one rounding of its exact value — for the product,
  of `ac − bd` and `ad + bc` (`AzFloat.mulSubMulPrecRound`, `mulAddMulPrecRound`).  With
  `NaN` or infinite components the extended-real rules of the real operations apply to these
  formulas component by component.
* `normSqrPrecRound`: `a² + b²`, one rounding.
* `divPrecRound`: for finite operands and a nonzero divisor, the exact numerators
  `ac + bd`, `bc − ad` and the exact denominator `c² + d²` are formed and each quotient is
  rounded once.  **Everything else gives `NaN`** in both components (division by zero and
  non-finite operands: conventions for complex infinities are not fixed yet).  The exact
  sums cost a precision that grows with the gap between the exponents of the terms.
* `cisPrecRound`: `cos x + i sin x` for a real float `x`.
-/

namespace Azurite.AzComplexFloat

/-- The result of a rounded complex operation: the value and the comparisons of its real and
imaginary parts with the exact ones. -/
abbrev Rounded : Type := AzComplexFloat × Ordering × Ordering

/-- Pair two rounded real results into a rounded complex one. -/
def pair (r i : AzFloat × Ordering) : Rounded := (⟨r.1, i.1⟩, r.2, i.2)

/-- `z + w`, the real part rounded to `(pRe, mRe)`, the imaginary part to `(pIm, mIm)`. -/
def addPrecRound (z w : AzComplexFloat) (pRe pIm : Nat) (mRe mIm : RoundingMode) : Rounded :=
  pair (AzFloat.addPrecRound z.re w.re pRe mRe) (AzFloat.addPrecRound z.im w.im pIm mIm)

/-- `z − w`, the real part rounded to `(pRe, mRe)`, the imaginary part to `(pIm, mIm)`. -/
def subPrecRound (z w : AzComplexFloat) (pRe pIm : Nat) (mRe mIm : RoundingMode) : Rounded :=
  pair (AzFloat.subPrecRound z.re w.re pRe mRe) (AzFloat.subPrecRound z.im w.im pIm mIm)

/-- `z · w`: `ac − bd` and `ad + bc`, rounded once to `(pRe, mRe)` and `(pIm, mIm)`. -/
def mulPrecRound (z w : AzComplexFloat) (pRe pIm : Nat) (mRe mIm : RoundingMode) : Rounded :=
  pair (AzFloat.mulSubMulPrecRound z.re w.re z.im w.im pRe mRe)
    (AzFloat.mulAddMulPrecRound z.re w.im z.im w.re pIm mIm)

/-- `z²`: `a² − b²` and `2ab`, rounded once to `(pRe, mRe)` and `(pIm, mIm)`. -/
def sqrPrecRound (z : AzComplexFloat) (pRe pIm : Nat) (mRe mIm : RoundingMode) : Rounded :=
  pair (AzFloat.mulSubMulPrecRound z.re z.re z.im z.im pRe mRe)
    (AzFloat.mulPrecRound (z.re <<< AzInt.ofInt 1) z.im pIm mIm)

/-- `z · x` for a real float `x`, the real part rounded to `(pRe, mRe)`, the imaginary
part to `(pIm, mIm)`. -/
def mulFloatPrecRound (z : AzComplexFloat) (x : AzFloat) (pRe pIm : Nat) (mRe mIm : RoundingMode) :
    Rounded :=
  pair (AzFloat.mulPrecRound z.re x pRe mRe) (AzFloat.mulPrecRound z.im x pIm mIm)

/-- `z / x` for a real float `x`, the real part rounded to `(pRe, mRe)`, the imaginary
part to `(pIm, mIm)`. -/
def divFloatPrecRound (z : AzComplexFloat) (x : AzFloat) (pRe pIm : Nat) (mRe mIm : RoundingMode) :
    Rounded :=
  pair (AzFloat.divPrecRound z.re x pRe mRe) (AzFloat.divPrecRound z.im x pIm mIm)

/-- `|z|² = a² + b²`, rounded once to precision `p` with `mode`. -/
def normSqrPrecRound (z : AzComplexFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  AzFloat.mulAddMulPrecRound z.re z.re z.im z.im p mode

/-- `z / w`, the real part rounded to `(pRe, mRe)`, the imaginary part to `(pIm, mIm)`,
for finite `z` and finite nonzero `w`; `NaN` otherwise. -/
def divPrecRound (z w : AzComplexFloat) (pRe pIm : Nat) (mRe mIm : RoundingMode) : Rounded :=
  if z.isFinite && w.isFinite && !w.isZero then
    let den := AzFloat.exactAdd (AzFloat.exactMul w.re w.re) (AzFloat.exactMul w.im w.im)
    let nr := AzFloat.exactAdd (AzFloat.exactMul z.re w.re) (AzFloat.exactMul z.im w.im)
    let ni := AzFloat.exactSub (AzFloat.exactMul z.im w.re) (AzFloat.exactMul z.re w.im)
    pair (AzFloat.divPrecRound nr den pRe mRe) (AzFloat.divPrecRound ni den pIm mIm)
  else (nan, .eq, .eq)

/-- `e^(ix) = cos x + i sin x` for a real float `x`: the cosine rounded to `(pRe, mRe)`, the
sine to `(pIm, mIm)` (one computation when precisions and modes agree). -/
def cisPrecRound (x : AzFloat) (pRe pIm : Nat) (mRe mIm : RoundingMode) : Rounded :=
  if pRe = pIm ∧ mRe = mIm then
    let sc := AzFloat.sinCosPrecRound x pRe mRe
    pair sc.2 sc.1
  else pair (AzFloat.cosPrecRound x pRe mRe) (AzFloat.sinPrecRound x pIm mIm)

end Azurite.AzComplexFloat
