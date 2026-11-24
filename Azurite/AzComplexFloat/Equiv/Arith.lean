/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzComplexFloat.Arith
import Azurite.AzFloat.Equiv.MulAddMul
import Azurite.AzFloat.Equiv.Div
import Azurite.AzFloat.Equiv.Sum
import Azurite.AzFloat.Equiv.Shift
import Azurite.AzFloat.Equiv.SinCos
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Correct rounding of the arithmetic on `AzComplexFloat`

`toComplex z : ℂ` is the value of a finite complex float and `roundC pRe pIm mRe mIm v` the complex
number `v` with both components correctly rounded (`AzFloat.roundVal`).  For finite operands
every operation of `AzComplexFloat/Arith.lean` **equals** the rounding of its exact value:

* `addPrecRound_eq_roundC`, `subPrecRound_eq_roundC`, `mulPrecRound_eq_roundC`,
  `sqrPrecRound_eq_roundC`, `mulFloatPrecRound_eq_roundC`;
* `divFloatPrecRound_eq_roundC` (real divisor `≠ 0`), `divPrecRound_eq_roundC` (divisor
  `≠ 0`);
* `normSqrPrecRound_eq_roundVal` (`Complex.normSq`), `cisPrecRound_eq_roundC`
  (`Complex.exp (x · I)`).

For all operands (`NaN` and infinities included) the componentwise operations are the
liftings of the extended-real specifications: `addPrecRound_eq`, `subPrecRound_eq`,
`mulPrecRound_eq`, `mulFloatPrecRound_eq`, `divFloatPrecRound_eq`, `normSqrPrecRound_eq`,
`cisPrecRound_eq`.
-/

namespace Azurite.AzComplexFloat

open AzFloat

/-- The value of a complex float with finite components (`0` stands in for a non-finite
component). -/
noncomputable def toComplex (z : AzComplexFloat) : ℂ := ⟨fval z.re, fval z.im⟩

/-- **The specification**: a complex number with both components correctly rounded to
`(pRe, mRe)` and `(pIm, mIm)`, and the two comparisons. -/
noncomputable def roundC (pRe pIm : ℕ) [NeZero pRe] [NeZero pIm] (mRe mIm : RoundingMode)
    (v : ℂ) : Rounded :=
  pair (roundVal pRe mRe (some ((v.re : ℝ) : EReal))) (roundVal pIm mIm (some ((v.im : ℝ) : EReal)))

@[simp] theorem toComplex_re (z : AzComplexFloat) : (toComplex z).re = fval z.re := rfl
@[simp] theorem toComplex_im (z : AzComplexFloat) : (toComplex z).im = fval z.im := rfl

theorem isFinite_iff (z : AzComplexFloat) :
    z.isFinite = true ↔ z.re.isFinite = true ∧ z.im.isFinite = true := by
  unfold isFinite
  rw [Bool.and_eq_true]

/-! ### All operands -/

variable (p pRe pIm : ℕ) [NeZero p] [NeZero pRe] [NeZero pIm] (mRe mIm mode : RoundingMode)

theorem addPrecRound_eq (z w : AzComplexFloat) :
    addPrecRound z w pRe pIm mRe mIm
      = pair (liftVal₂ Spec.add z.re w.re pRe mRe) (liftVal₂ Spec.add z.im w.im pIm mIm) := by
  unfold addPrecRound
  rw [addPrecRound_eq_liftVal₂, addPrecRound_eq_liftVal₂]

theorem subPrecRound_eq (z w : AzComplexFloat) :
    subPrecRound z w pRe pIm mRe mIm
      = pair (liftVal₂ Spec.sub z.re w.re pRe mRe) (liftVal₂ Spec.sub z.im w.im pIm mIm) := by
  unfold subPrecRound
  rw [subPrecRound_eq_liftVal₂, subPrecRound_eq_liftVal₂]

theorem mulPrecRound_eq (z w : AzComplexFloat) :
    mulPrecRound z w pRe pIm mRe mIm
      = pair (liftVal₄ Spec.mulSubMul z.re w.re z.im w.im pRe mRe)
          (liftVal₄ Spec.mulAddMul z.re w.im z.im w.re pIm mIm) := by
  unfold mulPrecRound
  rw [mulSubMulPrecRound_eq_liftVal₄, mulAddMulPrecRound_eq_liftVal₄]

theorem mulFloatPrecRound_eq (z : AzComplexFloat) (x : AzFloat) :
    mulFloatPrecRound z x pRe pIm mRe mIm
      = pair (liftVal₂ Spec.mul z.re x pRe mRe) (liftVal₂ Spec.mul z.im x pIm mIm) := by
  unfold mulFloatPrecRound
  rw [mulPrecRound_eq_liftVal₂, mulPrecRound_eq_liftVal₂]

theorem divFloatPrecRound_eq (z : AzComplexFloat) (x : AzFloat) :
    divFloatPrecRound z x pRe pIm mRe mIm
      = pair (liftVal₂ Spec.div z.re x pRe mRe) (liftVal₂ Spec.div z.im x pIm mIm) := by
  unfold divFloatPrecRound
  rw [divPrecRound_eq_liftVal₂, divPrecRound_eq_liftVal₂]

theorem normSqrPrecRound_eq (z : AzComplexFloat) :
    normSqrPrecRound z p mode = liftVal₄ Spec.mulAddMul z.re z.re z.im z.im p mode := by
  unfold normSqrPrecRound
  rw [mulAddMulPrecRound_eq_liftVal₄]

theorem cisPrecRound_eq (x : AzFloat) :
    cisPrecRound x pRe pIm mRe mIm
      = pair (liftVal Spec.cos x pRe mRe) (liftVal Spec.sin x pIm mIm) := by
  unfold cisPrecRound
  split
  · next h =>
    obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    rw [sinCosPrecRound_eq_liftVal]
  · rw [cosPrecRound_eq_liftVal, sinPrecRound_eq_liftVal]

/-! ### Finite operands: liftings at real values -/

theorem liftVal₂_finite {f : EReal → EReal → Option EReal} {g : ℝ → ℝ → ℝ}
    (hf : ∀ a b : ℝ, f a b = some ((g a b : ℝ) : EReal)) {x y : AzFloat}
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    liftVal₂ f x y p mode = roundVal p mode (some ((g (fval x) (fval y) : ℝ) : EReal)) := by
  unfold liftVal₂
  rw [toVal_of_isFinite hx, toVal_of_isFinite hy, Option.bind_some, Option.bind_some, hf]

theorem liftVal₄_finite {f : EReal → EReal → EReal → EReal → Option EReal}
    {g : ℝ → ℝ → ℝ → ℝ → ℝ}
    (hf : ∀ a b c d : ℝ, f a b c d = some ((g a b c d : ℝ) : EReal)) {x y z w : AzFloat}
    (hx : x.isFinite = true) (hy : y.isFinite = true) (hz : z.isFinite = true)
    (hw : w.isFinite = true) :
    liftVal₄ f x y z w p mode
      = roundVal p mode (some ((g (fval x) (fval y) (fval z) (fval w) : ℝ) : EReal)) := by
  unfold liftVal₄
  rw [toVal_of_isFinite hx, toVal_of_isFinite hy, toVal_of_isFinite hz, toVal_of_isFinite hw,
    Option.bind_some, Option.bind_some, Option.bind_some, Option.bind_some, hf]

theorem sub_coe_coe (a b : ℝ) : Spec.sub (a : EReal) (b : EReal) = some ((a - b : ℝ) : EReal) := by
  unfold Spec.sub
  rw [← EReal.coe_neg, Spec.add_coe_coe, sub_eq_add_neg]

theorem mulAddMul_coe (a b c d : ℝ) :
    Spec.mulAddMul (a : EReal) b c d = some ((a * b + c * d : ℝ) : EReal) := by
  unfold Spec.mulAddMul
  rw [Spec.mul_coe_coe, Spec.mul_coe_coe, Option.bind_some, Option.bind_some, Spec.add_coe_coe]

theorem mulSubMul_coe (a b c d : ℝ) :
    Spec.mulSubMul (a : EReal) b c d = some ((a * b - c * d : ℝ) : EReal) := by
  unfold Spec.mulSubMul
  rw [Spec.mul_coe_coe, Spec.mul_coe_coe, Option.bind_some, Option.bind_some, sub_coe_coe]

/-! ### Finite operands: the operations -/

variable {z w : AzComplexFloat}

/-- **Addition is correctly rounded.** -/
theorem addPrecRound_eq_roundC (hz : z.isFinite = true) (hw : w.isFinite = true) :
    addPrecRound z w pRe pIm mRe mIm = roundC pRe pIm mRe mIm (toComplex z + toComplex w) := by
  obtain ⟨hz1, hz2⟩ := (isFinite_iff z).mp hz
  obtain ⟨hw1, hw2⟩ := (isFinite_iff w).mp hw
  rw [addPrecRound_eq, liftVal₂_finite pRe mRe Spec.add_coe_coe hz1 hw1,
    liftVal₂_finite pIm mIm Spec.add_coe_coe hz2 hw2]
  rfl

/-- **Subtraction is correctly rounded.** -/
theorem subPrecRound_eq_roundC (hz : z.isFinite = true) (hw : w.isFinite = true) :
    subPrecRound z w pRe pIm mRe mIm = roundC pRe pIm mRe mIm (toComplex z - toComplex w) := by
  obtain ⟨hz1, hz2⟩ := (isFinite_iff z).mp hz
  obtain ⟨hw1, hw2⟩ := (isFinite_iff w).mp hw
  rw [subPrecRound_eq, liftVal₂_finite pRe mRe sub_coe_coe hz1 hw1,
    liftVal₂_finite pIm mIm sub_coe_coe hz2 hw2]
  rfl

/-- **Multiplication is correctly rounded.** -/
theorem mulPrecRound_eq_roundC (hz : z.isFinite = true) (hw : w.isFinite = true) :
    mulPrecRound z w pRe pIm mRe mIm = roundC pRe pIm mRe mIm (toComplex z * toComplex w) := by
  obtain ⟨hz1, hz2⟩ := (isFinite_iff z).mp hz
  obtain ⟨hw1, hw2⟩ := (isFinite_iff w).mp hw
  rw [mulPrecRound_eq, liftVal₄_finite pRe mRe mulSubMul_coe hz1 hw1 hz2 hw2,
    liftVal₄_finite pIm mIm mulAddMul_coe hz1 hw2 hz2 hw1]
  unfold roundC
  rw [Complex.mul_re, Complex.mul_im]
  rfl

/-- **Squaring is correctly rounded.** -/
theorem sqrPrecRound_eq_roundC (hz : z.isFinite = true) :
    sqrPrecRound z pRe pIm mRe mIm = roundC pRe pIm mRe mIm (toComplex z ^ 2) := by
  obtain ⟨hz1, hz2⟩ := (isFinite_iff z).mp hz
  unfold sqrPrecRound
  have hsh : (z.re <<< AzInt.ofInt 1).toVal = some ((2 * fval z.re : ℝ) : EReal) := by
    show (shiftLeft z.re (AzInt.ofInt 1)).toVal = _
    rw [toVal_shiftLeft, toVal_of_isFinite hz1, Option.map_some, AzInt.toInt_ofInt,
      ← EReal.coe_mul]
    norm_num [mul_comm]
  rw [mulSubMulPrecRound_eq_liftVal₄, liftVal₄_finite pRe mRe mulSubMul_coe hz1 hz1 hz2 hz2,
    mulPrecRound_eq_liftVal₂]
  unfold liftVal₂ roundC
  rw [hsh, toVal_of_isFinite hz2, Option.bind_some, Option.bind_some, Spec.mul_coe_coe]
  have h1 : (toComplex z ^ 2).re = fval z.re * fval z.re - fval z.im * fval z.im := by
    rw [pow_two, Complex.mul_re]; rfl
  have h2 : (toComplex z ^ 2).im = 2 * fval z.re * fval z.im := by
    rw [pow_two, Complex.mul_im]; simp only [toComplex_re, toComplex_im]; ring
  rw [h1, h2]

/-- **Multiplication by a real float is correctly rounded.** -/
theorem mulFloatPrecRound_eq_roundC (hz : z.isFinite = true) {x : AzFloat}
    (hx : x.isFinite = true) :
    mulFloatPrecRound z x pRe pIm mRe mIm
      = roundC pRe pIm mRe mIm (toComplex z * (fval x : ℂ)) := by
  obtain ⟨hz1, hz2⟩ := (isFinite_iff z).mp hz
  rw [mulFloatPrecRound_eq, liftVal₂_finite pRe mRe Spec.mul_coe_coe hz1 hx,
    liftVal₂_finite pIm mIm Spec.mul_coe_coe hz2 hx]
  unfold roundC
  rw [Complex.mul_re, Complex.mul_im]
  simp

/-- **Division by a nonzero real float is correctly rounded.** -/
theorem divFloatPrecRound_eq_roundC (hz : z.isFinite = true) {x : AzFloat}
    (hx : x.isFinite = true) (hx0 : fval x ≠ 0) :
    divFloatPrecRound z x pRe pIm mRe mIm
      = roundC pRe pIm mRe mIm (toComplex z / (fval x : ℂ)) := by
  obtain ⟨hz1, hz2⟩ := (isFinite_iff z).mp hz
  rw [divFloatPrecRound_eq]
  unfold liftVal₂ roundC
  rw [toVal_of_isFinite hz1, toVal_of_isFinite hz2, toVal_of_isFinite hx, Option.bind_some,
    Option.bind_some, Option.bind_some, Option.bind_some, Spec.div_coe_coe _ _ hx0,
    Spec.div_coe_coe _ _ hx0,
    Complex.div_ofReal_re, Complex.div_ofReal_im]
  rfl

/-- **`|z|²` is correctly rounded.** -/
theorem normSqrPrecRound_eq_roundVal (hz : z.isFinite = true) :
    normSqrPrecRound z p mode
      = roundVal p mode (some ((Complex.normSq (toComplex z) : ℝ) : EReal)) := by
  obtain ⟨hz1, hz2⟩ := (isFinite_iff z).mp hz
  rw [normSqrPrecRound_eq, liftVal₄_finite p mode mulAddMul_coe hz1 hz1 hz2 hz2,
    Complex.normSq_apply]
  rfl

/-- **`e^(ix)` is correctly rounded.** -/
theorem cisPrecRound_eq_roundC {x : AzFloat} (hx : x.isFinite = true) :
    cisPrecRound x pRe pIm mRe mIm
      = roundC pRe pIm mRe mIm (Complex.exp ((fval x : ℂ) * Complex.I)) := by
  rw [cisPrecRound_eq]
  unfold liftVal roundC
  rw [toVal_of_isFinite hx, Option.bind_some, Option.bind_some, Spec.cos_coe, Spec.sin_coe,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-! ### Division -/

theorem toVal_exactMul_finite {x y : AzFloat} (hx : x.isFinite = true)
    (hy : y.isFinite = true) :
    (exactMul x y).toVal = some ((fval x * fval y : ℝ) : EReal) := by
  rw [toVal_exactMul, toVal_of_isFinite hx, toVal_of_isFinite hy, Option.bind_some,
    Option.bind_some, Spec.mul_coe_coe]

theorem isFinite_exactMul {x y : AzFloat} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (exactMul x y).isFinite = true :=
  isFinite_of_toVal_coe (toVal_exactMul_finite hx hy)

theorem fval_exactMul {x y : AzFloat} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    fval (exactMul x y) = fval x * fval y :=
  fval_of_toVal_coe (toVal_exactMul_finite hx hy)

theorem toVal_neg_finite {x : AzFloat} (hx : x.isFinite = true) :
    (-x).toVal = some ((-fval x : ℝ) : EReal) := by
  rw [toVal_neg, toVal_of_isFinite hx, Option.map_some, EReal.coe_neg]

theorem toComplex_eq_zero_of_isZero (h : w.isZero = true) : toComplex w = 0 := by
  unfold isZero at h
  obtain ⟨h1, h2⟩ := of_decide_eq_true h
  apply Complex.ext
  · rw [toComplex_re, h1]; rfl
  · rw [toComplex_im, h2]; rfl

/-- **Division is correctly rounded**, for finite operands and a nonzero divisor. -/
theorem divPrecRound_eq_roundC (hz : z.isFinite = true) (hw : w.isFinite = true)
    (hw0 : toComplex w ≠ 0) :
    divPrecRound z w pRe pIm mRe mIm = roundC pRe pIm mRe mIm (toComplex z / toComplex w) := by
  obtain ⟨hz1, hz2⟩ := (isFinite_iff z).mp hz
  obtain ⟨hw1, hw2⟩ := (isFinite_iff w).mp hw
  have hnz : w.isZero = false := by
    by_contra h
    exact hw0 (toComplex_eq_zero_of_isZero (by simpa using h))
  unfold divPrecRound
  rw [hz, hw, hnz, Bool.and_self, Bool.not_false, Bool.and_self, ite_eq_left rfl]
  have hD : fval w.re * fval w.re + fval w.im * fval w.im ≠ 0 := by
    intro h
    obtain ⟨h1, h2⟩ := mul_self_add_mul_self_eq_zero.mp h
    exact hw0 (Complex.ext h1 h2)
  have hden : (exactAdd (exactMul w.re w.re) (exactMul w.im w.im)).toVal
      = some ((fval w.re * fval w.re + fval w.im * fval w.im : ℝ) : EReal) := by
    rw [toVal_exactAdd (isFinite_exactMul hw1 hw1) (isFinite_exactMul hw2 hw2),
      fval_exactMul hw1 hw1, fval_exactMul hw2 hw2]
  have hnr : (exactAdd (exactMul z.re w.re) (exactMul z.im w.im)).toVal
      = some ((fval z.re * fval w.re + fval z.im * fval w.im : ℝ) : EReal) := by
    rw [toVal_exactAdd (isFinite_exactMul hz1 hw1) (isFinite_exactMul hz2 hw2),
      fval_exactMul hz1 hw1, fval_exactMul hz2 hw2]
  have hni : (exactSub (exactMul z.im w.re) (exactMul z.re w.im)).toVal
      = some ((fval z.im * fval w.re - fval z.re * fval w.im : ℝ) : EReal) := by
    unfold exactSub
    have hf : (-(exactMul z.re w.im)).isFinite = true :=
      isFinite_of_toVal_coe (toVal_neg_finite (isFinite_exactMul hz1 hw2))
    rw [toVal_exactAdd (isFinite_exactMul hz2 hw1) hf, fval_exactMul hz2 hw1,
      fval_of_toVal_coe (toVal_neg_finite (isFinite_exactMul hz1 hw2)), fval_exactMul hz1 hw2,
      sub_eq_add_neg]
  simp only []
  rw [divPrecRound_eq_liftVal₂, divPrecRound_eq_liftVal₂]
  unfold liftVal₂ roundC
  rw [hden, hnr, hni, Option.bind_some, Option.bind_some, Option.bind_some, Option.bind_some,
    Spec.div_coe_coe _ _ hD, Spec.div_coe_coe _ _ hD]
  have h1 : (toComplex z / toComplex w).re
      = (fval z.re * fval w.re + fval z.im * fval w.im)
        / (fval w.re * fval w.re + fval w.im * fval w.im) := by
    rw [Complex.div_re, Complex.normSq_apply]
    simp only [toComplex_re, toComplex_im]
    field_simp
  have h2 : (toComplex z / toComplex w).im
      = (fval z.im * fval w.re - fval z.re * fval w.im)
        / (fval w.re * fval w.re + fval w.im * fval w.im) := by
    rw [Complex.div_im, Complex.normSq_apply]
    simp only [toComplex_re, toComplex_im]
    field_simp
  rw [h1, h2]

end Azurite.AzComplexFloat
