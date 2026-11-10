/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LambertW
import Azurite.AzFloat.Equiv.RatPowRat

/-!
# Equivalence: the real branches of the Lambert `W` function

`Spec.lambertW0`, `Spec.lambertWm1 : EReal → Option EReal` are the exact functions on the
extended reals (`none` is `NaN`), and `lambertW0PrecRound_eq`, `lambertWm1PrecRound_eq`
(floats), `lambertW0RatPrecRound_eq`, `lambertWm1RatPrecRound_eq` (rationals) say that the
drivers are their correct roundings in every mode, with the exact comparison and without fuel.
The three Ziv loops `lambertW0Pos`, `lambertW0Neg`, `lambertWm1Neg` are proven once for any
enclosed rational target (`lambertW0Pos_eq`, `lambertW0Neg_eq`, `lambertWm1Neg_eq`).
-/

open Real

namespace Azurite.AzFloat

namespace Spec

/-- `W₀` on the extended reals: `+∞ ↦ +∞`, `NaN` below `−e⁻¹` (and at `−∞`). -/
noncomputable def lambertW0 (a : EReal) : Option EReal :=
  if a = ⊤ then some ⊤ else if a < ((-Real.exp (-1) : ℝ) : EReal) then none
  else some ((Azurite.DLMF.lambertW0 a.toReal : ℝ) : EReal)

/-- `W₋₁` on the extended reals: `0 ↦ −∞` (the limit from the left), `NaN` outside `[−e⁻¹, 0]`
and at `±∞`. -/
noncomputable def lambertWm1 (a : EReal) : Option EReal :=
  if a = ⊤ then none else if a < ((-Real.exp (-1) : ℝ) : EReal) then none
  else if a = 0 then some ⊥ else if 0 < a then none
  else some ((Azurite.DLMF.lambertWm1 a.toReal : ℝ) : EReal)

theorem lambertW0_top : lambertW0 ⊤ = some ⊤ := by simp [lambertW0]

theorem lambertW0_bot : lambertW0 ⊥ = none := by
  unfold lambertW0
  rw [ite_eq_right bot_ne_top, ite_eq_left (EReal.bot_lt_coe _)]

theorem lambertW0_coe_of_lt {xv : ℝ} (h : xv < -Real.exp (-1)) : lambertW0 (xv : EReal) = none := by
  unfold lambertW0
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_left (EReal.coe_lt_coe_iff.mpr h)]

theorem lambertW0_coe_of_le {xv : ℝ} (h : -Real.exp (-1) ≤ xv) :
    lambertW0 (xv : EReal) = some ((Azurite.DLMF.lambertW0 xv : ℝ) : EReal) := by
  unfold lambertW0
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_right (not_lt.mpr (EReal.coe_le_coe_iff.mpr h)),
    EReal.toReal_coe]

theorem lambertWm1_top : lambertWm1 ⊤ = none := by simp [lambertWm1]

theorem lambertWm1_bot : lambertWm1 ⊥ = none := by
  unfold lambertWm1
  rw [ite_eq_right bot_ne_top, ite_eq_left (EReal.bot_lt_coe _)]

theorem lambertWm1_zero : lambertWm1 0 = some ⊥ := by
  unfold lambertWm1
  have h : ¬ ((0 : EReal) < ((-Real.exp (-1) : ℝ) : EReal)) := by
    rw [← EReal.coe_zero, EReal.coe_lt_coe_iff, not_lt]
    linarith [Real.exp_pos (-1)]
  rw [ite_eq_right EReal.zero_ne_top, ite_eq_right h, ite_eq_left rfl]

theorem lambertWm1_coe_of_lt {xv : ℝ} (h : xv < -Real.exp (-1)) :
    lambertWm1 (xv : EReal) = none := by
  unfold lambertWm1
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_left (EReal.coe_lt_coe_iff.mpr h)]

theorem lambertWm1_coe_of_pos {xv : ℝ} (h : 0 < xv) : lambertWm1 (xv : EReal) = none := by
  unfold lambertWm1
  have h1 : ¬ ((xv : EReal) < ((-Real.exp (-1) : ℝ) : EReal)) := by
    rw [EReal.coe_lt_coe_iff, not_lt]; linarith [Real.exp_pos (-1)]
  have h2 : (xv : EReal) ≠ 0 := by rw [← EReal.coe_zero, Ne, EReal.coe_eq_coe_iff]; exact h.ne'
  have h3 : (0 : EReal) < xv := by rw [← EReal.coe_zero, EReal.coe_lt_coe_iff]; exact h
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]

theorem lambertWm1_coe_of_mem {xv : ℝ} (h1 : -Real.exp (-1) ≤ xv) (h0 : xv < 0) :
    lambertWm1 (xv : EReal) = some ((Azurite.DLMF.lambertWm1 xv : ℝ) : EReal) := by
  unfold lambertWm1
  have h2 : (xv : EReal) ≠ 0 := by rw [← EReal.coe_zero, Ne, EReal.coe_eq_coe_iff]; exact h0.ne
  have h3 : ¬ ((0 : EReal) < xv) := by
    rw [← EReal.coe_zero, EReal.coe_lt_coe_iff]; exact not_lt.mpr h0.le
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_right (not_lt.mpr (EReal.coe_le_coe_iff.mpr h1)),
    ite_eq_right h2, ite_eq_right h3, EReal.toReal_coe]

end Spec

/-! ### The three Ziv loops -/

/-- `lambertW0Pos` is the correct rounding of `W₀ x` for a rational target `x > 0`. -/
theorem lambertW0Pos_eq (xAt : ℕ → AzFloat × AzFloat) (h : PosTarget xAt) {xv : ℝ}
    (hX : XEncl xAt xv) (hrat : ∃ r : ℚ, xv = r) (hpos : 0 < xv) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lambertW0Pos xAt h p mode
      = roundVal p mode (some ((Azurite.DLMF.lambertW0 xv : ℝ) : EReal)) := by
  obtain ⟨r, hr⟩ := hrat
  have hr0 : r ≠ 0 := by rintro rfl; rw [Rat.cast_zero] at hr; linarith
  obtain ⟨a₀, b₀, ha₀, hb₀, haW, hWb⟩ := aprioriW0Pos_spec hX hpos (le_refl 64)
  have hW := Azurite.DLMF.lambertW0_spec (Azurite.LambertW.neg_exp_neg_one_le_of_nonneg hpos.le)
  have hirr : Irrational (Azurite.DLMF.lambertW0 xv) := by
    rw [hr]
    exact Azurite.LambertW.irrational_lambertW0 hr0
      (by rw [← hr]; exact Azurite.LambertW.neg_exp_neg_one_le_of_nonneg hpos.le)
  unfold lambertW0Pos
  exact zivLoopCertified_eq_threshold' p mode _ _ (not_mem_floatSet_of_irrational p hirr) _
    (by unfold zivGuardBits; omega)
    (fun w _ => by
      obtain ⟨lv, hv', h1, h2, h3, h4, -⟩ := lambertApprox_spec true hX none ha₀ hb₀ hW.2
        haW hWb ⟨fun _ => hW.1, fun h => (Bool.false_ne_true h.symm).elim⟩ _ w
      exact ⟨lv, hv', h1, h2, h3, h4⟩) _

/-- `lambertW0Neg` is the correct rounding of `Spec.lambertW0 x` for a rational target `x < 0`. -/
theorem lambertW0Neg_eq (xAt : ℕ → AzFloat × AzFloat) (h : NegTarget xAt) {xv : ℝ}
    (hX : XEncl xAt xv) (hrat : ∃ r : ℚ, xv = r) (hneg : xv < 0) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lambertW0Neg xAt h p mode = roundVal p mode (Spec.lambertW0 (xv : EReal)) := by
  obtain ⟨r, hr⟩ := hrat
  have hr0 : r ≠ 0 := by rintro rfl; rw [Rat.cast_zero] at hr; linarith
  unfold lambertW0Neg
  split
  · rename_i hq
    have := qEncl_eq_none hX hneg _ hq
    rw [Spec.lambertW0_coe_of_lt this, roundVal_none]
  · rename_i lo hi hq
    obtain ⟨lov, hiv, hlo, hhi, hl0, hl, hh⟩ := qEncl_eq_some hX hneg _ hq
    have hx1 : -Real.exp (-1) < xv := by rw [neg_exp_neg_one_lt_iff]; linarith
    rw [Spec.lambertW0_coe_of_le hx1.le]
    obtain ⟨l', h', hl', hh', hl0', hlq', hqh'⟩ :=
      qTight_spec (q := (lo, hi)) hX hneg hlo hhi hl0 hl hh
    obtain ⟨a₀, b₀, ha₀, hb₀, haW, hWb⟩ := aprioriW0Neg_spec hx1 hneg hl' hh' hl0' hlq' hqh'
      (by omega : 64 ≤ 64 + 2 * compBits (some (qTight xAt (lo, hi))))
    have hW := Azurite.DLMF.lambertW0_spec hx1.le
    have hirr : Irrational (Azurite.DLMF.lambertW0 xv) := by
      rw [hr]
      exact Azurite.LambertW.irrational_lambertW0 hr0 (by rw [← hr]; exact hx1.le)
    exact zivLoopCertified_eq_threshold' p mode _ _ (not_mem_floatSet_of_irrational p hirr) _
      (by unfold zivGuardBits; omega)
      (fun w _ => by
        obtain ⟨lv, hv', h1, h2, h3, h4, -⟩ := lambertApprox_spec true hX _ ha₀ hb₀ hW.2
          haW hWb ⟨fun _ => hW.1, fun h => (Bool.false_ne_true h.symm).elim⟩ _ w
        exact ⟨lv, hv', h1, h2, h3, h4⟩) _

/-- `lambertWm1Neg` is the correct rounding of `Spec.lambertWm1 x` for a rational target
`x < 0`. -/
theorem lambertWm1Neg_eq (xAt : ℕ → AzFloat × AzFloat) (h : NegTarget xAt) {xv : ℝ}
    (hX : XEncl xAt xv) (hrat : ∃ r : ℚ, xv = r) (hneg : xv < 0) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lambertWm1Neg xAt h p mode = roundVal p mode (Spec.lambertWm1 (xv : EReal)) := by
  obtain ⟨r, hr⟩ := hrat
  unfold lambertWm1Neg
  split
  · rename_i hq
    have := qEncl_eq_none hX hneg _ hq
    rw [Spec.lambertWm1_coe_of_lt this, roundVal_none]
  · rename_i lo hi hq
    obtain ⟨lov, hiv, hlo, hhi, hl0, hl, hh⟩ := qEncl_eq_some hX hneg _ hq
    have hx1 : -Real.exp (-1) < xv := by rw [neg_exp_neg_one_lt_iff]; linarith
    rw [Spec.lambertWm1_coe_of_mem hx1.le hneg]
    obtain ⟨l', h', hl', hh', hl0', hlq', hqh'⟩ :=
      qTight_spec (q := (lo, hi)) hX hneg hlo hhi hl0 hl hh
    obtain ⟨a₀, b₀, ha₀, hb₀, haW, hWb⟩ := aprioriWm1_spec hX hx1 hneg hl' hh' hl0' hlq' hqh'
      (by omega : 64 ≤ 64 + 2 * compBits (some (qTight xAt (lo, hi))))
    have hW := Azurite.DLMF.lambertWm1_spec hx1.le hneg
    have hirr : Irrational (Azurite.DLMF.lambertWm1 xv) := by
      rw [hr]
      exact Azurite.LambertW.irrational_lambertWm1 (by rw [← hr]; exact hx1.le)
        (by rw [← hr]; exact hneg)
    exact zivLoopCertified_eq_threshold' p mode _ _ (not_mem_floatSet_of_irrational p hirr) _
      (by unfold zivGuardBits; omega)
      (fun w _ => by
        obtain ⟨lv, hv', h1, h2, h3, h4, -⟩ := lambertApprox_spec false hX _ ha₀ hb₀ hW.2
          haW hWb ⟨fun h => (Bool.false_ne_true h).elim, fun _ => hW.1⟩ _ w
        exact ⟨lv, hv', h1, h2, h3, h4⟩) _

/-! ### The float drivers -/

/-- The tiny-argument path of `W₀` answers with the rounding of `W₀ x`. -/
theorem lambertW0Tiny?_eq {nx : Roundable} {nxHi : AzFloat} {e : AzInt} {w p : ℕ} [NeZero p]
    {mode : RoundingMode} {r : AzFloat × Ordering} {xv h : ℝ} (hR : Rounds nx (-xv))
    (hH : nxHi.toVal = some (h : EReal)) (hh : -xv ≤ h) (hx0 : xv ≠ 0)
    (hlt : |xv| < (2 : ℝ) ^ e.toInt) (hT : lambertW0Tiny? nx nxHi e w p mode = some r) :
    r = roundVal p mode (Spec.lambertW0 (xv : EReal)) := by
  unfold lambertW0Tiny? at hT
  split_ifs at hT with hc
  obtain ⟨hs, he⟩ := hc
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp hT
  have : NeZero (w + 8) := ⟨by omega⟩
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  set t := (2 : ℝ) ^ e.toInt with ht
  have ht0 : 0 < t := by positivity
  have ht8 : t ≤ 1 / 8 := by
    rw [ht, htoInt, hs]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [zpow_neg, zpow_natCast, ← one_div, ← one_div_pow]
    calc (1 / 2 : ℝ) ^ e.abs.toNat ≤ (1 / 2 : ℝ) ^ 3 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 8 := by norm_num
  have hx8 : |xv| ≤ 1 / 8 := by linarith
  obtain ⟨hlo, hhi⟩ := Azurite.LambertW.lambertW0_tiny_bounds hx0 hx8
  have hdom : -Real.exp (-1) ≤ xv := by
    have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have : (1 : ℝ) / 3 < Real.exp (-1) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_lt_one_div_of_lt (Real.exp_pos 1) he3
    have := (abs_le.mp hx8).1
    linarith
  rw [Spec.lambertW0_coe_of_le hdom]
  have hd : (((one <<< e) <<< e) <<< AzInt.ofInt 2).toVal
      = some ((1 * t * t * (2 : ℝ) ^ (2 : ℤ) : ℝ) : EReal) := by
    rw [toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal
      (toVal_shiftLeft_of_toVal toVal_one' e) e), AzInt.toInt_ofInt]
  obtain ⟨hi, hhi', hhi1, -⟩ := addCeiling_abs hH hd (w + 8)
  have hsq : xv ^ 2 ≤ t * t := by
    rw [← sq_abs, sq]
    exact mul_le_mul hlt.le hlt.le (abs_nonneg xv) ht0.le
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi')
  rw [fval_of_toVal_coe hhi'] at hR2
  have hr := roundingPossible_eq' p (-mode) (v := -Azurite.DLMF.lambertW0 xv) hR hR2
    (by linarith) (by norm_num at hhi1; nlinarith)
    (Or.inl fun hEq => absurd hEq (by linarith)) hr'
  rw [hr]
  have hneg := roundVal_neg p mode (-Azurite.DLMF.lambertW0 xv)
  rw [neg_neg] at hneg
  exact hneg.symm

/-- **`W₀` is correctly rounded.** -/
theorem lambertW0PrecRound_eq (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lambertW0PrecRound x p mode = liftVal Spec.lambertW0 x p mode := by
  have hp := NeZero.ne p
  unfold liftVal
  cases x with
  | nan => simp [lambertW0PrecRound, toVal_nan]
  | infinity s =>
    cases s
    · simp only [lambertW0PrecRound, Bool.false_eq_true, ↓reduceIte, toVal_infinity,
        Option.bind_some, Spec.lambertW0_bot, roundVal_none]
    · simp only [lambertW0PrecRound, ↓reduceIte, toVal_infinity, Option.bind_some,
        Spec.lambertW0_top, roundVal_top]
  | zero =>
    simp only [lambertW0PrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.lambertW0_coe_of_le (by linarith [Real.exp_pos (-1)]),
      Azurite.DLMF.lambertW0_zero, EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    simp only [lambertW0PrecRound, toVal_finite, Option.bind_some, dite_eq_right hp]
    split
    · next r hT =>
      have hnx : (-(finite s e q m hv)).toVal = some ((-finiteVal s e m : ℝ) : EReal) := by
        rw [toVal_neg, toVal_finite, Option.map_some, EReal.coe_neg]
      have hR := rounds_setPrecRound (isFinite_of_toVal_coe hnx)
      rw [fval_of_toVal_coe hnx] at hR
      exact lambertW0Tiny?_eq hR hnx le_rfl (finiteVal_ne_zero s e hv)
        (abs_finiteVal_bounds s e hv).2 hT
    by_cases hs : s = true
    · rw [dite_eq_left hs]
      subst hs
      refine (lambertW0Pos_eq _ _ (floatAt_encl (toVal_finite true e q m hv))
        (finiteVal_rat true e hv) (finiteVal_true_pos e hv) p mode).trans ?_
      rw [Spec.lambertW0_coe_of_le (by linarith [Real.exp_pos (-1), finiteVal_true_pos e hv])]
    · rw [dite_eq_right hs]
      have hs' : s = false := Bool.eq_false_iff.mpr hs
      subst hs'
      exact lambertW0Neg_eq _ _ (floatAt_encl (toVal_finite false e q m hv))
        (finiteVal_rat false e hv) (finiteVal_false_neg e hv) p mode

/-- **`W₋₁` is correctly rounded.** -/
theorem lambertWm1PrecRound_eq (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lambertWm1PrecRound x p mode = liftVal Spec.lambertWm1 x p mode := by
  have hp := NeZero.ne p
  unfold liftVal
  cases x with
  | nan => simp [lambertWm1PrecRound, toVal_nan]
  | infinity s =>
    cases s
    · simp only [lambertWm1PrecRound, toVal_infinity, Bool.false_eq_true, ↓reduceIte,
        Option.bind_some, Spec.lambertWm1_bot, roundVal_none]
    · simp only [lambertWm1PrecRound, toVal_infinity, ↓reduceIte, Option.bind_some,
        Spec.lambertWm1_top, roundVal_none]
  | zero =>
    simp only [lambertWm1PrecRound, toVal_zero, Option.bind_some, Spec.lambertWm1_zero,
      roundVal_bot]
  | finite s e q m hv =>
    simp only [lambertWm1PrecRound, toVal_finite, Option.bind_some, dite_eq_right hp]
    by_cases hs : s = true
    · rw [dite_eq_left hs]
      subst hs
      rw [Spec.lambertWm1_coe_of_pos (finiteVal_true_pos e hv), roundVal_none]
    · rw [dite_eq_right hs]
      have hs' : s = false := Bool.eq_false_iff.mpr hs
      subst hs'
      exact lambertWm1Neg_eq _ _ (floatAt_encl (toVal_finite false e q m hv))
        (finiteVal_rat false e hv) (finiteVal_false_neg e hv) p mode

/-! ### The rational drivers -/

/-- **`W₀` of a rational is correctly rounded.** -/
theorem lambertW0RatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lambertW0RatPrecRound q p mode
      = roundVal p mode (Spec.lambertW0 (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold lambertW0RatPrecRound
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, EReal.coe_zero, ← EReal.coe_zero,
      Spec.lambertW0_coe_of_le (by linarith [Real.exp_pos (-1)]), Azurite.DLMF.lambertW0_zero,
      EReal.coe_zero, roundVal_zero]
  · rw [dite_eq_right h0, dite_eq_right hp]
    split
    · next r hT =>
      have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
      have hneg : ((AzRat.toRat (-q) : ℚ) : ℝ) = -((AzRat.toRat q : ℚ) : ℝ) := by
        rw [AzRat.toRat_neg]; push_cast; rfl
      have hR : Rounds (fun P M => ofAzRatRound (-q) P M) (-((AzRat.toRat q : ℚ) : ℝ)) := by
        intro P _ M
        show ofAzRatRound (-q) P M = _
        rw [ofAzRatRound_eq_roundVal, hneg]
      obtain ⟨c, hc, hc1, -⟩ := ofAzRatRound_ceiling_abs (-q) (p + zivGuardBits + 8)
      rw [hneg] at hc1
      refine lambertW0Tiny?_eq hR hc hc1 (coe_toRat_ne_zero_of_num_ne_zero q h0)
        (lt_of_lt_of_le (abs_toRat_lt_two_zpow q) ?_) hT
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    by_cases hs : q.sign = true
    · rw [dite_eq_left hs]
      refine (lambertW0Pos_eq _ _ (ratAt_encl q) ⟨_, rfl⟩ (toRat_pos_real q hs h0) p mode).trans ?_
      rw [Spec.lambertW0_coe_of_le (by linarith [Real.exp_pos (-1), toRat_pos_real q hs h0])]
    · rw [dite_eq_right hs]
      exact lambertW0Neg_eq _ _ (ratAt_encl q) ⟨_, rfl⟩
        (toRat_neg_real q (Bool.eq_false_iff.mpr hs) h0) p mode

/-- **`W₋₁` of a rational is correctly rounded.** -/
theorem lambertWm1RatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lambertWm1RatPrecRound q p mode
      = roundVal p mode (Spec.lambertWm1 (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold lambertWm1RatPrecRound
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, EReal.coe_zero,
      Spec.lambertWm1_zero, roundVal_bot]
  · rw [dite_eq_right h0, dite_eq_right hp]
    by_cases hs : q.sign = true
    · rw [dite_eq_left hs, Spec.lambertWm1_coe_of_pos (toRat_pos_real q hs h0), roundVal_none]
    · rw [dite_eq_right hs]
      exact lambertWm1Neg_eq _ _ (ratAt_encl q) ⟨_, rfl⟩
        (toRat_neg_real q (Bool.eq_false_iff.mpr hs) h0) p mode

end Azurite.AzFloat
