/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LambertW

/-!
# Equivalence: the real branches of the Lambert `W` function

`Spec.lambertW0`, `Spec.lambertWm1 : EReal → Option EReal` are the exact functions on the
extended reals (`none` is `NaN`), and `lambertW0PrecRound_eq`, `lambertWm1PrecRound_eq` say that
the drivers are their correct roundings in every mode, with the exact comparison and without
fuel.
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
    set xv := finiteVal s e m with hxv
    have hx : (finite s e q m hv).toVal = some (xv : EReal) := toVal_finite s e q m hv
    by_cases hs : s = true
    · rw [dite_eq_left hs]
      subst hs
      have hpos := finiteVal_true_pos e hv
      rw [← hxv] at hpos
      rw [Spec.lambertW0_coe_of_le (by linarith [Real.exp_pos (-1)])]
      obtain ⟨r, hr⟩ := exists_rat_of_toVal hx
      have hr0 : r ≠ 0 := by rintro rfl; rw [Rat.cast_zero] at hr; linarith
      obtain ⟨a₀, b₀, ha₀, hb₀, haW, hWb⟩ := aprioriW0Pos_spec hx hpos.le (le_refl 64)
      have hW := Azurite.DLMF.lambertW0_spec (Azurite.LambertW.neg_exp_neg_one_le_of_nonneg hpos.le)
      have hirr : Irrational (Azurite.DLMF.lambertW0 xv) := by
        rw [hr]
        exact Azurite.LambertW.irrational_lambertW0 hr0
          (by rw [← hr]; exact Azurite.LambertW.neg_exp_neg_one_le_of_nonneg hpos.le)
      exact zivLoopCertified_eq_threshold' p mode _ _ (not_mem_floatSet_of_irrational p hirr) _
        (by unfold zivGuardBits; omega)
        (fun w _ => by
          obtain ⟨lv, hv', h1, h2, h3, h4, -⟩ := lambertApprox_spec true hx none ha₀ hb₀ hW.2
            haW hWb ⟨fun _ => hW.1, fun h => (Bool.false_ne_true h.symm).elim⟩
            (sideCert_pos true e q m hv rfl) w
          exact ⟨lv, hv', h1, h2, h3, h4⟩) _
    · rw [dite_eq_right hs]
      have hs' : s = false := Bool.eq_false_iff.mpr hs
      subst hs'
      have hneg := finiteVal_false_neg e hv
      rw [← hxv] at hneg
      split
      · rename_i hq
        have := qEncl_eq_none hx hneg _ hq
        rw [Spec.lambertW0_coe_of_lt this, roundVal_none]
      · rename_i lo hi hq
        obtain ⟨lov, hiv, hlo, hhi, hl0, hl, hh⟩ := qEncl_eq_some hx hneg _ hq
        have hx1 : -Real.exp (-1) < xv := by rw [neg_exp_neg_one_lt_iff]; linarith
        rw [Spec.lambertW0_coe_of_le hx1.le]
        obtain ⟨r, hr⟩ := exists_rat_of_toVal hx
        have hr0 : r ≠ 0 := by rintro rfl; rw [Rat.cast_zero] at hr; linarith
        obtain ⟨l', h', hl', hh', hl0', hlq', hqh'⟩ :=
          qTight_spec (q := (lo, hi)) hx hneg hlo hhi hl0 hl hh
        obtain ⟨a₀, b₀, ha₀, hb₀, haW, hWb⟩ := aprioriW0Neg_spec hx1 hneg hl' hh' hl0' hlq' hqh'
          (by omega : 64 ≤ 64 + 2 * compBits (some (qTight (finite false e q m hv) (lo, hi))))
        have hW := Azurite.DLMF.lambertW0_spec hx1.le
        have hirr : Irrational (Azurite.DLMF.lambertW0 xv) := by
          rw [hr]
          exact Azurite.LambertW.irrational_lambertW0 hr0 (by rw [← hr]; exact hx1.le)
        exact zivLoopCertified_eq_threshold' p mode _ _ (not_mem_floatSet_of_irrational p hirr) _
          (by unfold zivGuardBits; omega)
          (fun w _ => by
            obtain ⟨lv, hv', h1, h2, h3, h4, -⟩ := lambertApprox_spec true hx _ ha₀ hb₀ hW.2
              haW hWb ⟨fun _ => hW.1, fun h => (Bool.false_ne_true h.symm).elim⟩
              (sideCert_neg false e q m hv rfl hq) w
            exact ⟨lv, hv', h1, h2, h3, h4⟩) _

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
    set xv := finiteVal s e m with hxv
    have hx : (finite s e q m hv).toVal = some (xv : EReal) := toVal_finite s e q m hv
    by_cases hs : s = true
    · rw [dite_eq_left hs]
      subst hs
      have hpos := finiteVal_true_pos e hv
      rw [← hxv] at hpos
      rw [Spec.lambertWm1_coe_of_pos hpos, roundVal_none]
    · rw [dite_eq_right hs]
      have hs' : s = false := Bool.eq_false_iff.mpr hs
      subst hs'
      have hneg := finiteVal_false_neg e hv
      rw [← hxv] at hneg
      split
      · rename_i hq
        have := qEncl_eq_none hx hneg _ hq
        rw [Spec.lambertWm1_coe_of_lt this, roundVal_none]
      · rename_i lo hi hq
        obtain ⟨lov, hiv, hlo, hhi, hl0, hl, hh⟩ := qEncl_eq_some hx hneg _ hq
        have hx1 : -Real.exp (-1) < xv := by rw [neg_exp_neg_one_lt_iff]; linarith
        rw [Spec.lambertWm1_coe_of_mem hx1.le hneg]
        obtain ⟨r, hr⟩ := exists_rat_of_toVal hx
        obtain ⟨l', h', hl', hh', hl0', hlq', hqh'⟩ :=
          qTight_spec (q := (lo, hi)) hx hneg hlo hhi hl0 hl hh
        obtain ⟨a₀, b₀, ha₀, hb₀, haW, hWb⟩ := aprioriWm1_spec hx hx1 hneg hl' hh' hl0' hlq' hqh'
          (by omega : 64 ≤ 64 + 2 * compBits (some (qTight (finite false e q m hv) (lo, hi))))
        have hW := Azurite.DLMF.lambertWm1_spec hx1.le hneg
        have hirr : Irrational (Azurite.DLMF.lambertWm1 xv) := by
          rw [hr]
          exact Azurite.LambertW.irrational_lambertWm1 (by rw [← hr]; exact hx1.le)
            (by rw [← hr]; exact hneg)
        exact zivLoopCertified_eq_threshold' p mode _ _ (not_mem_floatSet_of_irrational p hirr) _
          (by unfold zivGuardBits; omega)
          (fun w _ => by
            obtain ⟨lv, hv', h1, h2, h3, h4, -⟩ := lambertApprox_spec false hx _ ha₀ hb₀ hW.2
              haW hWb ⟨fun h => (Bool.false_ne_true h).elim, fun _ => hW.1⟩
              (sideCert_neg false e q m hv rfl hq) w
            exact ⟨lv, hv', h1, h2, h3, h4⟩) _

end Azurite.AzFloat
