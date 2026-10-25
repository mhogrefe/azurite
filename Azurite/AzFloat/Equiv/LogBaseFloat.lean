/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseFloat
import Azurite.AzFloat.Equiv.LogBase

/-!
# Equivalence: the logarithm in a float base

* `Spec.logBaseFloat a b`: the extended-real `log_b a` with the special cases of
  `logBaseFloatPrecRound` (`none` for `NaN`).
* `logBaseFloatPrecRound_eq_liftVal₂ : logBaseFloatPrecRound x b p mode = liftVal₂
  Spec.logBaseFloat x b p mode`: `log_b x` is correctly rounded in every mode, with the exact
  comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-! ### The specification -/

namespace Spec

open Classical in
/-- Extended-real `log_b a` with the special cases: `NaN` for negatives, for `a ∈ {∞, 0}` with
`b ∈ {∞, 0}`, and for `a = b = 1`; `0` for finite `a > 0` with `b ∈ {∞, 0}`; `±∞` for `b = 1`
by the side of `a`, for `a = ∞` by the side of `b`, and (swapped) for `a = 0`. -/
noncomputable def logBaseFloat (a b : EReal) : Option EReal :=
  if a < 0 ∨ b < 0 then none
  else if b = ⊤ ∨ b = 0 then (if a = ⊤ ∨ a = 0 then none else some 0)
  else if b = 1 then (if a = 1 then none else if 1 < a then some ⊤ else some ⊥)
  else if a = ⊤ then (if 1 < b then some ⊤ else some ⊥)
  else if a = 0 then (if 1 < b then some ⊥ else some ⊤)
  else some ((Real.log a.toReal / Real.log b.toReal : ℝ) : EReal)

theorem logBaseFloat_neg_left {a : EReal} (ha : a < 0) (b : EReal) : logBaseFloat a b = none := by
  unfold logBaseFloat
  rw [ite_eq_left (Or.inl ha)]

theorem logBaseFloat_neg_right (a : EReal) {b : EReal} (hb : b < 0) :
    logBaseFloat a b = none := by
  unfold logBaseFloat
  rw [ite_eq_left (Or.inr hb)]

theorem logBaseFloat_top_right {a : EReal} (ha : ¬ a < 0) :
    logBaseFloat a ⊤ = if a = ⊤ ∨ a = 0 then none else some 0 := by
  unfold logBaseFloat
  rw [ite_eq_right (not_or.mpr ⟨ha, not_lt.mpr le_top⟩), ite_eq_left (Or.inl rfl)]

theorem logBaseFloat_zero_right {a : EReal} (ha : ¬ a < 0) :
    logBaseFloat a 0 = if a = ⊤ ∨ a = 0 then none else some 0 := by
  unfold logBaseFloat
  rw [ite_eq_right (not_or.mpr ⟨ha, lt_irrefl 0⟩), ite_eq_left (Or.inr rfl)]

theorem one_ne_top : (1 : EReal) ≠ ⊤ := by rw [← EReal.coe_one]; exact EReal.coe_ne_top 1

theorem logBaseFloat_one_right {a : EReal} (ha : ¬ a < 0) :
    logBaseFloat a 1 = if a = 1 then none else if 1 < a then some ⊤ else some ⊥ := by
  unfold logBaseFloat
  rw [ite_eq_right (not_or.mpr ⟨ha, not_lt.mpr zero_le_one⟩),
    ite_eq_right (not_or.mpr ⟨one_ne_top, one_ne_zero⟩), ite_eq_left rfl]

/-- `log_b ∞ = ±∞` for a positive real base, by the side of `1` (`log_1 ∞ = ∞`). -/
theorem logBaseFloat_top_left {bv : ℝ} (hb : 0 < bv) :
    logBaseFloat ⊤ (bv : EReal) = some (if 1 ≤ bv then ⊤ else ⊥) := by
  by_cases hb1 : bv = 1
  · rw [hb1, EReal.coe_one, logBaseFloat_one_right (not_lt.mpr le_top),
      ite_eq_right one_ne_top.symm, ite_eq_left (by rw [← EReal.coe_one]; exact EReal.coe_lt_top 1),
      ite_eq_left le_rfl]
  · unfold logBaseFloat
    rw [ite_eq_right (not_or.mpr ⟨not_lt.mpr le_top, not_lt.mpr (EReal.coe_nonneg.mpr hb.le)⟩),
      ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top bv, mt EReal.coe_eq_zero.mp hb.ne'⟩),
      ite_eq_right (by rw [← EReal.coe_one]; exact mt EReal.coe_eq_coe_iff.mp hb1),
      ite_eq_left rfl]
    by_cases h : 1 < bv
    · rw [ite_eq_left (by rw [← EReal.coe_one]; exact EReal.coe_lt_coe_iff.mpr h), ite_eq_left h.le]
    · rw [ite_eq_right (by rw [← EReal.coe_one]; exact mt EReal.coe_lt_coe_iff.mp h),
        ite_eq_right (fun h' => h (lt_of_le_of_ne h' (Ne.symm hb1)))]

/-- `log_b 0 = ∓∞` for a positive real base, by the side of `1` (`log_1 0 = −∞`). -/
theorem logBaseFloat_zero_left {bv : ℝ} (hb : 0 < bv) :
    logBaseFloat 0 (bv : EReal) = some (if 1 ≤ bv then ⊥ else ⊤) := by
  by_cases hb1 : bv = 1
  · rw [hb1, EReal.coe_one, logBaseFloat_one_right (lt_irrefl 0), ite_eq_right zero_ne_one,
      ite_eq_right (not_lt.mpr zero_le_one), ite_eq_left le_rfl]
  · unfold logBaseFloat
    rw [ite_eq_right (not_or.mpr ⟨lt_irrefl 0, not_lt.mpr (EReal.coe_nonneg.mpr hb.le)⟩),
      ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top bv, mt EReal.coe_eq_zero.mp hb.ne'⟩),
      ite_eq_right (by rw [← EReal.coe_one]; exact mt EReal.coe_eq_coe_iff.mp hb1),
      ite_eq_right EReal.zero_ne_top, ite_eq_left rfl]
    by_cases h : 1 < bv
    · rw [ite_eq_left (by rw [← EReal.coe_one]; exact EReal.coe_lt_coe_iff.mpr h), ite_eq_left h.le]
    · rw [ite_eq_right (by rw [← EReal.coe_one]; exact mt EReal.coe_lt_coe_iff.mp h),
        ite_eq_right (fun h' => h (lt_of_le_of_ne h' (Ne.symm hb1)))]

theorem logBaseFloat_coe_top {xv : ℝ} (hx : 0 < xv) : logBaseFloat (xv : EReal) ⊤ = some 0 := by
  rw [logBaseFloat_top_right (not_lt.mpr (EReal.coe_nonneg.mpr hx.le)),
    ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top xv, mt EReal.coe_eq_zero.mp hx.ne'⟩)]

theorem logBaseFloat_coe_zero {xv : ℝ} (hx : 0 < xv) : logBaseFloat (xv : EReal) 0 = some 0 := by
  rw [logBaseFloat_zero_right (not_lt.mpr (EReal.coe_nonneg.mpr hx.le)),
    ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top xv, mt EReal.coe_eq_zero.mp hx.ne'⟩)]

theorem logBaseFloat_coe_one {xv : ℝ} (hx : 0 < xv) :
    logBaseFloat (xv : EReal) 1 = if xv = 1 then none else if 1 < xv then some ⊤ else some ⊥ := by
  rw [logBaseFloat_one_right (not_lt.mpr (EReal.coe_nonneg.mpr hx.le))]
  simp only [← EReal.coe_one, EReal.coe_eq_coe_iff, EReal.coe_lt_coe_iff]

theorem logBaseFloat_coe_coe {xv bv : ℝ} (hx : 0 < xv) (hb : 0 < bv) (hb1 : bv ≠ 1) :
    logBaseFloat (xv : EReal) (bv : EReal) = some ((Real.log xv / Real.log bv : ℝ) : EReal) := by
  unfold logBaseFloat
  rw [ite_eq_right (not_or.mpr ⟨not_lt.mpr (EReal.coe_nonneg.mpr hx.le),
      not_lt.mpr (EReal.coe_nonneg.mpr hb.le)⟩),
    ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top bv, mt EReal.coe_eq_zero.mp hb.ne'⟩),
    ite_eq_right (by rw [← EReal.coe_one]; exact mt EReal.coe_eq_coe_iff.mp hb1),
    ite_eq_right (EReal.coe_ne_top xv), ite_eq_right (mt EReal.coe_eq_zero.mp hx.ne'),
    EReal.toReal_coe, EReal.toReal_coe]

end Spec

/-! ### Helpers -/

theorem bind_none_of_forall {α β : Type} {o : Option α} {f : α → Option β}
    (h : ∀ a, f a = none) : o.bind f = none := by
  cases o with
  | none => rfl
  | some a => exact h a

/-- A positive finite float is at least `1` exactly when its exponent is at least `1`. -/
theorem one_le_finiteVal_iff (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    1 ≤ finiteVal true e m ↔ (e.sign = true ∧ e.abs ≠ 0) := by
  constructor
  · intro h
    by_contra hge
    have := finiteVal_false_gt_neg_one e hv hge
    rw [finiteVal_false] at this
    linarith
  · intro hge
    have := finiteVal_false_le_neg_one e hv hge
    rw [finiteVal_false] at this
    linarith

theorem finiteVal_eq_one_of_eqIEEE (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (h : eqIEEE (finite true e q m hv) one = true) : finiteVal true e m = 1 := by
  obtain ⟨v, hx, h1⟩ := (eqIEEE_iff _ _).mp h
  rw [toVal_finite] at hx
  rw [toVal_one', ← hx, Option.some.injEq, EReal.coe_eq_coe_iff] at h1
  exact h1.symm

/-! ### The equivalence -/

/-- The general case rounds `ln x / ln b`. -/
theorem logBaseFloatFinite_eq (ex : AzInt) {qx : ℕ} {mx : AzNat} (hvx : FiniteValid qx mx)
    (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    (hb1 : finiteVal true eb mb ≠ 1) (hx1 : finiteVal true ex mx ≠ 1) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    logBaseFloatFinite ex hvx eb hvb hb1 hx1 p mode
      = roundVal p mode
          (some ((Real.log (finiteVal true ex mx) / Real.log (finiteVal true eb mb) : ℝ) :
            EReal)) := by
  unfold logBaseFloatFinite
  split
  · rename_i r hx
    rw [ofAzRatRound_eq_roundVal, logBaseFloat_exact_value ex hvx eb hvb hb1 r hx]
  · rename_i hx
    have hirr := irrational_logBaseFloat_of_none ex hvx eb hvb hb1 hx1 hx
    exact zivLoopCertified_eq_threshold p mode _ _ _ (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          logBaseFloatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) ex hvx eb hvb hb1
            hirr
        exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

/-- **`log_b x` with a float base is correctly rounded.** -/
theorem logBaseFloatPrecRound_eq_liftVal₂ (x b : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    logBaseFloatPrecRound x b p mode = liftVal₂ Spec.logBaseFloat x b p mode := by
  unfold liftVal₂
  cases x with
  | nan => rfl
  | infinity sx =>
    cases sx with
    | false =>
      simp only [logBaseFloatPrecRound, toVal_infinity, Bool.false_eq_true, ↓reduceIte,
        Option.bind_some]
      rw [bind_none_of_forall (Spec.logBaseFloat_neg_left EReal.bot_lt_zero), roundVal_none]
    | true =>
      simp only [logBaseFloatPrecRound, toVal_infinity, ↓reduceIte, Option.bind_some]
      cases b with
      | nan => rfl
      | infinity sb =>
        cases sb
        · simp only [toVal_infinity, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
            Spec.logBaseFloat_neg_right _ EReal.bot_lt_zero, roundVal_none]
        · simp only [toVal_infinity, ↓reduceIte, Option.bind_some]
          rw [Spec.logBaseFloat_top_right (not_lt.mpr le_top), ite_eq_left (Or.inl rfl),
            roundVal_none]
      | zero =>
        simp only [toVal_zero, Option.bind_some]
        rw [Spec.logBaseFloat_zero_right (not_lt.mpr le_top), ite_eq_left (Or.inl rfl),
          roundVal_none]
      | finite sb eb qb mb hvb =>
        cases sb with
        | false =>
          simp only [toVal_finite, Option.bind_some]
          rw [finiteVal_false, Spec.logBaseFloat_neg_right _
            (EReal.coe_neg'.mpr (neg_neg_iff_pos.mpr (finiteVal_true_pos eb hvb))), roundVal_none]
        | true =>
          simp only [toVal_finite, Option.bind_some]
          rw [Spec.logBaseFloat_top_left (finiteVal_true_pos eb hvb)]
          by_cases hge : eb.sign = true ∧ eb.abs ≠ 0
          · rw [ite_eq_left hge, ite_eq_left ((one_le_finiteVal_iff eb hvb).mpr hge)]
            exact (roundVal_inf p mode true).symm
          · rw [ite_eq_right hge, ite_eq_right (mt (one_le_finiteVal_iff eb hvb).mp hge)]
            exact (roundVal_inf p mode false).symm
  | zero =>
    simp only [logBaseFloatPrecRound, toVal_zero, Option.bind_some]
    cases b with
    | nan => rfl
    | infinity sb =>
      cases sb
      · simp only [toVal_infinity, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
          Spec.logBaseFloat_neg_right _ EReal.bot_lt_zero, roundVal_none]
      · simp only [toVal_infinity, ↓reduceIte, Option.bind_some]
        rw [Spec.logBaseFloat_top_right (lt_irrefl 0), ite_eq_left (Or.inr rfl), roundVal_none]
    | zero =>
      simp only [toVal_zero, Option.bind_some]
      rw [Spec.logBaseFloat_zero_right (lt_irrefl 0), ite_eq_left (Or.inr rfl), roundVal_none]
    | finite sb eb qb mb hvb =>
      cases sb with
      | false =>
        simp only [toVal_finite, Option.bind_some]
        rw [finiteVal_false, Spec.logBaseFloat_neg_right _
          (EReal.coe_neg'.mpr (neg_neg_iff_pos.mpr (finiteVal_true_pos eb hvb))), roundVal_none]
      | true =>
        simp only [toVal_finite, Option.bind_some]
        rw [Spec.logBaseFloat_zero_left (finiteVal_true_pos eb hvb)]
        by_cases hge : eb.sign = true ∧ eb.abs ≠ 0
        · rw [ite_eq_left hge, ite_eq_left ((one_le_finiteVal_iff eb hvb).mpr hge)]
          exact (roundVal_inf p mode false).symm
        · rw [ite_eq_right hge, ite_eq_right (mt (one_le_finiteVal_iff eb hvb).mp hge)]
          exact (roundVal_inf p mode true).symm
  | finite sx ex qx mx hvx =>
    cases sx with
    | false =>
      simp only [logBaseFloatPrecRound, toVal_finite, Option.bind_some]
      rw [finiteVal_false, bind_none_of_forall (Spec.logBaseFloat_neg_left
        (EReal.coe_neg'.mpr (neg_neg_iff_pos.mpr (finiteVal_true_pos ex hvx)))), roundVal_none]
    | true =>
      have hx := finiteVal_true_pos ex hvx
      simp only [logBaseFloatPrecRound, toVal_finite, Option.bind_some]
      cases b with
      | nan => rfl
      | infinity sb =>
        cases sb
        · simp only [toVal_infinity, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
            Spec.logBaseFloat_neg_right _ EReal.bot_lt_zero, roundVal_none]
        · simp only [toVal_infinity, ↓reduceIte, Option.bind_some, Spec.logBaseFloat_coe_top hx,
            roundVal_zero]
      | zero =>
        simp only [toVal_zero, Option.bind_some, Spec.logBaseFloat_coe_zero hx, roundVal_zero]
      | finite sb eb qb mb hvb =>
        cases sb with
        | false =>
          simp only [toVal_finite, Option.bind_some]
          rw [finiteVal_false, Spec.logBaseFloat_neg_right _
            (EReal.coe_neg'.mpr (neg_neg_iff_pos.mpr (finiteVal_true_pos eb hvb))), roundVal_none]
        | true =>
          have hb := finiteVal_true_pos eb hvb
          simp only [toVal_finite, Option.bind_some]
          split_ifs with hb1 hx1 hge hx1' hp
          · -- `b = 1`, `x = 1`
            rw [finiteVal_eq_one_of_eqIEEE eb hvb hb1, EReal.coe_one, Spec.logBaseFloat_coe_one hx,
              ite_eq_left (finiteVal_eq_one_of_eqIEEE ex hvx hx1), roundVal_none]
          · -- `b = 1`, `x > 1`
            have hne := finiteVal_ne_one_of_not_eqIEEE ex hvx hx1
            have hgt : 1 < finiteVal true ex mx :=
              lt_of_le_of_ne ((one_le_finiteVal_iff ex hvx).mpr hge) (Ne.symm hne)
            rw [finiteVal_eq_one_of_eqIEEE eb hvb hb1, EReal.coe_one, Spec.logBaseFloat_coe_one hx,
              ite_eq_right hne, ite_eq_left hgt]
            exact (roundVal_inf p mode true).symm
          · -- `b = 1`, `x < 1`
            have hne := finiteVal_ne_one_of_not_eqIEEE ex hvx hx1
            have hlt : ¬ 1 < finiteVal true ex mx := fun h =>
              hge ((one_le_finiteVal_iff ex hvx).mp h.le)
            rw [finiteVal_eq_one_of_eqIEEE eb hvb hb1, EReal.coe_one, Spec.logBaseFloat_coe_one hx,
              ite_eq_right hne, ite_eq_right hlt]
            exact (roundVal_inf p mode false).symm
          · -- `x = 1`
            have hbne := finiteVal_ne_one_of_not_eqIEEE eb hvb hb1
            rw [Spec.logBaseFloat_coe_coe hx hb hbne, finiteVal_eq_one_of_eqIEEE ex hvx hx1',
              Real.log_one, zero_div, EReal.coe_zero, roundVal_zero]
          · exact absurd hp (NeZero.ne p)
          · have hbne := finiteVal_ne_one_of_not_eqIEEE eb hvb hb1
            rw [Spec.logBaseFloat_coe_coe hx hb hbne]
            exact logBaseFloatFinite_eq ex hvx eb hvb hbne _ p mode

end Azurite.AzFloat
