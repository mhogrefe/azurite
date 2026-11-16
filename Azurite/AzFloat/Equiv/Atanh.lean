/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atanh
import Azurite.AzFloat.AtanhRat
import Azurite.AzFloat.Equiv.AsecBracket
import Azurite.AzFloat.Equiv.AtanRatWithPeriodBracket
import Azurite.AzFloat.Equiv.RatPowRat

/-!
# Equivalence: `atanh x` and `atanh q`

`Spec.atanh a = artanh a` for `|a| < 1` (`±∞` at `±1`, undefined for `|a| > 1` and at `±∞`),
`atanhPrecRound_eq_liftVal : atanhPrecRound x p mode = liftVal Spec.atanh x p mode` and
`atanhRatPrecRound_eq : atanhRatPrecRound q p mode = roundVal p mode (Spec.atanh q)`, for
`p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `atanh`: `artanh a` for `|a| < 1`, `±∞` at `±1`, undefined for `|a| > 1` and
at `±∞`. -/
noncomputable def atanh (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then none
  else if a.toReal = 1 then some ⊤ else if a.toReal = -1 then some ⊥
  else if 1 < |a.toReal| then none else some ((Real.artanh a.toReal : ℝ) : EReal)

theorem atanh_coe {r : ℝ} (hr : |r| < 1) :
    atanh (r : EReal) = some ((Real.artanh r : ℝ) : EReal) := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hr
  unfold atanh
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe,
    ite_eq_right h2.ne, ite_eq_right h1.ne', ite_eq_right (not_lt.mpr hr.le)]

theorem atanh_coe_of_one_lt {r : ℝ} (hr : 1 < |r|) : atanh (r : EReal) = none := by
  have h1 : r ≠ 1 := fun h => by rw [h, abs_one] at hr; exact lt_irrefl _ hr
  have h2 : r ≠ -1 := fun h => by rw [h, abs_neg, abs_one] at hr; exact lt_irrefl _ hr
  unfold atanh
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe,
    ite_eq_right h1, ite_eq_right h2, ite_eq_left hr]

theorem atanh_one : atanh ((1 : ℝ) : EReal) = some ⊤ := by
  unfold atanh
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top 1, EReal.coe_ne_bot 1⟩), EReal.toReal_coe,
    ite_eq_left rfl]

theorem atanh_neg_one : atanh ((-1 : ℝ) : EReal) = some ⊥ := by
  unfold atanh
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top (-1), EReal.coe_ne_bot (-1)⟩),
    EReal.toReal_coe, ite_eq_right (by norm_num), ite_eq_left rfl]

@[simp] theorem atanh_top : atanh ⊤ = none := by
  unfold atanh
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem atanh_bot : atanh ⊥ = none := by
  unfold atanh
  rw [ite_eq_left (Or.inr rfl)]

end Spec

/-- The value of `atanh` at a real of absolute value `1` with sign bit `s`. -/
theorem atanh_spec_abs_one {s : Bool} {xv : ℝ} (hs : s = true ↔ 0 < xv) (h1 : |xv| = 1)
    (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (infinity s, Ordering.eq) = roundVal p mode (Spec.atanh (xv : EReal)) := by
  cases s with
  | true =>
    have hpos := hs.mp rfl
    rw [abs_of_pos hpos] at h1
    rw [h1, Spec.atanh_one, roundVal_top]
  | false =>
    have hneg : xv < 0 := by
      rcases lt_trichotomy xv 0 with h | h | h
      · exact h
      · rw [h, abs_zero] at h1
        norm_num at h1
      · exact absurd (hs.mpr h) (by simp)
    rw [abs_of_neg hneg] at h1
    have : xv = -1 := by linarith
    rw [this, Spec.atanh_neg_one, roundVal_bot]

/-- **`atanh` is correctly rounded.** -/
theorem atanhPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    atanhPrecRound x p mode = liftVal Spec.atanh x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [atanhPrecRound]
  | zero =>
    simp only [atanhPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.atanh_coe (by norm_num), Real.artanh_zero, EReal.coe_zero,
      roundVal_zero]
  | finite s e q m hv =>
    simp only [atanhPrecRound, toVal_finite, Option.bind_some]
    set xv := finiteVal s e m with hxv
    have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
    have hsgn := finiteVal_sign_iff s e hv
    have hb := abs_finiteVal_bounds s e hv
    rw [← hxv] at hsgn hb
    have habs : (finite s e q m hv).abs.toVal = some ((|xv| : ℝ) : EReal) := by
      rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
      congr 1
    by_cases h1 : eqIEEE (finite s e q m hv).abs one = true
    · rw [ite_eq_left h1]
      obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp h1
      rw [habs] at hv1
      rw [toVal_one'] at hv2
      have habs1 : |xv| = 1 := by
        have := hv1.trans hv2.symm
        exact_mod_cast Option.some.inj this
      exact atanh_spec_abs_one hsgn habs1 p mode
    · rw [ite_eq_right h1]
      have hne : |xv| ≠ 1 := fun h =>
        h1 ((eqIEEE_iff _ _).mpr ⟨_, habs, by rw [h]; exact toVal_one'⟩)
      by_cases he : e.sign = true ∧ e.abs.toNat ≠ 0
      · rw [dite_eq_left he, Spec.atanh_coe_of_one_lt (one_lt_abs_of_exponent hb.1 he hne),
          roundVal_none]
      · rw [dite_eq_right he, dite_eq_right (NeZero.ne p)]
        have hlt : |xv| < 1 := abs_lt_one_of_exponent hb.2 he
        rw [Spec.atanh_coe hlt]
        split
        · next r hT => exact atanhTiny?_eq hv p mode hT
        exact zivLoopCertified_eq_threshold' p mode _ _
          (not_mem_floatSet_of_irrational p
            (irrational_atanh_of_toVal (toVal_finite s e q m hv) hx0 hlt))
          _ (by unfold zivGuardBits; omega)
          (fun w hw => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := atanhApprox_spec
              (toVal_finite s e q m hv) hlt (finiteVal_neg_iff s e hv) (w := w)
              (by unfold zivGuardBits at hw; omega)
            exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

/-- **`atanh q` is correctly rounded.** -/
theorem atanhRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    atanhRatPrecRound q p mode
      = roundVal p mode (Spec.atanh (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold atanhRatPrecRound
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0,
      Spec.atanh_coe (by norm_num), Real.artanh_zero, EReal.coe_zero, roundVal_zero]
  · rw [dite_eq_right h0]
    by_cases h1 : q.num = q.den
    · rw [ite_eq_left h1]
      exact atanh_spec_abs_one (toRat_sign_iff q h0) ((abs_toRat_eq_one_iff q).mpr h1) p mode
    · rw [ite_eq_right h1]
      by_cases h2 : q.den ≤ q.num
      · rw [dite_eq_left h2]
        have hge := (one_le_abs_toRat_iff q).mp h2
        have hne : |((AzRat.toRat q : ℚ) : ℝ)| ≠ 1 := fun h =>
          h1 ((abs_toRat_eq_one_iff q).mp h)
        rw [Spec.atanh_coe_of_one_lt (lt_of_le_of_ne hge (Ne.symm hne)), roundVal_none]
      · rw [dite_eq_right h2, dite_eq_right hp]
        have hlt := abs_toRat_lt_one_of q h2
        rw [Spec.atanh_coe hlt]
        split
        · next r hT => exact atanhTinyRat?_eq q h0 hT
        exact zivLoopCertified_eq_threshold' p mode _ _
          (not_mem_floatSet_of_irrational p (irrational_atanh_toRat q h0 hlt)) _
          (by unfold zivGuardBits; omega)
          (fun w hw => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
              atanhRatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q h0 hlt
            exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
