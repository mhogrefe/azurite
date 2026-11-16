/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acosh
import Azurite.AzFloat.AcoshRat

/-!
# Equivalence: `acosh x` and `acosh q`

`Spec.acosh a = arcosh a` for `a ≥ 1` (`+∞` at `+∞`, undefined below `1`),
`acoshPrecRound_eq_liftVal : acoshPrecRound x p mode = liftVal Spec.acosh x p mode` and
`acoshRatPrecRound_eq : acoshRatPrecRound q p mode = roundVal p mode (Spec.acosh q)`, for
`p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `acosh`: `arcosh a` for `a ≥ 1`, `+∞` at `+∞`, undefined below `1`. -/
noncomputable def acosh (a : EReal) : Option EReal :=
  if a = ⊤ then some ⊤ else if a = ⊥ then none
  else if a.toReal < 1 then none else some ((Real.arcosh a.toReal : ℝ) : EReal)

theorem acosh_coe {r : ℝ} (hr : 1 ≤ r) :
    acosh (r : EReal) = some ((Real.arcosh r : ℝ) : EReal) := by
  unfold acosh
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe,
    ite_eq_right (not_lt.mpr hr)]

theorem acosh_coe_of_lt_one {r : ℝ} (hr : r < 1) : acosh (r : EReal) = none := by
  unfold acosh
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe,
    ite_eq_left hr]

@[simp] theorem acosh_top : acosh ⊤ = some ⊤ := by
  unfold acosh
  rw [ite_eq_left rfl]

@[simp] theorem acosh_bot : acosh ⊥ = none := by
  unfold acosh
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

end Spec

/-- **`acosh` is correctly rounded.** -/
theorem acoshPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    acoshPrecRound x p mode = liftVal Spec.acosh x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [acoshPrecRound]
  | zero =>
    simp only [acoshPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.acosh_coe_of_lt_one (by norm_num), roundVal_none]
  | finite s e q m hv =>
    simp only [acoshPrecRound, toVal_finite, Option.bind_some]
    set xv := finiteVal s e m with hxv
    have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
    have hsgn := finiteVal_sign_iff s e hv
    have hb := abs_finiteVal_bounds s e hv
    rw [← hxv] at hsgn hb
    by_cases hs : s = true
    · rw [dite_eq_left hs]
      have hpos : 0 < xv := hsgn.mp hs
      by_cases h1 : eqIEEE (finite s e q m hv) one = true
      · rw [dite_eq_left h1]
        obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp h1
        rw [toVal_finite] at hv1
        rw [toVal_one'] at hv2
        have hx1 : xv = 1 := by
          have := hv1.trans hv2.symm
          exact_mod_cast Option.some.inj this
        rw [hx1, Spec.acosh_coe le_rfl, Real.arcosh_zero, EReal.coe_zero, roundVal_zero]
      · rw [dite_eq_right h1]
        by_cases he : e.sign = true ∧ e.abs.toNat ≠ 0
        · rw [dite_eq_left he, dite_eq_right (NeZero.ne p)]
          have hgt : 1 < xv := one_lt_of_acosh_cond hv hs h1 he
          rw [Spec.acosh_coe hgt.le]
          exact zivLoopCertified_eq_threshold' p mode _ _
            (not_mem_floatSet_of_irrational p
              (irrational_acosh_of_toVal (toVal_finite s e q m hv) hgt))
            _ (by unfold zivGuardBits; omega)
            (fun w hw => by
              obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := acoshApprox_spec
                (toVal_finite s e q m hv) hgt.le (w := w)
                (by unfold zivGuardBits at hw; omega)
              exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _
        · rw [dite_eq_right he]
          have hlt : xv < 1 := by
            have habs : |xv| < 1 := by
              refine lt_of_lt_of_le hb.2 ?_
              have htoInt : e.toInt
                  = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
              have hle : e.toInt ≤ 0 := by
                rw [htoInt]
                by_cases hsg : e.sign = true
                · have h0 : e.abs.toNat = 0 := by
                    by_contra hne
                    exact he ⟨hsg, hne⟩
                  simp [hsg, h0]
                · simp [hsg]
              exact zpow_le_one_of_nonpos₀ (by norm_num) hle
            exact (le_abs_self xv).trans_lt habs
          rw [Spec.acosh_coe_of_lt_one hlt, roundVal_none]
    · rw [dite_eq_right hs]
      have hneg : xv < 0 := by
        rcases lt_or_gt_of_ne hx0 with h | h
        · exact h
        · exact absurd (hsgn.mpr h) hs
      rw [Spec.acosh_coe_of_lt_one (by linarith), roundVal_none]

/-- **`acosh q` is correctly rounded.** -/
theorem acoshRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    acoshRatPrecRound q p mode
      = roundVal p mode (Spec.acosh (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold acoshRatPrecRound
  by_cases hc : q.sign = true ∧ q.den ≤ q.num
  · rw [dite_eq_left hc]
    by_cases h1 : q.num = q.den
    · rw [dite_eq_left h1]
      have habs := (abs_toRat_eq_one_iff q).mpr h1
      have h0 : q.num ≠ 0 := fun h => by
        rw [coe_toRat_eq_zero_of_num_eq_zero q h, abs_zero] at habs
        norm_num at habs
      rw [abs_of_pos ((toRat_sign_iff q h0).mp hc.1)] at habs
      rw [habs, Spec.acosh_coe le_rfl, Real.arcosh_zero, EReal.coe_zero, roundVal_zero]
    · rw [dite_eq_right h1, dite_eq_right hp]
      have hgt := one_lt_toRat_of_acosh_cond q hc h1
      rw [Spec.acosh_coe hgt.le]
      exact zivLoopCertified_eq_threshold' p mode _ _
        (not_mem_floatSet_of_irrational p (irrational_acosh_toRat q hgt)) _
        (by unfold zivGuardBits; omega)
        (fun w hw => by
          obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
            acoshRatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q hgt.le
          exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _
  · rw [dite_eq_right hc, Spec.acosh_coe_of_lt_one (toRat_lt_one_of_not_acosh_cond q hc),
      roundVal_none]

end Azurite.AzFloat
