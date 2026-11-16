/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Asech
import Azurite.AzFloat.AsechRat
import Azurite.AzFloat.Equiv.Acosh
import Azurite.AzFloat.Equiv.AsecRat
import Azurite.AzFloat.Equiv.RatPowRat

/-!
# Equivalence: `asech x` and `asech q`

`Spec.asech a = acosh (1/a)` for a finite `a ≠ 0` (`+∞` at `0`, undefined at `±∞`),
`asechPrecRound_eq_liftVal : asechPrecRound x p mode = liftVal Spec.asech x p mode` and
`asechRatPrecRound_eq : asechRatPrecRound q p mode = roundVal p mode (Spec.asech q)`, for
`p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `asech`: `acosh (1/a)` for a finite `a ≠ 0` (so `arcosh (1/a)` on `(0, 1]`,
undefined for `a < 0` and `a > 1`), `+∞` at `0`, undefined at `±∞`. -/
noncomputable def asech (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then none
  else if a.toReal = 0 then some ⊤ else acosh ((a.toReal⁻¹ : ℝ) : EReal)

theorem asech_coe {r : ℝ} (hr : r ≠ 0) : asech (r : EReal) = acosh ((r⁻¹ : ℝ) : EReal) := by
  unfold asech
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe,
    ite_eq_right hr]

theorem asech_zero : asech ((0 : ℝ) : EReal) = some ⊤ := by
  unfold asech
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top 0, EReal.coe_ne_bot 0⟩), EReal.toReal_coe,
    ite_eq_left rfl]

@[simp] theorem asech_top : asech ⊤ = none := by
  unfold asech
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem asech_bot : asech ⊥ = none := by
  unfold asech
  rw [ite_eq_left (Or.inr rfl)]

end Spec

/-- **`asech` is correctly rounded.** -/
theorem asechPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    asechPrecRound x p mode = liftVal Spec.asech x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [asechPrecRound]
  | zero =>
    simp only [asechPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.asech_zero, roundVal_top]
  | finite s e q m hv =>
    simp only [asechPrecRound, toVal_finite, Option.bind_some]
    set xv := finiteVal s e m with hxv
    have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
    have hsgn := finiteVal_sign_iff s e hv
    have hb := abs_finiteVal_bounds s e hv
    rw [← hxv] at hsgn hb
    rw [Spec.asech_coe hx0]
    by_cases hs : s = true
    · rw [dite_eq_left hs]
      have hpos : 0 < xv := hsgn.mp hs
      by_cases h1 : eqIEEE (finite s e q m hv) one = true
      · rw [ite_eq_left h1]
        obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp h1
        rw [toVal_finite] at hv1
        rw [toVal_one'] at hv2
        have hx1 : xv = 1 := by
          have := hv1.trans hv2.symm
          exact_mod_cast Option.some.inj this
        rw [hx1, inv_one, Spec.acosh_coe le_rfl, Real.arcosh_zero, EReal.coe_zero,
          roundVal_zero]
      · rw [ite_eq_right h1]
        have hne : |xv| ≠ 1 := fun h => by
          rw [abs_of_pos hpos] at h
          exact h1 ((eqIEEE_iff _ _).mpr
            ⟨_, toVal_finite s e q m hv, by rw [← hxv, h]; exact toVal_one'⟩)
        by_cases he : e.sign = true ∧ e.abs.toNat ≠ 0
        · rw [dite_eq_left he]
          have hgt := one_lt_abs_of_exponent hb.1 he hne
          rw [abs_of_pos hpos] at hgt
          rw [Spec.acosh_coe_of_lt_one (inv_lt_one_of_one_lt₀ hgt), roundVal_none]
        · rw [dite_eq_right he, dite_eq_right (NeZero.ne p)]
          have hlt : xv < 1 := lt_of_le_of_lt (le_abs_self _) (abs_lt_one_of_exponent hb.2 he)
          rw [Spec.acosh_coe ((one_le_inv₀ hpos).mpr hlt.le)]
          exact zivLoopCertified_eq_threshold' p mode _ _
            (not_mem_floatSet_of_irrational p
              (irrational_asech_of_toVal (toVal_finite s e q m hv) hpos hlt))
            _ (by unfold zivGuardBits; omega)
            (fun w hw => by
              obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := asechApprox_spec
                (toVal_finite s e q m hv) hpos hlt.le (w := w)
                (by unfold zivGuardBits at hw; omega)
              exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _
    · rw [dite_eq_right hs]
      have hneg : xv < 0 := by
        rcases lt_or_gt_of_ne hx0 with h | h
        · exact h
        · exact absurd (hsgn.mpr h) hs
      have hinv : xv⁻¹ < 0 := inv_lt_zero.mpr hneg
      rw [Spec.acosh_coe_of_lt_one (by linarith), roundVal_none]

/-- **`asech q` is correctly rounded.** -/
theorem asechRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    asechRatPrecRound q p mode
      = roundVal p mode (Spec.asech (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold asechRatPrecRound
  by_cases h0 : q.num = 0
  · rw [ite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Spec.asech_zero, roundVal_top]
  · have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
    rw [ite_eq_right h0, acoshRatPrecRound_eq, coe_toRat_inv, Spec.asech_coe hq0]

end Azurite.AzFloat
