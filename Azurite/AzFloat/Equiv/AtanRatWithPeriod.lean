/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanRatWithPeriod
import Azurite.AzFloat.Equiv.AtanWithPeriod

/-!
# Equivalence: `arctan (q) u / (2π)` for a rational `q`

`atanRatWithPeriodPrecRound_eq :
  atanRatWithPeriodPrecRound q u p mode = roundVal p mode (Spec.atanWithPeriod q u)` for
`p ≠ 0`.
-/

namespace Azurite.AzFloat

/-- **`arctan (q) u / (2π)` of a rational is correctly rounded.** -/
theorem atanRatWithPeriodPrecRound_eq (q : AzRat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    atanRatWithPeriodPrecRound q u p mode
      = roundVal p mode (Spec.atanWithPeriod (((AzRat.toRat q : ℚ) : ℝ) : EReal) u.toNat) := by
  have hp := NeZero.ne p
  have hpi := Real.pi_pos
  unfold atanRatWithPeriodPrecRound
  rw [Spec.atanWithPeriod_coe]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Real.arctan_zero, zero_mul,
      zero_div, EReal.coe_zero, roundVal_zero]
  · rw [dite_eq_right h0]
    by_cases hu : u.toNat = 0
    · rw [dite_eq_left hu, hu, Nat.cast_zero, mul_zero, zero_div, EReal.coe_zero, roundVal_zero]
    · rw [dite_eq_right hu]
      set qv := ((AzRat.toRat q : ℚ) : ℝ) with hqv
      have hs := toRat_sign_iff q h0
      have hq0 : qv ≠ 0 := coe_toRat_ne_zero_of_num_ne_zero q h0
      by_cases h1 : q.num = q.den
      · rw [dite_eq_left h1, setPrecRound_eq_roundVal (toVal_turnFraction q.sign u 3)]
        have habs1 : |qv| = 1 := (abs_toRat_eq_one_iff q).mpr h1
        congr 3
        cases hsg : q.sign with
        | true =>
          rw [abs_of_pos (hs.mp hsg)] at habs1
          have hq1 : qv = 1 := habs1
          simp only [↓reduceIte, one_mul]
          rw [hq1, Real.arctan_one]
          field_simp
          norm_num
        | false =>
          have hlt : qv < 0 := by
            rcases lt_or_gt_of_ne hq0 with h | h
            · exact h
            · rw [hs.mpr h] at hsg; cases hsg
          rw [abs_of_neg hlt] at habs1
          have hx1 : qv = -1 := by linarith
          simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
          rw [hx1, Real.arctan_neg, Real.arctan_one]
          field_simp
          norm_num
      · rw [dite_eq_right h1, dite_eq_right hp]
        exact zivLoopCertified_eq_threshold' p mode _
          (Real.arctan qv * u.toNat / (2 * Real.pi))
          (not_mem_floatSet_of_irrational p (irrational_atanPeriod_toRat q h0 h1 hu))
          _ (by unfold zivGuardBits; omega)
          (fun w _ => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
              atanRatPeriodApprox_spec q h0 (AzNat.ofNat u.toNat) w
            rw [AzNat.toNat_ofNat] at hlo hhi
            exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
