/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinRatWithPeriod
import Azurite.AzFloat.Equiv.AsinWithPeriod

/-!
# Equivalence: `arcsin (q) u / (2π)` for a rational `q`

`asinRatWithPeriodPrecRound_eq :
  asinRatWithPeriodPrecRound q u p mode = roundVal p mode (Spec.asinWithPeriod q u)` for
`p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

/-- **`arcsin (q) u / (2π)` of a rational is correctly rounded.** -/
theorem asinRatWithPeriodPrecRound_eq (q : AzRat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    asinRatWithPeriodPrecRound q u p mode
      = roundVal p mode (Spec.asinWithPeriod (((AzRat.toRat q : ℚ) : ℝ) : EReal) u.toNat) := by
  have hp := NeZero.ne p
  unfold asinRatWithPeriodPrecRound
  set qv := ((AzRat.toRat q : ℚ) : ℝ) with hqv
  by_cases h0 : q.num = 0
  · have hq0 : qv = 0 := coe_toRat_eq_zero_of_num_eq_zero q h0
    rw [dite_eq_left h0, hq0, Spec.asinWithPeriod_coe (by simp), arcsin_zero, zero_mul,
      zero_div, EReal.coe_zero, roundVal_zero]
  · rw [dite_eq_right h0]
    have hs : q.sign = true ↔ 0 < qv := toRat_sign_iff q h0
    have hq0 : qv ≠ 0 := coe_toRat_ne_zero_of_num_ne_zero q h0
    by_cases h1 : q.num = q.den
    · rw [dite_eq_left h1, setPrecRound_eq_roundVal (toVal_turnFraction q.sign u 2)]
      have habs1 : |qv| = 1 := (abs_toRat_eq_one_iff q).mpr h1
      rw [Spec.asinWithPeriod_coe habs1.le, eq_signed_of_abs_eq hs hq0 habs1, asinPeriod_one]
    · rw [dite_eq_right h1]
      have hne1 : |qv| ≠ 1 := fun h => h1 ((abs_toRat_eq_one_iff q).mp h)
      by_cases hle : q.num ≤ q.den
      · rw [dite_eq_left hle]
        have hlt1 : |qv| < 1 := lt_of_le_of_ne ((abs_toRat_le_one_iff q).mp hle) hne1
        rw [Spec.asinWithPeriod_coe hlt1.le]
        by_cases hu : u.toNat = 0
        · rw [dite_eq_left hu, hu, Nat.cast_zero, mul_zero, zero_div, EReal.coe_zero,
            roundVal_zero]
        · rw [dite_eq_right hu]
          by_cases hh : (q.abs + q.abs).num = (q.abs + q.abs).den
          · rw [dite_eq_left hh, turnTwelfth_eq]
            have habsh : |qv| = 1 / 2 := (abs_toRat_eq_half_iff q).mpr hh
            rw [eq_signed_of_abs_eq hs hq0 habsh, asinPeriod_half]
          · rw [dite_eq_right hh, dite_eq_right hp]
            have hneh : |qv| ≠ 1 / 2 := fun h => hh ((abs_toRat_eq_half_iff q).mp h)
            exact zivLoopCertified_eq_threshold' p mode _ (arcsin qv * u.toNat / (2 * π))
              (not_mem_floatSet_of_irrational p
                (irrational_asinPeriod_toRat q h0 hlt1 hneh hu)) _
              (by unfold zivGuardBits; omega)
              (fun w _ => by
                obtain ⟨lv, hv', hl, hh', hlo, hhi, -⟩ :=
                  asinRatPeriodApprox_spec q h0 hlt1 (AzNat.ofNat u.toNat) w
                rw [AzNat.toNat_ofNat] at hlo hhi
                exact ⟨lv, hv', hl, hh', hlo, hhi⟩) _
      · rw [dite_eq_right hle]
        have hgt : 1 < |qv| := not_le.mp fun h => hle ((abs_toRat_le_one_iff q).mpr h)
        rw [Spec.asinWithPeriod_coe_of_one_lt hgt, roundVal_none]

end Azurite.AzFloat
