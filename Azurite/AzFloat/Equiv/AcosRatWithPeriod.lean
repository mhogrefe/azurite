/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosRatWithPeriod
import Azurite.AzFloat.Equiv.AcosWithPeriod

/-!
# Equivalence: `arccos (q) u / (2π)` for a rational `q`

`acosRatWithPeriodPrecRound_eq :
  acosRatWithPeriodPrecRound q u p mode = roundVal p mode (Spec.acosWithPeriod q u)` for
`p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

/-- **`arccos (q) u / (2π)` of a rational is correctly rounded.** -/
theorem acosRatWithPeriodPrecRound_eq (q : AzRat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    acosRatWithPeriodPrecRound q u p mode
      = roundVal p mode (Spec.acosWithPeriod (((AzRat.toRat q : ℚ) : ℝ) : EReal) u.toNat) := by
  have hp := NeZero.ne p
  obtain ⟨hv0, hvm1, hvh, hvmh⟩ := acosPeriod_values (u.toNat : ℝ)
  unfold acosRatWithPeriodPrecRound
  set qv := ((AzRat.toRat q : ℚ) : ℝ) with hqv
  by_cases h0 : q.num = 0
  · have hq0 : qv = 0 := coe_toRat_eq_zero_of_num_eq_zero q h0
    rw [dite_eq_left h0, ite_eq_right hp, hq0, Spec.acosWithPeriod_coe (by simp)]
    exact turnRatio_eq u 1 4 p mode hv0
  · rw [dite_eq_right h0]
    have hs : q.sign = true ↔ 0 < qv := toRat_sign_iff q h0
    have hq0 : qv ≠ 0 := coe_toRat_ne_zero_of_num_ne_zero q h0
    by_cases h1 : q.num = q.den
    · rw [dite_eq_left h1]
      have habs1 : |qv| = 1 := (abs_toRat_eq_one_iff q).mpr h1
      rw [Spec.acosWithPeriod_coe habs1.le, eq_signed_of_abs_eq hs hq0 habs1]
      cases q.sign with
      | true =>
        simp only [↓reduceIte]
        rw [arccos_one, zero_mul, zero_div, EReal.coe_zero, roundVal_zero]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ite_eq_right hp]
        exact turnRatio_eq u 1 2 p mode hvm1
    · rw [dite_eq_right h1]
      have hne1 : |qv| ≠ 1 := fun h => h1 ((abs_toRat_eq_one_iff q).mp h)
      by_cases hle : q.num ≤ q.den
      · rw [dite_eq_left hle]
        have hlt1 : |qv| < 1 := lt_of_le_of_ne ((abs_toRat_le_one_iff q).mp hle) hne1
        rw [Spec.acosWithPeriod_coe hlt1.le]
        by_cases hu : u.toNat = 0
        · rw [dite_eq_left hu, hu, Nat.cast_zero, mul_zero, zero_div, EReal.coe_zero,
            roundVal_zero]
        · rw [dite_eq_right hu, dite_eq_right hp]
          by_cases hh : (q.abs + q.abs).num = (q.abs + q.abs).den
          · rw [dite_eq_left hh]
            have habsh : |qv| = 1 / 2 := (abs_toRat_eq_half_iff q).mpr hh
            rw [eq_signed_of_abs_eq hs hq0 habsh]
            cases q.sign with
            | true =>
              simp only [↓reduceIte]
              exact turnRatio_eq u 1 6 p mode hvh
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact turnRatio_eq u 1 3 p mode hvmh
          · rw [dite_eq_right hh]
            have hneh : |qv| ≠ 1 / 2 := fun h => hh ((abs_toRat_eq_half_iff q).mp h)
            have hirr := irrational_acosPeriod_toRat q h0 hlt1 hneh hu
            set ψ := arccos qv * u.toNat / (2 * π) with hψ
            have key : ∀ (o : Bool) (m' : RoundingMode),
                zivLoopCertified (acosRatPeriodApprox o q (AzNat.ofNat u.toNat)) p m'
                  (p + zivGuardBits)
                  (acosRatPeriodApprox_isSome_exists p m' o q h0 hlt1 hneh
                    (by rw [AzNat.toNat_ofNat]; exact hu) (p + zivGuardBits)
                    (by unfold zivGuardBits; omega))
                = roundVal p m' (some (((if o then -1 else 1) * ψ : ℝ) : EReal)) :=
              fun o m' =>
              zivLoopCertified_eq_threshold' p m' _ _
                (not_mem_floatSet_of_irrational p (by
                  cases o with
                  | false => simpa using hirr
                  | true => simpa using hirr.neg)) _ (by unfold zivGuardBits; omega)
                (fun w _ => by
                  obtain ⟨lv, hv', hl, hh', hlo, hhi, -⟩ :=
                    acosRatPeriodApprox_spec o q h0 hlt1 (AzNat.ofNat u.toNat) w
                  rw [AzNat.toNat_ofNat] at hlo hhi
                  exact ⟨lv, hv', hl, hh', hlo, hhi⟩) _
            dsimp only
            set o := acosPeriodOrientOf (ratAbsLeHalf q) q.sign with hodef
            rw [key o (if o then -mode else mode)]
            exact orient_roundVal o p mode ψ
      · rw [dite_eq_right hle]
        have hgt : 1 < |qv| := not_le.mp fun h => hle ((abs_toRat_le_one_iff q).mpr h)
        rw [Spec.acosWithPeriod_coe_of_one_lt hgt, roundVal_none]

end Azurite.AzFloat
