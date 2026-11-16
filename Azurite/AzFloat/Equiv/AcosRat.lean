/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcosRat
import Azurite.AzFloat.Equiv.Acos

/-!
# Equivalence: `arccos q` for a rational `q`

`acosRatPrecRound_eq : acosRatPrecRound q p mode = roundVal p mode (Spec.acos q)` for `p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

/-- **`arccos q` is correctly rounded.** -/
theorem acosRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    acosRatPrecRound q p mode
      = roundVal p mode (Spec.acos (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold acosRatPrecRound
  set qv := ((AzRat.toRat q : ℚ) : ℝ) with hqv
  by_cases h0 : q.num = 0
  · have hq0 : qv = 0 := coe_toRat_eq_zero_of_num_eq_zero q h0
    rw [dite_eq_left h0, hq0, Spec.acos_coe (by simp), arccos_zero,
      piDiv2PrecRound_eq_liftVal₀]
    rfl
  · rw [dite_eq_right h0]
    have hs : q.sign = true ↔ 0 < qv := toRat_sign_iff q h0
    have hq0 : qv ≠ 0 := coe_toRat_ne_zero_of_num_ne_zero q h0
    by_cases h1 : q.num = q.den
    · rw [dite_eq_left h1]
      have habs1 : |qv| = 1 := (abs_toRat_eq_one_iff q).mpr h1
      rw [Spec.acos_coe habs1.le, eq_signed_of_abs_eq hs hq0 habs1]
      cases q.sign with
      | true =>
        simp only [↓reduceIte]
        rw [arccos_one, EReal.coe_zero, roundVal_zero]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [arccos_neg_one, piPrecRound_eq_liftVal₀]
        rfl
    · rw [dite_eq_right h1]
      have hne1 : |qv| ≠ 1 := fun h => h1 ((abs_toRat_eq_one_iff q).mp h)
      by_cases hle : q.num ≤ q.den
      · rw [dite_eq_left hle, dite_eq_right hp]
        have hlt1 : |qv| < 1 := lt_of_le_of_ne ((abs_toRat_le_one_iff q).mp hle) hne1
        rw [Spec.acos_coe hlt1.le]
        exact zivLoopCertified_eq_threshold' p mode _ (arccos qv)
          (not_mem_floatSet_of_irrational p (irrational_arccos_toRat q hlt1)) _
          (by unfold zivGuardBits; omega)
          (fun w _ => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := acosRatApprox_spec q h0 hlt1 w
            exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _
      · rw [dite_eq_right hle]
        have hgt : 1 < |qv| := not_le.mp fun h => hle ((abs_toRat_le_one_iff q).mpr h)
        rw [Spec.acos_coe_of_one_lt hgt, roundVal_none]

end Azurite.AzFloat
