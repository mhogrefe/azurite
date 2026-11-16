/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinRat
import Azurite.AzFloat.Equiv.Asin

/-!
# Equivalence: `arcsin q` for a rational `q`

`asinRatPrecRound_eq : asinRatPrecRound q p mode = roundVal p mode (Spec.asin q)` for `p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

/-- **`arcsin q` is correctly rounded.** -/
theorem asinRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    asinRatPrecRound q p mode
      = roundVal p mode (Spec.asin (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  have hpi2 := fun (p : ℕ) [NeZero p] (m : RoundingMode) => piDiv2PrecRound_eq_liftVal₀ p m
  unfold asinRatPrecRound
  set qv := ((AzRat.toRat q : ℚ) : ℝ) with hqv
  by_cases h0 : q.num = 0
  · have hq0 : qv = 0 := coe_toRat_eq_zero_of_num_eq_zero q h0
    rw [dite_eq_left h0, hq0, Spec.asin_coe (by simp), arcsin_zero, EReal.coe_zero,
      roundVal_zero]
  · rw [dite_eq_right h0]
    have hs := toRat_sign_iff q h0
    have hq0 : qv ≠ 0 := coe_toRat_ne_zero_of_num_ne_zero q h0
    by_cases h1 : q.num = q.den
    · rw [dite_eq_left h1, signedRound_eq hpi2]
      have habs1 : |qv| = 1 := (abs_toRat_eq_one_iff q).mpr h1
      rw [Spec.asin_coe habs1.le]
      cases hsg : q.sign with
      | true =>
        have hq1 : qv = 1 := by rw [← habs1, abs_of_pos (hs.mp hsg)]
        simp only [↓reduceIte]
        rw [hq1, arcsin_one]
      | false =>
        have hlt : qv < 0 := by
          rcases lt_or_gt_of_ne hq0 with h | h
          · exact h
          · rw [hs.mpr h] at hsg; cases hsg
        have hq1 : qv = -1 := by
          rw [abs_of_neg hlt] at habs1
          linarith
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hq1, arcsin_neg_one]
    · rw [dite_eq_right h1]
      have hne1 : |qv| ≠ 1 := fun h => h1 ((abs_toRat_eq_one_iff q).mp h)
      by_cases hle : q.num ≤ q.den
      · rw [dite_eq_left hle, dite_eq_right hp]
        have hlt1 : |qv| < 1 := lt_of_le_of_ne ((abs_toRat_le_one_iff q).mp hle) hne1
        rw [Spec.asin_coe hlt1.le]
        split
        · next r hT => exact asinTinyRat?_eq q h0 hT
        exact zivLoopCertified_eq_threshold' p mode _ (arcsin qv)
          (not_mem_floatSet_of_irrational p (irrational_arcsin_toRat q h0 hlt1.le)) _
          (by unfold zivGuardBits; omega)
          (fun w _ => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := asinRatApprox_spec q h0 hlt1 w
            exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _
      · rw [dite_eq_right hle]
        have hgt : 1 < |qv| := not_le.mp fun h => hle ((abs_toRat_le_one_iff q).mpr h)
        rw [Spec.asin_coe_of_one_lt hgt, roundVal_none]

end Azurite.AzFloat
