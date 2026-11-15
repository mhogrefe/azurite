/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Rat
import Azurite.AzFloat.Equiv.Atan2

/-!
# Equivalence: `atan2 (y, x)` for rationals

`atan2RatPrecRound_eq :
  atan2RatPrecRound y x p mode = roundVal p mode (Spec.atan2 y x)` for `p ≠ 0`, i.e. the
rounding of `Complex.arg (x + iy)`.
-/

open Real

namespace Azurite.AzFloat

/-- **`atan2 (y, x)` of rationals is correctly rounded.** -/
theorem atan2RatPrecRound_eq (y x : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    atan2RatPrecRound y x p mode
      = roundVal p mode (Spec.atan2 (((AzRat.toRat y : ℚ) : ℝ) : EReal)
        (((AzRat.toRat x : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  have hpi2 := fun (p : ℕ) [NeZero p] (m : RoundingMode) => piDiv2PrecRound_eq_liftVal₀ p m
  unfold atan2RatPrecRound
  rw [Spec.atan2_coe_coe]
  set yv := ((AzRat.toRat y : ℚ) : ℝ) with hyv
  set xv := ((AzRat.toRat x : ℚ) : ℝ) with hxv
  by_cases hy : y.num = 0
  · rw [dite_eq_left hy]
    have hy0 : yv = 0 := coe_toRat_eq_zero_of_num_eq_zero y hy
    rw [hy0]
    by_cases hx : x.num = 0
    · have hx0 : xv = 0 := coe_toRat_eq_zero_of_num_eq_zero x hx
      rw [x.zero_sign hx, hx0]
      simp only [↓reduceIte]
      have h : Complex.arg ⟨0, 0⟩ = 0 := Complex.arg_zero
      rw [h, EReal.coe_zero, roundVal_zero]
    · have hs := toRat_sign_iff x hx
      have hx0 : xv ≠ 0 := coe_toRat_ne_zero_of_num_ne_zero x hx
      cases hsg : x.sign with
      | true =>
        have h : Complex.arg ⟨xv, 0⟩ = 0 := Complex.arg_ofReal_of_nonneg (hs.mp hsg).le
        simp only [↓reduceIte]
        rw [h, EReal.coe_zero, roundVal_zero]
      | false =>
        have hneg : xv < 0 := by
          rcases lt_or_gt_of_ne hx0 with h | h
          · exact h
          · rw [hs.mpr h] at hsg; cases hsg
        have h : Complex.arg ⟨xv, 0⟩ = π := Complex.arg_ofReal_of_neg hneg
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [h, piPrecRound_eq_liftVal₀]
        rfl
  · rw [dite_eq_right hy]
    have hsy := toRat_sign_iff y hy
    have hy0 : yv ≠ 0 := coe_toRat_ne_zero_of_num_ne_zero y hy
    have hneg : (!y.sign) = true ↔ yv < 0 := by
      cases hsg : y.sign with
      | true =>
        have := hsy.mp hsg
        simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_lt]
        exact this.le
      | false =>
        simp only [Bool.not_false, true_iff]
        rcases lt_or_gt_of_ne hy0 with h | h
        · exact h
        · rw [hsy.mpr h] at hsg; cases hsg
    by_cases hx : x.num = 0
    · rw [dite_eq_left hx]
      have hx0 : xv = 0 := coe_toRat_eq_zero_of_num_eq_zero x hx
      rw [signedRound_eq hpi2, hx0, arg_zero_re hy0]
      cases hsg : y.sign with
      | true => rw [ite_eq_left (hsy.mp hsg)]; rfl
      | false =>
        rw [hsg] at hneg
        rw [ite_eq_right (not_lt.mpr (hneg.mp rfl).le)]
        rfl
    · rw [dite_eq_right hx, dite_eq_right hp]
      have hx0 : xv ≠ 0 := coe_toRat_ne_zero_of_num_ne_zero x hx
      have hxpos := toRat_sign_iff x hx
      have hval := arg_eq_atan2Abs hx0 hy0 hneg hxpos
      have hy0' : AzRat.toRat y ≠ 0 := fun h => hy0 (by rw [hyv, h, Rat.cast_zero])
      have hx0' : AzRat.toRat x ≠ 0 := fun h => hx0 (by rw [hxv, h, Rat.cast_zero])
      have hirr := irrational_atan2Abs_of_rat hy0' hx0' hxpos
      have key : ∀ m : RoundingMode,
          zivLoopCertified (atan2RatApprox y x) p m (p + zivGuardBits)
            (atan2RatApprox_isSome_exists p m y x hy hx (p + zivGuardBits)
              (by unfold zivGuardBits; omega))
          = roundVal p m (some ((-atan2Abs |yv| |xv| x.sign : ℝ) : EReal)) := fun m =>
        zivLoopCertified_eq_threshold' p m _ _
          (not_mem_floatSet_of_irrational p hirr.neg) _ (by unfold zivGuardBits; omega)
          (fun w _ => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := atan2RatApprox_spec y x hy hx w
            exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _
      by_cases hsg : y.sign = true
      · rw [hsg] at hval
        simp only [hsg, ↓reduceIte]
        rw [key (-mode), hval]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, one_mul]
        rw [← roundVal_neg, neg_neg]
      · have hsg' : y.sign = false := by simpa using hsg
        rw [hsg'] at hval
        simp only [hsg', Bool.false_eq_true, ↓reduceIte]
        rw [key mode, hval]
        simp

end Azurite.AzFloat
