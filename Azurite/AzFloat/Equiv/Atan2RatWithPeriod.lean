/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2RatWithPeriod
import Azurite.AzFloat.Equiv.Atan2WithPeriod

/-!
# Equivalence: `atan2 (y, x) u / (2π)` for rationals

`atan2RatWithPeriodPrecRound_eq :
  atan2RatWithPeriodPrecRound y x u p mode = roundVal p mode (Spec.atan2WithPeriod y x u)` for
`p ≠ 0`, i.e. the rounding of `Complex.arg (x + iy) · u / (2π)`.
-/

open Real

namespace Azurite.AzFloat

/-- **`atan2 (y, x) u / (2π)` of rationals is correctly rounded.** -/
theorem atan2RatWithPeriodPrecRound_eq (y x : AzRat) (u : UInt64) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    atan2RatWithPeriodPrecRound y x u p mode
      = roundVal p mode (Spec.atan2WithPeriod (((AzRat.toRat y : ℚ) : ℝ) : EReal)
        (((AzRat.toRat x : ℚ) : ℝ) : EReal) u.toNat) := by
  have hp := NeZero.ne p
  unfold atan2RatWithPeriodPrecRound
  rw [Spec.atan2WithPeriod_of (Spec.atan2_coe_coe _ _)]
  set yv := ((AzRat.toRat y : ℚ) : ℝ) with hyv
  set xv := ((AzRat.toRat x : ℚ) : ℝ) with hxv
  have hzero : ∀ {θ : ℝ}, θ = 0 →
      ((zero, Ordering.eq) : AzFloat × Ordering)
        = roundVal p mode (some ((θ * u.toNat / (2 * π) : ℝ) : EReal)) := fun h => by
    rw [h, zero_mul, zero_div, EReal.coe_zero, roundVal_zero]
  by_cases hy : y.num = 0
  · rw [dite_eq_left hy]
    have hy0 : yv = 0 := coe_toRat_eq_zero_of_num_eq_zero y hy
    rw [hy0]
    by_cases hx : x.num = 0
    · have hx0 : xv = 0 := coe_toRat_eq_zero_of_num_eq_zero x hx
      rw [x.zero_sign hx, hx0]
      simp only [↓reduceIte]
      exact hzero Complex.arg_zero
    · have hs := toRat_sign_iff x hx
      have hx0 : xv ≠ 0 := coe_toRat_ne_zero_of_num_ne_zero x hx
      cases hsg : x.sign with
      | true =>
        simp only [↓reduceIte]
        exact hzero (Complex.arg_ofReal_of_nonneg (hs.mp hsg).le)
      | false =>
        have hneg : xv < 0 := by
          rcases lt_or_gt_of_ne hx0 with h | h
          · exact h
          · rw [hs.mpr h] at hsg; cases hsg
        have h : Complex.arg ⟨xv, 0⟩ = π := Complex.arg_ofReal_of_neg hneg
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [h]
        exact turnFracN_round_pos 1 u 1 p mode (by
          push_cast
          rw [div_eq_iff (by positivity)]
          ring)
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
    have hylt : y.sign = false → yv < 0 := fun h => hneg.mp (by rw [h]; rfl)
    by_cases hx : x.num = 0
    · rw [dite_eq_left hx]
      have hx0 : xv = 0 := coe_toRat_eq_zero_of_num_eq_zero x hx
      rw [hx0, arg_zero_re hy0]
      cases hsg : y.sign with
      | true =>
        rw [ite_eq_left (hsy.mp hsg)]
        exact turnFracN_round_pos 1 u 2 p mode (by
          push_cast
          rw [div_eq_iff (by positivity)]
          ring)
      | false =>
        rw [ite_eq_right (not_lt.mpr (hylt hsg).le)]
        exact turnFracN_round_neg 1 u 2 p mode (by
          push_cast
          rw [div_eq_iff (by positivity)]
          ring)
    · rw [dite_eq_right hx]
      have hx0 : xv ≠ 0 := coe_toRat_ne_zero_of_num_ne_zero x hx
      have hxpos := toRat_sign_iff x hx
      have hval := arg_eq_atan2Abs hx0 hy0 hneg hxpos
      by_cases hu : u.toNat = 0
      · rw [dite_eq_left hu, hu, Nat.cast_zero, mul_zero, zero_div, EReal.coe_zero,
          roundVal_zero]
      · rw [dite_eq_right hu]
        by_cases h1 : (y.abs / x.abs).num = (y.abs / x.abs).den
        · rw [dite_eq_left h1]
          have habs : |yv| = |xv| := by
            have h := (abs_toRat_eq_one_iff (y.abs / x.abs)).mpr h1
            rw [toRat_abs_div_abs, abs_div, abs_abs, abs_abs,
              div_eq_one_iff_eq (abs_ne_zero.mpr hx0)] at h
            exact h
          have hb0 : |xv| ≠ 0 := abs_ne_zero.mpr hx0
          have hquot : arctan (|xv| / |xv|) = π / 4 := by rw [div_self hb0, arctan_one]
          rw [habs] at hval
          unfold atan2Abs at hval
          rw [hquot] at hval
          rw [hval]
          cases hsy' : y.sign <;> cases hsx' : x.sign <;>
            simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
          · exact turnFracN_round_neg 3 u 3 p mode (by
              push_cast
              rw [div_eq_iff (by positivity)]
              ring)
          · exact turnFracN_round_neg 1 u 3 p mode (by
              push_cast
              rw [div_eq_iff (by positivity)]
              ring)
          · exact turnFracN_round_pos 3 u 3 p mode (by
              push_cast
              rw [div_eq_iff (by positivity)]
              ring)
          · exact turnFracN_round_pos 1 u 3 p mode (by
              push_cast
              rw [div_eq_iff (by positivity)]
              ring)
        · rw [dite_eq_right h1, dite_eq_right hp]
          have hy0' : AzRat.toRat y ≠ 0 := fun h => hy0 (by rw [hyv, h, Rat.cast_zero])
          have hx0' : AzRat.toRat x ≠ 0 := fun h => hx0 (by rw [hxv, h, Rat.cast_zero])
          have hne : |yv| ≠ |xv| := fun h => by
            apply h1
            apply (abs_toRat_eq_one_iff (y.abs / x.abs)).mp
            rw [toRat_abs_div_abs, h, div_self (abs_ne_zero.mpr hx0), abs_one]
          have hper := arg_period_eq hx0 hy0 hneg hxpos (u.toNat : ℝ)
          have hirr := irrational_atan2AbsPeriod_of_rat hy0' hx0' hne hxpos hu
          set ψ := atan2Abs |yv| |xv| x.sign * u.toNat / (2 * π) with hψ
          have key : ∀ (o : Bool) (m : RoundingMode),
              zivLoopCertified (atan2RatPeriodApprox o y x (AzNat.ofNat u.toNat)) p m
                (p + zivGuardBits)
                (atan2RatPeriodApprox_isSome_exists p m o y x hy hx h1
                  (by rw [AzNat.toNat_ofNat]; exact hu) (p + zivGuardBits)
                  (by unfold zivGuardBits; omega))
              = roundVal p m (some (((if o then -1 else 1) * ψ : ℝ) : EReal)) := fun o m =>
            zivLoopCertified_eq_threshold' p m _ _
              (not_mem_floatSet_of_irrational p (by
                cases o with
                | false => simpa using hirr
                | true => simpa using hirr.neg)) _ (by unfold zivGuardBits; omega)
              (fun w _ => by
                obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
                  atan2RatPeriodApprox_spec o y x hy hx (AzNat.ofNat u.toNat) w
                rw [AzNat.toNat_ofNat] at hlo hhi
                exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _
          rw [hper]
          dsimp only
          set o := atan2RatPeriodOrient (y.abs / x.abs) x.sign with hodef
          rw [key o (if o = !y.sign then mode else -mode)]
          by_cases ho : o = !y.sign
          · rw [ite_eq_left ho, ite_eq_left ho, ho]
          · rw [ite_eq_right ho, ite_eq_right ho]
            have hflip : ∀ a b : Bool, ¬ a = !b → (if (!b) = true then (-1 : ℝ) else 1) * ψ
                = -((if a = true then (-1 : ℝ) else 1) * ψ) := by
              intro a b h
              cases a <;> cases b <;> simp at h ⊢
            rw [hflip o y.sign ho, roundVal_neg]

end Azurite.AzFloat
