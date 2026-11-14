/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinBracket
import Azurite.AzFloat.Equiv.CosBracket
import Azurite.AzFloat.Equiv.PowRatBracket
import Azurite.AzFloat.Equiv.RatPowRat

/-!
# Equivalence: sign, irrationality and the tiny-argument path of `sin x`

`sin_eq_sign_mul_sin_abs`, `irrational_sin_of_toVal`, `sinTiny?_eq`, `finiteVal_neg_iff`,
`sin_eq_of_neg_iff`.  The bracket itself (`sinBracket_spec`) is in `Equiv/SinCosBracket.lean`.
-/

namespace Azurite.AzFloat

/-- The sign of `sin x` relative to `sin |x|`. -/
theorem sin_eq_sign_mul_sin_abs (xv : ℝ) :
    Real.sin xv = (if xv < 0 then -1 else 1) * Real.sin |xv| := by
  split_ifs with h
  · rw [abs_of_neg h, Real.sin_neg]; ring
  · rw [abs_of_nonneg (not_lt.mp h), one_mul]

/-- `sin x` is irrational for a nonzero finite float `x`. -/
theorem irrational_sin_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (Real.sin xv) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hx0
    rw [hq, Rat.cast_zero]
  rw [hq]
  exact irrational_sin_rat hq0

/-- The tiny-argument path answers with the rounding of `sin x`. -/
theorem sinTiny?_eq {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ)
    [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : sinTiny? s (finite s e q m hv) e q p mode = some r) :
    r = roundVal p mode (some ((Real.sin (finiteVal s e m) : ℝ) : EReal)) := by
  unfold sinTiny? at h
  dsimp only at h
  set w := max p q + zivGuardBits with hw
  have : NeZero (w + 8) := ⟨by omega⟩
  set xv := finiteVal s e m with hxv
  have hx : (finite s e q m hv).toVal = some (xv : EReal) := toVal_finite s e q m hv
  have hlt := (abs_finiteVal_bounds s e hv).2
  rw [← hxv] at hlt
  have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
  set a := |xv| with ha
  have ha0 : 0 < a := abs_pos.mpr hx0
  set t := (2 : ℝ) ^ e.toInt with ht
  have ht0 : 0 < t := by positivity
  have habs : (finite s e q m hv).abs.toVal = some ((a : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hnx : (-(finite s e q m hv).abs).toVal = some ((-a : ℝ) : EReal) := by
    rw [toVal_neg, habs, Option.map_some, EReal.coe_neg]
  have hd : (((finite s e q m hv).abs <<< e) <<< e).toVal = some ((a * t * t : ℝ) : EReal) :=
    toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal habs e) e
  obtain ⟨hi, hhi, hhi1, -⟩ := addCeiling_abs hnx hd (w + 8)
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hnx)
  rw [fval_of_toVal_coe hnx] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  have hs1 := Real.sin_lt ha0
  have hs2 := Real.sin_gt_sub_cube ha0
  have hcube : a ^ 3 ≤ a * t * t := by
    have h1 : a * a ≤ t * t := mul_le_mul hlt.le hlt.le ha0.le ht0.le
    nlinarith
  have hsgn := finiteVal_sign_iff s e hv
  rw [← hxv] at hsgn
  cases s with
  | true =>
    simp only [↓reduceIte] at h
    split_ifs at h with hc
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
    have hpos : 0 < xv := hsgn.mp rfl
    have hax : a = xv := abs_of_pos hpos
    have hr := roundingPossible_eq' p (-mode) (v := -Real.sin a) hR1 hR2 (by linarith)
      (by linarith) (Or.inl fun hEq => absurd hEq (by linarith)) hr'
    rw [hr, ← hax]
    have hneg := roundVal_neg p mode (-Real.sin a)
    rw [neg_neg] at hneg
    exact hneg.symm
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    split_ifs at h with hc
    have hneg : xv < 0 := by
      rcases lt_or_gt_of_ne hx0 with h' | h'
      · exact h'
      · exact absurd (hsgn.mpr h') (by simp)
    have hax : xv = -a := by rw [ha, abs_of_neg hneg, neg_neg]
    have hr := roundingPossible_eq' p mode (v := -Real.sin a) hR1 hR2 (by linarith)
      (by linarith) (Or.inl fun hEq => absurd hEq (by linarith)) h
    rw [hr, hax, Real.sin_neg]

/-- `!s` is the sign bit of a negative float. -/
theorem finiteVal_neg_iff (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    (!s) = true ↔ finiteVal s e m < 0 := by
  have h1 := finiteVal_sign_iff s e hv
  have h0 := finiteVal_ne_zero s e hv
  cases s
  · simp only [Bool.not_false, true_iff]
    rcases lt_or_gt_of_ne h0 with h | h
    · exact h
    · exact absurd (h1.mpr h) (by simp)
  · simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_lt]
    exact (h1.mp rfl).le

/-- `sin x = ± sin |x|` with the sign bit of `x`. -/
theorem sin_eq_of_neg_iff {neg : Bool} {xv : ℝ} (hneg : neg = true ↔ xv < 0) :
    Real.sin xv = (if neg then -1 else 1) * Real.sin |xv| := by
  rw [sin_eq_sign_mul_sin_abs]
  cases neg with
  | false =>
    have : ¬ xv < 0 := fun h => by simpa using hneg.mpr h
    simp [this]
  | true => simp [hneg.mp rfl]

end Azurite.AzFloat
