/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinRatBracket
import Azurite.AzFloat.Equiv.AsinBracket
import Azurite.AzFloat.Equiv.SqrtRat
import Azurite.AzFloat.Equiv.TanRatBracket
import Azurite.AzFloat.Equiv.AtanRatWithPeriodBracket
import Azurite.AzRat.Equiv.Sub
import Azurite.AzRat.Equiv.Mul

/-!
# Equivalence: the bracket of `arcsin q` for a rational `q`

`asinRatBracket_spec` (width at most `2^(−w)`), `arcsin_toRat_eq`, `asinRatApprox_spec`,
`irrational_arcsin_toRat`, `asinRatApprox_isSome_exists` (the Ziv certificate),
`asinTinyRat?_eq`.
-/

open Real

namespace Azurite.AzFloat

/-- **The bracket of `arcsin |q|`** for a rational `0 < |q| < 1`: width at most `2^(−w)`. -/
theorem asinRatBracket_spec (q : AzRat) (h0 : q.num ≠ 0)
    (h1 : |(AzRat.toRat q : ℝ)| < 1) (w : ℕ) :
    ∃ lo hi : ℝ, (asinRatBracket q w).1.toVal = some (lo : EReal) ∧
      (asinRatBracket q w).2.toVal = some (hi : EReal) ∧ 0 ≤ lo ∧
      lo ≤ arcsin |(AzRat.toRat q : ℝ)| ∧ arcsin |(AzRat.toRat q : ℝ)| ≤ hi ∧
      hi - lo ≤ (1 / 2 : ℝ) ^ w := by
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  set a := |(AzRat.toRat q : ℝ)| with ha
  have ha0 : 0 < a := abs_pos.mpr hq0
  have habs : ((AzRat.toRat q.abs : ℚ) : ℝ) = a := by
    rw [AzRat.toRat_abs, Rat.cast_abs]
  unfold asinRatBracket
  dsimp only
  set K := atanWork (ratExpBound q) w with hK
  have hKw : w + 8 ≤ K := by
    rw [hK]
    unfold atanWork
    omega
  set P := K + 64 + 8 with hP
  have hP8 : 8 ≤ P := by omega
  have : NeZero P := ⟨by omega⟩
  set ε := (1 / 2 : ℝ) ^ P with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 256 := by
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hP8
    rw [← hε] at this
    norm_num at this
    linarith
  -- the rational `1 − a²` and its square root
  have hr : ((AzRat.toRat (1 - q.abs * q.abs) : ℚ) : ℝ) = 1 - a ^ 2 := by
    rw [AzRat.toRat_sub, AzRat.toRat_mul, AzRat.toRat_one]
    push_cast
    rw [habs]
    ring
  have hr0 : 0 ≤ 1 - a ^ 2 := by nlinarith
  set s := √(1 - a ^ 2) with hs
  have hs0 : 0 ≤ s := sqrt_nonneg _
  have hs1 : s ≤ 1 := by
    rw [hs]
    exact sqrt_le_one.mpr (by nlinarith)
  obtain ⟨sl, hsl, hsl0, hsl1, hsl2⟩ := roundVal_floor_err P hs0
  obtain ⟨sh, hsh, hsh1, hsh2⟩ := roundVal_ceiling_err P hs0
  rw [← hε] at hsl2 hsh2
  have hslv : (sqrtRatPrecRound (1 - q.abs * q.abs) P .Floor).1.toVal = some (sl : EReal) := by
    rw [sqrtRatPrecRound_eq, hr, Spec.sqrt_coe _ hr0]
    exact hsl
  have hshv : (sqrtRatPrecRound (1 - q.abs * q.abs) P .Ceiling).1.toVal
      = some (sh : EReal) := by
    rw [sqrtRatPrecRound_eq, hr, Spec.sqrt_coe _ hr0]
    exact hsh
  have hsε : s * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right hs1 hε0.le
  -- the two roundings of `a`
  obtain ⟨al, hal, hal1, hal2⟩ := ofAzRatRound_floor_abs q.abs P
  obtain ⟨ah, hah, hah1, hah2⟩ := ofAzRatRound_ceiling_abs q.abs P
  rw [habs] at hal1 hal2 hah1 hah2
  rw [abs_of_pos ha0, ← hε] at hal2 hah2
  have haε : a * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right h1.le hε0.le
  have haε2 : a * ε ≤ a * (1 / 256) := mul_le_mul_of_nonneg_left hε1 ha0.le
  obtain ⟨tl, th, htl, hth, htl0, htl1, hth1, htw⟩ := asinArgOf_spec hP8 hal hah
    (S := ((sqrtRatPrecRound (1 - q.abs * q.abs) P .Floor).1,
      (sqrtRatPrecRound (1 - q.abs * q.abs) P .Ceiling).1)) hslv hshv ha0 h1.le
    (by linarith) (by rw [← hε]; linarith) hal1 hah1 (by rw [← hε]; linarith) hs0 hs1 hsl0
    (by rw [← hε]; linarith) hsl1 hsh1 (by rw [← hε]; linarith)
  exact asinDouble_spec ha0 h1.le hKw htl hth htl0 htl1 hth1 htw

/-- `arcsin q = ± arcsin |q|` with the sign of the rational. -/
theorem arcsin_toRat_eq (q : AzRat) (h0 : q.num ≠ 0) :
    arcsin (AzRat.toRat q : ℝ)
      = (if (!q.sign) = true then -1 else 1) * arcsin |(AzRat.toRat q : ℝ)| := by
  have hs := toRat_sign_iff q h0
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  refine arcsin_eq_of_neg_iff ?_
  cases hsg : q.sign with
  | true =>
    have := hs.mp hsg
    simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_lt]
    exact this.le
  | false =>
    simp only [Bool.not_false, true_iff]
    rcases lt_or_gt_of_ne hq0 with h | h
    · exact h
    · rw [hs.mpr h] at hsg; cases hsg

/-- `asinRatApprox` as a pair of `Roundable`s bracketing `arcsin q`. -/
theorem asinRatApprox_spec (q : AzRat) (h0 : q.num ≠ 0) (h1 : |(AzRat.toRat q : ℝ)| < 1)
    (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (asinRatApprox q w).1 lv ∧ Rounds (asinRatApprox q w).2 hv ∧
      lv ≤ arcsin (AzRat.toRat q : ℝ) ∧ arcsin (AzRat.toRat q : ℝ) ≤ hv ∧
      hv - lv ≤ (1 / 2 : ℝ) ^ w := by
  obtain ⟨lo, hi, hlo, hhi, -, hl, hh, hwid⟩ := asinRatBracket_spec q h0 h1 w
  obtain ⟨lv, hv, hR1, hR2, hl', hh', he⟩ := enclApprox_spec (!q.sign) hlo hhi hl hh
  rw [arcsin_toRat_eq q h0]
  exact ⟨lv, hv, hR1, hR2, hl', hh', by rw [he]; exact hwid⟩

/-- `arcsin q` is irrational for a nonzero rational `q` with `|q| ≤ 1`. -/
theorem irrational_arcsin_toRat (q : AzRat) (h0 : q.num ≠ 0)
    (h1 : |(AzRat.toRat q : ℝ)| ≤ 1) : Irrational (arcsin (AzRat.toRat q : ℝ)) := by
  obtain ⟨h2, h3⟩ := abs_le.mp h1
  exact irrational_arcsin_rat
    (fun h => coe_toRat_ne_zero_of_num_ne_zero q h0 (by rw [h, Rat.cast_zero])) h2 h3

/-- The Ziv certificate for `arcsin q`, `q` a rational with `0 < |q| < 1`. -/
theorem asinRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (h1 : |(AzRat.toRat q : ℝ)| < 1) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (asinRatApprox q (w₀ * 2 ^ f)).1 (asinRatApprox q (w₀ * 2 ^ f)).2
      p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (asinRatApprox q)
    (irrational_arcsin_toRat q h0 h1.le) (fun w => (1 / 2 : ℝ) ^ w)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) 0
    (fun w _ => asinRatApprox_spec q h0 h1 w) w₀ hw₀

/-- The tiny-argument path of `arcsin q` answers with the rounding of `arcsin q`. -/
theorem asinTinyRat?_eq (q : AzRat) (h0 : q.num ≠ 0) {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} (hT : asinTinyRat? q p mode = some r) :
    r = roundVal p mode (some ((arcsin (AzRat.toRat q : ℝ) : ℝ) : EReal)) := by
  unfold asinTinyRat? at hT
  have hc : (ratExpBound q).sign = false
      ∧ p + zivGuardBits + 8 ≤ (ratExpBound q).abs.toNat := by
    unfold tanTinyRat? at hT
    replace hT := eq_some_of_guardedBy hT
    unfold tanTinyCore? at hT
    dsimp only at hT
    by_contra hc
    rw [ite_eq_right hc] at hT
    exact absurd hT (by simp)
  have hlt : |(AzRat.toRat q : ℝ)| < (2 : ℝ) ^ (ratExpBound q).toInt :=
    lt_of_lt_of_le (abs_toRat_lt_two_zpow q) (zpow_le_zpow_right₀ (by norm_num) (by omega))
  have hhalf := two_zpow_le_half hc.1 (by
    have := hc.2
    unfold zivGuardBits at this
    omega)
  rw [← asinPatch_eq (by linarith : |(AzRat.toRat q : ℝ)| ≤ 1 / 2)]
  exact tanTinyRat?_eq_of asinPatch_neg asinPatch_bounds q h0 hT

end Azurite.AzFloat
