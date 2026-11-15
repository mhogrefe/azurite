/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2RatBracket
import Azurite.AzFloat.Equiv.Atan2Bracket
import Azurite.AzFloat.Equiv.AtanRatWithPeriodBracket
import Azurite.AzRat.Equiv.Div

/-!
# Equivalence: the bracket of `atan2 (y, x)` for rationals

`atan2RatBracket_spec` (width at most `2^(−w)`), `toRat_abs_div_abs`,
`irrational_atan2Abs_of_rat`, `atan2RatApprox_spec`, `atan2RatApprox_isSome_exists` (the Ziv
certificate).
-/

open Real

namespace Azurite.AzFloat

/-- **The bracket of `atan2 (t, ±1)`** for a positive rational `t`: width at most `2^(−w)`. -/
theorem atan2RatBracket_spec (t : AzRat) (ht0 : 0 < (AzRat.toRat t : ℝ)) (xpos : Bool) (w : ℕ) :
    ∃ lo hi : ℝ, (atan2RatBracket t xpos w).1.toVal = some (lo : EReal) ∧
      (atan2RatBracket t xpos w).2.toVal = some (hi : EReal) ∧
      lo ≤ atan2Abs (AzRat.toRat t : ℝ) 1 xpos ∧ atan2Abs (AzRat.toRat t : ℝ) 1 xpos ≤ hi ∧
      hi - lo ≤ (1 / 2 : ℝ) ^ w := by
  set tv := ((AzRat.toRat t : ℚ) : ℝ) with htv
  have hnum : t.num ≠ 0 := fun h => ht0.ne' ((AzRat.toRat_eq_zero_iff t).mpr h)
  have habs : |tv| = tv := abs_of_pos ht0
  have hπ := pi_lt_four
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have h8 : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by
    rw [pow_add]
    norm_num
    ring
  have h72 : (1 / 2 : ℝ) ^ (w + 72) ≤ (1 / 2 : ℝ) ^ w / 1024 := by
    have h10 : (1 / 2 : ℝ) ^ (w + 10) = (1 / 2 : ℝ) ^ w / 1024 := by
      rw [pow_add]
      norm_num
      ring
    rw [← h10]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hw1 : (1 / 2 : ℝ) ^ w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold atan2RatBracket
  by_cases hc : t.num ≤ t.den
  · simp only [hc, ↓reduceIte]
    cases xpos with
    | true =>
      simp only [↓reduceIte, atan2Abs, div_one]
      obtain ⟨lo, hi, hlo, hhi, -, h1, h2, h3⟩ := atanRatAbsEncl_spec t hnum w
      rw [← htv, habs] at h1 h2
      exact ⟨lo, hi, hlo, hhi, h1, h2, h3⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, atan2Abs, div_one]
      obtain ⟨al, ah, hal, hah, hal0, h1, h2, h3⟩ := atanRatAbsEncl_spec t hnum (w + 8)
      rw [← htv, habs] at h1 h2
      have hat := arctan_lt_pi_div_two tv
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ := piShiftEncl_spec false false hal hah hal0 h1 h2
        (by linarith) h3 (V := w + 72) (by omega)
      simp only [Bool.false_eq_true, ↓reduceIte] at hl hh
      exact ⟨lo, hi, hlo, hhi, by linarith, by linarith, by linarith⟩
  · simp only [hc, ↓reduceIte]
    have ht1 : 1 < tv := by
      have := not_le.mp fun h => hc ((abs_toRat_le_one_iff t).mpr h)
      rwa [← htv, habs] at this
    have hsv : ((AzRat.toRat t⁻¹ : ℚ) : ℝ) = tv⁻¹ := by
      rw [AzRat.toRat_inv, Rat.cast_inv]
    have hs0 : 0 < tv⁻¹ := inv_pos.mpr ht0
    have hsnum : t⁻¹.num ≠ 0 := fun h => by
      have := (AzRat.toRat_eq_zero_iff t⁻¹).mpr h
      rw [hsv] at this
      exact hs0.ne' this
    obtain ⟨al, ah, hal, hah, hal0, h1, h2, h3⟩ := atanRatAbsEncl_spec t⁻¹ hsnum (w + 8)
    rw [hsv, abs_of_pos hs0] at h1 h2
    have hat := arctan_lt_pi_div_two tv⁻¹
    have hinv : arctan tv = π / 2 - arctan tv⁻¹ := by
      rw [← arctan_inv_of_pos hs0, inv_inv]
    cases xpos with
    | true =>
      simp only [Bool.not_true, ↓reduceIte, atan2Abs, div_one]
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ := piShiftEncl_spec true false hal hah hal0 h1 h2
        (by linarith) h3 (V := w + 72) (by omega)
      simp only [Bool.false_eq_true, ↓reduceIte] at hl hh
      exact ⟨lo, hi, hlo, hhi, by linarith, by linarith, by linarith⟩
    | false =>
      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, atan2Abs, div_one]
      obtain ⟨lo, hi, hlo, hhi, hl, hh, hwd⟩ := piShiftEncl_spec true true hal hah hal0 h1 h2
        (by linarith) h3 (V := w + 72) (by omega)
      simp only [↓reduceIte] at hl hh
      exact ⟨lo, hi, hlo, hhi, by linarith, by linarith, by linarith⟩

/-- The value of the quotient `|y|/|x|`. -/
theorem toRat_abs_div_abs (y x : AzRat) :
    ((AzRat.toRat (y.abs / x.abs) : ℚ) : ℝ) = |(AzRat.toRat y : ℝ)| / |(AzRat.toRat x : ℝ)| := by
  rw [AzRat.toRat_div, AzRat.toRat_abs, AzRat.toRat_abs]
  push_cast
  rfl

/-- `atan2 (|y|, x)` is irrational for nonzero rationals `y`, `x`. -/
theorem irrational_atan2Abs_of_rat {qy qx : ℚ} (hy0 : qy ≠ 0) (hx0 : qx ≠ 0) {xpos : Bool}
    (hxpos : xpos = true ↔ 0 < (qx : ℝ)) :
    Irrational (atan2Abs |(qy : ℝ)| |(qx : ℝ)| xpos) := by
  have hy0' : (qy : ℝ) ≠ 0 := by exact_mod_cast hy0
  have hx0' : (qx : ℝ) ≠ 0 := by exact_mod_cast hx0
  have hpos : 0 < |(qy : ℝ)| := abs_pos.mpr hy0'
  have h := arg_eq_atan2Abs (x := (qx : ℝ)) (y := |(qy : ℝ)|) hx0' hpos.ne' (neg := false)
    (by simp [abs_nonneg]) hxpos
  rw [abs_abs] at h
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at h
  rw [← h, ← Rat.cast_abs]
  exact irrational_arg_of_rat (abs_ne_zero.mpr hy0)

/-- `atan2RatApprox` as a pair of `Roundable`s bracketing `−atan2 (|y|, x)`. -/
theorem atan2RatApprox_spec (y x : AzRat) (hy : y.num ≠ 0) (hx : x.num ≠ 0) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (atan2RatApprox y x w).1 lv ∧ Rounds (atan2RatApprox y x w).2 hv ∧
      lv ≤ -atan2Abs |(AzRat.toRat y : ℝ)| |(AzRat.toRat x : ℝ)| x.sign ∧
      -atan2Abs |(AzRat.toRat y : ℝ)| |(AzRat.toRat x : ℝ)| x.sign ≤ hv ∧
      hv - lv ≤ (1 / 2 : ℝ) ^ w := by
  have hy0 := coe_toRat_ne_zero_of_num_ne_zero y hy
  have hx0 := coe_toRat_ne_zero_of_num_ne_zero x hx
  have ht := toRat_abs_div_abs y x
  have ht0 : 0 < ((AzRat.toRat (y.abs / x.abs) : ℚ) : ℝ) := by
    rw [ht]
    exact div_pos (abs_pos.mpr hy0) (abs_pos.mpr hx0)
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := atan2RatBracket_spec (y.abs / x.abs) ht0 x.sign w
  have hval : atan2Abs ((AzRat.toRat (y.abs / x.abs) : ℚ) : ℝ) 1 x.sign
      = atan2Abs |(AzRat.toRat y : ℝ)| |(AzRat.toRat x : ℝ)| x.sign := by
    unfold atan2Abs
    rw [ht, div_one]
  rw [hval] at h1 h2
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec true hlo hhi h1 h2
  simp only [↓reduceIte, neg_one_mul] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- The Ziv certificate for `−atan2 (|y|, x)`, `y`, `x` nonzero rationals. -/
theorem atan2RatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (y x : AzRat)
    (hy : y.num ≠ 0) (hx : x.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (atan2RatApprox y x (w₀ * 2 ^ f)).1
      (atan2RatApprox y x (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hy0 : AzRat.toRat y ≠ 0 := fun h =>
    coe_toRat_ne_zero_of_num_ne_zero y hy (by rw [h, Rat.cast_zero])
  have hx0 : AzRat.toRat x ≠ 0 := fun h =>
    coe_toRat_ne_zero_of_num_ne_zero x hx (by rw [h, Rat.cast_zero])
  exact exists_isSome_of_irrational_threshold p mode (atan2RatApprox y x)
    (irrational_atan2Abs_of_rat hy0 hx0 (toRat_sign_iff x hx)).neg (fun w => (1 / 2 : ℝ) ^ w)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) 0
    (fun w _ => atan2RatApprox_spec y x hy hx w) w₀ hw₀

end Azurite.AzFloat
