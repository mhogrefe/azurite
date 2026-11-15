/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanRatWithPeriodBracket
import Azurite.AzFloat.Equiv.AtanRatBracket
import Azurite.AzFloat.Equiv.AtanWithPeriodBracket

/-!
# Equivalence: the enclosure of `arctan |q|` for a rational `q`

`atanRatAbsEncl_spec` (width at most `2^(−w)`), `abs_toRat_eq_one_iff` (`|q| = 1` iff
`num = den`).
-/

open Real

namespace Azurite.AzFloat

/-- **The enclosure of `arctan |q|`**: nonnegative lower end, width at most `2^(−w)`. -/
theorem atanRatAbsEncl_spec (q : AzRat) (h0 : q.num ≠ 0) (w : ℕ) :
    IsEncl0W (atanRatAbsEncl q w) (arctan |(AzRat.toRat q : ℝ)|) ((1 / 2 : ℝ) ^ w) := by
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  set a := |(AzRat.toRat q : ℝ)| with ha
  have ha0 : 0 < a := abs_pos.mpr hq0
  have habs : ((AzRat.toRat q.abs : ℚ) : ℝ) = a := by
    rw [AzRat.toRat_abs, Rat.cast_abs]
  have hat0 : 0 ≤ arctan a := arctan_nonneg.mpr ha0.le
  unfold atanRatAbsEncl
  dsimp only
  set e := ratExpBound q with he
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  split_ifs with hc
  · obtain ⟨hs, hn⟩ := hc
    have : NeZero (w + 64) := ⟨by omega⟩
    set n := e.abs.toNat with hndef
    set t := (2 : ℝ) ^ e.toInt with ht
    have ht0 : 0 < t := by positivity
    have htn : t = (1 / 2 : ℝ) ^ n := by
      rw [ht, htoInt, hs]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    have ht1 : t ≤ 1 := by
      rw [htn]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    set tt := t * t with htt
    have htt0 : 0 ≤ tt := by positivity
    have htt1 : tt ≤ 1 := by
      rw [htt]
      nlinarith
    have httw : tt ≤ (1 / 2 : ℝ) ^ (w + 8) := by
      rw [htt, htn, ← pow_add]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hlt : a < t :=
      lt_of_lt_of_le (abs_toRat_lt_two_zpow q)
        (zpow_le_zpow_right₀ (by norm_num) (by show e.toInt - 1 ≤ e.toInt; omega))
    have ha1 : a ≤ 1 := hlt.le.trans ht1
    obtain ⟨lv, hv, hlv, hhv, hl0, hl1, hh1, hd⟩ :=
      ofAzRatRound_unit q.abs habs ha0.le ha1 (w + 64) (by omega)
    have hsh : (((ofAzRatRound q.abs (w + 64) .Floor).1 <<< e) <<< e).toVal
        = some ((lv * tt : ℝ) : EReal) := by
      have h := toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal hlv e) e
      rw [h, htt, mul_assoc]
    obtain ⟨r, hr, hr1, hr2⟩ := subFloor_abs hlv hsh (w + 64)
    obtain ⟨cv, hcv, hcv0, hcvle, hcveq⟩ := clampNonneg_spec hr
    have haa : a * a ≤ tt := mul_le_mul hlt.le hlt.le ha0.le ht0.le
    have hcube : a ^ 3 ≤ a * tt := by
      have := mul_le_mul_of_nonneg_left haa ha0.le
      nlinarith
    have m1 : lv * tt ≤ a * tt := mul_le_mul_of_nonneg_right hl1 htt0
    have m2 : a * tt ≤ tt := by
      have := mul_le_mul_of_nonneg_right ha1 htt0
      linarith
    have m3 : lv * tt ≤ lv := by
      have := mul_le_mul_of_nonneg_left htt1 hl0
      linarith
    have m4 : 0 ≤ lv * tt := mul_nonneg hl0 htt0
    have m5 : (a - lv) * tt ≤ a - lv := by
      have := mul_le_mul_of_nonneg_left htt1 (by linarith : 0 ≤ a - lv)
      linarith
    have hlow := sub_cube_div_three_le_arctan ha0.le
    have ha3 : 0 ≤ a ^ 3 := by positivity
    have hup := arctan_le_self ha0.le
    have hrc : r ≤ cv := by
      rcases le_or_gt 0 r with h | h
      · rw [hcveq h]
      · linarith
    have hsub : |lv - lv * tt| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 64) := by positivity
    have m6 := mul_le_mul_of_nonneg_right hsub hu0
    have h8 : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by
      rw [pow_add]
      norm_num
      ring
    have h64 : (1 / 2 : ℝ) ^ (w + 64) ≤ (1 / 2 : ℝ) ^ w / 2 ^ 64 := by
      rw [pow_add]
      have : (1 / 2 : ℝ) ^ 64 = 1 / 2 ^ 64 := by norm_num
      rw [this]
      ring_nf
      rfl
    have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
    have h64' : (1 / 2 : ℝ) ^ w / 2 ^ 64 ≤ (1 / 2 : ℝ) ^ w / 1024 :=
      div_le_div_of_nonneg_left hw0 (by norm_num) (by norm_num)
    refine ⟨cv, hv, hcv, hhv, hcv0, hcvle.trans (max_le ?_ hat0), by linarith, by linarith⟩
    linarith
  · obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := atanRatBracket_spec q h0 w
    obtain ⟨cv, hcv, hcv0, hcvle, hcveq⟩ := clampNonneg_spec hlo
    have hrc : lo ≤ cv := by
      rcases le_or_gt 0 lo with h | h
      · rw [hcveq h]
      · linarith
    exact ⟨cv, hi, hcv, hhi, hcv0, hcvle.trans (max_le h1 hat0), h2, by linarith⟩

/-- `|q| = 1` iff the numerator and the denominator coincide. -/
theorem abs_toRat_eq_one_iff (q : AzRat) : |(AzRat.toRat q : ℝ)| = 1 ↔ q.num = q.den := by
  have hden := den_pos_real q
  rw [abs_coe_toRat, div_eq_one_iff_eq hden.ne', Nat.cast_inj]
  exact ⟨fun h => AzNat.toNat_injective h, fun h => by rw [h]⟩

end Azurite.AzFloat
