/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinRatWithPeriodBracket
import Azurite.AzFloat.Equiv.AsinRatBracket
import Azurite.AzFloat.Equiv.AsinWithPeriodBracket
import Azurite.AzRat.Equiv.Add

/-!
# Equivalence: the bracket of `arcsin (q) u / (2π)` for a rational `q`

`asinRatAbsEncl_spec` (width at most `2^(−w)`), `abs_toRat_eq_half_iff` (`|q| = 1/2` iff
`num = den` for `|q| + |q|`), `irrational_asinPeriod_toRat`, `asinRatPeriodApprox_spec`,
`asinRatPeriodApprox_isSome_exists` (the Ziv certificate).
-/

open Real

namespace Azurite.AzFloat

/-- **The enclosure of `arcsin |q|`**: nonnegative lower end, width at most `2^(−w)`. -/
theorem asinRatAbsEncl_spec (q : AzRat) (h0 : q.num ≠ 0) (h1 : |(AzRat.toRat q : ℝ)| < 1)
    (w : ℕ) :
    IsEncl0W (asinRatAbsEncl q w) (arcsin |(AzRat.toRat q : ℝ)|) ((1 / 2 : ℝ) ^ w) := by
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  set a := |(AzRat.toRat q : ℝ)| with ha
  have ha0 : 0 < a := abs_pos.mpr hq0
  have habs : ((AzRat.toRat q.abs : ℚ) : ℝ) = a := by
    rw [AzRat.toRat_abs, Rat.cast_abs]
  unfold asinRatAbsEncl
  dsimp only
  set e := ratExpBound q with he
  split_ifs with hc
  · obtain ⟨hs, hn⟩ := hc
    have : NeZero (w + 64) := ⟨by omega⟩
    have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
    set n := e.abs.toNat with hndef
    set t := (2 : ℝ) ^ e.toInt with ht
    have ht0 : 0 < t := by positivity
    have htn : t = (1 / 2 : ℝ) ^ n := by
      rw [ht, htoInt, hs]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    have hthalf : t ≤ 1 / 2 := two_zpow_le_half hs (by omega)
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
    obtain ⟨lv, hv, hlv, hhv, hl0, hl1, hh1, hd⟩ :=
      ofAzRatRound_unit q.abs habs ha0.le h1.le (w + 64) (by omega)
    have hsh : (((ofAzRatRound q.abs (w + 64) .Ceiling).1 <<< e) <<< e).toVal
        = some ((hv * tt : ℝ) : EReal) := by
      have h := toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal hhv e) e
      rw [h, htt, mul_assoc]
    obtain ⟨r, hr, hr1, hr2⟩ := addCeiling_abs hhv hsh (w + 64)
    obtain ⟨hb1, hb2⟩ := arcsin_bounds_of_small ha0 (hlt.le.trans hthalf)
    have haa : a * a ≤ tt := mul_le_mul hlt.le hlt.le ha0.le ht0.le
    have hcube : a ^ 3 ≤ a * tt := by
      have := mul_le_mul_of_nonneg_left haa ha0.le
      nlinarith
    have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 64) := by positivity
    have hu1 : (1 / 2 : ℝ) ^ (w + 64) ≤ 1 / 4 := by
      have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
        (by omega : 2 ≤ w + 64)
      norm_num at this
      linarith
    have hhv2 : hv ≤ 2 := by linarith
    have hhv0 : 0 ≤ hv := by linarith
    have m1 : a * tt ≤ hv * tt := mul_le_mul_of_nonneg_right hh1 htt0
    have m2 : hv * tt ≤ 2 * tt := mul_le_mul_of_nonneg_right hhv2 htt0
    have habs2 : |hv + hv * tt| ≤ 4 := by
      rw [abs_of_nonneg (by nlinarith [mul_nonneg hhv0 htt0])]
      linarith
    have m3 := mul_le_mul_of_nonneg_right habs2 hu0
    have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
    have h8 : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by
      rw [pow_add]
      norm_num
      ring
    have h64 : (1 / 2 : ℝ) ^ (w + 64) ≤ (1 / 2 : ℝ) ^ w / 1024 := by
      have h10 : (1 / 2 : ℝ) ^ (w + 10) = (1 / 2 : ℝ) ^ w / 1024 := by
        rw [pow_add]
        norm_num
        ring
      rw [← h10]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact ⟨lv, r, hlv, hr, hl0, hl1.trans hb1.le, by linarith, by linarith⟩
  · obtain ⟨lo, hi, hlo, hhi, hlo0, hl, hh, hwid⟩ := asinRatBracket_spec q h0 h1 w
    exact ⟨lo, hi, hlo, hhi, hlo0, hl, hh, hwid⟩

/-- `|q| = 1/2` iff the numerator and the denominator of `|q| + |q|` coincide. -/
theorem abs_toRat_eq_half_iff (q : AzRat) :
    |(AzRat.toRat q : ℝ)| = 1 / 2 ↔ (q.abs + q.abs).num = (q.abs + q.abs).den := by
  rw [← abs_toRat_eq_one_iff, AzRat.toRat_add, AzRat.toRat_abs]
  push_cast
  rw [show |(AzRat.toRat q : ℝ)| + |(AzRat.toRat q : ℝ)| = 2 * |(AzRat.toRat q : ℝ)| by ring,
    abs_mul, abs_abs, abs_two]
  constructor <;> intro h <;> linarith

/-- `arcsin (q) U / (2π)` is irrational for a rational `q` with `|q| < 1`, `|q| ∉ {0, 1/2}`. -/
theorem irrational_asinPeriod_toRat (q : AzRat) (h0 : q.num ≠ 0)
    (h1 : |(AzRat.toRat q : ℝ)| < 1) (hh : |(AzRat.toRat q : ℝ)| ≠ 1 / 2) {U : ℕ}
    (hU : U ≠ 0) : Irrational (arcsin (AzRat.toRat q : ℝ) * U / (2 * π)) := by
  have hq0 := coe_toRat_ne_zero_of_num_ne_zero q h0
  refine irrational_arcsin_rat_mul_div_two_pi
    (fun h => hq0 (by rw [h, Rat.cast_zero])) ?_ ?_ ?_ ?_ h1.le hU
  · intro h
    rw [h, abs_one] at h1
    exact lt_irrefl _ h1
  · intro h
    rw [h, abs_neg, abs_one] at h1
    exact lt_irrefl _ h1
  · intro h
    exact hh (by rw [h]; norm_num)
  · intro h
    exact hh (by rw [h, abs_neg]; norm_num)

/-- `asinRatPeriodApprox` as a pair of `Roundable`s bracketing `arcsin (q) u / (2π)`. -/
theorem asinRatPeriodApprox_spec (q : AzRat) (h0 : q.num ≠ 0) (h1 : |(AzRat.toRat q : ℝ)| < 1)
    (u : AzNat) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (asinRatPeriodApprox q u w).1 lv ∧
      Rounds (asinRatPeriodApprox q u w).2 hv ∧
      lv ≤ arcsin (AzRat.toRat q : ℝ) * u.toNat / (2 * π) ∧
      arcsin (AzRat.toRat q : ℝ) * u.toNat / (2 * π) ≤ hv ∧
      hv - lv ≤ u.toNat * (3 * (1 / 2 : ℝ) ^ w) := by
  have hθ : arcsin |(AzRat.toRat q : ℝ)| ≤ 2 := by
    have := arcsin_le_pi_div_two |(AzRat.toRat q : ℝ)|
    linarith [pi_lt_four]
  obtain ⟨lo, hi, hlo, hhi, hl, hh, hwid⟩ :=
    asinPeriodScale_spec (asinRatAbsEncl_spec q h0 h1 w) hθ u
  obtain ⟨lv, hv, hR1, hR2, hl', hh', he⟩ := enclApprox_spec (!q.sign) hlo hhi hl hh
  have hval : arcsin (AzRat.toRat q : ℝ) * u.toNat / (2 * π)
      = (if (!q.sign) = true then -1 else 1)
        * (arcsin |(AzRat.toRat q : ℝ)| * u.toNat / (2 * π)) := by
    rw [arcsin_toRat_eq q h0]
    ring
  rw [hval]
  exact ⟨lv, hv, hR1, hR2, hl', hh', by rw [he]; exact hwid⟩

/-- The Ziv certificate for `arcsin (q) u / (2π)`: `0 < |q| < 1`, `|q| ≠ 1/2`, `u ≠ 0`. -/
theorem asinRatPeriodApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (h1 : |(AzRat.toRat q : ℝ)| < 1) (hh : |(AzRat.toRat q : ℝ)| ≠ 1 / 2)
    {u : AzNat} (hu : u.toNat ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (asinRatPeriodApprox q u (w₀ * 2 ^ f)).1
      (asinRatPeriodApprox q u (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  refine exists_isSome_of_irrational_threshold p mode (asinRatPeriodApprox q u)
    (irrational_asinPeriod_toRat q h0 h1 hh hu)
    (fun w => u.toNat * (3 * (1 / 2 : ℝ) ^ w)) ?_ 0
    (fun w _ => asinRatPeriodApprox_spec q h0 h1 u w) w₀ hw₀
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).const_mul 3).const_mul (u.toNat : ℝ)
  simpa using h

end Azurite.AzFloat
