/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinWithPeriodBracket
import Azurite.AzFloat.Equiv.AsinBracket
import Azurite.AzFloat.Equiv.AtanWithPeriodBracket
import Azurite.Transcendental.NivenSin

/-!
# Equivalence: the bracket of `arcsin (x) u / (2π)`

* `arcsin_one_half` (`arcsin (1/2) = π/6`); **`irrational_arcsin_rat_mul_div_two_pi`**:
  `arcsin (q) U / (2π)` is irrational for a rational `q ∈ [−1, 1]` other than `0`, `±1/2`,
  `±1`, and `U ≠ 0` (Niven's theorem for the sine: `q = sin (2πr)` with `|r| ≤ 1/4` rational
  forces `r ∈ {0, ±1/12, ±1/4}`); `irrational_asinPeriod_of_toVal`.
* `asinAbsEncl_spec` (width at most `2^(−w)`), `asinPeriodScale_spec` (the scaled enclosure,
  width at most `3U 2^(−w)`), `asinPeriodApprox_spec`, `asinPeriodApprox_isSome_exists` (the
  Ziv certificate).
-/

open Real

namespace Azurite.AzFloat

/-! ### Real analysis -/

/-- `arcsin (1/2) = π/6`. -/
theorem arcsin_one_half : arcsin (1 / 2) = π / 6 := by
  have hπ := pi_pos
  exact arcsin_eq_of_sin_eq sin_pi_div_six ⟨by linarith, by linarith⟩

/-- `arcsin (q) U / (2π)` is irrational for a rational `q ∈ [−1, 1]` other than `0`, `±1/2`,
`±1`. -/
theorem irrational_arcsin_rat_mul_div_two_pi {q : ℚ} (hq0 : q ≠ 0) (hq1 : (q : ℝ) ≠ 1)
    (hqm : (q : ℝ) ≠ -1) (hqh : (q : ℝ) ≠ 1 / 2) (hqmh : (q : ℝ) ≠ -(1 / 2))
    (hle : |(q : ℝ)| ≤ 1) {U : ℕ} (hU : U ≠ 0) : Irrational (arcsin q * U / (2 * π)) := by
  rintro ⟨v, hv⟩
  have hU0 : (0 : ℝ) < U := by exact_mod_cast Nat.pos_of_ne_zero hU
  have hpi := pi_pos
  obtain ⟨hl1, hl2⟩ := abs_le.mp hle
  set r : ℚ := v / U with hrdef
  have hr : 2 * π * (r : ℝ) = arcsin q := by
    rw [hrdef, Rat.cast_div, Rat.cast_natCast, hv]
    field_simp
  have hsin : sin (2 * π * (r : ℝ)) = q := by rw [hr, sin_arcsin hl1 hl2]
  have hq0' : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
  have hlt : |(r : ℝ)| ≤ 1 / 4 := by
    have h1 := arcsin_le_pi_div_two (q : ℝ)
    have h2 := neg_pi_div_two_le_arcsin (q : ℝ)
    rw [← hr] at h1 h2
    rw [abs_le]
    constructor <;> nlinarith
  have hden : r.den = 1 ∨ r.den = 2 ∨ r.den = 4 ∨ r.den = 12 := by
    by_contra h
    push Not at h
    exact (irrational_sin_two_pi_mul_rat h.1 h.2.1 h.2.2.1 h.2.2.2) ⟨q, hsin.symm⟩
  have hcast : (r : ℝ) = r.num / r.den := Rat.cast_def r
  have hcop := r.reduced
  rcases hden with h | h | h | h
  · exact hq0' (by rw [← hsin, sin_two_pi_mul_rat_of_den_dvd_two (by rw [h]; norm_num)])
  · exact hq0' (by rw [← hsin, sin_two_pi_mul_rat_of_den_dvd_two (by rw [h])])
  · rw [h] at hcast hcop
    have hn : |r.num| ≤ 1 := by
      have h1 : |(r.num : ℝ)| ≤ 1 := by
        rw [hcast, abs_div] at hlt
        norm_num at hlt
        linarith
      exact_mod_cast h1
    rw [abs_le] at hn
    generalize r.num = n at hcast hcop hn
    obtain ⟨h1, h2⟩ := hn
    interval_cases n
    · have hr' : (r : ℝ) = -(1 / 4) := by rw [hcast]; norm_num
      rw [hr', show 2 * π * -(1 / 4) = -(π / 2) by ring, sin_neg, sin_pi_div_two] at hsin
      exact hqm hsin.symm
    · exact absurd hcop (by decide)
    · have hr' : (r : ℝ) = 1 / 4 := by rw [hcast]; norm_num
      rw [hr', show 2 * π * (1 / 4) = π / 2 by ring, sin_pi_div_two] at hsin
      exact hq1 hsin.symm
  · rw [h] at hcast hcop
    have hn : |r.num| ≤ 3 := by
      have h1 : |(r.num : ℝ)| ≤ 3 := by
        rw [hcast, abs_div] at hlt
        norm_num at hlt
        linarith
      exact_mod_cast h1
    rw [abs_le] at hn
    generalize r.num = n at hcast hcop hn
    obtain ⟨h1, h2⟩ := hn
    interval_cases n
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · have hr' : (r : ℝ) = -(1 / 12) := by rw [hcast]; norm_num
      rw [hr', show 2 * π * -(1 / 12) = -(π / 6) by ring, sin_neg, sin_pi_div_six] at hsin
      exact hqmh hsin.symm
    · exact absurd hcop (by decide)
    · have hr' : (r : ℝ) = 1 / 12 := by rw [hcast]; norm_num
      rw [hr', show 2 * π * (1 / 12) = π / 6 by ring, sin_pi_div_six] at hsin
      exact hqh hsin.symm
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)

/-- `arcsin (x) U / (2π)` is irrational for a finite float `x` with `|x| < 1`,
`|x| ∉ {0, 1/2}`. -/
theorem irrational_asinPeriod_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) (hx1 : |xv| < 1) (hxh : |xv| ≠ 1 / 2) {U : ℕ} (hU : U ≠ 0) :
    Irrational (arcsin xv * U / (2 * π)) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hq, Rat.cast_zero])
  rw [hq] at hx1 hxh ⊢
  refine irrational_arcsin_rat_mul_div_two_pi hq0 ?_ ?_ ?_ ?_ hx1.le hU
  · intro h
    rw [h, abs_one] at hx1
    exact lt_irrefl _ hx1
  · intro h
    rw [h, abs_neg, abs_one] at hx1
    exact lt_irrefl _ hx1
  · intro h
    exact hxh (by rw [h]; norm_num)
  · intro h
    exact hxh (by rw [h, abs_neg]; norm_num)

/-! ### The enclosures -/

/-- **The enclosure of `arcsin |x|`**: nonnegative lower end, width at most `2^(−w)`. -/
theorem asinAbsEncl_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) (hx1 : |xv| < 1) {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt) (w : ℕ) :
    IsEncl0W (asinAbsEncl x ex w) (arcsin |xv|) ((1 / 2 : ℝ) ^ w) := by
  set a := |xv| with ha
  have ha0 : 0 < a := abs_pos.mpr hx0
  have habs : x.abs.toVal = some ((a : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  unfold asinAbsEncl
  split_ifs with hc
  · obtain ⟨hs, hn⟩ := hc
    dsimp only
    have : NeZero (w + 64) := ⟨by omega⟩
    have htoInt : ex.toInt = if ex.sign then (ex.abs.toNat : ℤ) else -(ex.abs.toNat : ℤ) := rfl
    set n := ex.abs.toNat with hndef
    set t := (2 : ℝ) ^ ex.toInt with ht
    have ht0 : 0 < t := by positivity
    have htn : t = (1 / 2 : ℝ) ^ n := by
      rw [ht, htoInt, hs]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    have hthalf : t ≤ 1 / 2 := two_zpow_le_half hs (by omega)
    set tt := t * t with htt
    have htt0 : 0 ≤ tt := by positivity
    have httw : tt ≤ (1 / 2 : ℝ) ^ (w + 8) := by
      rw [htt, htn, ← pow_add]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hsh : ((x.abs <<< ex) <<< ex).toVal = some ((a * tt : ℝ) : EReal) := by
      have h := toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal habs ex) ex
      rw [h, htt, mul_assoc]
    obtain ⟨r, hr, hr1, hr2⟩ := addCeiling_abs habs hsh (w + 64)
    obtain ⟨hb1, hb2⟩ := arcsin_bounds_of_small ha0 (hex.le.trans hthalf)
    have haa : a * a ≤ tt := mul_le_mul hex.le hex.le ha0.le ht0.le
    have hcube : a ^ 3 ≤ a * tt := by
      have := mul_le_mul_of_nonneg_left haa ha0.le
      nlinarith
    have hatt : a * tt ≤ tt := by
      have := mul_le_mul_of_nonneg_right hx1.le htt0
      linarith
    have hatt0 : 0 ≤ a * tt := mul_nonneg ha0.le htt0
    have habs2 : |a + a * tt| ≤ 2 := by
      rw [abs_of_nonneg (by linarith)]
      have : tt ≤ 1 := by
        rw [htt]
        nlinarith
      linarith
    have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 64) := by positivity
    have m1 := mul_le_mul_of_nonneg_right habs2 hu0
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
    exact ⟨a, r, habs, hr, ha0.le, hb1.le, by linarith, by linarith⟩
  · obtain ⟨lo, hi, hlo, hhi, hlo0, h1, h2, h3⟩ := asinBracket_spec hx hx0 hx1 ex w
    exact ⟨lo, hi, hlo, hhi, hlo0, h1, h2, h3⟩

/-- **The scaled enclosure**: `atanPeriodScale` of a nonnegative enclosure of an angle
`0 ≤ θ ≤ 2` of width `2^(−w)`, at `w + 64` bits, encloses `θ U / (2π)` with width at most
`3U 2^(−w)`. -/
theorem asinPeriodScale_spec {A : Encl} {θ : ℝ} {w : ℕ} (hA : IsEncl0W A θ ((1 / 2 : ℝ) ^ w))
    (hθ : θ ≤ 2) (u : AzNat) :
    ∃ lo hi : ℝ, (atanPeriodScale A u (w + 64)).1.toVal = some (lo : EReal) ∧
      (atanPeriodScale A u (w + 64)).2.toVal = some (hi : EReal) ∧
      lo ≤ θ * u.toNat / (2 * π) ∧ θ * u.toNat / (2 * π) ≤ hi ∧
      hi - lo ≤ u.toNat * (3 * (1 / 2 : ℝ) ^ w) := by
  have hw1 : (1 / 2 : ℝ) ^ w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ :=
    atanPeriodScale_spec hA hθ hw1 u (V := w + 64) (by omega)
  refine ⟨lo, hi, hlo, hhi, h1, h2, hwid.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))⟩
  have h64 : (1 / 2 : ℝ) ^ 64 ≤ 1 / 108 := by norm_num
  rw [pow_add]
  nlinarith

/-- `asinPeriodApprox neg` as a pair of `Roundable`s bracketing `± arcsin |x| u / (2π)`. -/
theorem asinPeriodApprox_spec (neg : Bool) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) (hx1 : |xv| < 1) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) (u : AzNat) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (asinPeriodApprox neg x ex u w).1 lv ∧
      Rounds (asinPeriodApprox neg x ex u w).2 hv ∧
      lv ≤ (if neg then -1 else 1) * (arcsin |xv| * u.toNat / (2 * π)) ∧
      (if neg then -1 else 1) * (arcsin |xv| * u.toNat / (2 * π)) ≤ hv ∧
      hv - lv ≤ u.toNat * (3 * (1 / 2 : ℝ) ^ w) := by
  have hθ : arcsin |xv| ≤ 2 := by
    have := arcsin_le_pi_div_two |xv|
    linarith [pi_lt_four]
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ :=
    asinPeriodScale_spec (asinAbsEncl_spec hx hx0 hx1 hex w) hθ u
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec neg hlo hhi h1 h2
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `arcsin (x) U / (2π) = ± arcsin |x| U / (2π)` with the sign bit of `x`. -/
theorem asinPeriod_eq_of_neg_iff {neg : Bool} {xv : ℝ} (hneg : neg = true ↔ xv < 0) (U : ℝ) :
    arcsin xv * U / (2 * π) = (if neg then -1 else 1) * (arcsin |xv| * U / (2 * π)) := by
  rw [arcsin_eq_of_neg_iff hneg]
  ring

/-- The Ziv certificate for `arcsin (x) u / (2π)`: `x` a finite float with `0 < |x| < 1`,
`|x| ≠ 1/2`, `u ≠ 0`. -/
theorem asinPeriodApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0)
    (hx1 : |xv| < 1) (hxh : |xv| ≠ 1 / 2) (hneg : neg = true ↔ xv < 0) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) {u : AzNat} (hu : u.toNat ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (asinPeriodApprox neg x ex u (w₀ * 2 ^ f)).1
      (asinPeriodApprox neg x ex u (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  refine exists_isSome_of_irrational_threshold p mode (asinPeriodApprox neg x ex u)
    (v := (if neg then -1 else 1) * (arcsin |xv| * u.toNat / (2 * π))) ?_
    (fun w => u.toNat * (3 * (1 / 2 : ℝ) ^ w)) ?_ 0
    (fun w _ => asinPeriodApprox_spec neg hx hx0 hx1 hex u w) w₀ hw₀
  · rw [← asinPeriod_eq_of_neg_iff hneg]
    exact irrational_asinPeriod_of_toVal hx hx0 hx1 hxh hu
  · have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 3).const_mul (u.toNat : ℝ)
    simpa using h

end Azurite.AzFloat
