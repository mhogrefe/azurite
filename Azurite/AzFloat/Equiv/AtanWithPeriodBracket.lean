/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanWithPeriodBracket
import Azurite.AzFloat.Equiv.AtanBracket
import Azurite.Transcendental.NivenTan

/-!
# Equivalence: the bracket of `arctan (x) u / (2π)`

* `irrational_arctan_rat_mul_div_two_pi`: `arctan (q) U / (2π)` is irrational for a rational
  `q ∉ {0, 1, −1}` and `U ≠ 0` (Niven's theorem for the tangent: `q = tan (2πr)` with
  `|r| < 1/4` rational forces `r ∈ {0, ±1/8}`), `irrational_atanPeriod_of_toVal`.
* `atanAbsEncl_spec` (width at most `2^(−w)`), `atanPeriodScale_spec` (width at most
  `U (2δ + 108·2^(−V))`), `atanPeriodApprox_spec`, `atanPeriodApprox_isSome_exists` (the Ziv
  certificate).
-/

open Real

namespace Azurite.AzFloat

/-! ### Irrationality -/

/-- `arctan (q) U / (2π)` is irrational for a rational `q` other than `0`, `1`, `−1`. -/
theorem irrational_arctan_rat_mul_div_two_pi {q : ℚ} (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (hqm : q ≠ -1) {U : ℕ} (hU : U ≠ 0) : Irrational (arctan q * U / (2 * π)) := by
  rintro ⟨v, hv⟩
  have hU0 : (0 : ℝ) < U := by exact_mod_cast Nat.pos_of_ne_zero hU
  have hpi := pi_pos
  set r : ℚ := v / U with hrdef
  have hr : 2 * π * (r : ℝ) = arctan q := by
    rw [hrdef, Rat.cast_div, Rat.cast_natCast, hv]
    field_simp
  have htan : tan (2 * π * (r : ℝ)) = q := by rw [hr, tan_arctan]
  have hlt : |(r : ℝ)| < 1 / 4 := by
    have h1 := arctan_lt_pi_div_two (q : ℝ)
    have h2 := neg_pi_div_two_lt_arctan (q : ℝ)
    rw [← hr] at h1 h2
    rw [abs_lt]
    constructor <;> nlinarith
  have hden : r.den = 1 ∨ r.den = 2 ∨ r.den = 4 ∨ r.den = 8 := by
    by_contra h
    push Not at h
    exact (irrational_tan_two_pi_mul_rat h.1 h.2.1 h.2.2.1 h.2.2.2) ⟨q, htan.symm⟩
  have hdpos : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hd8 : (r.den : ℝ) ≤ 8 := by
    rcases hden with h | h | h | h <;> rw [h] <;> norm_num
  have hcast : (r : ℝ) = r.num / r.den := Rat.cast_def r
  have hnum : |(r.num : ℝ)| < r.den / 4 := by
    have habs : |(r : ℝ)| = |(r.num : ℝ)| / r.den := by rw [hcast, abs_div, abs_of_pos hdpos]
    rw [habs, div_lt_iff₀ hdpos] at hlt
    linarith
  have hnum2 : |r.num| < 2 := by
    have : |(r.num : ℝ)| < 2 := by linarith
    exact_mod_cast this
  have hcases : r.num = 0 ∨ r.num = 1 ∨ r.num = -1 := by
    rw [abs_lt] at hnum2
    omega
  have hd : r.num ≠ 0 → r.den = 8 := fun hn => by
    have h1 : (1 : ℝ) ≤ |(r.num : ℝ)| := by
      have : (1 : ℤ) ≤ |r.num| := Int.one_le_abs hn
      exact_mod_cast this
    rcases hden with h' | h' | h' | h'
    · rw [h'] at hnum; norm_num at hnum; linarith
    · rw [h'] at hnum; norm_num at hnum; linarith
    · rw [h'] at hnum; norm_num at hnum; linarith
    · exact h'
  rcases hcases with h | h | h
  · have hr0 : r = 0 := Rat.zero_of_num_zero h
    rw [hr0, Rat.cast_zero, mul_zero] at hr
    exact hq0 (by exact_mod_cast arctan_eq_zero_iff.mp hr.symm)
  · have hr8 : (r : ℝ) = 1 / 8 := by
      rw [hcast, h, hd (by rw [h]; norm_num)]
      norm_num
    rw [hr8, show 2 * π * (1 / 8) = π / 4 by ring, tan_pi_div_four] at htan
    exact hq1 (by exact_mod_cast htan.symm)
  · have hr8 : (r : ℝ) = -(1 / 8) := by
      rw [hcast, h, hd (by rw [h]; norm_num)]
      norm_num
    rw [hr8, show 2 * π * -(1 / 8) = -(π / 4) by ring, tan_neg, tan_pi_div_four] at htan
    exact hqm (by exact_mod_cast htan.symm)

/-- `arctan (x) U / (2π)` is irrational for a finite float `x ∉ {0, ±1}` and `U ≠ 0`. -/
theorem irrational_atanPeriod_of_toVal {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) (hx1 : |xv| ≠ 1) {U : ℕ} (hU : U ≠ 0) :
    Irrational (arctan xv * U / (2 * π)) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  rw [hq]
  refine irrational_arctan_rat_mul_div_two_pi ?_ ?_ ?_ hU
  · rintro rfl
    exact hx0 (by rw [hq, Rat.cast_zero])
  · rintro rfl
    exact hx1 (by rw [hq, Rat.cast_one, abs_one])
  · rintro rfl
    exact hx1 (by rw [hq]; norm_num)

/-! ### The enclosures -/

/-- **The enclosure of `arctan |x|`**: nonnegative lower end, width at most `2^(−w)`. -/
theorem atanAbsEncl_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) {ex : AzInt} (hex1 : (2 : ℝ) ^ (ex.toInt - 1) ≤ |xv|)
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) (w : ℕ) :
    IsEncl0W (atanAbsEncl x ex w) (arctan |xv|) ((1 / 2 : ℝ) ^ w) := by
  have htoInt : ex.toInt = if ex.sign then (ex.abs.toNat : ℤ) else -(ex.abs.toNat : ℤ) := rfl
  set a := |xv| with ha
  have ha0 : 0 < a := abs_pos.mpr hx0
  have habs : x.abs.toVal = some ((a : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hat0 : 0 ≤ arctan a := arctan_nonneg.mpr ha0.le
  unfold atanAbsEncl
  split_ifs with hc
  · -- tiny argument
    obtain ⟨hs, hn⟩ := hc
    dsimp only
    have : NeZero (w + 64) := ⟨by omega⟩
    set n := ex.abs.toNat with hndef
    set t := (2 : ℝ) ^ ex.toInt with ht
    have ht0 : 0 < t := by positivity
    have htn : t = (1 / 2 : ℝ) ^ n := by
      rw [ht, htoInt, hs]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    have ht1 : t ≤ 1 := by
      rw [htn]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have htt : t * t ≤ (1 / 2 : ℝ) ^ (w + 8) := by
      rw [htn, ← pow_add]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hsh : ((x.abs <<< ex) <<< ex).toVal = some ((a * t * t : ℝ) : EReal) :=
      toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal habs ex) ex
    obtain ⟨r, hr, hr1, hr2⟩ := subFloor_abs habs hsh (w + 64)
    obtain ⟨cv, hcv, hcv0, hcvle, hcveq⟩ := clampNonneg_spec hr
    have ha1 : a ≤ 1 := hex.le.trans ht1
    have haa : a * a ≤ t * t := mul_le_mul hex.le hex.le ha0.le ht0.le
    have hcube : a ^ 3 ≤ a * t * t := by
      have := mul_le_mul_of_nonneg_left haa ha0.le
      nlinarith
    have hatt : a * t * t ≤ t * t := by
      have := mul_le_mul_of_nonneg_right ha1 (mul_nonneg ht0.le ht0.le)
      nlinarith
    have hatt0 : 0 ≤ a * t * t := by positivity
    have hlow := sub_cube_div_three_le_arctan ha0.le
    have ha3 : 0 ≤ a ^ 3 := by positivity
    have hup := arctan_le_self ha0.le
    have hrc : r ≤ cv := by
      rcases le_or_gt 0 r with h | h
      · rw [hcveq h]
      · linarith
    have hsub : |a - a * t * t| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith
    have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 64) := by positivity
    have m1 := mul_le_mul_of_nonneg_right hsub hu0
    have h8 : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by
      rw [pow_add]
      norm_num
      ring
    have h64 : (1 / 2 : ℝ) ^ (w + 64) ≤ (1 / 2 : ℝ) ^ w / 256 := by
      rw [← h8]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
    exact ⟨cv, a, hcv, habs, hcv0, hcvle.trans (max_le (by linarith) hat0), hup, by linarith⟩
  · dsimp only
    obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := atanBracket_spec hx hx0 hex1 hex w
    obtain ⟨cv, hcv, hcv0, hcvle, hcveq⟩ := clampNonneg_spec hlo
    have hrc : lo ≤ cv := by
      rcases le_or_gt 0 lo with h | h
      · rw [hcveq h]
      · linarith
    exact ⟨cv, hi, hcv, hhi, hcv0, hcvle.trans (max_le h1 hat0), h2, by linarith⟩

/-- **The scaling by `u/(2π)`** of a nonnegative enclosure of `0 ≤ θ ≤ 2` of width `δ ≤ 1`:
an enclosure of `θ U / (2π)` of width at most `U (2δ + 108·2^(−V))`. -/
theorem atanPeriodScale_spec {A : Encl} {θ δ : ℝ} (hA : IsEncl0W A θ δ) (hθ : θ ≤ 2)
    (hδ : δ ≤ 1) (u : AzNat) {V : ℕ} (hV : 64 ≤ V) :
    ∃ lo hi : ℝ, (atanPeriodScale A u V).1.toVal = some (lo : EReal) ∧
      (atanPeriodScale A u V).2.toVal = some (hi : EReal) ∧
      lo ≤ θ * u.toNat / (2 * π) ∧ θ * u.toNat / (2 * π) ≤ hi ∧
      hi - lo ≤ u.toNat * (2 * δ + 108 * (1 / 2 : ℝ) ^ V) := by
  unfold atanPeriodScale
  dsimp only
  have : NeZero V := ⟨by omega⟩
  set e := (1 / 2 : ℝ) ^ V with he
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 / 2 ^ 64 := by
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hV
    rw [← he] at this
    norm_num at this ⊢
    linarith
  have hπ := pi_gt_three
  have hπ4 := pi_lt_four
  have hθ0 : 0 ≤ θ := hA.nonneg
  have hδ0 : 0 ≤ δ := by
    obtain ⟨l, h, -, -, -, h1, h2, h3⟩ := hA
    linarith
  obtain ⟨pl, ph, hpl, hph, -, hpl1, hph1, hpw⟩ := piBracket_spec_width hV
  rw [← he] at hpw
  have hP : IsEnclW (piBracket V) π (8 * e) := ⟨pl, ph, hpl, hph, hpl1.le, hph1, hpw⟩
  have hd := IsEncl0W.div_pos hA hP hθ (by linarith) hδ (by linarith) hV
  rw [← he] at hd
  obtain ⟨dl, dh, hdl, hdh, hdl0, hdl1, hdh1, hdw⟩ := hd
  set U := (u.toNat : ℝ) with hUdef
  have hU0 : 0 ≤ U := by positivity
  have huf : (ofAzNat u <<< AzInt.ofInt (-1)).toVal = some ((U / 2 : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal (toVal_ofAzNat u) (AzInt.ofInt (-1))
    rw [h, AzInt.toInt_ofInt, zpow_neg_one, div_eq_mul_inv]
  set Uh := U / 2 with hUh
  have hUh0 : 0 ≤ Uh := by positivity
  obtain ⟨lo, hlo, hlo1, hlo2⟩ := mulFloor_abs hdl huf V
  obtain ⟨hi, hhi, hhi1, hhi2⟩ := mulCeiling_abs hdh huf V
  rw [← he] at hlo2 hhi2
  have hval : θ * U / (2 * π) = θ / π * Uh := by
    rw [hUh]
    field_simp
  have hθπ : θ / π ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hdh6 : dh ≤ 6 := by linarith
  have hdh0 : 0 ≤ dh := hdl0.trans (hdl1.trans hdh1)
  have m1 := mul_le_mul_of_nonneg_right hdl1 hUh0
  have m2 := mul_le_mul_of_nonneg_right hdh1 hUh0
  have m3 := mul_le_mul_of_nonneg_right hdw hUh0
  have m4 := mul_le_mul_of_nonneg_right hdh6 hUh0
  have m5 := mul_le_mul_of_nonneg_right (hdl1.trans (hdh1.trans hdh6)) hUh0
  have hUe0 : 0 ≤ Uh * e := mul_nonneg hUh0 he0
  rw [abs_of_nonneg (mul_nonneg hdl0 hUh0)] at hlo2
  rw [abs_of_nonneg (mul_nonneg hdh0 hUh0)] at hhi2
  have m6 := mul_le_mul_of_nonneg_right m4 he0
  have m7 := mul_le_mul_of_nonneg_right m5 he0
  refine ⟨lo, hi, hlo, hhi, by rw [hval]; linarith, by rw [hval]; linarith, ?_⟩
  have hfin : U * (2 * δ + 108 * e) = Uh * (4 * δ + 216 * e) := by
    rw [hUh]
    ring
  rw [hfin]
  nlinarith

/-- `atanPeriodApprox neg` as a pair of `Roundable`s bracketing `± arctan |x| u / (2π)`. -/
theorem atanPeriodApprox_spec (neg : Bool) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) {ex : AzInt}
    (hex1 : (2 : ℝ) ^ (ex.toInt - 1) ≤ |xv|) (hex : |xv| < (2 : ℝ) ^ ex.toInt) (u : AzNat)
    (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (atanPeriodApprox neg x ex u w).1 lv ∧
      Rounds (atanPeriodApprox neg x ex u w).2 hv ∧
      lv ≤ (if neg then -1 else 1) * (arctan |xv| * u.toNat / (2 * π)) ∧
      (if neg then -1 else 1) * (arctan |xv| * u.toNat / (2 * π)) ≤ hv ∧
      hv - lv ≤ u.toNat * (3 * (1 / 2 : ℝ) ^ w) := by
  have hA := atanAbsEncl_spec hx hx0 hex1 hex w
  have hw1 : (1 / 2 : ℝ) ^ w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hθ : arctan |xv| ≤ 2 := by
    have := arctan_lt_pi_div_two |xv|
    linarith [pi_lt_four]
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ :=
    atanPeriodScale_spec hA hθ hw1 u (V := w + 64) (by omega)
  have hU0 : (0 : ℝ) ≤ u.toNat := by positivity
  have hwid' : hi - lo ≤ u.toNat * (3 * (1 / 2 : ℝ) ^ w) := by
    refine hwid.trans (mul_le_mul_of_nonneg_left ?_ hU0)
    have h64 : (1 / 2 : ℝ) ^ 64 ≤ 1 / 108 := by norm_num
    rw [pow_add]
    nlinarith
  simp only [atanPeriodApprox]
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR1
    have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR2
    exact ⟨lo, hi, hR1, hR2, h1, h2, hwid'⟩
  | true =>
    simp only [↓reduceIte, neg_one_mul]
    have hnlo : (-(atanPeriodScale (atanAbsEncl x ex w) u (w + 64)).2).toVal
        = some ((-hi : ℝ) : EReal) := by
      rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
    have hnhi : (-(atanPeriodScale (atanAbsEncl x ex w) u (w + 64)).1).toVal
        = some ((-lo : ℝ) : EReal) := by
      rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
    have hR3 := rounds_setPrecRound (isFinite_of_toVal_coe hnlo)
    rw [fval_of_toVal_coe hnlo] at hR3
    have hR4 := rounds_setPrecRound (isFinite_of_toVal_coe hnhi)
    rw [fval_of_toVal_coe hnhi] at hR4
    exact ⟨-hi, -lo, hR3, hR4, by linarith, by linarith, by linarith⟩

/-- `arctan (x) U / (2π) = ± arctan |x| U / (2π)` with the sign bit of `x`. -/
theorem atanPeriod_eq_of_neg_iff {neg : Bool} {xv : ℝ} (hneg : neg = true ↔ xv < 0) (U : ℝ) :
    arctan xv * U / (2 * π) = (if neg then -1 else 1) * (arctan |xv| * U / (2 * π)) := by
  rw [arctan_eq_of_neg_iff hneg]
  ring

/-- The Ziv certificate for `arctan (x) u / (2π)`, `x ∉ {0, ±1}` a finite float, `u ≠ 0`. -/
theorem atanPeriodApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0)
    (hx1 : |xv| ≠ 1) (hneg : neg = true ↔ xv < 0) {ex : AzInt}
    (hex1 : (2 : ℝ) ^ (ex.toInt - 1) ≤ |xv|) (hex : |xv| < (2 : ℝ) ^ ex.toInt) {u : AzNat}
    (hu : u.toNat ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (atanPeriodApprox neg x ex u (w₀ * 2 ^ f)).1
      (atanPeriodApprox neg x ex u (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  refine exists_isSome_of_irrational_threshold p mode (atanPeriodApprox neg x ex u)
    (v := (if neg then -1 else 1) * (arctan |xv| * u.toNat / (2 * π))) ?_
    (fun w => u.toNat * (3 * (1 / 2 : ℝ) ^ w)) ?_ 0
    (fun w _ => atanPeriodApprox_spec neg hx hx0 hex1 hex u w) w₀ hw₀
  · rw [← atanPeriod_eq_of_neg_iff hneg]
    exact irrational_atanPeriod_of_toVal hx hx0 hx1 hu
  · have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 3).const_mul (u.toNat : ℝ)
    simpa using h

end Azurite.AzFloat
