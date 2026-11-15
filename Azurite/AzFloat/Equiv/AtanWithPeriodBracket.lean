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
  `|r| < 1/4` rational forces `r ∈ {0, ±1/8}`).
* `atanPeriodScale_spec`: the scaling by `u/(2π)`, width at most `U (2δ + 108·2^(−V))`.
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

/-! ### The enclosures -/

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

end Azurite.AzFloat
