/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section7
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# DLMF 5.7.5: `ψ(1 + z)` through `cot` and odd zeta values

Formalization of <https://dlmf.nist.gov/5.7> (part 2).

* 5.7.5, `ψ(1 + z) = 1/(2z) − (π/2) cot(πz) + 1/(z² − 1) + 1 − γ − ∑_{k≥1} (ζ(2k + 1) − 1) z^{2k}`,
  `|z| < 2`, `z ≠ 0, ±1` (`dlmf_5_7_5`, `dlmf_5_7_5_eq`). Proven directly: 5.7.6 at `1 + z` plus
  half of Mathlib's partial fractions of `π cot πz` (`cot_series_rep'`) leaves
  `∑_{n≥1} −z²/(n(n² − z²))`; the `n = 1` term is `1 + 1/(z² − 1)`, and for `n ≥ 2` the terms
  expand geometrically in `z²/n²`, summed over `ℕ × ℕ` (`hasSum_zeta_odd_series`).
-/

open Complex Filter Topology Set Finset
open scoped Real

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-- `ζ(2i + 3) − 1 = ∑_{m≥0} 1/(m + 2)^{2i+3}`. -/
theorem hasSum_zeta_sub_one (i : ℕ) :
    HasSum (fun m : ℕ => 1 / ((m : ℂ) + 2) ^ (2 * i + 3)) (riemannZeta (2 * i + 3) - 1) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_zeta_add_two (2 * i + 1))
  simp only [sum_range_one, Nat.cast_zero, zero_add, one_pow, div_one] at h
  convert h using 1
  · funext m
    push_cast
    ring_nf
  · push_cast
    ring_nf

theorem norm_natCast_add_two (m : ℕ) : ‖(m : ℂ) + 2‖ = (m : ℝ) + 2 := by
  rw [show (m : ℂ) + 2 = (((m : ℝ) + 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- `∑_{m≥0} z²/((m + 2)((m + 2)² − z²)) = ∑_{i≥0} (ζ(2i + 3) − 1) z^{2i+2}`, `|z| < 2`. -/
theorem hasSum_zeta_odd_series {z : ℂ} (hz : ‖z‖ < 2) {S : ℂ}
    (hS : HasSum (fun m : ℕ => z ^ 2 / (((m : ℂ) + 2) * (((m : ℂ) + 2) ^ 2 - z ^ 2))) S) :
    HasSum (fun i : ℕ => (riemannZeta (2 * i + 3) - 1) * z ^ (2 * i + 2)) S := by
  set f : ℕ × ℕ → ℂ := fun p => z ^ (2 * p.2 + 2) / ((p.1 : ℂ) + 2) ^ (2 * p.2 + 3) with hf
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hsum : Summable f := by
    have hg : Summable fun i : ℕ => ((‖z‖ / 2) ^ 2) ^ i :=
      summable_geometric_of_lt_one (by positivity) (by
        rw [div_pow, div_lt_one (by norm_num)]
        nlinarith)
    have hprod := (summable_inv_succ_sq.mul_of_nonneg hg (fun k => by positivity)
      (fun j => by positivity)).mul_left (‖z‖ ^ 2)
    refine Summable.of_norm_bounded hprod fun p => ?_
    obtain ⟨m, i⟩ := p
    simp only [hf, norm_div, norm_pow, norm_natCast_add_two]
    have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h2 : (2 : ℝ) ≤ (m : ℝ) + 2 := by linarith
    have h3 : 1 / ((m : ℝ) + 2) ^ 3 ≤ 1 / ((m : ℝ) + 1) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (m : ℝ), mul_nonneg h0 (sq_nonneg (m : ℝ))]
    have h4 : (‖z‖ / ((m : ℝ) + 2)) ^ 2 ≤ (‖z‖ / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left hz0 (by norm_num) h2) 2
    calc ‖z‖ ^ (2 * i + 2) / ((m : ℝ) + 2) ^ (2 * i + 3)
        = ‖z‖ ^ 2 * ((‖z‖ / ((m : ℝ) + 2)) ^ 2) ^ i * (1 / ((m : ℝ) + 2) ^ 3) := by
          rw [div_pow, div_pow, ← pow_mul, ← pow_mul]
          field_simp
          ring
      _ ≤ ‖z‖ ^ 2 * ((‖z‖ / 2) ^ 2) ^ i * (1 / ((m : ℝ) + 1) ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h4 i)
            (by positivity)) h3 (by positivity) (by positivity)
      _ = ‖z‖ ^ 2 * (1 / ((m : ℝ) + 1) ^ 2 * ((‖z‖ / 2) ^ 2) ^ i) := by ring
  -- inner sums over `i`: geometric in `z²/(m + 2)²`
  have hi : ∀ m : ℕ, HasSum (fun i => f (m, i))
      (z ^ 2 / (((m : ℂ) + 2) * (((m : ℂ) + 2) ^ 2 - z ^ 2))) := by
    intro m
    have hm2 : (m : ℂ) + 2 ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_natCast_add_two]; positivity
    have hq : ‖z ^ 2 / ((m : ℂ) + 2) ^ 2‖ < 1 := by
      rw [norm_div, norm_pow, norm_pow, norm_natCast_add_two, div_lt_one (by positivity)]
      have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    have hd : ((m : ℂ) + 2) ^ 2 - z ^ 2 ≠ 0 := by
      intro h
      have h' : ‖z‖ ^ 2 = ((m : ℝ) + 2) ^ 2 := by
        rw [← norm_pow, ← norm_natCast_add_two, ← norm_pow, sub_eq_zero.mp h]
      have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    have hg := (hasSum_geometric_of_norm_lt_one hq).mul_left (z ^ 2 / ((m : ℂ) + 2) ^ 3)
    convert hg using 1
    · funext i
      simp only [hf]
      rw [div_pow, ← pow_mul, ← pow_mul]
      field_simp
      ring
    · rw [show 1 - z ^ 2 / ((m : ℂ) + 2) ^ 2 = (((m : ℂ) + 2) ^ 2 - z ^ 2) / ((m : ℂ) + 2) ^ 2 by
          field_simp, inv_div]
      field_simp
  -- inner sums over `m`: odd zeta values
  have hk : ∀ i : ℕ, HasSum (fun m => f (m, i))
      ((riemannZeta (2 * i + 3) - 1) * z ^ (2 * i + 2)) := by
    intro i
    have := (hasSum_zeta_sub_one i).mul_left (z ^ (2 * i + 2))
    convert this using 1
    · funext m
      simp only [hf]
      ring
    · ring
  have hA := hsum.hasSum.prod_fiberwise hi
  have hB := ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hsum.hasSum).prod_fiberwise
    (fun i => by simpa using hk i)
  rw [hA.unique hS] at hB
  exact hB

/-- **DLMF 5.7.5**: `ψ(1 + z) = 1/(2z) − (π/2) cot(πz) + 1/(z² − 1) + 1 − γ
− ∑_{k=1}^∞ (ζ(2k + 1) − 1) z^{2k}`, `|z| < 2`, `z ≠ 0, ±1`, as the sum of the series
(indexed by `k = i + 1`). -/
theorem dlmf_5_7_5 {z : ℂ} (hz : ‖z‖ < 2) (h0 : z ≠ 0) (h1 : z ≠ 1) (hm1 : z ≠ -1) :
    HasSum (fun i : ℕ => (riemannZeta (2 * i + 3) - 1) * z ^ (2 * i + 2))
      (1 / (2 * z) - π / 2 * cot (π * z) + 1 / (z ^ 2 - 1) + 1 - γ - digamma (1 + z)) := by
  have hp : 1 + z ∉ gammaPoles := by
    rintro ⟨m, hm⟩
    have hzm : z = -((m : ℂ) + 1) := by linear_combination -hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact hm1 (by simpa using hzm)
    · rw [hzm, norm_neg, show (m : ℂ) + 1 = (((m : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at hz
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
      linarith
  have hZ : z ∈ integerComplement := by
    rintro ⟨n, hn⟩
    have hn' : |(n : ℝ)| < 2 := by rw [← hn, norm_intCast] at hz; exact hz
    have hn'' : |n| < 2 := by exact_mod_cast hn'
    have : n = -1 ∨ n = 0 ∨ n = 1 := by
      rcases abs_lt.mp hn'' with ⟨ha, hb⟩
      omega
    rcases this with rfl | rfl | rfl
    · exact hm1 (by rw [← hn]; simp)
    · exact h0 (by rw [← hn]; simp)
    · exact h1 (by rw [← hn]; simp)
  have hC := (summable_cotTerm hZ).hasSum
  rw [← cot_series_rep' hZ] at hC
  have hD := ((hasSum_nat_add_iff' 1).mpr ((dlmf_5_7_6 hp).add (hC.mul_left (1 / 2)))).neg
  have hne : ∀ m : ℕ, z ≠ (m : ℂ) + 2 ∧ z ≠ -((m : ℂ) + 2) := by
    intro m
    have h2 : (2 : ℝ) ≤ (m : ℝ) + 2 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    constructor
    · intro h; rw [h, norm_natCast_add_two] at hz; linarith
    · intro h; rw [h, norm_neg, norm_natCast_add_two] at hz; linarith
  have hE : HasSum (fun m : ℕ => z ^ 2 / (((m : ℂ) + 2) * (((m : ℂ) + 2) ^ 2 - z ^ 2)))
      (-(digamma (1 + z) + γ + 1 / 2 * (π * cot (π * z) - 1 / z) -
        ∑ k ∈ range 1, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 + z)) +
          1 / 2 * cotTerm z k))) := by
    convert hD using 1
    funext m
    obtain ⟨ha, hb⟩ := hne m
    have hm2 : (m : ℂ) + 2 ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_natCast_add_two]; positivity
    have hc : z - ((m : ℂ) + 2) ≠ 0 := sub_ne_zero.mpr ha
    have hd : z + ((m : ℂ) + 2) ≠ 0 := fun h => hb (by linear_combination h)
    have he : ((m : ℂ) + 2) ^ 2 - z ^ 2 ≠ 0 := by
      rw [show ((m : ℂ) + 2) ^ 2 - z ^ 2 = -((z - ((m : ℂ) + 2)) * (z + ((m : ℂ) + 2))) by ring]
      exact neg_ne_zero.mpr (mul_ne_zero hc hd)
    simp only [cotTerm]
    push_cast
    rw [show (m : ℂ) + 1 + 1 = (m : ℂ) + 2 by ring,
      show (m : ℂ) + 1 + (1 + z) = z + ((m : ℂ) + 2) by ring]
    field_simp
    ring
  have h := hasSum_zeta_odd_series hz hE
  convert h using 1
  simp only [sum_range_one, cotTerm, Nat.cast_zero, zero_add]
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hz2 : z + 1 ≠ 0 := fun h => hm1 (by linear_combination h)
  have hz3 : z ^ 2 - 1 ≠ 0 := by
    rw [show z ^ 2 - 1 = (z - 1) * (z + 1) by ring]; exact mul_ne_zero hz1 hz2
  have hz4 : 1 + z ≠ 0 := by rw [add_comm]; exact hz2
  field_simp
  ring

/-- **DLMF 5.7.5**, as an equation. -/
theorem dlmf_5_7_5_eq {z : ℂ} (hz : ‖z‖ < 2) (h0 : z ≠ 0) (h1 : z ≠ 1) (hm1 : z ≠ -1) :
    digamma (1 + z) = 1 / (2 * z) - π / 2 * cot (π * z) + 1 / (z ^ 2 - 1) + 1 - γ -
      ∑' i : ℕ, (riemannZeta (2 * i + 3) - 1) * z ^ (2 * i + 2) := by
  rw [(dlmf_5_7_5 hz h0 h1 hm1).tsum_eq]
  ring

end Azurite.DLMF
