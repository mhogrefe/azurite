/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11BoydSqrt

/-!
# DLMF 5.11.11

Formalization of <https://dlmf.nist.gov/5.11.E11> (Boyd 1994): for `|ph z| ≤ ½π` and `K ≥ 1`,
`|R_K(z)| ≤ (1 + ζ(K)) Γ(K) / (2 (2π)^{K+1} |z|^K) · (1 + min(sec(ph z), 2K^{1/2}))`,
`1 + ζ(1)` read as `4`.

* `dlmf_5_11_11_sec` (`Section11BoydBound.lean`): the `sec` branch, all `K ≥ 1`, `|ph z| < ½π`.
* `dlmf_5_11_11_sqrt`: the `2K^{1/2}` branch for `K ≥ 3`, `|ph z| < ½π`; first for `0 ≤ ph z`
  (`boyd_sqrt_upper`, path rotated to `ph s = arctan K^{−1/2}`), then by `R_K(z̄) = conj R_K(z)`
  (`stirlingR_conj`).
* `dlmf_5_11_11_closed`: the `2K^{1/2}` branch on the closed sector `|ph z| ≤ ½π` (continuity
  up to the imaginary axis, where `sec(ph z)` is infinite).
* `dlmf_5_11_11`: the `min` form for `K ≥ 3`, `|ph z| < ½π`.

For `K = 1, 2` only the `sec` branch is proved: Nemes's proof of the `2K^{1/2}` branch for `K = 2`
uses a numerically computed integral, and for `K = 1` it is unproved in the literature.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Nat ComplexConjugate

namespace Azurite.DLMF

/-! ### The angle `arctan K^{−1/2}` -/

theorem arctan_inv_sqrt_facts {K : ℝ} (hK : 1 ≤ K) :
    0 < Real.arctan (1 / Real.sqrt K) ∧ Real.arctan (1 / Real.sqrt K) < π / 2 ∧
      Real.sin (Real.arctan (1 / Real.sqrt K)) ≤ Real.cos (Real.arctan (1 / Real.sqrt K)) ∧
      (Real.sin (Real.arctan (1 / Real.sqrt K)))⁻¹ = Real.sqrt K * Real.sqrt (1 + 1 / K) ∧
      Real.cos (Real.arctan (1 / Real.sqrt K)) = (Real.sqrt (1 + 1 / K))⁻¹ := by
  have hK0 : 0 < K := by linarith
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hs1 : 1 ≤ Real.sqrt K := by rw [Real.one_le_sqrt]; exact hK
  have hx2 : (1 / Real.sqrt K) ^ 2 = 1 / K := by
    rw [div_pow, Real.sq_sqrt hK0.le, one_pow]
  have ha : 0 < Real.sqrt (1 + 1 / K) := Real.sqrt_pos.mpr (by positivity)
  have hsin : Real.sin (Real.arctan (1 / Real.sqrt K)) =
      (Real.sqrt K * Real.sqrt (1 + 1 / K))⁻¹ := by
    rw [Real.sin_arctan, hx2, mul_inv, one_div, div_eq_mul_inv]
  have hcos : Real.cos (Real.arctan (1 / Real.sqrt K)) = (Real.sqrt (1 + 1 / K))⁻¹ := by
    rw [Real.cos_arctan, hx2, one_div]
  refine ⟨Real.arctan_pos.mpr (by positivity), Real.arctan_lt_pi_div_two _, ?_, ?_, hcos⟩
  · rw [hsin, hcos]
    gcongr
    nlinarith
  · rw [hsin, inv_inv]

/-! ### The upper quadrant -/

/-- The `2K^{1/2}` branch for `0 ≤ ph z < ½π`, `K = j + 2 ≥ 3` (Nemes, Theorem 1.3). -/
theorem boyd_sqrt_upper {j : ℕ} (hj : 1 ≤ j) {z : ℂ} (hz : 0 < z.re) (him : 0 ≤ z.im) :
    ‖stirlingR (j + 2) z‖ ≤ (1 + (riemannZeta (j + 2)).re) * (j + 1)! /
      (2 * (2 * π) ^ (j + 3) * ‖z‖ ^ (j + 2)) * (1 + 2 * Real.sqrt ((j : ℝ) + 2)) := by
  have hz0 := ne_zero_of_pos_re hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hπ := Real.pi_pos
  set K : ℝ := (j : ℝ) + 2 with hKdef
  have hK : 1 ≤ K := by rw [hKdef]; linarith [j.cast_nonneg (α := ℝ)]
  obtain ⟨hϑ0, hϑ2, hsc, hsin, hcos⟩ := arctan_inv_sqrt_facts hK
  set ϑ := Real.arctan (1 / Real.sqrt K)
  set ζ := (riemannZeta (j + 2)).re with hζ
  have hζ0 : 0 ≤ ζ := zeta_re_nonneg j
  set a := Real.sqrt (1 + 1 / K) with ha
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by positivity)
  set F : ℝ := (j + 1)! / (2 * π) ^ (j + 2) with hF
  have hF0 : 0 < F := by positivity
  -- the first integral, rotated
  set P := ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (j + 1) * boydA t / (1 - t * I / z) with hPdef
  have hProt : P = cexp (ϑ * I) * ∫ r in Ioi (0 : ℝ), boydF (j + 1) z (r * cexp (ϑ * I)) :=
    boydF_rotate hz him hϑ0.le hϑ2 le_add_self
  have hP : ‖P‖ ≤ Real.sqrt K * (1 + ζ) * F := by
    rw [hProt, norm_mul, norm_exp_ofReal_mul_I, one_mul]
    refine (norm_integral_boydF_rot_le hz him hϑ0 hϑ2 hsc j).trans ?_
    rw [hsin, hcos, inv_pow, inv_inv]
    have hkey := zeta_mul_le hj
    rw [← hKdef, ← ha] at hkey
    have hsK := Real.sqrt_nonneg K
    calc Real.sqrt K * a * a ^ (j + 2) * ((j + 1)! * ζ / (2 * π) ^ (j + 2))
        = Real.sqrt K * (ζ * a ^ (j + 3)) * F := by rw [hF]; ring
      _ ≤ Real.sqrt K * (1 + ζ) * F := by gcongr
  -- the second integral
  set Q := ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (j + 1) * boydB t / (1 + t * I / z) with hQdef
  have hQ : ‖Q‖ ≤ (1 + ζ) * F / 2 := by
    have h1 := norm_integral_le_boydMom (F := fun t : ℝ =>
      (t : ℂ) ^ (j + 1) * boydB t / (1 + t * I / z)) (j + 1) (C := 1)
      fun t ht => norm_boydB_div_le hz ht (j + 1) (Or.inr ⟨him, le_rfl⟩)
    refine h1.trans ?_
    rw [one_mul]
    refine (boydMom_le j).trans (le_of_eq ?_)
    rw [hF, hζ]
    field_simp
  -- assemble
  rw [show stirlingR (j + 2) z = boydRem (j + 1) z from stirlingR_eq_boydRem hz (j + 1),
    boydRem, ← hPdef, ← hQdef, norm_mul]
  have hpre : ‖1 / (2 * π * z ^ (j + 1 + 1))‖ = 1 / (2 * π * ‖z‖ ^ (j + 2)) := by
    rw [norm_div, norm_one, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg hπ.le]
  rw [hpre]
  have hsum : ‖I ^ (j + 1) * P + (-I) ^ (j + 1) * Q‖ ≤ ‖P‖ + ‖Q‖ := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_I, one_pow, one_mul, one_mul]
  calc 1 / (2 * π * ‖z‖ ^ (j + 2)) * ‖I ^ (j + 1) * P + (-I) ^ (j + 1) * Q‖
      ≤ 1 / (2 * π * ‖z‖ ^ (j + 2)) * (Real.sqrt K * (1 + ζ) * F + (1 + ζ) * F / 2) := by
        gcongr
        exact hsum.trans (add_le_add hP hQ)
    _ = _ := by
        rw [hF, hKdef]
        field_simp
        ring

/-! ### Conjugation -/

theorem stirlingR_conj (K : ℕ) {z : ℂ} (hz : z.arg ≠ π) :
    stirlingR K (conj z) = conj (stirlingR K z) := by
  simp [stirlingR, scaledGamma_conj hz, map_sum]

/-- **DLMF 5.11.11** (the `2K^{1/2}` branch, `K ≥ 3`, `|ph z| < ½π`). -/
theorem dlmf_5_11_11_sqrt {K : ℕ} (hK : 3 ≤ K) {z : ℂ} (hz : 0 < z.re) :
    ‖stirlingR K z‖ ≤ (1 + boydZeta K) * Real.Gamma K / (2 * (2 * π) ^ (K + 1) * ‖z‖ ^ K) *
      (1 + 2 * Real.sqrt K) := by
  obtain ⟨j, rfl⟩ : ∃ j, K = j + 2 := ⟨K - 2, by omega⟩
  have hj : 1 ≤ j := by omega
  have hzeta : boydZeta (j + 2) = (riemannZeta (j + 2)).re := by
    simp [boydZeta]
  have hGamma : Real.Gamma ((j + 2 : ℕ) : ℝ) = (j + 1)! := by
    rw [show ((j + 2 : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  rw [hzeta, hGamma, show (j + 2 + 1) = j + 3 by ring]
  push_cast
  rcases le_total 0 z.im with him | him
  · exact boyd_sqrt_upper hj hz him
  · have hz' : 0 < (conj z).re := by rwa [conj_re]
    have him' : 0 ≤ (conj z).im := by rw [conj_im]; linarith
    have harg : z.arg ≠ π := by
      intro h
      have := (arg_eq_pi_iff.mp h).1
      linarith
    have h := boyd_sqrt_upper hj hz' him'
    rwa [stirlingR_conj _ harg, RCLike.norm_conj, RCLike.norm_conj] at h

theorem continuousAt_stirlingR (K : ℕ) {z : ℂ} (hz : z.re = 0) (hz0 : z ≠ 0) :
    ContinuousAt (stirlingR K) z := by
  have him : z.im ≠ 0 := fun h => hz0 (Complex.ext hz h)
  have hzI : z = (z.im : ℂ) * I := by apply Complex.ext <;> simp [hz]
  have hG : ContinuousAt scaledGamma z := by
    have := (continuousAt_scaledGamma_I him).1
    rwa [← hzI] at this
  unfold stirlingR
  refine hG.sub (tendsto_finsetSum _ fun k _ => ?_)
  exact continuousAt_const.div (continuousAt_id.pow k) (pow_ne_zero _ hz0)

/-- **DLMF 5.11.11** (the `2K^{1/2}` branch on the closed sector `|ph z| ≤ ½π`, `K ≥ 3`). -/
theorem dlmf_5_11_11_closed {K : ℕ} (hK : 3 ≤ K) {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    ‖stirlingR K z‖ ≤ (1 + boydZeta K) * Real.Gamma K / (2 * (2 * π) ^ (K + 1) * ‖z‖ ^ K) *
      (1 + 2 * Real.sqrt K) := by
  rcases hz.lt_or_eq with hre | hre
  · exact dlmf_5_11_11_sqrt hK hre
  set B : ℂ → ℝ := fun w => (1 + boydZeta K) * Real.Gamma K /
    (2 * (2 * π) ^ (K + 1) * ‖w‖ ^ K) * (1 + 2 * Real.sqrt K) with hB
  have hpath : Tendsto (fun ε : ℝ => z + ε) (𝓝[>] 0) (𝓝 z) := by
    have : Tendsto (fun ε : ℝ => z + ε) (𝓝 0) (𝓝 (z + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add continuous_ofReal).tendsto 0
    rw [ofReal_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun ε : ℝ => ‖stirlingR K (z + ε)‖) (𝓝[>] 0) (𝓝 ‖stirlingR K z‖) :=
    ((continuousAt_stirlingR K hre.symm hz0).tendsto.comp hpath).norm
  have hBc : ContinuousAt B z := by
    have hn : ‖z‖ ^ K ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz0)
    rw [hB]
    exact ((continuousAt_const.div (continuousAt_const.mul (continuous_norm.continuousAt.pow K))
      (mul_ne_zero (by positivity) hn)).mul continuousAt_const)
  have h2 : Tendsto (fun ε : ℝ => B (z + ε)) (𝓝[>] 0) (𝓝 (B z)) := hBc.tendsto.comp hpath
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hre' : 0 < (z + ε).re := by
    rw [add_re, ← hre, ofReal_re, zero_add]; exact hε
  exact dlmf_5_11_11_sqrt hK hre'

/-- **DLMF 5.11.11** (Boyd): for `|ph z| < ½π` and `K ≥ 3`,
`|R_K(z)| ≤ (1 + ζ(K)) Γ(K)/(2 (2π)^{K+1} |z|^K) · (1 + min(sec(ph z), 2K^{1/2}))`. -/
theorem dlmf_5_11_11 {K : ℕ} (hK : 3 ≤ K) {z : ℂ} (hz : 0 < z.re) :
    ‖stirlingR K z‖ ≤ (1 + boydZeta K) * Real.Gamma K / (2 * (2 * π) ^ (K + 1) * ‖z‖ ^ K) *
      (1 + min (1 / Real.cos (arg z)) (2 * Real.sqrt K)) := by
  rcases le_total (1 / Real.cos (arg z)) (2 * Real.sqrt K) with h | h
  · rw [min_eq_left h]; exact dlmf_5_11_11_sec (by omega) hz
  · rw [min_eq_right h]; exact dlmf_5_11_11_sqrt hK hz

end Azurite.DLMF
