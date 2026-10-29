/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# DLMF §1.10(xi): Generating Functions

Formalizations of <https://dlmf.nist.gov/1.10.xi>.

* 1.10.26–1.10.27: `dlmf_1_10_27`. If `F(x; z) = ∑ pₙ(x) zⁿ` for `|z| < R` (the radius may depend
  on `x`; `R : ℝ≥0∞` allows `R = ∞`), then `pₙ(x) = (2πi)⁻¹ ∮_{|z|=r} F(x; z)/z^{n+1} dz` for
  every `0 < r < R`.
* Proof. On `|z| = r` the series is dominated by `|pₖ| rᵏ`, which is summable by comparison with
  the convergent series at a radius `ρ ∈ (r, R)`. So the sum and the integral can be swapped, and
  then `∮ zᵏ / z^{n+1} dz = 2πi δₖₙ` (`circleIntegral_pow_div_pow`).
-/

open Filter Topology Set Metric Complex MeasureTheory
open scoped Real ENNReal

namespace Azurite.DLMF

/-- `∮_{|z|=r} zᵏ / z^{n+1} dz` is `2πi` for `k = n` and `0` otherwise. -/
theorem circleIntegral_pow_div_pow {r : ℝ} (hr : 0 < r) (k n : ℕ) :
    (∮ z in C(0, r), z ^ k / z ^ (n + 1)) = if k = n then 2 * π * I else 0 := by
  have hEq : EqOn (fun z : ℂ => z ^ k / z ^ (n + 1)) (fun z => (z - 0) ^ ((k : ℤ) - n - 1))
      (sphere 0 r) := by
    intro z hz
    have hz0 : z ≠ 0 := ne_zero_of_mem_sphere hr.ne' ⟨z, hz⟩
    simp only [sub_zero]
    rw [show (k : ℤ) - n - 1 = (k : ℤ) - (n + 1 : ℕ) by push_cast; ring, zpow_sub₀ hz0,
      zpow_natCast, zpow_natCast]
  rw [circleIntegral.integral_congr hr.le hEq]
  split_ifs with h
  · subst h
    simp only [sub_self, zero_sub, Int.reduceNeg, zpow_neg_one]
    exact circleIntegral.integral_sub_center_inv 0 hr.ne'
  · exact circleIntegral.integral_sub_zpow_of_ne (by omega) 0 0 r

/-- **DLMF 1.10.26–1.10.27**: if `F(x; z) = ∑_{n=0}^∞ pₙ(x) zⁿ` for `|z| < R` (`R` may depend on
`x`), then `pₙ(x) = (2πi)⁻¹ ∮_{|z|=r} F(x; z)/z^{n+1} dz` for `0 < r < R`. -/
theorem dlmf_1_10_27 {α : Type*} {F : α → ℂ → ℂ} {p : ℕ → α → ℂ} {R : α → ℝ≥0∞} {x : α}
    (hF : ∀ z : ℂ, ENNReal.ofReal ‖z‖ < R x → HasSum (fun n => p n x * z ^ n) (F x z))
    {r : ℝ} (hr : 0 < r) (hrR : ENNReal.ofReal r < R x) (n : ℕ) :
    p n x = (2 * π * I)⁻¹ * ∮ z in C(0, r), F x z / z ^ (n + 1) := by
  -- a radius `ρ ∈ (r, R)`, where the terms are bounded
  obtain ⟨ρ, -, hrρ, hρR⟩ := ENNReal.lt_iff_exists_real_btwn.mp hrR
  have hρ : r < ρ := by
    by_contra h
    exact (lt_irrefl _) (hrρ.trans_le (ENNReal.ofReal_le_ofReal (not_lt.mp h)))
  have hρ0 : 0 < ρ := hr.trans hρ
  have hsρ := hF (ρ : ℂ) (by rwa [norm_real, Real.norm_of_nonneg hρ0.le])
  set q := r / ρ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := (div_lt_one hρ0).mpr hρ
  set u : ℕ → ℝ := fun k => ‖p k x‖ * r ^ k with hu
  have hus : Summable u := by
    refine Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hq0 hq1) ?_
    have h0 := (hsρ.summable.tendsto_atTop_zero).norm
    rw [norm_zero] at h0
    filter_upwards [h0.eventually (gt_mem_nhds one_pos)] with k hk
    rw [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hρ0.le] at hk
    rw [hu, norm_mul, norm_norm, norm_pow, Real.norm_of_nonneg hr.le, hq, div_pow]
    rw [le_div_iff₀ (pow_pos hρ0 k)]
    calc ‖p k x‖ * r ^ k * ρ ^ k = ‖p k x‖ * ρ ^ k * r ^ k := by ring
      _ ≤ 1 * r ^ k := by gcongr
      _ = r ^ k := one_mul _
  -- interchange sum and integral
  have hsum : HasSum (fun k => ∮ z in C(0, r), p k x * z ^ k / z ^ (n + 1))
      (∮ z in C(0, r), F x z / z ^ (n + 1)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k _ => r * (u k / r ^ (n + 1))) (fun k => ?_) (fun k => ?_) ?_ ?_ ?_
    · have : Continuous fun θ => deriv (circleMap 0 r) θ •
          (p k x * circleMap 0 r θ ^ k / circleMap 0 r θ ^ (n + 1)) := by
        simp only [deriv_circleMap]
        exact ((continuous_circleMap 0 r).mul continuous_const).smul
          ((continuous_const.mul ((continuous_circleMap 0 r).pow k)).div
            ((continuous_circleMap 0 r).pow (n + 1))
            fun θ => pow_ne_zero _ (circleMap_ne_center hr.ne'))
      exact this.aestronglyMeasurable
    · refine Eventually.of_forall fun θ _ => le_of_eq ?_
      rw [deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, norm_I, abs_of_pos hr,
        norm_div, norm_mul, norm_pow, norm_pow, norm_circleMap_zero, abs_of_pos hr, hu]
      ring
    · exact Eventually.of_forall fun θ _ => (hus.div_const _).mul_left _
    · simp only [tsum_mul_left, tsum_div_const]
      exact intervalIntegrable_const
    · refine Eventually.of_forall fun θ _ => ?_
      set z := circleMap 0 r θ
      have hz : ENNReal.ofReal ‖z‖ < R x := by
        rwa [norm_circleMap_zero, abs_of_pos hr]
      have h := ((hF z hz).div_const (z ^ (n + 1))).const_smul (deriv (circleMap 0 r) θ)
      exact h
  -- only the `k = n` term survives
  have hterm : ∀ k, (∮ z in C(0, r), p k x * z ^ k / z ^ (n + 1)) =
      if k = n then p k x * (2 * π * I) else 0 := fun k => by
    simp_rw [mul_div_assoc]
    rw [circleIntegral.integral_const_mul, circleIntegral_pow_div_pow hr]
    split_ifs <;> simp
  simp_rw [hterm] at hsum
  have hsingle := hasSum_single (f := fun k => if k = n then p k x * (2 * π * I) else 0) n
    (fun k hk => by simp [hk])
  have hn : (if n = n then p n x * (2 * π * I) else 0) = p n x * (2 * π * I) := by simp
  rw [hn] at hsingle
  rw [← hsingle.unique hsum]
  field_simp

end Azurite.DLMF
