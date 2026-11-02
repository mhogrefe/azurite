/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section15Fractional
import Azurite.DLMF.Chapter2.Section6StieltjesExample

/-!
# DLMF §2.6(iii): Fractional Integrals — the convolution, 2.6.36 and the regularized 2.6.39

* 2.6.33 is `fracIntegral` of §1.15(vi) (`dlmf_1_15_47`), with real order `μ > 0`; 2.6.34 is
  `convProd`, and 2.6.35 (`dlmf_2_6_35`) is the identity `I^μ f = (1/Γ(μ)) (t^{μ−1} ∗ f)`.
* 2.6.36: `(t^{μ−1} ∗ t^{−s−α})(x) = ∫₀^x (x−t)^{μ−1} t^{−s−α} dt` converges only for `s = 0`,
  `α < 1` (`dlmf_2_6_36_zero`, the beta integral `Γ(μ)Γ(1−α)/Γ(μ+1−α) x^{μ−α}`) and diverges
  otherwise (`dlmf_2_6_36_diverges`).
* The kernel `(x−t)^{μ−1}` has the Taylor expansion in `t`
  `(x−t)^{μ−1} = ∑_{i<n} binom(μ−1, i)(−1)^i x^{μ−1−i} tⁱ + tⁿ Kₙ(x, t)` (`fracKer`,
  `fracKer_expansion`), with `Kₙ(x, t) = x^{μ−1−n} kₙ(t/x)` (`fracKerUnit`, `fracKer_eq_scale`);
  `kₙ` is bounded near `0` and `O((1−u)^{μ−1})` near `1` (`fracKerUnit_bound`).
* **The regularized 2.6.39** (`dlmf_2_6_39_reg`): for `0 < α < 1`, `s < n` and `x > 0`,
  `∑_{i<n} binom(μ−1, i)(−1)^i x^{μ−s−α}/(i−s−α+1) + ∫₀^x Kₙ(x, t) t^{n−s−α} dt
    = Γ(μ)Γ(1−s−α)/Γ(μ+1−s−α) · x^{μ−s−α}`:
  the left side is the Hadamard finite part of the divergent `∫₀^x (x−t)^{μ−1} t^{−s−α} dt`
  (the divergent moments `∫₀^x t^{i−s−α} dt` replaced by `x^{i−s−α+1}/(i−s−α+1)`), and the
  identity is the analytic continuation in the exponent of the beta integral 5.12.1. Proof: the
  function `λ ↦ ∑_{i<n} binom(μ−1,i)(−1)^i/(i+λ+1) + ∫₀¹ u^{n+λ} kₙ(u) du`, continued through
  `mellinTrunc₁Cont` (2.5.25, `kₙ` has a binomial expansion at `0+`), agrees with
  `Γ(μ)Γ(λ+1)/Γ(μ+λ+1)` for `ℜλ > −1` and hence on `ℂ ∖ ℤ` (`fracKerCont_eq`). This is the
  function-level content of DLMF's distributional `t^{μ−1} ∗ t^{−s−α}`; the distribution algebra
  `K⁺` (2.6.37) itself is not formalized (`docs/dlmf_plan.md`).
-/

open MeasureTheory Filter Topology Set Complex Asymptotics
open scoped Real Nat Interval

namespace Azurite.DLMF

/-! ### 2.6.34–2.6.36 -/

/-- **DLMF 2.6.34**: the convolution `(f ∗ g)(x) = ∫₀^x f(x−t) g(t) dt`. -/
noncomputable def convProd (f g : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..x, f (x - t) * g t

/-- **DLMF 2.6.35**: `I^μ f(x) = (1/Γ(μ)) (t^{μ−1} ∗ f)(x)`. -/
theorem dlmf_2_6_35 (μ : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    fracIntegral μ f x = 1 / Gamma μ * convProd (fun t : ℝ => (t : ℂ) ^ (μ - 1)) f x := by
  rw [fracIntegral, fracIntegralFrom, one_div, convProd]

/-- **DLMF 2.6.36** for `s = 0`, `0 < α < 1`: the only convergent case,
`∫₀^x (x−t)^{μ−1} t^{−α} dt = Γ(μ)Γ(1−α)/Γ(μ+1−α) x^{μ−α}`. -/
theorem dlmf_2_6_36_zero {μ α : ℝ} (hμ : 0 < μ) (hα : α < 1) {x : ℝ} (hx : 0 < x) :
    (∫ t in (0 : ℝ)..x, ((x - t : ℝ) : ℂ) ^ ((μ : ℂ) - 1) * (t : ℂ) ^ (-(α : ℂ))) =
      Gamma μ * Gamma (1 - α) / Gamma (μ + (1 - α)) * (x : ℂ) ^ ((μ : ℂ) - α) := by
  have h := (integral_beta_shift (α := μ) (β := 1 - α) (by simpa using hμ) (by simp; linarith)
    (t := 0) hx).2
  simp only [sub_zero] at h
  rw [show (1 : ℂ) - α - 1 = -(α : ℂ) by ring, show (μ : ℂ) + (1 - α) - 1 = μ - α by ring] at h
  rw [h]
  ring

/-- **DLMF 2.6.36**: for `s + α ≥ 1` the integral `∫₀^x (x−t)^{μ−1} t^{−s−α} dt` does not exist
(the integrand is not integrable near `t = 0`). -/
theorem dlmf_2_6_36_diverges {μ α : ℝ} {s : ℕ} (hsα : 1 ≤ s + α) {x : ℝ}
    (hx : 0 < x) :
    ¬ IntervalIntegrable
      (fun t : ℝ => ((x - t : ℝ) : ℂ) ^ ((μ : ℂ) - 1) * (t : ℂ) ^ (-((s : ℂ) + α))) volume 0 x := by
  intro hint
  have hsub : [[(0 : ℝ), x]] \ {0} ⊆ Ioc 0 x := fun t ht => by
    rw [uIcc_of_le hx.le] at ht
    exact ⟨lt_of_le_of_ne ht.1.1 (Ne.symm ht.2), ht.1.2⟩
  have hmem : [[(0 : ℝ), x]] \ {0} ∈ 𝓝[[[(0 : ℝ), x]] \ {0}] 0 := self_mem_nhdsWithin
  -- a lower bound for `(x − t)^{μ−1}` on `(0, x/2]`
  set m : ℝ := min (x ^ (μ - 1)) ((x / 2) ^ (μ - 1)) with hm
  have hm0 : 0 < m := lt_min (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos (by linarith) _)
  have hker : ∀ t ∈ Ioc 0 (x / 2), m ≤ (x - t) ^ (μ - 1) := by
    intro t ht
    rcases le_or_gt 1 μ with h1 | h1
    · calc m ≤ (x / 2) ^ (μ - 1) := min_le_right _ _
        _ ≤ (x - t) ^ (μ - 1) :=
          Real.rpow_le_rpow (by linarith) (by linarith [ht.2]) (by linarith)
    · calc m ≤ x ^ (μ - 1) := min_le_left _ _
        _ ≤ (x - t) ^ (μ - 1) :=
          Real.rpow_le_rpow_of_nonpos (by linarith [ht.1, ht.2]) (by linarith [ht.1])
            (by linarith)
  refine not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton
    (f := fun t : ℝ => Real.log t) (c := 0) hx.ne (by simp) ?_ ?_ ?_ hint.norm
  · filter_upwards [hmem] with t ht
    exact (Real.hasDerivAt_log (hsub ht).1.ne').differentiableAt
  · have h1 : Tendsto (fun t : ℝ => ‖Real.log t‖) (𝓝[>] 0) atTop := by
      refine (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      simp only [Function.comp_apply, Real.norm_eq_abs]
      rw [abs_of_neg (Real.log_neg ht.1 ht.2)]
    exact h1.mono_left (nhdsWithin_mono _ fun t ht => (hsub ht).1)
  · refine IsBigO.of_bound (1 / m) ?_
    have hsmall : Ioo (-1 : ℝ) (min (x / 2) 1) ∈ 𝓝[[[(0 : ℝ), x]] \ {0}] 0 :=
      nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (lt_min (by linarith) one_pos))
    filter_upwards [hmem, hsmall] with t ht ht'
    obtain ⟨ht0, htx⟩ := hsub ht
    have ht2 : t ≤ x / 2 := (lt_min_iff.mp ht'.2).1.le
    have ht1 : t ≤ 1 := (lt_min_iff.mp ht'.2).2.le
    have hxt : 0 < x - t := by linarith
    rw [(Real.hasDerivAt_log ht0.ne').deriv, norm_norm, norm_mul, norm_cpow_eq_rpow_re_of_pos hxt,
      norm_cpow_eq_rpow_re_of_pos ht0, sub_re, ofReal_re, one_re, neg_re, add_re, natCast_re,
      ofReal_re, Real.norm_of_nonneg (inv_nonneg.mpr ht0.le)]
    have hk := hker t ⟨ht0, ht2⟩
    have hp : t ^ (-1 : ℝ) ≤ t ^ (-((s : ℝ) + α)) :=
      Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by linarith)
    rw [Real.rpow_neg_one] at hp
    calc t⁻¹ ≤ t ^ (-((s : ℝ) + α)) := hp
      _ = 1 / m * (m * t ^ (-((s : ℝ) + α))) := by field_simp
      _ ≤ 1 / m * ((x - t) ^ (μ - 1) * t ^ (-((s : ℝ) + α))) := by
        gcongr

/-! ### The kernel expansion -/

/-- `kₙ(u) = ((1−u)^{μ−1} − ∑_{i<n} binom(μ−1, i)(−u)^i)/uⁿ` on `(0, 1)`, and `0` for `u ≥ 1`:
the `n`-th Taylor remainder of `(1−u)^{μ−1}` divided by `uⁿ`. -/
noncomputable def fracKerUnit (μ : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  if u < 1 then ((1 - u) ^ (μ - 1) - ∑ i ∈ Finset.range n, Ring.choose (μ - 1) i * (-u) ^ i) / u ^ n
  else 0

/-- `Kₙ(x, t) = ((x−t)^{μ−1} − ∑_{i<n} binom(μ−1, i)(−1)^i x^{μ−1−i} tⁱ)/tⁿ`. -/
noncomputable def fracKer (μ : ℝ) (n : ℕ) (x t : ℝ) : ℝ :=
  ((x - t) ^ (μ - 1) -
    ∑ i ∈ Finset.range n, Ring.choose (μ - 1) i * (-1) ^ i * x ^ (μ - 1 - i) * t ^ i) / t ^ n

theorem fracKerUnit_of_lt {μ : ℝ} {n : ℕ} {u : ℝ} (hu : u < 1) :
    fracKerUnit μ n u =
      ((1 - u) ^ (μ - 1) - ∑ i ∈ Finset.range n, Ring.choose (μ - 1) i * (-u) ^ i) / u ^ n := by
  simp [fracKerUnit, hu]

theorem fracKerUnit_of_one_le {μ : ℝ} {n : ℕ} {u : ℝ} (hu : 1 ≤ u) : fracKerUnit μ n u = 0 := by
  simp [fracKerUnit, not_lt.mpr hu]

/-- The Taylor expansion of the kernel: `(x−t)^{μ−1} = ∑_{i<n} … + tⁿ Kₙ(x, t)` for `t ≠ 0`. -/
theorem fracKer_expansion (μ : ℝ) (n : ℕ) (x : ℝ) {t : ℝ} (ht : t ≠ 0) :
    (x - t) ^ (μ - 1) =
      ∑ i ∈ Finset.range n, Ring.choose (μ - 1) i * (-1) ^ i * x ^ (μ - 1 - i) * t ^ i +
        fracKer μ n x t * t ^ n := by
  rw [fracKer, div_mul_cancel₀ _ (pow_ne_zero n ht)]
  ring

/-- `tⁿ Kₙ(x, t) = t^{n+1} K_{n+1}(x, t) + binom(μ−1, n)(−1)ⁿ x^{μ−1−n} tⁿ`. -/
theorem fracKer_succ (μ : ℝ) (n : ℕ) (x : ℝ) {t : ℝ} (ht : t ≠ 0) :
    fracKer μ n x t * t ^ n =
      fracKer μ (n + 1) x t * t ^ (n + 1) +
        Ring.choose (μ - 1) n * (-1) ^ n * x ^ (μ - 1 - n) * t ^ n := by
  have h1 := fracKer_expansion μ n x ht
  have h2 := fracKer_expansion μ (n + 1) x ht
  rw [Finset.sum_range_succ] at h2
  linarith

theorem fracKer_zero (μ : ℝ) (x t : ℝ) : fracKer μ 0 x t = (x - t) ^ (μ - 1) := by
  simp [fracKer]

/-- `Kₙ(x, t) = x^{μ−1−n} kₙ(t/x)` for `0 < t < x`. -/
theorem fracKer_eq_scale {μ : ℝ} (n : ℕ) {x t : ℝ} (ht : 0 < t) (htx : t < x) :
    fracKer μ n x t = x ^ (μ - 1 - n) * fracKerUnit μ n (t / x) := by
  have hx : 0 < x := lt_trans ht htx
  have hu : t / x < 1 := (div_lt_one hx).mpr htx
  rw [fracKerUnit_of_lt hu, fracKer]
  have e1 : (1 - t / x) ^ (μ - 1) = (x - t) ^ (μ - 1) / x ^ (μ - 1) := by
    rw [← Real.div_rpow (by linarith) hx.le]
    congr 1
    field_simp
  have e2 : ∀ i : ℕ, Ring.choose (μ - 1) i * (-(t / x)) ^ i =
      Ring.choose (μ - 1) i * (-1) ^ i * (x ^ (μ - 1 - i) * t ^ i) / x ^ (μ - 1) := by
    intro i
    rw [Real.rpow_sub hx, Real.rpow_natCast, neg_eq_neg_one_mul, mul_pow, div_pow]
    field_simp
  simp only [e1, e2, ← Finset.sum_div]
  rw [Real.rpow_sub hx, Real.rpow_natCast, div_pow]
  have hxμ : x ^ (μ - 1) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have hxn : x ^ n ≠ 0 := pow_ne_zero n hx.ne'
  have htn : t ^ n ≠ 0 := pow_ne_zero n ht.ne'
  field_simp

/-! ### Bounds on `kₙ` -/

/-- `kₙ` is bounded near `0+` (the binomial series). -/
theorem fracKerUnit_isBigO (μ : ℝ) (n : ℕ) :
    (fun u => fracKerUnit μ n u) =O[𝓝[>] 0] fun _ => (1 : ℝ) := by
  have hneg : Tendsto (fun u : ℝ => -u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by simpa using continuous_neg.tendsto (0 : ℝ))
  obtain ⟨C, hC⟩ := ((one_add_rpow_sub_sum_isBigO (μ - 1) n).comp_tendsto hneg).bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hC, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with u hu hu'
  rw [fracKerUnit_of_lt hu'.2, norm_div, Real.norm_of_nonneg (pow_nonneg hu'.1.le n),
    div_le_iff₀ (pow_pos hu'.1 n), norm_one, mul_one, Real.norm_eq_abs]
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_neg, abs_pow, abs_of_pos hu'.1,
    ← sub_eq_add_neg] at hu
  exact hu

/-- A bound for `kₙ` on `(0, 1/2]`. -/
theorem fracKerUnit_bound_half (μ : ℝ) (n : ℕ) :
    ∃ B, ∀ u ∈ Ioc (0 : ℝ) (1 / 2), |fracKerUnit μ n u| ≤ B := by
  obtain ⟨C, hC⟩ := (fracKerUnit_isBigO μ n).bound
  obtain ⟨δ, hδ, hδC⟩ := Metric.mem_nhdsWithin_iff.mp hC
  -- on `[δ/2, 1/2]` the kernel is continuous
  have hcont : ContinuousOn (fracKerUnit μ n) (Icc (δ / 2) (1 / 2)) := by
    have : ∀ u ∈ Icc (δ / 2) (1 / 2), fracKerUnit μ n u =
        ((1 - u) ^ (μ - 1) - ∑ i ∈ Finset.range n, Ring.choose (μ - 1) i * (-u) ^ i) / u ^ n :=
      fun u hu => fracKerUnit_of_lt (by linarith [hu.2])
    refine ContinuousOn.congr ?_ this
    refine ContinuousOn.div ?_ (continuousOn_pow n) fun u hu => pow_ne_zero n (by linarith [hu.1])
    refine ContinuousOn.sub ?_ (continuousOn_finsetSum _ fun i _ =>
      continuousOn_const.mul (continuousOn_neg.pow i))
    exact (continuousOn_const.sub continuousOn_id).rpow_const fun u hu =>
      Or.inl (by show (1 : ℝ) - u ≠ 0; linarith [hu.2])
  obtain ⟨B₁, hB₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C B₁, fun u hu => ?_⟩
  rcases lt_or_ge u δ with h | h
  · have := hδC ⟨by rw [Metric.mem_ball, dist_zero_right, Real.norm_of_nonneg hu.1.le]; exact h,
      hu.1⟩
    rw [mem_ofPred_eq, Real.norm_eq_abs, norm_one, mul_one] at this
    exact this.trans (le_max_left _ _)
  · have := hB₁ u ⟨by linarith, hu.2⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_right _ _)

/-- A bound for `kₙ` on `(0, 1)`: `|kₙ(u)| ≤ C₁ + C₂ (1−u)^{μ−1}`. -/
theorem fracKerUnit_bound (μ : ℝ) (n : ℕ) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ u ∈ Ioo (0 : ℝ) 1, |fracKerUnit μ n u| ≤ C₁ + C₂ * (1 - u) ^ (μ - 1) := by
  obtain ⟨B, hB⟩ := fracKerUnit_bound_half μ n
  set S : ℝ := ∑ i ∈ Finset.range n, |Ring.choose (μ - 1) i|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨max B (2 ^ n * S), 2 ^ n, le_max_of_le_right (by positivity), by positivity,
    fun u hu => ?_⟩
  have hpos : 0 ≤ (1 - u) ^ (μ - 1) := Real.rpow_nonneg (by linarith [hu.2]) _
  rcases le_or_gt u (1 / 2) with h | h
  · calc |fracKerUnit μ n u| ≤ B := hB u ⟨hu.1, h⟩
      _ ≤ max B (2 ^ n * S) := le_max_left _ _
      _ ≤ max B (2 ^ n * S) + 2 ^ n * (1 - u) ^ (μ - 1) :=
          le_add_of_nonneg_right (mul_nonneg (by positivity) hpos)
  · rw [fracKerUnit_of_lt hu.2, abs_div, abs_of_pos (pow_pos hu.1 n), div_le_iff₀ (pow_pos hu.1 n)]
    have hun : (1 / 2 : ℝ) ^ n ≤ u ^ n := pow_le_pow_left₀ (by norm_num) h.le n
    have hsum : |∑ i ∈ Finset.range n, Ring.choose (μ - 1) i * (-u) ^ i| ≤ S := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_pow, abs_neg, abs_of_pos hu.1]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hu.1.le hu.2.le)
    have h2 : (2 : ℝ) ^ n * u ^ n ≥ 1 := by
      have : (2 : ℝ) ^ n * (1 / 2) ^ n = 1 := by rw [← mul_pow]; norm_num
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
    calc |(1 - u) ^ (μ - 1) - ∑ i ∈ Finset.range n, Ring.choose (μ - 1) i * (-u) ^ i|
        ≤ (1 - u) ^ (μ - 1) + S := by
          refine (abs_sub _ _).trans ?_
          rw [abs_of_nonneg hpos]
          linarith
      _ = (S + (1 - u) ^ (μ - 1)) * 1 := by ring
      _ ≤ (S + (1 - u) ^ (μ - 1)) * (2 ^ n * u ^ n) := by gcongr
      _ = (2 ^ n * S + 2 ^ n * (1 - u) ^ (μ - 1)) * u ^ n := by ring
      _ ≤ (max B (2 ^ n * S) + 2 ^ n * (1 - u) ^ (μ - 1)) * u ^ n := by
          gcongr
          exact le_max_right _ _

theorem continuousOn_fracKerUnit (μ : ℝ) (n : ℕ) : ContinuousOn (fracKerUnit μ n) (Ioo 0 1) := by
  have : ∀ u ∈ Ioo (0 : ℝ) 1, fracKerUnit μ n u =
      ((1 - u) ^ (μ - 1) - ∑ i ∈ Finset.range n, Ring.choose (μ - 1) i * (-u) ^ i) / u ^ n :=
    fun u hu => fracKerUnit_of_lt hu.2
  refine ContinuousOn.congr ?_ this
  refine ContinuousOn.div ?_ (continuousOn_pow n) fun u hu => pow_ne_zero n hu.1.ne'
  refine ContinuousOn.sub ?_ (continuousOn_finsetSum _ fun i _ =>
    continuousOn_const.mul (continuousOn_neg.pow i))
  exact (continuousOn_const.sub continuousOn_id).rpow_const fun u hu =>
    Or.inl (by show (1 : ℝ) - u ≠ 0; linarith [hu.2])

/-- `kₙ` is integrable on `(0, ∞)` (it vanishes on `[1, ∞)`). -/
theorem integrableOn_fracKerUnit {μ : ℝ} (hμ : 0 < μ) (n : ℕ) :
    IntegrableOn (fracKerUnit μ n) (Ioi 0) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb⟩ := fracKerUnit_bound μ n
  have h1 : IntegrableOn (fracKerUnit μ n) (Ioo 0 1) := by
    have hdom : IntegrableOn (fun u : ℝ => C₁ + C₂ * (1 - u) ^ (μ - 1)) (Ioo 0 1) := by
      refine (integrableOn_const (by simp)).add (IntegrableOn.mono_set
        ((integrableOn_sub_rpow (a := 0) (x := 1) zero_le_one (by linarith)).const_mul C₂)
        Ioo_subset_Ioc_self)
    refine Integrable.mono' hdom ((continuousOn_fracKerUnit μ n).aestronglyMeasurable
      measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.norm_eq_abs]
    exact hb u hu
  have h2 : IntegrableOn (fracKerUnit μ n) (Ici 1) := by
    refine (integrableOn_zero (s := Ici (1 : ℝ))).congr_fun (fun u hu => ?_) measurableSet_Ici
    exact (fracKerUnit_of_one_le hu).symm
  have : Ioi (0 : ℝ) ⊆ Ioo 0 1 ∪ Ici 1 := fun u hu => by
    rcases lt_or_ge u 1 with h | h
    · exact Or.inl ⟨hu, h⟩
    · exact Or.inr h
  exact (h1.union h2).mono_set this

theorem integrableOn_fracKerUnit' {μ : ℝ} (hμ : 0 < μ) (n : ℕ) :
    IntegrableOn (fun u => (fracKerUnit μ n u : ℂ)) (Ioi 0) :=
  (integrableOn_fracKerUnit hμ n).ofReal

/-! ### The binomial expansion of `kₙ` at `0+` -/

/-- The coefficients of `kₙ` at `0+`: `kₙ(u) ∼ ∑_m binom(μ−1, n+m)(−1)^{n+m} u^m`. -/
noncomputable def fracKerCoeff (μ : ℝ) (n m : ℕ) : ℂ :=
  ((Ring.choose (μ - 1) (n + m) * (-1) ^ (n + m) : ℝ) : ℂ)

theorem fracKerUnit_exp_zero (μ : ℝ) (n : ℕ) :
    IsGenAsympExpansionDLMF (𝓝[>] (0 : ℝ)) (fun (m : ℕ) (u : ℝ) => (u : ℂ) ^ (m : ℂ))
      (fun u => (fracKerUnit μ n u : ℂ)) fun m u => fracKerCoeff μ n m * (u : ℂ) ^ (m : ℂ) := by
  refine ⟨fun s => ?_, fun m => ?_⟩
  · unfold IsLittleODLMF
    have h0 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 0) := by
      have := (continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    refine h0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    rw [← cpow_sub _ _ ht0]
    push_cast
    rw [show (s : ℂ) + 1 - s = 1 by ring, cpow_one]
  · refine isBigODLMF_cpow_zero_of_isBigO_rpow ?_
    rw [natCast_re]
    have hneg : Tendsto (fun u : ℝ => -u) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using continuous_neg.tendsto (0 : ℝ))
    have h := ((one_add_rpow_sub_sum_isBigO (μ - 1) (n + m)).comp_tendsto hneg).mul
      (isBigO_refl (fun u : ℝ => (u ^ n)⁻¹) (𝓝[>] 0))
    refine (isBigO_ofReal_left.mpr h).congr' ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with u hu
      have hsum : ∑ j ∈ Finset.range m, Ring.choose (μ - 1) (n + j) * (-u) ^ (n + j) =
          u ^ n * ∑ j ∈ Finset.range m, Ring.choose (μ - 1) (n + j) * (-1) ^ (n + j) * u ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_add, neg_eq_neg_one_mul, mul_pow, mul_pow]
        ring
      have hun : u ^ n ≠ 0 := pow_ne_zero n hu.1.ne'
      have hreal : ((1 + -u) ^ (μ - 1) -
          ∑ s ∈ Finset.range (n + m), Ring.choose (μ - 1) s * (-u) ^ s) * (u ^ n)⁻¹ =
          fracKerUnit μ n u -
            ∑ j ∈ Finset.range m, Ring.choose (μ - 1) (n + j) * (-1) ^ (n + j) * u ^ j := by
        rw [fracKerUnit_of_lt hu.2, Finset.sum_range_add, hsum, ← sub_eq_add_neg]
        field_simp
        ring
      simp only [Function.comp_apply]
      rw [hreal]
      simp only [fracKerCoeff, ofReal_sub, ofReal_sum, ofReal_mul, ofReal_pow, ofReal_neg,
        ofReal_one, cpow_natCast]
    · filter_upwards [self_mem_nhdsWithin] with u hu
      have hu : (0 : ℝ) < u := hu
      simp only [Function.comp_apply, Real.norm_eq_abs, abs_neg, abs_of_pos hu]
      rw [pow_add, Real.rpow_natCast]
      field_simp

/-! ### The regularized 2.6.39 -/

/-- The continuation of `λ ↦ ∑_{i<n} binom(μ−1,i)(−1)^i/(i+λ+1) + ∫₀¹ u^{n+λ} kₙ(u) du` to `ℂ`. -/
noncomputable def fracKerCont (μ : ℝ) (n : ℕ) (lam : ℂ) : ℂ :=
  ∑ i ∈ Finset.range n, ((Ring.choose (μ - 1) i : ℝ) : ℂ) * (-1) ^ i / ((i : ℂ) + lam + 1) +
    mellinTrunc₁Cont (fun u => (fracKerUnit μ n u : ℂ)) (fracKerCoeff μ n) (fun m : ℕ => (m : ℂ))
      ((n : ℂ) + lam + 1)

/-- Off `ℤ`, the continuation is analytic. -/
theorem differentiableAt_fracKerCont {μ : ℝ} (hμ : 0 < μ) (n : ℕ) {lam : ℂ}
    (hlam : ∀ k : ℤ, lam ≠ k) : DifferentiableAt ℂ (fracKerCont μ n) lam := by
  refine DifferentiableAt.add ?_ ?_
  · refine DifferentiableAt.fun_sum fun i _ => (differentiableAt_const _).div
      ((differentiableAt_id.const_add _).add_const _) fun h => hlam (-(i : ℤ) - 1) ?_
    push_cast
    linear_combination h
  · have h := (dlmf_2_5_25 α_mono (fracKerUnit_exp_zero μ n)
      (integrableOn_fracKerUnit' hμ n).locallyIntegrableOn α_tendsto).2.1 ((n : ℂ) + lam + 1)
      fun m h => hlam (-(n : ℤ) - m - 1) (by push_cast; linear_combination h)
    exact h.comp lam ((differentiableAt_id.const_add _).add_const _)

/-- The honest value for `ℜλ > −n−1`: the continuation is the convergent integral. -/
theorem fracKerCont_eq_integral {μ : ℝ} (hμ : 0 < μ) (n : ℕ) {lam : ℂ}
    (hlam : -(n : ℝ) - 1 < lam.re) :
    fracKerCont μ n lam =
      ∑ i ∈ Finset.range n, ((Ring.choose (μ - 1) i : ℝ) : ℂ) * (-1) ^ i / ((i : ℂ) + lam + 1) +
        ∫ u in Ioo (0 : ℝ) 1, (u : ℂ) ^ ((n : ℂ) + lam) * (fracKerUnit μ n u : ℂ) := by
  rw [fracKerCont, mellinTrunc₁Cont_eq α_mono (fracKerUnit_exp_zero μ n)
    (integrableOn_fracKerUnit' hμ n).locallyIntegrableOn (N := 0)
    ⟨by simp; linarith, fun s hs => absurd hs (Nat.not_lt_zero s)⟩, mellinTrunc₁Ext_zero, mellin]
  congr 1
  have : ∀ u ∈ Ioi (0 : ℝ), (u : ℂ) ^ ((n : ℂ) + lam + 1 - 1) •
      trunc₁ (fun u => (fracKerUnit μ n u : ℂ)) u =
      (Ioo 0 1).indicator (fun u : ℝ => (u : ℂ) ^ ((n : ℂ) + lam) * (fracKerUnit μ n u : ℂ)) u := by
    intro u hu
    simp only [trunc₁, indicator, add_sub_cancel_right, smul_eq_mul]
    by_cases h1 : u < 1
    · have : u ∈ Ioc (0 : ℝ) 1 := ⟨hu, h1.le⟩
      have : u ∈ Ioo (0 : ℝ) 1 := ⟨hu, h1⟩
      simp [*]
    · have h1' : (1 : ℝ) ≤ u := not_lt.mp h1
      by_cases h2 : u ∈ Ioc (0 : ℝ) 1
      · have : u = 1 := le_antisymm h2.2 h1'
        subst this
        simp [fracKerUnit_of_one_le le_rfl]
      · have : u ∉ Ioo (0 : ℝ) 1 := fun h => h2 ⟨h.1, h.2.le⟩
        simp [h2, this]
  rw [setIntegral_congr_fun measurableSet_Ioi this, setIntegral_indicator measurableSet_Ioo,
    inter_eq_right.mpr Ioo_subset_Ioi_self]

/-- The beta function side. -/
noncomputable def fracBeta (μ : ℝ) (lam : ℂ) : ℂ := Gamma μ * Gamma (lam + 1) / Gamma (μ + lam + 1)

theorem differentiableAt_fracBeta (μ : ℝ) {lam : ℂ} (hlam : ∀ k : ℤ, lam ≠ k) :
    DifferentiableAt ℂ (fracBeta μ) lam := by
  have h1 : DifferentiableAt ℂ (fun lam : ℂ => Gamma (lam + 1)) lam := by
    refine (differentiableAt_Gamma (lam + 1) fun m h => hlam (-(m : ℤ) - 1) ?_).comp lam
      (differentiableAt_id.add_const _)
    push_cast
    linear_combination h
  have h2 : DifferentiableAt ℂ (fun lam : ℂ => (Gamma ((μ : ℂ) + lam + 1))⁻¹) lam :=
    (differentiable_one_div_Gamma _).comp lam ((differentiableAt_id.const_add _).add_const _)
  have : fracBeta μ = fun lam => Gamma μ * Gamma (lam + 1) * (Gamma ((μ : ℂ) + lam + 1))⁻¹ := by
    ext lam
    rw [fracBeta, div_eq_mul_inv]
  rw [this]
  exact ((differentiableAt_const _).mul h1).mul h2

/-- The honest identity for `ℜλ > −1`: the Taylor split of the beta integral. -/
theorem fracKerCont_eq_fracBeta_of_re {μ : ℝ} (hμ : 0 < μ) (n : ℕ) {lam : ℂ} (hlam : -1 < lam.re) :
    fracKerCont μ n lam = fracBeta μ lam := by
  rw [fracKerCont_eq_integral hμ n (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])]
  -- the beta integral
  have hB := betaIntegral_eq_Gamma_mul_div (lam + 1) μ (by simp; linarith) (by simpa using hμ)
  rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hB
  have e1 : ∀ u ∈ Ioo (0 : ℝ) 1, (u : ℂ) ^ (lam + 1 - 1) * (1 - (u : ℂ)) ^ ((μ : ℂ) - 1) =
      ∑ i ∈ Finset.range n,
        ((Ring.choose (μ - 1) i : ℝ) : ℂ) * (-1) ^ i * (u : ℂ) ^ ((i : ℂ) + lam) +
        (u : ℂ) ^ ((n : ℂ) + lam) * (fracKerUnit μ n u : ℂ) := by
    intro u hu
    have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.1.ne'
    have hun : (u : ℂ) ^ n ≠ 0 := pow_ne_zero n hu0
    have hpow : (1 - (u : ℂ)) ^ ((μ : ℂ) - 1) = (((1 - u) ^ (μ - 1) : ℝ) : ℂ) := by
      rw [ofReal_cpow (by linarith [hu.2] : (0 : ℝ) ≤ 1 - u)]
      push_cast
      rfl
    have hkC : (fracKerUnit μ n u : ℂ) = ((((1 - u) ^ (μ - 1) : ℝ) : ℂ) -
        ∑ i ∈ Finset.range n, ((Ring.choose (μ - 1) i : ℝ) : ℂ) * (-1) ^ i * (u : ℂ) ^ i) /
          (u : ℂ) ^ n := by
      rw [fracKerUnit_of_lt hu.2, ofReal_div, ofReal_sub, ofReal_sum, ofReal_pow]
      simp only [ofReal_mul, ofReal_pow, ofReal_neg]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [neg_eq_neg_one_mul, mul_pow]
      ring
    have hpow' : ∀ i : ℕ, (u : ℂ) ^ ((i : ℂ) + lam) = (u : ℂ) ^ i * (u : ℂ) ^ lam := fun i => by
      rw [cpow_add _ _ hu0, cpow_natCast]
    simp only [hpow', add_sub_cancel_right]
    rw [hpow, hkC]
    have e : ∑ i ∈ Finset.range n, ((Ring.choose (μ - 1) i : ℝ) : ℂ) * (-1) ^ i *
        ((u : ℂ) ^ i * (u : ℂ) ^ lam) =
        (∑ i ∈ Finset.range n, ((Ring.choose (μ - 1) i : ℝ) : ℂ) * (-1) ^ i * (u : ℂ) ^ i) *
          (u : ℂ) ^ lam := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e]
    field_simp
    ring
  -- integrability of the pieces
  have hint : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (lam + 1 - 1) * (1 - (u : ℂ)) ^ ((μ : ℂ) - 1))
      (Ioo 0 1) := by
    have := betaIntegral_convergent (u := lam + 1) (v := μ) (by simp; linarith) (by simpa using hμ)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at this
    exact this
  have hpow_int : ∀ i : ℕ, IntegrableOn (fun u : ℝ => (u : ℂ) ^ ((i : ℂ) + lam)) (Ioo 0 1) :=
    fun i => (StieltjesSetup.integrableOn_Ioc_cpow (by simp; linarith [(Nat.cast_nonneg i :
      (0 : ℝ) ≤ i)])).mono_set Ioo_subset_Ioc_self
  have hsum_int : IntegrableOn (fun u : ℝ => ∑ i ∈ Finset.range n,
      ((Ring.choose (μ - 1) i : ℝ) : ℂ) * (-1) ^ i * (u : ℂ) ^ ((i : ℂ) + lam)) (Ioo 0 1) :=
    integrable_finsetSum _ fun i _ => (hpow_int i).const_mul _
  have hk_int : IntegrableOn (fun u : ℝ => (u : ℂ) ^ ((n : ℂ) + lam) * (fracKerUnit μ n u : ℂ))
      (Ioo 0 1) := by
    refine IntegrableOn.congr_fun (hint.sub hsum_int) (fun u hu => ?_) measurableSet_Ioo
    simp only [Pi.sub_apply]
    rw [e1 u hu]
    ring
  -- the moments
  have hmom : ∀ i : ℕ,
      (∫ u in Ioo (0 : ℝ) 1, (u : ℂ) ^ ((i : ℂ) + lam)) = 1 / ((i : ℂ) + lam + 1) := by
    intro i
    have hre : -1 < ((i : ℂ) + lam).re := by simp; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    have hne : (i : ℂ) + lam + 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_cpow (Or.inl hre), ofReal_one, one_cpow, ofReal_zero, zero_cpow hne, sub_zero]
  rw [fracBeta, show (μ : ℂ) + lam + 1 = lam + 1 + μ by ring, mul_comm (Gamma (μ : ℂ)), ← hB,
    setIntegral_congr_fun measurableSet_Ioo e1, integral_add hsum_int hk_int,
    integral_finsetSum _ fun i _ => (hpow_int i).const_mul _]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, hmom, mul_one_div]

/-- **The identity on `ℂ ∖ ℤ`**: `∑_{i<n} binom(μ−1,i)(−1)^i/(i+λ+1) + ∫₀¹ u^{n+λ} kₙ(u) du`
(continued) equals `Γ(μ)Γ(λ+1)/Γ(μ+λ+1)`. -/
theorem fracKerCont_eq {μ : ℝ} (hμ : 0 < μ) (n : ℕ) {lam : ℂ} (hlam : ∀ k : ℤ, lam ≠ k) :
    fracKerCont μ n lam = fracBeta μ lam := by
  set U : Set ℂ := (range ((↑) : ℤ → ℂ))ᶜ with hU
  have hUo : IsOpen U := isClosed_range_intCast.isOpen_compl
  have hUc : IsPreconnected U :=
    ((countable_range _).isConnected_compl_of_one_lt_rank (by
      rw [rank_real_complex]; norm_num)).isPreconnected
  have hmem : ∀ w, w ∈ U ↔ ∀ k : ℤ, w ≠ k := fun w => notMem_range_intCast_iff
  have hf : AnalyticOnNhd ℂ (fracKerCont μ n) U :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      (differentiableAt_fracKerCont hμ n ((hmem w).mp hw)).differentiableWithinAt) hUo
  have hg : AnalyticOnNhd ℂ (fracBeta μ) U :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      (differentiableAt_fracBeta μ ((hmem w).mp hw)).differentiableWithinAt) hUo
  have h₀ : (1 / 2 : ℂ) ∈ U := (hmem _).mpr fun k h => by
    have := congrArg Complex.re h
    simp at this
    have h2 : (2 : ℝ) * k = 1 := by linarith
    have : (2 : ℤ) * k = 1 := by exact_mod_cast h2
    omega
  have hfg : fracKerCont μ n =ᶠ[𝓝 (1 / 2 : ℂ)] fracBeta μ := by
    filter_upwards [Metric.ball_mem_nhds (1 / 2 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hre := abs_re_le_norm (w - 1 / 2)
    rw [sub_re, show ((1 / 2 : ℂ)).re = 1 / 2 by norm_num] at hre
    have h1 : -1 < w.re := by linarith [(abs_lt.mp (hre.trans_lt hw)).1]
    exact fracKerCont_eq_fracBeta_of_re hμ n h1
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc h₀ hfg ((hmem lam).mpr hlam)

/-- `−(s + α) ∉ ℤ` for `0 < α < 1`. -/
theorem neg_natCast_add_ne_intCast {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (s : ℕ) (k : ℤ) :
    -((s : ℂ) + α) ≠ k := by
  intro h
  have := congrArg Complex.re h
  simp at this
  have h1 : ((-(s : ℤ) - k : ℤ) : ℝ) = α := by push_cast; linarith
  have h2 : (0 : ℤ) < -(s : ℤ) - k := by exact_mod_cast (h1 ▸ hα0)
  have h3 : -(s : ℤ) - k < 1 := by exact_mod_cast (h1 ▸ hα1)
  omega

/-- The real form on the unit interval: for `0 < α < 1`, `s < n`,
`∑_{i<n} binom(μ−1,i)(−1)^i/(i−s−α+1) + ∫₀¹ u^{n−s−α} kₙ(u) du = Γ(μ)Γ(1−s−α)/Γ(μ+1−s−α)`. -/
theorem fracKerUnit_reg {μ α : ℝ} (hμ : 0 < μ) (hα0 : 0 < α) (hα1 : α < 1) {s n : ℕ} (hs : s < n) :
    ∑ i ∈ Finset.range n, Ring.choose (μ - 1) i * (-1) ^ i / ((i : ℝ) - s - α + 1) +
      ∫ u in Ioo (0 : ℝ) 1, u ^ ((n : ℝ) - s - α) * fracKerUnit μ n u =
      Real.Gamma μ * Real.Gamma (1 - s - α) / Real.Gamma (μ + 1 - s - α) := by
  have hs' : (s : ℝ) + 1 ≤ n := by exact_mod_cast hs
  have h := fracKerCont_eq hμ n (lam := -((s : ℂ) + α)) (neg_natCast_add_ne_intCast hα0 hα1 s)
  rw [fracKerCont_eq_integral hμ n (by simp; linarith), fracBeta] at h
  apply ofReal_injective
  rw [ofReal_add, ofReal_sum, ofReal_div, ofReal_mul, ← Gamma_ofReal, ← Gamma_ofReal,
    ← Gamma_ofReal]
  have e1 : ∀ i : ℕ, ((Ring.choose (μ - 1) i * (-1) ^ i / ((i : ℝ) - s - α + 1) : ℝ) : ℂ) =
      ((Ring.choose (μ - 1) i : ℝ) : ℂ) * (-1) ^ i / ((i : ℂ) + -((s : ℂ) + α) + 1) := by
    intro i
    push_cast
    ring
  have e2 : ((∫ u in Ioo (0 : ℝ) 1, u ^ ((n : ℝ) - s - α) * fracKerUnit μ n u : ℝ) : ℂ) =
      ∫ u in Ioo (0 : ℝ) 1, (u : ℂ) ^ ((n : ℂ) + -((s : ℂ) + α)) * (fracKerUnit μ n u : ℂ) := by
    rw [show ((∫ u in Ioo (0 : ℝ) 1, u ^ ((n : ℝ) - s - α) * fracKerUnit μ n u : ℝ) : ℂ) =
      @RCLike.ofReal ℂ _ (∫ u in Ioo (0 : ℝ) 1, u ^ ((n : ℝ) - s - α) * fracKerUnit μ n u) from
      rfl, ← integral_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    change ((u ^ ((n : ℝ) - s - α) * fracKerUnit μ n u : ℝ) : ℂ) = _
    rw [ofReal_mul, ofReal_cpow hu.1.le]
    push_cast
    ring_nf
  simp only [e1]
  rw [e2, h]
  push_cast
  ring_nf

/-- **DLMF 2.6.39, regularized**: for `0 < α < 1`, `s < n`, `x > 0`,
`∑_{i<n} binom(μ−1,i)(−1)^i x^{μ−s−α}/(i−s−α+1) + ∫₀^x Kₙ(x,t) t^{n−s−α} dt
  = Γ(μ)Γ(1−s−α)/Γ(μ+1−s−α) · x^{μ−s−α}`:
the finite part of the divergent `(t^{μ−1} ∗ t^{−s−α})(x)` of 2.6.36. -/
theorem dlmf_2_6_39_reg {μ α : ℝ} (hμ : 0 < μ) (hα0 : 0 < α) (hα1 : α < 1) {s n : ℕ} (hs : s < n)
    {x : ℝ} (hx : 0 < x) :
    ∑ i ∈ Finset.range n,
        Ring.choose (μ - 1) i * (-1) ^ i * (x ^ (μ - s - α) / ((i : ℝ) - s - α + 1)) +
      ∫ t in Ioo (0 : ℝ) x, fracKer μ n x t * t ^ ((n : ℝ) - s - α) =
      Real.Gamma μ * Real.Gamma (1 - s - α) / Real.Gamma (μ + 1 - s - α) * x ^ (μ - s - α) := by
  have hunit := fracKerUnit_reg hμ hα0 hα1 hs
  -- scaling `t = x u`
  have hscale : (∫ t in Ioo (0 : ℝ) x, fracKer μ n x t * t ^ ((n : ℝ) - s - α)) =
      x ^ (μ - s - α) * ∫ u in Ioo (0 : ℝ) 1, u ^ ((n : ℝ) - s - α) * fracKerUnit μ n u := by
    set g : ℝ → ℝ := fun u => x ^ (μ - 1 - n) * x ^ ((n : ℝ) - s - α) *
      (u ^ ((n : ℝ) - s - α) * fracKerUnit μ n u) with hg
    have e1 : ∀ t ∈ Ioo (0 : ℝ) x, fracKer μ n x t * t ^ ((n : ℝ) - s - α) = g (t / x) := by
      intro t ht
      rw [hg]
      simp only
      rw [fracKer_eq_scale n ht.1 ht.2, Real.div_rpow ht.1.le hx.le]
      have : x ^ ((n : ℝ) - s - α) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
      field_simp
    rw [setIntegral_congr_fun measurableSet_Ioo e1, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hx.le, intervalIntegral.integral_comp_div g hx.ne',
      zero_div, div_self hx.ne', intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, integral_const_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc]
    congr 1
    rw [mul_assoc, ← Real.rpow_add hx, mul_comm, ← Real.rpow_add_one hx.ne']
    congr 1
    ring
  rw [hscale, ← hunit, add_mul, Finset.sum_mul]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · ring

end Azurite.DLMF
