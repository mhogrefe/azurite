/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section9Series
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# DLMF §1.9(vi): Power Series

Formalizations of <https://dlmf.nist.gov/1.9.vi>.  A power series is given by its coefficients
`a : ℕ → ℂ`; `psum a z₀ z = ∑' aₙ (z − z₀)ⁿ` and `pradius a ∈ [0, ∞]` is Mathlib's radius of the
scalar series `FormalMultilinearSeries.ofScalars ℂ a`.  Convergence is in DLMF's sense
(`SeriesConverges`, §1.9(v)).

* Circle of convergence: `dlmf_1_9_vi_converges` (absolute convergence for `|z − z₀| < R`),
  `dlmf_1_9_vi_diverges` (divergence for `|z − z₀| > R`), `dlmf_1_9_vi_uniform` (uniform on
  `|z − z₀| ≤ ρ < R`), `dlmf_1_9_vi_analytic` (the sum is analytic inside).
* 1.9.48: `dlmf_1_9_48` (`aₙ = f⁽ⁿ⁾(z₀)/n!`); 1.9.49: `dlmf_1_9_49` (Cauchy–Hadamard, from
  Mathlib's `radius_eq_liminf`); 1.9.63: `dlmf_1_9_63` (`f⁽ᵐ⁾ = ∑ (n+1)_m a_{n+m} (z − z₀)ⁿ`, with
  `(n+1)_m = Nat.ascFactorial (n + 1) m`), via `hasDerivAt_psum` (term-by-term differentiation,
  `dcoeff a n = (n + 1) a_{n+1}`, `le_pradius_dcoeff`) and `iterate_dcoeff_apply`.
* Operations: `dlmf_1_9_50`; `cauchyCoeff` (1.9.52), `dlmf_1_9_51` (absolutely convergent series)
  and `dlmf_1_9_51_psum` (inside both circles).
* Reciprocal (1.9.53–1.9.56): `recipCoeff`, `dlmf_1_9_54`, `dlmf_1_9_55`, `dlmf_1_9_56`
  (`cauchyCoeff_recipCoeff`: the Cauchy product of `a` and `b` is `1`).
* Logarithm (1.9.57–1.9.59, `a₀ = 1`): `logCoeff`, `dlmf_1_9_57` (principal value), `dlmf_1_9_58`,
  `dlmf_1_9_59` (also for `n = 1`); proof: `f · L′ = f′` coefficientwise
  (`cauchyCoeff_logCoeff`), so `L − ln f` has zero derivative on a small disk where `f` stays in
  the slit plane (`exists_ball_slitPlane`).
* Powers (1.9.60–1.9.62, `a₀ = 1`, `ν ∈ ℂ`): `powCoeff`, `dlmf_1_9_60` (principal value),
  `dlmf_1_9_61`, `dlmf_1_9_62`; proof: `f · P′ = ν f′ P` (`cauchyCoeff_powCoeff`), so
  `P · exp(−ν ln f)` is constant.
* Positive radius of the recursively defined coefficients: `norm_le_of_recursion` (geometric
  growth from `|x_{n+1}| ≤ E ρ^{n+1} + B ∑ |a_{k+1}| |x_{n−k}|`), `pradius_pos_of_bound`,
  `exists_coeff_bound`.
-/

open Filter Topology Set Finset Metric Complex
open scoped NNReal ENNReal

namespace Azurite.DLMF

/-! ### Radius of convergence -/

/-- The sum `∑ aₙ (z − z₀)ⁿ` of a power series. -/
noncomputable def psum (a : ℕ → ℂ) (z₀ z : ℂ) : ℂ := ∑' n, a n * (z - z₀) ^ n

/-- The radius of convergence `R ∈ [0, ∞]` of `∑ aₙ (z − z₀)ⁿ`. -/
noncomputable def pradius (a : ℕ → ℂ) : ℝ≥0∞ := (FormalMultilinearSeries.ofScalars ℂ a).radius

theorem norm_ofScalars (a : ℕ → ℂ) (n : ℕ) :
    ‖FormalMultilinearSeries.ofScalars ℂ a n‖ = ‖a n‖ :=
  FormalMultilinearSeries.ofScalars_norm ℂ a n

theorem summable_norm_mul_pow_of_lt {a : ℕ → ℂ} {r : ℝ≥0} (h : (r : ℝ≥0∞) < pradius a) :
    Summable fun n => ‖a n‖ * (r : ℝ) ^ n := by
  simpa only [norm_ofScalars] using (FormalMultilinearSeries.ofScalars ℂ a).summable_norm_mul_pow h

theorem summable_norm_term {a : ℕ → ℂ} {z₀ z : ℂ} (h : (‖z - z₀‖₊ : ℝ≥0∞) < pradius a) :
    Summable fun n => ‖a n * (z - z₀) ^ n‖ := by
  simpa only [norm_mul, norm_pow, coe_nnnorm] using summable_norm_mul_pow_of_lt h

theorem le_pradius_of_tendsto {a : ℕ → ℂ} {r : ℝ≥0} {l : ℝ}
    (h : Tendsto (fun n => ‖a n‖ * (r : ℝ) ^ n) atTop (𝓝 l)) : (r : ℝ≥0∞) ≤ pradius a :=
  (FormalMultilinearSeries.ofScalars ℂ a).le_radius_of_tendsto (by simpa only [norm_ofScalars])

theorem le_pradius_of_bound {a : ℕ → ℂ} {r : ℝ≥0} (C : ℝ)
    (h : ∀ n, ‖a n‖ * (r : ℝ) ^ n ≤ C) : (r : ℝ≥0∞) ≤ pradius a :=
  (FormalMultilinearSeries.ofScalars ℂ a).le_radius_of_bound C fun n => by
    rw [norm_ofScalars]; exact h n

theorem le_pradius_of_summable {a : ℕ → ℂ} {r : ℝ≥0}
    (h : Summable fun n => ‖a n‖ * (r : ℝ) ^ n) : (r : ℝ≥0∞) ≤ pradius a :=
  le_pradius_of_tendsto h.tendsto_atTop_zero

/-- DLMF §1.9(vi): the series converges (absolutely) for `|z − z₀| < R`. -/
theorem dlmf_1_9_vi_converges {a : ℕ → ℂ} {z₀ z : ℂ} (h : (‖z - z₀‖₊ : ℝ≥0∞) < pradius a) :
    SeriesConverges (fun n => a n * (z - z₀) ^ n) (psum a z₀ z) ∧
      SeriesConvergesAbsolutely (fun n => a n * (z - z₀) ^ n) := by
  have hs := summable_norm_term h
  exact ⟨seriesConverges_iff.mpr hs.of_norm.hasSum.tendsto_sum_nat,
    seriesConvergesAbsolutely_iff.mpr hs⟩

/-- DLMF §1.9(vi): the series diverges for `|z − z₀| > R`. -/
theorem dlmf_1_9_vi_diverges {a : ℕ → ℂ} {z₀ z : ℂ} (h : pradius a < (‖z - z₀‖₊ : ℝ≥0∞)) :
    SeriesDiverges fun n => a n * (z - z₀) ^ n := by
  rintro ⟨s, hs⟩
  have h0 := (tendsto_norm_zero.comp hs.tendsto_zero)
  have : (‖z - z₀‖₊ : ℝ≥0∞) ≤ pradius a := le_pradius_of_tendsto (l := 0) (by
    simpa only [Function.comp_def, norm_mul, norm_pow, coe_nnnorm] using h0)
  exact absurd h (not_lt.mpr this)

/-- DLMF §1.9(vi): for `|z − z₀| ≤ ρ < R` the convergence is uniform (and absolute). -/
theorem dlmf_1_9_vi_uniform {a : ℕ → ℂ} {z₀ : ℂ} {ρ : ℝ≥0} (h : (ρ : ℝ≥0∞) < pradius a) :
    SeriesConvergesUniformlyOn (fun n z => a n * (z - z₀) ^ n) (psum a z₀)
      (closedBall z₀ ρ) := by
  refine dlmf_1_9_v_Mtest (M := fun n => ‖a n‖ * (ρ : ℝ) ^ n)
    ⟨_, seriesConverges_iff.mpr (summable_norm_mul_pow_of_lt h).hasSum.tendsto_sum_nat⟩
    fun n z hz => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
    (mem_closedBall_iff_norm.mp hz) n) (norm_nonneg _)

/-- **DLMF 1.9.49** (Cauchy–Hadamard): `R = liminf |aₙ|^{−1/n}`. -/
theorem dlmf_1_9_49 (a : ℕ → ℂ) :
    pradius a = liminf (fun n : ℕ => (((‖a n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞))⁻¹) atTop := by
  rw [pradius, FormalMultilinearSeries.radius_eq_liminf]
  congr 1
  funext n
  have h : ‖FormalMultilinearSeries.ofScalars ℂ a n‖₊ = ‖a n‖₊ :=
    NNReal.eq (by simpa only [coe_nnnorm] using norm_ofScalars a n)
  rw [h, one_div]

/-! ### Differentiation -/

/-- The coefficients `(n + 1) a_{n+1}` of the derived series. -/
noncomputable def dcoeff (a : ℕ → ℂ) (n : ℕ) : ℂ := (n + 1) * a (n + 1)

theorem summable_norm_mul_pow_dcoeff {a : ℕ → ℂ} {r : ℝ≥0} (h : (r : ℝ≥0∞) < pradius a) :
    Summable fun n => ‖dcoeff a n‖ * (r : ℝ) ^ n := by
  obtain ⟨r', hrr', hr'R⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  have hr'0 : (0 : ℝ) < r' := by
    have : (r : ℝ) < r' := by exact_mod_cast hrr'
    exact lt_of_le_of_lt r.coe_nonneg this
  set q : ℝ := r / r' with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    rw [hq, div_lt_one hr'0]
    exact_mod_cast hrr'
  have hgeo : Summable fun n : ℕ => ((n : ℝ) + 1) * q ^ n := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
      (by rwa [Real.norm_of_nonneg hq0])
    exact (h1.add (summable_geometric_of_lt_one hq0 hq1)).congr fun n => by ring
  set K := ∑' n : ℕ, ((n : ℝ) + 1) * q ^ n
  have hK : ∀ n : ℕ, ((n : ℝ) + 1) * q ^ n ≤ K := fun n =>
    hgeo.le_tsum n fun j _ => by positivity
  have hS := (summable_nat_add_iff 1).mpr (summable_norm_mul_pow_of_lt hr'R)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((hS.mul_left (K / r')))
  simp only [dcoeff, norm_mul]
  have hn : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (n + 1)
  rw [hn]
  have hrq : (r : ℝ) = q * r' := by rw [hq]; field_simp
  rw [hrq, mul_pow, pow_succ]
  have := hK n
  calc ((n : ℝ) + 1) * ‖a (n + 1)‖ * (q ^ n * (r' : ℝ) ^ n)
      = (((n : ℝ) + 1) * q ^ n) * (‖a (n + 1)‖ * (r' : ℝ) ^ n) := by ring
    _ ≤ K * (‖a (n + 1)‖ * (r' : ℝ) ^ n) := by gcongr
    _ = K / r' * (‖a (n + 1)‖ * ((r' : ℝ) ^ n * r')) := by field_simp

theorem le_pradius_dcoeff (a : ℕ → ℂ) : pradius a ≤ pradius (dcoeff a) :=
  ENNReal.le_of_forall_nnreal_lt fun _ hr =>
    le_pradius_of_summable (summable_norm_mul_pow_dcoeff hr)

theorem le_pradius_iterate_dcoeff (a : ℕ → ℂ) (m : ℕ) : pradius a ≤ pradius (dcoeff^[m] a) := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (le_pradius_dcoeff _)

theorem mem_ball_of_nnnorm_lt {z₀ z : ℂ} {ρ : ℝ≥0} (h : (‖z - z₀‖₊ : ℝ≥0∞) < ρ) :
    z ∈ ball z₀ ρ := by
  rw [mem_ball, dist_eq_norm, ← coe_nnnorm]
  exact_mod_cast h

/-- Term-by-term differentiation inside the circle of convergence. -/
theorem hasDerivAt_psum {a : ℕ → ℂ} {z₀ z : ℂ} (h : (‖z - z₀‖₊ : ℝ≥0∞) < pradius a) :
    HasDerivAt (psum a z₀) (psum (dcoeff a) z₀ z) z := by
  obtain ⟨ρ, hzρ, hρR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  have hzt : z ∈ ball z₀ ρ := mem_ball_of_nnnorm_lt hzρ
  have hu : Summable fun n : ℕ => ‖a n‖ * n * (ρ : ℝ) ^ (n - 1) := by
    refine (summable_nat_add_iff 1).mp ((summable_norm_mul_pow_dcoeff hρR).congr fun n => ?_)
    simp only [dcoeff, norm_mul, Nat.add_sub_cancel]
    have hn : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (n + 1)
    rw [hn]
    push_cast
    ring
  have hbound : ∀ n y, y ∈ ball z₀ ρ →
      ‖a n * (n * (y - z₀) ^ (n - 1))‖ ≤ ‖a n‖ * n * (ρ : ℝ) ^ (n - 1) := by
    intro n y hy
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (by rw [← dist_eq_norm]; exact (mem_ball.mp hy).le) _) (by positivity)
  have key := hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => ‖a n‖ * n * (ρ : ℝ) ^ (n - 1))
    (g := fun n w => a n * (w - z₀) ^ n) (g' := fun n w => a n * (n * (w - z₀) ^ (n - 1)))
    hu isOpen_ball (convex_ball _ _).isPreconnected
    (fun n y _ => by
      simpa using (((hasDerivAt_id y).sub_const z₀).pow n).const_mul (a n))
    hbound hzt (summable_norm_term h).of_norm hzt
  have hsum : Summable fun n : ℕ => a n * (n * (z - z₀) ^ (n - 1)) :=
    Summable.of_norm_bounded hu fun n => hbound n z hzt
  unfold psum
  convert key using 1
  rw [hsum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, dcoeff, Nat.add_sub_cancel]
  congr 1
  funext n
  push_cast
  ring

theorem differentiableOn_psum (a : ℕ → ℂ) (z₀ : ℂ) :
    DifferentiableOn ℂ (psum a z₀) (Metric.eball z₀ (pradius a)) := fun z hz => by
  have h : (‖z - z₀‖₊ : ℝ≥0∞) < pradius a := by
    rwa [Metric.mem_eball, edist_eq_enorm_sub] at hz
  exact (hasDerivAt_psum h).differentiableAt.differentiableWithinAt

/-- DLMF §1.9(vi): inside the circle of convergence the sum is analytic. -/
theorem dlmf_1_9_vi_analytic (a : ℕ → ℂ) (z₀ : ℂ) :
    AnalyticOnNhd ℂ (psum a z₀) (Metric.eball z₀ (pradius a)) :=
  (differentiableOn_psum a z₀).analyticOnNhd Metric.isOpen_eball

theorem iterate_dcoeff_apply (a : ℕ → ℂ) (m n : ℕ) :
    dcoeff^[m] a n = ((n + 1).ascFactorial m : ℂ) * a (n + m) := by
  induction m generalizing a n with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih, dcoeff, Nat.ascFactorial_succ]
    push_cast
    rw [show n + m + 1 = n + (m + 1) by ring]
    ring

/-- **DLMF 1.9.63**: `f^{(m)}(z) = ∑ (n + 1)_m a_{n+m} (z − z₀)ⁿ` for `|z − z₀| < R`. -/
theorem dlmf_1_9_63 (a : ℕ → ℂ) (z₀ : ℂ) (m : ℕ) {z : ℂ}
    (h : (‖z - z₀‖₊ : ℝ≥0∞) < pradius a) :
    iteratedDeriv m (psum a z₀) z =
      ∑' n, ((n + 1).ascFactorial m : ℂ) * a (n + m) * (z - z₀) ^ n := by
  have key : ∀ m, ∀ z, (‖z - z₀‖₊ : ℝ≥0∞) < pradius a →
      iteratedDeriv m (psum a z₀) z = psum (dcoeff^[m] a) z₀ z := by
    intro m
    induction m with
    | zero => intro z _; simp
    | succ m ih =>
      intro z hz
      have hU : Metric.eball z₀ (pradius a) ∈ 𝓝 z :=
        Metric.isOpen_eball.mem_nhds (by rwa [Metric.mem_eball, edist_eq_enorm_sub])
      have hev : iteratedDeriv m (psum a z₀) =ᶠ[𝓝 z] psum (dcoeff^[m] a) z₀ :=
        eventually_of_mem hU fun w hw => ih w (by rwa [Metric.mem_eball, edist_eq_enorm_sub] at hw)
      rw [iteratedDeriv_succ, hev.deriv_eq, Function.iterate_succ_apply']
      exact (hasDerivAt_psum (hz.trans_le (le_pradius_iterate_dcoeff a m))).deriv
  rw [key m z h, psum]
  simp only [iterate_dcoeff_apply]

/-- **DLMF 1.9.48**: `aₙ = f^{(n)}(z₀)/n!` (for `R > 0`). -/
theorem dlmf_1_9_48 (a : ℕ → ℂ) (z₀ : ℂ) (hR : 0 < pradius a) (n : ℕ) :
    a n = iteratedDeriv n (psum a z₀) z₀ / n.factorial := by
  rw [dlmf_1_9_63 a z₀ n (by simpa using hR), tsum_eq_single 0 fun k hk => by simp [hk]]
  simp only [zero_add, Nat.one_ascFactorial, sub_self, pow_zero, mul_one]
  rw [mul_comm, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]

/-! ### Operations -/

/-- **DLMF 1.9.50**: `∑ (aₙ ± bₙ) zⁿ = ∑ aₙ zⁿ ± ∑ bₙ zⁿ` when both converge. -/
theorem dlmf_1_9_50 {a b : ℕ → ℂ} {z A B : ℂ} (ha : SeriesConverges (fun n => a n * z ^ n) A)
    (hb : SeriesConverges (fun n => b n * z ^ n) B) :
    SeriesConverges (fun n => (a n + b n) * z ^ n) (A + B) ∧
      SeriesConverges (fun n => (a n - b n) * z ^ n) (A - B) := by
  refine ⟨(ha.add hb).congr fun n => ?_, (ha.sub hb).congr fun n => ?_⟩
  · simp only [partialSum, ← sum_add_distrib, add_mul]
  · simp only [partialSum, ← sum_sub_distrib, sub_mul]

/-- **DLMF 1.9.52**: the Cauchy-product coefficients `cₙ = ∑_{k=0}^{n} a_k b_{n−k}`. -/
def cauchyCoeff (a b : ℕ → ℂ) (n : ℕ) : ℂ := ∑ k ∈ range (n + 1), a k * b (n - k)

theorem cauchyCoeff_mul_pow (a b : ℕ → ℂ) (z : ℂ) (n : ℕ) :
    ∑ k ∈ range (n + 1), a k * z ^ k * (b (n - k) * z ^ (n - k)) = cauchyCoeff a b n * z ^ n := by
  rw [cauchyCoeff, sum_mul]
  refine sum_congr rfl fun k hk => ?_
  rw [← pow_mul_pow_sub z (Nat.lt_succ_iff.mp (mem_range.mp hk))]
  ring

/-- **DLMF 1.9.51**: `(∑ aₙ zⁿ)(∑ bₙ zⁿ) = ∑ cₙ zⁿ` for absolutely convergent series (in
particular inside both circles of convergence); the product series converges absolutely. -/
theorem dlmf_1_9_51 {a b : ℕ → ℂ} {z : ℂ} (ha : SeriesConvergesAbsolutely fun n => a n * z ^ n)
    (hb : SeriesConvergesAbsolutely fun n => b n * z ^ n) :
    SeriesConverges (fun n => cauchyCoeff a b n * z ^ n)
        ((∑' n, a n * z ^ n) * ∑' n, b n * z ^ n) ∧
      SeriesConvergesAbsolutely fun n => cauchyCoeff a b n * z ^ n := by
  rw [seriesConvergesAbsolutely_iff] at ha hb ⊢
  have hs := summable_norm_sum_mul_range_of_summable_norm ha hb
  simp only [cauchyCoeff_mul_pow] at hs
  refine ⟨seriesConverges_iff.mpr ?_, hs⟩
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm ha hb]
  simp only [cauchyCoeff_mul_pow]
  exact hs.of_norm.hasSum.tendsto_sum_nat

/-- DLMF 1.9.51 inside both circles of convergence (center `0`). -/
theorem dlmf_1_9_51_psum {a b : ℕ → ℂ} {z : ℂ} (ha : (‖z‖₊ : ℝ≥0∞) < pradius a)
    (hb : (‖z‖₊ : ℝ≥0∞) < pradius b) :
    psum a 0 z * psum b 0 z = psum (cauchyCoeff a b) 0 z := by
  have ha' := summable_norm_term (z₀ := 0) (by simpa using ha)
  have hb' := summable_norm_term (z₀ := 0) (by simpa using hb)
  simp only [sub_zero] at ha' hb'
  unfold psum
  simp only [sub_zero]
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm ha' hb']
  simp only [cauchyCoeff_mul_pow]

/-! ### Coefficient growth from recursions -/

/-- If `|aₖ| ≤ M ρᵏ` (`k ≥ 1`), `|x₀| ≤ E` and
`|x_{n+1}| ≤ E ρ^{n+1} + B ∑_{k=0}^{n} |a_{k+1}| |x_{n−k}|`, then `|xₙ| ≤ E (ρ (1 + BM))ⁿ`. -/
theorem norm_le_of_recursion {a x : ℕ → ℂ} {M ρ E B : ℝ} (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hB : 0 ≤ B) (ha : ∀ k, ‖a (k + 1)‖ ≤ M * ρ ^ (k + 1)) (h0 : ‖x 0‖ ≤ E)
    (hrec : ∀ n, ‖x (n + 1)‖ ≤
      E * ρ ^ (n + 1) + B * ∑ k ∈ range (n + 1), ‖a (k + 1)‖ * ‖x (n - k)‖) :
    ∀ n, ‖x n‖ ≤ E * (ρ * (1 + B * M)) ^ n := by
  set c := 1 + B * M with hc
  have hc1 : 1 ≤ c := by rw [hc]; nlinarith
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simpa using h0
    have hsum : ∑ k ∈ range (n + 1), ‖a (k + 1)‖ * ‖x (n - k)‖ ≤
        M * E * ρ ^ (n + 1) * ∑ j ∈ range (n + 1), c ^ j := by
      rw [← sum_range_reflect (fun j => c ^ j) (n + 1), mul_sum]
      refine sum_le_sum fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
      have h1 := ih (n - k) (by omega)
      calc ‖a (k + 1)‖ * ‖x (n - k)‖ ≤ (M * ρ ^ (k + 1)) * (E * (ρ * c) ^ (n - k)) :=
            mul_le_mul (ha k) h1 (norm_nonneg _) (by positivity)
        _ = M * E * (ρ ^ (k + 1) * ρ ^ (n - k)) * c ^ (n - k) := by rw [mul_pow]; ring
        _ = M * E * ρ ^ (n + 1) * c ^ (n + 1 - 1 - k) := by
            rw [← pow_add, show k + 1 + (n - k) = n + 1 by omega,
              show n + 1 - 1 - k = n - k by omega]
    have hgeom : B * M * ∑ j ∈ range (n + 1), c ^ j = c ^ (n + 1) - 1 := by
      rw [← geom_sum_mul, hc]
      ring
    calc ‖x (n + 1)‖ ≤ E * ρ ^ (n + 1) +
          B * ∑ k ∈ range (n + 1), ‖a (k + 1)‖ * ‖x (n - k)‖ := hrec n
      _ ≤ E * ρ ^ (n + 1) + B * (M * E * ρ ^ (n + 1) * ∑ j ∈ range (n + 1), c ^ j) := by
          gcongr
      _ = E * ρ ^ (n + 1) * (1 + B * M * ∑ j ∈ range (n + 1), c ^ j) := by ring
      _ = E * (ρ * c) ^ (n + 1) := by rw [hgeom, mul_pow]; ring

theorem pradius_pos_of_bound {x : ℕ → ℂ} {E L : ℝ} (hL : 0 ≤ L)
    (h : ∀ n, ‖x n‖ ≤ E * L ^ n) : 0 < pradius x := by
  set r : ℝ≥0 := ⟨1 / (L + 1), by positivity⟩
  have hr : (0 : ℝ) < r := by show 0 < 1 / (L + 1); positivity
  have hLr : L * r ≤ 1 := by
    show L * (1 / (L + 1)) ≤ 1
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  have hr' : (0 : ℝ≥0∞) < r := ENNReal.coe_pos.mpr (by exact_mod_cast hr)
  refine lt_of_lt_of_le hr' (le_pradius_of_bound (max E 0) fun n => ?_)
  calc ‖x n‖ * (r : ℝ) ^ n ≤ E * L ^ n * (r : ℝ) ^ n := by gcongr; exact h n
    _ = E * (L * r) ^ n := by rw [mul_pow]; ring
    _ ≤ max E 0 * 1 := by
        refine mul_le_mul (le_max_left _ _) (pow_le_one₀ (by positivity) hLr) (by positivity)
          (le_max_right _ _)
    _ = max E 0 := mul_one _

/-- Coefficients of a series with positive radius grow at most geometrically. -/
theorem exists_coeff_bound {a : ℕ → ℂ} (hR : 0 < pradius a) :
    ∃ M ρ : ℝ, 0 ≤ M ∧ 0 ≤ ρ ∧ ∀ k, ‖a k‖ ≤ M * ρ ^ k := by
  obtain ⟨r, hr0, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hR
  have hr : (0 : ℝ) < r := by exact_mod_cast hr0
  have hs := summable_norm_mul_pow_of_lt hrR
  refine ⟨∑' n, ‖a n‖ * (r : ℝ) ^ n, 1 / r, tsum_nonneg fun n => by positivity, by positivity,
    fun k => ?_⟩
  have := hs.le_tsum k fun j _ => by positivity
  rw [div_pow, one_pow, mul_one_div, le_div_iff₀ (by positivity)]
  exact this

theorem sum_range_succ_reflect (f : ℕ → ℂ) (n : ℕ) :
    ∑ j ∈ range (n + 1), f j = ∑ k ∈ range (n + 1), f (n - k) := by
  rw [← sum_range_reflect f (n + 1)]
  simp only [Nat.add_sub_cancel]

theorem psum_zero_eq (a : ℕ → ℂ) : psum a 0 0 = a 0 := by
  rw [psum, tsum_eq_single 0 fun k hk => by simp [hk]]
  simp

/-! ### Reciprocal: 1.9.53–1.9.56 -/

/-- The coefficients `bₙ` of `1/f` (1.9.55–1.9.56). -/
noncomputable def recipCoeff (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => (a 0)⁻¹
  | n + 1 => -(∑ k : Fin (n + 1), a (n + 1 - k) * recipCoeff a k) / a 0

theorem recipCoeff_succ (a : ℕ → ℂ) (n : ℕ) :
    recipCoeff a (n + 1) = -(∑ k ∈ range (n + 1), a (n + 1 - k) * recipCoeff a k) / a 0 := by
  rw [recipCoeff, Fin.sum_univ_eq_sum_range (fun k => a (n + 1 - k) * recipCoeff a k)]

/-- **DLMF 1.9.56**: `bₙ = −(a₁ b_{n−1} + a₂ b_{n−2} + ⋯ + aₙ b₀)/a₀`, `n ≥ 1`. -/
theorem dlmf_1_9_56 (a : ℕ → ℂ) (n : ℕ) :
    recipCoeff a (n + 1) = -(∑ k ∈ range (n + 1), a (k + 1) * recipCoeff a (n - k)) / a 0 := by
  rw [recipCoeff_succ, sum_range_succ_reflect (fun k => a (n + 1 - k) * recipCoeff a k)]
  congr 2
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [show n + 1 - (n - k) = k + 1 by omega]

/-- **DLMF 1.9.55**: `b₀ = 1/a₀`, `b₁ = −a₁/a₀²`, `b₂ = (a₁² − a₀a₂)/a₀³`. -/
theorem dlmf_1_9_55 {a : ℕ → ℂ} (ha : a 0 ≠ 0) :
    recipCoeff a 0 = 1 / a 0 ∧ recipCoeff a 1 = -a 1 / a 0 ^ 2 ∧
      recipCoeff a 2 = (a 1 ^ 2 - a 0 * a 2) / a 0 ^ 3 := by
  refine ⟨by simp [recipCoeff], ?_, ?_⟩
  · rw [recipCoeff_succ]
    simp [recipCoeff]
    field_simp
  · rw [recipCoeff_succ, sum_range_succ, sum_range_one, recipCoeff_succ]
    simp [recipCoeff]
    field_simp
    ring

theorem cauchyCoeff_recipCoeff {a : ℕ → ℂ} (ha : a 0 ≠ 0) (n : ℕ) :
    cauchyCoeff a (recipCoeff a) n = if n = 0 then 1 else 0 := by
  rcases n with _ | n
  · simp [cauchyCoeff, recipCoeff, ha]
  · rw [cauchyCoeff, sum_range_succ']
    have e1 : ∀ k ∈ range (n + 1), a (k + 1) * recipCoeff a (n + 1 - (k + 1)) =
        a (k + 1) * recipCoeff a (n - k) := fun k _ => by rw [Nat.add_sub_add_right]
    rw [sum_congr rfl e1, Nat.sub_zero, dlmf_1_9_56]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    field_simp
    ring

theorem pradius_recipCoeff_pos {a : ℕ → ℂ} (ha : a 0 ≠ 0) (hR : 0 < pradius a) :
    0 < pradius (recipCoeff a) := by
  obtain ⟨M, ρ, hM, hρ, hb⟩ := exists_coeff_bound hR
  have hA : 0 < ‖a 0‖ := norm_pos_iff.mpr ha
  refine pradius_pos_of_bound (E := ‖a 0‖⁻¹) (by positivity)
    (norm_le_of_recursion (B := ‖a 0‖⁻¹) hM hρ (by positivity)
      (fun k => hb (k + 1)) (by simp [recipCoeff]) fun n => ?_)
  rw [dlmf_1_9_56, norm_div, norm_neg, div_eq_inv_mul]
  exact le_add_of_nonneg_of_le (by positivity) (mul_le_mul_of_nonneg_left
    ((norm_sum_le _ _).trans (sum_le_sum fun k _ => (norm_mul _ _).le)) (by positivity))

/-- Choose a positive radius below two given positive radii. -/
theorem exists_pos_lt_min {R₁ R₂ : ℝ≥0∞} (h₁ : 0 < R₁) (h₂ : 0 < R₂) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r → (‖z‖₊ : ℝ≥0∞) < R₁ ∧ (‖z‖₊ : ℝ≥0∞) < R₂ := by
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_min h₁ h₂)
  refine ⟨r, by exact_mod_cast hr0, fun z hz => ?_⟩
  have : (‖z‖₊ : ℝ≥0∞) < r := by exact_mod_cast hz
  exact ⟨this.trans (hr.trans_le (min_le_left _ _)), this.trans (hr.trans_le (min_le_right _ _))⟩

/-- **DLMF 1.9.53–1.9.54**: for `f(z) = a₀ + a₁z + ⋯` with `a₀ ≠ 0` (and positive radius),
`1/f(z) = b₀ + b₁z + ⋯` for all sufficiently small `|z|`. -/
theorem dlmf_1_9_54 {a : ℕ → ℂ} (ha : a 0 ≠ 0) (hR : 0 < pradius a) :
    ∃ r > 0, ∀ z : ℂ, ‖z‖ < r →
      SeriesConverges (fun n => recipCoeff a n * z ^ n) (1 / psum a 0 z) := by
  obtain ⟨r, hr, hz⟩ := exists_pos_lt_min hR (pradius_recipCoeff_pos ha hR)
  refine ⟨r, hr, fun z hzr => ?_⟩
  obtain ⟨h1, h2⟩ := hz z hzr
  have hprod := dlmf_1_9_51_psum h1 h2
  have hone : psum (cauchyCoeff a (recipCoeff a)) 0 z = 1 := by
    rw [psum, tsum_eq_single 0 fun k hk => by simp [cauchyCoeff_recipCoeff ha, hk]]
    simp [cauchyCoeff_recipCoeff ha]
  rw [hone] at hprod
  have hf : psum a 0 z ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hconv := (dlmf_1_9_vi_converges (z₀ := 0) (z := z) (by simpa using h2)).1
  simp only [sub_zero] at hconv
  rwa [eq_one_div_of_mul_eq_one_right hprod] at hconv

/-! ### Logarithm: 1.9.57–1.9.59 -/

/-- The coefficients `qₙ` of `ln f` (1.9.58–1.9.59), `q₀ = 0`. -/
noncomputable def logCoeff (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => ((n + 1) * a (n + 1) -
      ∑ k : Fin (n + 1), (k : ℂ) * a (n + 1 - k) * logCoeff a k) / (n + 1)

theorem logCoeff_succ (a : ℕ → ℂ) (n : ℕ) :
    logCoeff a (n + 1) = ((n + 1) * a (n + 1) -
      ∑ j ∈ range (n + 1), (j : ℂ) * a (n + 1 - j) * logCoeff a j) / (n + 1) := by
  rw [logCoeff, Fin.sum_univ_eq_sum_range (fun j => (j : ℂ) * a (n + 1 - j) * logCoeff a j)]

theorem sum_logCoeff_reflect (a : ℕ → ℂ) (n : ℕ) :
    ∑ j ∈ range (n + 1), (j : ℂ) * a (n + 1 - j) * logCoeff a j =
      ∑ k ∈ range n, ((n - k : ℕ) : ℂ) * a (k + 1) * logCoeff a (n - k) := by
  rw [sum_range_succ', Nat.cast_zero, zero_mul, zero_mul, add_zero,
    ← sum_range_reflect (fun k => ((n - k : ℕ) : ℂ) * a (k + 1) * logCoeff a (n - k)) n]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.mp hj
  rw [show n - (n - 1 - j) = j + 1 by omega, show n - 1 - j + 1 = n - j by omega,
    show n + 1 - (j + 1) = n - j by omega]

/-- **DLMF 1.9.59**: `qₙ = (n aₙ − (n−1) a₁ q_{n−1} − (n−2) a₂ q_{n−2} − ⋯ − a_{n−1} q₁)/n`
(stated for all `n ≥ 1`; DLMF lists `n ≥ 2`). -/
theorem dlmf_1_9_59 (a : ℕ → ℂ) (n : ℕ) :
    logCoeff a (n + 1) = ((n + 1) * a (n + 1) -
      ∑ k ∈ range n, ((n - k : ℕ) : ℂ) * a (k + 1) * logCoeff a (n - k)) / (n + 1) := by
  rw [logCoeff_succ, sum_logCoeff_reflect]

/-- **DLMF 1.9.58**: `q₁ = a₁`, `q₂ = (2a₂ − a₁²)/2`, `q₃ = (3a₃ − 3a₁a₂ + a₁³)/3`. -/
theorem dlmf_1_9_58 (a : ℕ → ℂ) :
    logCoeff a 1 = a 1 ∧ logCoeff a 2 = (2 * a 2 - a 1 ^ 2) / 2 ∧
      logCoeff a 3 = (3 * a 3 - 3 * a 1 * a 2 + a 1 ^ 3) / 3 := by
  have h1 : logCoeff a 1 = a 1 := by
    rw [dlmf_1_9_59]
    simp
  have h2 : logCoeff a 2 = (2 * a 2 - a 1 ^ 2) / 2 := by
    rw [dlmf_1_9_59]
    simp [h1]
    ring
  refine ⟨h1, h2, ?_⟩
  rw [dlmf_1_9_59]
  simp [sum_range_succ, h1, h2]
  ring

theorem cauchyCoeff_logCoeff {a : ℕ → ℂ} (ha : a 0 = 1) (n : ℕ) :
    cauchyCoeff a (dcoeff (logCoeff a)) n = dcoeff a n := by
  have hrec := logCoeff_succ a n
  have hn : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  rw [eq_div_iff hn, sum_logCoeff_reflect] at hrec
  rw [cauchyCoeff, sum_range_succ', dcoeff, dcoeff, Nat.sub_zero, ha]
  have e : ∀ k ∈ range n, a (k + 1) * dcoeff (logCoeff a) (n - (k + 1)) =
      ((n - k : ℕ) : ℂ) * a (k + 1) * logCoeff a (n - k) := fun k hk => by
    have hk := mem_range.mp hk
    rw [dcoeff, show n - (k + 1) + 1 = n - k by omega,
      show ((n - (k + 1) : ℕ) : ℂ) + 1 = ((n - k : ℕ) : ℂ) by
        rw [show n - k = n - (k + 1) + 1 by omega]; push_cast; ring]
    ring
  rw [sum_congr rfl e]
  linear_combination hrec

theorem pradius_logCoeff_pos {a : ℕ → ℂ} (hR : 0 < pradius a) : 0 < pradius (logCoeff a) := by
  obtain ⟨M, ρ, hM, hρ, hb⟩ := exists_coeff_bound hR
  refine pradius_pos_of_bound (E := M) (by positivity)
    (norm_le_of_recursion (B := 1) hM hρ zero_le_one (fun k => hb (k + 1))
      (by simp [logCoeff, hM]) fun n => ?_)
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [dlmf_1_9_59, norm_div, div_le_iff₀ (by rw [show ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 by
    exact_mod_cast Complex.norm_natCast (n + 1)]; exact hn)]
  rw [show ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 by exact_mod_cast Complex.norm_natCast (n + 1)]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, show ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 by exact_mod_cast Complex.norm_natCast (n + 1)]
  have hsum : ‖∑ k ∈ range n, ((n - k : ℕ) : ℂ) * a (k + 1) * logCoeff a (n - k)‖ ≤
      (n + 1) * ∑ k ∈ range (n + 1), ‖a (k + 1)‖ * ‖logCoeff a (n - k)‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum, sum_range_succ]
    refine le_add_of_le_of_nonneg (sum_le_sum fun k hk => ?_) (by positivity)
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    have : ((n - k : ℕ) : ℝ) ≤ n + 1 := by
      have := Nat.sub_le n k
      exact_mod_cast (Nat.cast_le.mpr this).trans (by linarith)
    calc ((n - k : ℕ) : ℝ) * ‖a (k + 1)‖ * ‖logCoeff a (n - k)‖
        ≤ (n + 1) * ‖a (k + 1)‖ * ‖logCoeff a (n - k)‖ := by gcongr
      _ = (n + 1) * (‖a (k + 1)‖ * ‖logCoeff a (n - k)‖) := by ring
  have := hb (n + 1)
  nlinarith

/-- The ball on which the expansions of `ln f` and `f^ν` are established. -/
theorem exists_ball_slitPlane {a x : ℕ → ℂ} (ha : a 0 = 1) (hR : 0 < pradius a)
    (hx : 0 < pradius x) :
    ∃ r > 0, ∀ z : ℂ, ‖z‖ < r → (‖z‖₊ : ℝ≥0∞) < pradius a ∧ (‖z‖₊ : ℝ≥0∞) < pradius x ∧
      psum a 0 z ∈ slitPlane := by
  obtain ⟨r₁, hr₁, h₁⟩ := exists_pos_lt_min hR hx
  have hc : ContinuousAt (psum a 0) 0 := (hasDerivAt_psum (z := 0) (by simpa using hR)).continuousAt
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hc 1 one_pos
  refine ⟨min r₁ δ, lt_min hr₁ hδ, fun z hz => ?_⟩
  obtain ⟨hza, hzx⟩ := h₁ z (hz.trans_le (min_le_left _ _))
  refine ⟨hza, hzx, ?_⟩
  have h1 := hδc (x := z) (by rw [dist_zero_right]; exact hz.trans_le (min_le_right _ _))
  rw [psum_zero_eq, ha, dist_eq_norm] at h1
  refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
  have := abs_re_le_norm (psum a 0 z - 1)
  rw [sub_re, one_re] at this
  linarith [(abs_sub_lt_iff.mp (this.trans_lt h1)).2]

theorem psum_mul_left (c : ℂ) (a : ℕ → ℂ) (z₀ z : ℂ) :
    psum (fun n => c * a n) z₀ z = c * psum a z₀ z := by
  unfold psum
  simp_rw [mul_assoc]
  exact tsum_mul_left

/-- **DLMF 1.9.57**: with `a₀ = 1`, `ln f(z) = q₁z + q₂z² + ⋯` (principal value) for all
sufficiently small `|z|`. -/
theorem dlmf_1_9_57 {a : ℕ → ℂ} (ha : a 0 = 1) (hR : 0 < pradius a) :
    ∃ r > 0, ∀ z : ℂ, ‖z‖ < r →
      SeriesConverges (fun n => logCoeff a n * z ^ n) (log (psum a 0 z)) := by
  set q := logCoeff a
  obtain ⟨r, hr, hU⟩ := exists_ball_slitPlane ha hR (pradius_logCoeff_pos hR)
  have hmem : ∀ z ∈ ball (0 : ℂ) r, ‖z‖ < r := fun z hz => by rwa [mem_ball, dist_zero_right] at hz
  have hdq : ∀ z ∈ ball (0 : ℂ) r, HasDerivAt (psum q 0) (psum (dcoeff q) 0 z) z := fun z hz =>
    hasDerivAt_psum (by simpa using (hU z (hmem z hz)).2.1)
  have hdf : ∀ z ∈ ball (0 : ℂ) r, HasDerivAt (psum a 0) (psum (dcoeff a) 0 z) z := fun z hz =>
    hasDerivAt_psum (by simpa using (hU z (hmem z hz)).1)
  have hdl : ∀ z ∈ ball (0 : ℂ) r, HasDerivAt (fun w => log (psum a 0 w))
      ((psum a 0 z)⁻¹ * psum (dcoeff a) 0 z) z := fun z hz =>
    (hasDerivAt_log (hU z (hmem z hz)).2.2).comp z (hdf z hz)
  have hkey : ∀ z ∈ ball (0 : ℂ) r,
      psum (dcoeff q) 0 z = (psum a 0 z)⁻¹ * psum (dcoeff a) 0 z := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hU z (hmem z hz)
    have hprod := dlmf_1_9_51_psum h1 (h2.trans_le (le_pradius_dcoeff q))
    have hc : cauchyCoeff a (dcoeff q) = dcoeff a := funext (cauchyCoeff_logCoeff ha)
    rw [hc] at hprod
    rw [← hprod, ← mul_assoc, inv_mul_cancel₀ (slitPlane_ne_zero h3), one_mul]
  have heq : EqOn (psum q 0) (fun w => log (psum a 0 w)) (ball 0 r) := by
    refine isOpen_ball.eqOn_of_deriv_eq (convex_ball _ _).isPreconnected
      (fun z hz => (hdq z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hdl z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => by rw [(hdq z hz).deriv, (hdl z hz).deriv, hkey z hz])
      (mem_ball_self hr) ?_
    simp only [psum_zero_eq, ha, log_one, q]
    rw [logCoeff]
  refine ⟨r, hr, fun z hz => ?_⟩
  have hconv := (dlmf_1_9_vi_converges (z₀ := 0) (z := z) (by simpa using (hU z hz).2.1)).1
  simp only [sub_zero] at hconv
  rwa [heq (by rwa [mem_ball, dist_zero_right])] at hconv

/-! ### Powers: 1.9.60–1.9.62 -/

/-- The coefficients `pₙ` of `f^ν` (1.9.61–1.9.62), `p₀ = 1`. -/
noncomputable def powCoeff (ν : ℂ) (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => (∑ k : Fin (n + 1),
      (((n + 1 - k : ℕ) : ℂ) * ν - k) * a (n + 1 - k) * powCoeff ν a k) / (n + 1)

/-- **DLMF 1.9.62**: `pₙ = ((ν−n+1)a₁p_{n−1} + (2ν−n+2)a₂p_{n−2} + ⋯ + nνaₙ)/n`, i.e.
`pₙ = (1/n) ∑_{k=1}^{n} (kν − (n − k)) aₖ p_{n−k}`. -/
theorem dlmf_1_9_62 (ν : ℂ) (a : ℕ → ℂ) (n : ℕ) :
    powCoeff ν a (n + 1) = (∑ k ∈ range (n + 1),
      (((k + 1 : ℕ) : ℂ) * ν - ((n - k : ℕ) : ℂ)) * a (k + 1) * powCoeff ν a (n - k)) /
        (n + 1) := by
  rw [powCoeff, Fin.sum_univ_eq_sum_range
    (fun j => (((n + 1 - j : ℕ) : ℂ) * ν - j) * a (n + 1 - j) * powCoeff ν a j),
    sum_range_succ_reflect]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  have hk := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [show n + 1 - (n - k) = k + 1 by omega]

/-- **DLMF 1.9.61**: `p₀ = 1`, `p₁ = νa₁`, `p₂ = ν((ν − 1)a₁² + 2a₂)/2` (the recursion only
involves `a₁, a₂, …`). -/
theorem dlmf_1_9_61 (ν : ℂ) (a : ℕ → ℂ) :
    powCoeff ν a 0 = 1 ∧ powCoeff ν a 1 = ν * a 1 ∧
      powCoeff ν a 2 = ν * ((ν - 1) * a 1 ^ 2 + 2 * a 2) / 2 := by
  have h1 : powCoeff ν a 1 = ν * a 1 := by
    rw [dlmf_1_9_62]
    simp [powCoeff]
  refine ⟨by rw [powCoeff], h1, ?_⟩
  rw [dlmf_1_9_62]
  simp [sum_range_succ, h1, powCoeff]
  ring

theorem cauchyCoeff_powCoeff (ν : ℂ) {a : ℕ → ℂ} (ha : a 0 = 1) (n : ℕ) :
    cauchyCoeff a (dcoeff (powCoeff ν a)) n = ν * cauchyCoeff (dcoeff a) (powCoeff ν a) n := by
  have hrec := dlmf_1_9_62 ν a n
  have hn : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  rw [eq_div_iff hn] at hrec
  have hext : ∑ k ∈ range (n + 1), ((n - k : ℕ) : ℂ) * a (k + 1) * powCoeff ν a (n - k) =
      ∑ k ∈ range n, ((n - k : ℕ) : ℂ) * a (k + 1) * powCoeff ν a (n - k) := by
    rw [sum_range_succ]
    simp
  have hsplit : ∑ k ∈ range (n + 1),
      (((k + 1 : ℕ) : ℂ) * ν - ((n - k : ℕ) : ℂ)) * a (k + 1) * powCoeff ν a (n - k) =
      ν * ∑ k ∈ range (n + 1), dcoeff a k * powCoeff ν a (n - k) -
        ∑ k ∈ range n, ((n - k : ℕ) : ℂ) * a (k + 1) * powCoeff ν a (n - k) := by
    rw [← hext, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    simp only [dcoeff]
    push_cast
    ring
  rw [cauchyCoeff, cauchyCoeff, sum_range_succ', dcoeff, Nat.sub_zero, ha]
  have e : ∀ k ∈ range n, a (k + 1) * dcoeff (powCoeff ν a) (n - (k + 1)) =
      ((n - k : ℕ) : ℂ) * a (k + 1) * powCoeff ν a (n - k) := fun k hk => by
    have hk := mem_range.mp hk
    rw [dcoeff, show n - (k + 1) + 1 = n - k by omega,
      show ((n - (k + 1) : ℕ) : ℂ) + 1 = ((n - k : ℕ) : ℂ) by
        rw [show n - k = n - (k + 1) + 1 by omega]; push_cast; ring]
    ring
  rw [sum_congr rfl e]
  linear_combination hrec + hsplit

theorem pradius_powCoeff_pos (ν : ℂ) {a : ℕ → ℂ} (hR : 0 < pradius a) :
    0 < pradius (powCoeff ν a) := by
  obtain ⟨M, ρ, hM, hρ, hb⟩ := exists_coeff_bound hR
  refine pradius_pos_of_bound (E := 1) (by positivity)
    (norm_le_of_recursion (B := ‖ν‖ + 1) hM hρ (by positivity) (fun k => hb (k + 1))
      (by simp [powCoeff]) fun n => ?_)
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hnorm : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (n + 1)
  rw [dlmf_1_9_62, norm_div, hnorm, div_le_iff₀ hn]
  have hsum : ‖∑ k ∈ range (n + 1), (((k + 1 : ℕ) : ℂ) * ν - ((n - k : ℕ) : ℂ)) * a (k + 1) *
      powCoeff ν a (n - k)‖ ≤ (n + 1) * ((‖ν‖ + 1) *
        ∑ k ∈ range (n + 1), ‖a (k + 1)‖ * ‖powCoeff ν a (n - k)‖) := by
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun k hk => ?_
    have hk := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [norm_mul, norm_mul]
    have hc : ‖((k + 1 : ℕ) : ℂ) * ν - ((n - k : ℕ) : ℂ)‖ ≤ (‖ν‖ + 1) * (n + 1) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
      have h1 : ((k + 1 : ℕ) : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ hk
      have h2 : ((n - k : ℕ) : ℝ) ≤ n + 1 := by
        exact_mod_cast (Nat.cast_le.mpr (Nat.sub_le n k)).trans (by linarith)
      nlinarith [norm_nonneg ν]
    calc ‖((k + 1 : ℕ) : ℂ) * ν - ((n - k : ℕ) : ℂ)‖ * ‖a (k + 1)‖ * ‖powCoeff ν a (n - k)‖
        ≤ (‖ν‖ + 1) * (n + 1) * ‖a (k + 1)‖ * ‖powCoeff ν a (n - k)‖ := by gcongr
      _ = (n + 1) * ((‖ν‖ + 1) * (‖a (k + 1)‖ * ‖powCoeff ν a (n - k)‖)) := by ring
  have hρn : 0 ≤ 1 * ρ ^ (n + 1) := by positivity
  nlinarith

/-- **DLMF 1.9.60**: with `a₀ = 1`, `(f(z))^ν = p₀ + p₁z + p₂z² + ⋯` (principal value) for all
sufficiently small `|z|`. -/
theorem dlmf_1_9_60 (ν : ℂ) {a : ℕ → ℂ} (ha : a 0 = 1) (hR : 0 < pradius a) :
    ∃ r > 0, ∀ z : ℂ, ‖z‖ < r →
      SeriesConverges (fun n => powCoeff ν a n * z ^ n) (psum a 0 z ^ ν) := by
  set p := powCoeff ν a
  obtain ⟨r, hr, hU⟩ := exists_ball_slitPlane ha hR (pradius_powCoeff_pos ν hR)
  have hmem : ∀ z ∈ ball (0 : ℂ) r, ‖z‖ < r := fun z hz => by rwa [mem_ball, dist_zero_right] at hz
  have hdp : ∀ z ∈ ball (0 : ℂ) r, HasDerivAt (psum p 0) (psum (dcoeff p) 0 z) z := fun z hz =>
    hasDerivAt_psum (by simpa using (hU z (hmem z hz)).2.1)
  have hdf : ∀ z ∈ ball (0 : ℂ) r, HasDerivAt (psum a 0) (psum (dcoeff a) 0 z) z := fun z hz =>
    hasDerivAt_psum (by simpa using (hU z (hmem z hz)).1)
  set E : ℂ → ℂ := fun w => exp (-(ν * log (psum a 0 w))) with hE
  have hdE : ∀ z ∈ ball (0 : ℂ) r, HasDerivAt E
      (E z * -(ν * ((psum a 0 z)⁻¹ * psum (dcoeff a) 0 z))) z := fun z hz =>
    (((hasDerivAt_log (hU z (hmem z hz)).2.2).comp z (hdf z hz)).const_mul ν).neg.cexp
  have hkey : ∀ z ∈ ball (0 : ℂ) r,
      psum a 0 z * psum (dcoeff p) 0 z = ν * (psum (dcoeff a) 0 z * psum p 0 z) := by
    intro z hz
    obtain ⟨h1, h2, _⟩ := hU z (hmem z hz)
    rw [dlmf_1_9_51_psum h1 (h2.trans_le (le_pradius_dcoeff p)),
      dlmf_1_9_51_psum (h1.trans_le (le_pradius_dcoeff a)) h2, ← psum_mul_left]
    congr 1
    exact funext (cauchyCoeff_powCoeff ν ha)
  have hd0 : ∀ z ∈ ball (0 : ℂ) r, HasDerivAt (fun w => psum p 0 w * E w) 0 z := by
    intro z hz
    have hf0 := slitPlane_ne_zero (hU z (hmem z hz)).2.2
    convert (hdp z hz).mul (hdE z hz) using 1
    have hP' : psum (dcoeff p) 0 z = ν * (psum (dcoeff a) 0 z * psum p 0 z) / psum a 0 z := by
      rw [eq_div_iff hf0, mul_comm]
      exact hkey z hz
    rw [hP']
    field_simp
    ring
  have hconst : ∀ z ∈ ball (0 : ℂ) r, psum p 0 z * E z = 1 := by
    intro z hz
    have := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
      (fun w hw => (hd0 w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hd0 w hw).deriv) hz (mem_ball_self hr)
    rw [this]
    have hp0 : powCoeff ν a 0 = 1 := by rw [powCoeff]
    simp [hE, psum_zero_eq, ha, p, hp0]
  refine ⟨r, hr, fun z hz => ?_⟩
  have hzU : z ∈ ball (0 : ℂ) r := by rwa [mem_ball, dist_zero_right]
  have hconv := (dlmf_1_9_vi_converges (z₀ := 0) (z := z) (by simpa using (hU z hz).2.1)).1
  simp only [sub_zero] at hconv
  have hP : psum p 0 z = psum a 0 z ^ ν := by
    rw [cpow_def_of_ne_zero (slitPlane_ne_zero (hU z hz).2.2)]
    have h1 : psum p 0 z * exp (-(ν * log (psum a 0 z))) = 1 := hconst z hzU
    rw [exp_neg, mul_inv_eq_one₀ (exp_ne_zero _)] at h1
    rw [h1, mul_comm]
  rwa [hP] at hconv

end Azurite.DLMF
