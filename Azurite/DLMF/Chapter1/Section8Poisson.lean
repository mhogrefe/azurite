/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section8
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# DLMF §1.8(iv): Poisson's Summation Formula

Formalizations of <https://dlmf.nist.gov/1.8.iv> (1.8.13 was moved by DLMF to 1.8.6_1).

* 1.8.14 `dlmf_1_8_14`: for `f ∈ C²` with `f`, `f″` integrable over `ℝ`, both series converge and
  `∑ₙ f(x + n) = ∑ₙ e^{2πinx} ∫ f(t) e^{−2πint} dt`.  The extra regularity Mathlib's
  `Real.tsum_eq_tsum_fourier` needs is derived from DLMF's hypotheses.
  - On every unit interval, `‖f‖ ≤ ∫ ‖f‖ + ∫ ‖f′‖` (`norm_le_integral_add`) and
    `‖f′‖ ≤ 6 ∫ ‖f‖ + ∫ ‖f″‖` (`norm_deriv_le_integral`, integration by parts against the weight
    `6(t − a)(a + 1 − t)`).
  - Hence `f′` is integrable and the translates of `f` are summable on compacts (`poisson_aux`).
  - `|∫ f e^{−2πint}| ≤ ∫ |f″| / (4π²n²)` gives summability of the coefficients.
* `dlmf_1_8_iv_fourier`: the integral in 1.8.14 is `√(2π) 𝓕(f)(−2πn)` for DLMF's transform 1.14.1.
* 1.8.15 `dlmf_1_8_15`: for `f` continuous, of bounded variation and integrable on `[0, ∞)`:
  `½f(0) + ∑_{n ≥ 1} f(n) = ∫₀^∞ f + 2 ∑_{n ≥ 1} ∫₀^∞ f(x) cos(2πnx) dx`.  The right-hand series
  converges conditionally, so it is stated through its partial sums.  DLMF's `f(x) → 0` is implied.
  The proof goes through **Jordan's test**:
  - the period-one Dirichlet kernel `dirichlet1` has partial integrals bounded by `2` on
    `[0, ½]` (`abs_integral_dirichlet1_le`, via Mathlib's second mean value theorem);
  - with Riemann–Lebesgue, `∫₀^{1/2} h Dₖ → h(0+)/2` for monotone `h`
    (`tendsto_integral_monotone_mul_dirichlet1`), then `∫₀^{1/2} g Dₖ → g(0)/2` for `g` of bounded
    variation and continuous at `0` (`tendsto_integral_bv_mul_dirichlet1`, through the variation
    decomposition), with a uniform bound (`abs_integral_bv_mul_dirichlet1_le`).
  Each `[n, n+1]` contributes `(f(n) + f(n+1))/2` in the limit (`tendsto_piece`).  Tannery's theorem
  (`tendsto_tsum_of_dominated_convergence`) sums the pieces, dominated by `|f(n)|` and the
  variation on `[n, n+1]`.
* 1.8.16 `dlmf_1_8_16`: `∑ₙ e^{−(n+x)²ω} = √(π/ω)(1 + 2∑_{n ≥ 1} e^{−n²π²/ω} cos(2nπx))`,
  `ℜω > 0`, complex `x`, from Mathlib's `Complex.tsum_exp_neg_quadratic` and the summability of
  the Jacobi theta series.
-/

namespace Azurite.DLMF

open MeasureTheory Set Filter Topology Real
open scoped FourierTransform

/-! ### Bounds on unit intervals -/

theorem norm_sub_le_integral_norm {g g' : ℝ → ℂ} (hd : ∀ x, HasDerivAt g (g' x) x)
    (hc : Continuous g') {a x t : ℝ} (hx : x ∈ Icc a (a + 1)) (ht : t ∈ Icc a (a + 1)) :
    ‖g x - g t‖ ≤ ∫ s in a..a + 1, ‖g' s‖ := by
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable _ _)]
  refine intervalIntegral.norm_integral_le_integral_norm_uIoc.trans ?_
  rw [intervalIntegral.integral_of_le (by linarith : a ≤ a + 1)]
  refine setIntegral_mono_set (hc.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (ae_of_all _ fun _ => norm_nonneg _) (ae_of_all _ fun s (hs : s ∈ Set.uIoc t x) => ?_)
  rw [Set.mem_uIoc] at hs
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by linarith [ht.1], by linarith [hx.2]⟩
  · exact ⟨by linarith [hx.1], by linarith [ht.2]⟩

/-- On a unit interval, `‖g x‖ ≤ ∫ ‖g‖ + ∫ ‖g′‖`. -/
theorem norm_le_integral_add {g g' : ℝ → ℂ} (hd : ∀ x, HasDerivAt g (g' x) x)
    (hc : Continuous g') {a x : ℝ} (hx : x ∈ Icc a (a + 1)) :
    ‖g x‖ ≤ (∫ t in a..a + 1, ‖g t‖) + ∫ t in a..a + 1, ‖g' t‖ := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  set V := ∫ s in a..a + 1, ‖g' s‖
  have hpt : ∀ t ∈ Icc a (a + 1), ‖g x‖ ≤ ‖g t‖ + V := fun t ht => by
    have h1 := norm_sub_le_integral_norm hd hc hx ht
    calc ‖g x‖ = ‖g t + (g x - g t)‖ := by ring_nf
      _ ≤ ‖g t‖ + ‖g x - g t‖ := norm_add_le _ _
      _ ≤ ‖g t‖ + V := by linarith
  calc ‖g x‖ = ∫ _ in a..a + 1, ‖g x‖ := by simp
    _ ≤ ∫ t in a..a + 1, (‖g t‖ + V) :=
        intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
          ((hgc.norm.intervalIntegrable _ _).add intervalIntegrable_const) hpt
    _ = (∫ t in a..a + 1, ‖g t‖) + V := by
        rw [intervalIntegral.integral_add (hgc.norm.intervalIntegrable _ _)
          intervalIntegrable_const]
        simp

/-- On a unit interval, `‖f′ x‖ ≤ 6 ∫ ‖f‖ + ∫ ‖f″‖` (integration by parts against the weight
`6 (t − a)(a + 1 − t)`). -/
theorem norm_deriv_le_integral {f f' f'' : ℝ → ℂ} (hd : ∀ x, HasDerivAt f (f' x) x)
    (hd' : ∀ x, HasDerivAt f' (f'' x) x) (hc : Continuous f'') {a x : ℝ}
    (hx : x ∈ Icc a (a + 1)) :
    ‖f' x‖ ≤ 6 * (∫ t in a..a + 1, ‖f t‖) + ∫ t in a..a + 1, ‖f'' t‖ := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hf'c : Continuous f' := continuous_iff_continuousAt.mpr fun x => (hd' x).continuousAt
  have hab : a ≤ a + 1 := by linarith
  set V := ∫ s in a..a + 1, ‖f'' s‖
  set φ : ℝ → ℝ := fun t => 6 * (t - a) * (a + 1 - t)
  set φ' : ℝ → ℝ := fun t => 6 * (2 * a + 1 - 2 * t)
  have hφd : ∀ t, HasDerivAt (fun t => (φ t : ℂ)) (φ' t : ℂ) t := fun t => by
    have : HasDerivAt φ (φ' t) t := by
      have h := ((((hasDerivAt_id t).sub_const a).const_mul 6).mul
        ((hasDerivAt_id t).const_sub (a + 1)))
      convert h using 1
      · funext y; simp only [φ, Pi.mul_apply, id]
      · simp only [φ', id]; ring
    exact this.ofReal_comp
  have hφc : Continuous φ := by fun_prop
  have hφ'c : Continuous φ' := by fun_prop
  -- `∫ φ = 1`
  have hint1 : ∫ t in a..a + 1, φ t = 1 := by
    have hF : ∀ t, HasDerivAt (fun t => 3 * (t - a) ^ 2 - 2 * (t - a) ^ 3) (φ t) t := fun t => by
      have h := ((((hasDerivAt_id t).sub_const a).pow 2).const_mul 3).sub
        ((((hasDerivAt_id t).sub_const a).pow 3).const_mul 2)
      convert h using 1
      · funext y; simp only [Pi.sub_apply, Pi.pow_apply, id]
      · simp only [φ, id]; norm_num; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)
      (hφc.intervalIntegrable _ _)]
    ring
  -- integration by parts: `∫ φ f′ = −∫ φ′ f`
  have hibp : ∫ t in a..a + 1, (φ t : ℂ) * f' t = -∫ t in a..a + 1, (φ' t : ℂ) * f t := by
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t _ => hφd t) (fun t _ => hd t)
      ((Complex.continuous_ofReal.comp hφ'c).intervalIntegrable _ _)
      (hf'c.intervalIntegrable _ _)]
    simp [φ]
  have hsplit : f' x = (∫ t in a..a + 1, (φ t : ℂ) * f' t) +
      ∫ t in a..a + 1, (φ t : ℂ) * (f' x - f' t) := by
    have i1 : IntervalIntegrable (fun t => (φ t : ℂ) * f' t) volume a (a + 1) :=
      (show Continuous fun t => (φ t : ℂ) * f' t from
        (Complex.continuous_ofReal.comp hφc).mul hf'c).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t => (φ t : ℂ) * (f' x - f' t)) volume a (a + 1) :=
      (show Continuous fun t => (φ t : ℂ) * (f' x - f' t) from
        (Complex.continuous_ofReal.comp hφc).mul (continuous_const.sub hf'c)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add i1 i2]
    have : ∀ t, (φ t : ℂ) * f' t + (φ t : ℂ) * (f' x - f' t) = (φ t : ℂ) * f' x :=
      fun t => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, hint1]
    simp
  have hb1 : ‖∫ t in a..a + 1, (φ' t : ℂ) * f t‖ ≤ 6 * ∫ t in a..a + 1, ‖f t‖ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le hab (ae_of_all _ fun t ht => ?_)
      ((hfc.norm.intervalIntegrable _ _).const_mul 6)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    simp only [φ', abs_le]
    constructor <;> nlinarith [ht.1, ht.2]
  have hb2 : ‖∫ t in a..a + 1, (φ t : ℂ) * (f' x - f' t)‖ ≤ V := by
    calc ‖∫ t in a..a + 1, (φ t : ℂ) * (f' x - f' t)‖ ≤ ∫ t in a..a + 1, φ t * V :=
          intervalIntegral.norm_integral_le_of_norm_le hab (ae_of_all _ fun t ht => by
            have hφ0 : 0 ≤ φ t := by
              simp only [φ]; have := ht.1; have := ht.2; positivity
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hφ0]
            exact mul_le_mul_of_nonneg_left
              (norm_sub_le_integral_norm hd' hc hx (Ioc_subset_Icc_self ht)) hφ0)
          ((hφc.intervalIntegrable _ _).mul_const V)
      _ = V := by rw [intervalIntegral.integral_mul_const, hint1, one_mul]
  rw [hsplit, hibp]
  calc ‖-(∫ t in a..a + 1, (φ' t : ℂ) * f t) + ∫ t in a..a + 1, (φ t : ℂ) * (f' x - f' t)‖
      ≤ ‖∫ t in a..a + 1, (φ' t : ℂ) * f t‖ + ‖∫ t in a..a + 1, (φ t : ℂ) * (f' x - f' t)‖ := by
        rw [← norm_neg (∫ t in a..a + 1, (φ' t : ℂ) * f t)]
        exact norm_add_le _ _
    _ ≤ 6 * (∫ t in a..a + 1, ‖f t‖) + V := add_le_add hb1 hb2

/-- `n ↦ ∫_n^{n+1} ‖h‖` is summable over `ℤ` for integrable `h`. -/
theorem summable_integral_norm_Ioc {h : ℝ → ℂ} (hh : Integrable h) :
    Summable fun n : ℤ => ∫ t in (n : ℝ)..(n + 1), ‖h t‖ := by
  have := hasSum_integral_iUnion (μ := volume) (f := fun t => ‖h t‖)
    (fun n : ℤ => measurableSet_Ioc (a := (n : ℝ)) (b := n + 1)) (pairwise_disjoint_Ioc_intCast ℝ)
    (by rw [iUnion_Ioc_intCast]; exact hh.norm.integrableOn)
  refine this.summable.congr fun n => ?_
  rw [intervalIntegral.integral_of_le (by linarith)]

theorem integral_norm_nonneg' (h : ℝ → ℂ) (n : ℤ) : 0 ≤ ∫ t in (n : ℝ)..(n + 1), ‖h t‖ :=
  intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _

theorem norm_fourier_le (g : ℝ → ℂ) (w : ℝ) : ‖𝓕 g w‖ ≤ ∫ t, ‖g t‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext t
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-! ### 1.8.14 -/

/-- For `f ∈ C²` with `f` and `f″` integrable, `f′` is integrable and the bounds
`∫_n^{n+1} ‖f‖ + ∫_n^{n+1} ‖f′‖` on `sup_{[n, n+1]} ‖f‖` are summable over `n ∈ ℤ`. -/
theorem poisson_aux {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfi : Integrable f)
    (hf''i : Integrable (deriv (deriv f))) :
    Integrable (deriv f) ∧ Summable (fun n : ℤ =>
      (∫ t in (n : ℝ)..(n + 1), ‖f t‖) + ∫ t in (n : ℝ)..(n + 1), ‖deriv f t‖) := by
  have hf1 : ContDiff ℝ 1 (deriv f) := ContDiff.deriv' (n := 1) (by convert hf; norm_num)
  have hd : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
    (hf.differentiable (by norm_num) x).hasDerivAt
  have hd' : ∀ x, HasDerivAt (deriv f) (deriv (deriv f) x) x := fun x =>
    (hf1.differentiable one_ne_zero x).hasDerivAt
  have hc'' : Continuous (deriv (deriv f)) := hf1.continuous_deriv le_rfl
  have hS1 := summable_integral_norm_Ioc hfi
  have hS2 := summable_integral_norm_Ioc hf''i
  have hint : Integrable (deriv f) := by
    let F : C(ℝ, ℂ) := ⟨deriv f, hf1.continuous⟩
    refine Real.integrable_of_summable_norm_Icc (f := F) ?_
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((hS1.mul_left 6).add hS2)
    refine (ContinuousMap.norm_le _ (add_nonneg (mul_nonneg (by norm_num)
      (integral_norm_nonneg' f n)) (integral_norm_nonneg' _ n))).mpr fun y => ?_
    have hy : (y : ℝ) + n ∈ Icc (n : ℝ) (n + 1) := ⟨by linarith [y.2.1], by linarith [y.2.2]⟩
    exact norm_deriv_le_integral hd hd' hc'' hy
  exact ⟨hint, hS1.add (summable_integral_norm_Ioc hint)⟩

/-- **DLMF 1.8.14** (Poisson's summation formula): if `f` is twice continuously differentiable and
`f`, `f″` are integrable over `ℝ`, then both series converge and
`∑ₙ f(x + n) = ∑ₙ e^{2πinx} ∫ f(t) e^{−2πint} dt`. -/
theorem dlmf_1_8_14 {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfi : Integrable f)
    (hf''i : Integrable (deriv (deriv f))) (x : ℝ) :
    Summable (fun n : ℤ => f (x + n)) ∧
      Summable (fun n : ℤ => Complex.exp (2 * π * Complex.I * n * x) *
        ∫ t, f t * Complex.exp (-2 * π * Complex.I * n * t)) ∧
      ∑' n : ℤ, f (x + n) = ∑' n : ℤ, Complex.exp (2 * π * Complex.I * n * x) *
        ∫ t, f t * Complex.exp (-2 * π * Complex.I * n * t) := by
  obtain ⟨hf'i, hT⟩ := poisson_aux hf hfi hf''i
  have hf1 : ContDiff ℝ 1 (deriv f) := ContDiff.deriv' (n := 1) (by convert hf; norm_num)
  have hd : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
    (hf.differentiable (by norm_num) x).hasDerivAt
  set T : ℤ → ℝ := fun n =>
    (∫ t in (n : ℝ)..(n + 1), ‖f t‖) + ∫ t in (n : ℝ)..(n + 1), ‖deriv f t‖
  have hT0 : ∀ n, 0 ≤ T n := fun n =>
    add_nonneg (integral_norm_nonneg' f n) (integral_norm_nonneg' _ n)
  have hpt : ∀ y : ℝ, ‖f y‖ ≤ T ⌊y⌋ := fun y => by
    have hy : y ∈ Icc (⌊y⌋ : ℝ) (⌊y⌋ + 1) := ⟨Int.floor_le y, (Int.lt_floor_add_one y).le⟩
    exact norm_le_integral_add hd hf1.continuous hy
  -- uniform summability on compacts
  have h_norm : ∀ K : TopologicalSpace.Compacts ℝ, Summable fun n : ℤ =>
      ‖((⟨f, hf.continuous⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))).restrict K‖ := by
    intro K
    obtain ⟨r, hr⟩ := K.isCompact.isBounded.subset_closedBall 0
    set M : ℤ := ⌈r⌉
    have hfl : ∀ y ∈ K, ⌊y⌋ ∈ Finset.Icc (-M) M := fun y hy => by
      have h := hr hy
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at h
      rw [Finset.mem_Icc]
      constructor
      · have : (-(M : ℝ)) ≤ y := by linarith [Int.le_ceil r]
        exact Int.le_floor.mpr (by exact_mod_cast this)
      · exact (Int.floor_le_floor h.2).trans (Int.floor_le_ceil r)
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (summable_sum fun k _ => hT.comp_injective (add_right_injective k) :
        Summable fun n : ℤ => ∑ k ∈ Finset.Icc (-M) M, T (k + n))
    refine (ContinuousMap.norm_le _ (Finset.sum_nonneg fun k _ => hT0 _)).mpr fun y => ?_
    simp only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_addRight, ContinuousMap.coe_mk]
    refine (hpt _).trans ?_
    rw [Int.floor_add_intCast]
    exact Finset.single_le_sum (f := fun k => T (k + n)) (fun k _ => hT0 _) (hfl y y.2)
  -- summability of the Fourier transform at the integers
  have hF1 := Real.fourier_deriv hfi (hf.differentiable (by norm_num)) hf'i
  have hF2 := Real.fourier_deriv hf'i (hf1.differentiable one_ne_zero) hf''i
  set C := ∫ t, ‖deriv (deriv f) t‖
  have h_sum : Summable fun n : ℤ => 𝓕 f n := by
    have hsq : Summable fun n : ℤ => 1 / (n : ℝ) ^ 2 :=
      Real.summable_one_div_int_pow.mpr one_lt_two
    refine Summable.of_norm_bounded_eventually (hsq.mul_left (C / (4 * π ^ 2))) ?_
    filter_upwards [eventually_cofinite_ne 0] with n hn
    have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have hnr : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have heq : 𝓕 (deriv (deriv f)) n = (2 * π * Complex.I * n) ^ 2 * 𝓕 f n := by
      rw [hF2, hF1]; simp only [smul_eq_mul]; push_cast; ring
    have hk : (2 * π * Complex.I * n) ^ 2 ≠ 0 := by
      apply pow_ne_zero; apply mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_)
        Complex.I_ne_zero) hn'
      exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hFn : 𝓕 f n = 𝓕 (deriv (deriv f)) n / (2 * π * Complex.I * n) ^ 2 := by
      rw [heq]; field_simp
    rw [hFn, norm_div, norm_pow]
    have hnorm : ‖2 * π * Complex.I * (n : ℂ)‖ ^ 2 = 4 * π ^ 2 * (n : ℝ) ^ 2 := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_intCast,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      simp only [Complex.norm_ofNat, mul_one]
      rw [mul_pow, mul_pow, sq_abs]
      ring
    rw [hnorm, div_le_iff₀ (by positivity)]
    have hb := norm_fourier_le (deriv (deriv f)) n
    have : C / (4 * π ^ 2) * (1 / (n : ℝ) ^ 2) * (4 * π ^ 2 * (n : ℝ) ^ 2) = C := by
      field_simp
    linarith
  have hP := Real.tsum_eq_tsum_fourier h_norm h_sum x
  have hFeq : ∀ n : ℤ, 𝓕 f n = ∫ t, f t * Complex.exp (-2 * π * Complex.I * n * t) := fun n => by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  have hexp : ∀ n : ℤ, fourier n (x : UnitAddCircle) = Complex.exp (2 * π * Complex.I * n * x) :=
    fun n => by rw [fourier_coe_apply]; push_cast; rw [div_one]
  refine ⟨?_, ?_, ?_⟩
  · exact Summable.of_norm_bounded (hT.comp_injective (add_right_injective ⌊x⌋)) fun n => by
      refine (hpt _).trans (le_of_eq ?_)
      simp [Int.floor_add_intCast, add_comm]
  · refine Summable.of_norm_bounded h_sum.norm fun n => ?_
    rw [← hFeq, norm_mul, Complex.norm_exp]
    have : (2 * π * Complex.I * n * x : ℂ).re = 0 := by simp
    rw [this, Real.exp_zero, one_mul]
  · simp only [ContinuousMap.coe_mk] at hP
    rw [hP]
    exact tsum_congr fun n => by rw [hFeq, hexp, mul_comm]

/-- **DLMF §1.8(iv)**: with DLMF's Fourier transform (1.14.1),
`𝓕(f)(x) = (2π)^{−1/2} ∫ f(t) e^{ixt} dt`, the integral in 1.8.14 is `√(2π) 𝓕(f)(−2πn)`. -/
theorem dlmf_1_8_iv_fourier (f : ℝ → ℂ) (n : ℤ) :
    ∫ t, f t * Complex.exp (-2 * π * Complex.I * n * t) =
      (√(2 * π) : ℂ) * ((1 / √(2 * π) : ℂ) *
        ∫ t, f t * Complex.exp (Complex.I * ((-2 * π * n : ℝ) : ℂ) * t)) := by
  have hs : (√(2 * π) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  rw [← mul_assoc, mul_one_div_cancel hs, one_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  congr 2
  push_cast
  ring

/-! ### 1.8.16 -/

/-- **DLMF 1.8.16**: for `ℜω > 0`,
`∑ₙ e^{−(n+x)²ω} = √(π/ω) (1 + 2 ∑_{n ≥ 1} e^{−n²π²/ω} cos(2nπx))`. -/
theorem dlmf_1_8_16 {ω : ℂ} (hω : 0 < ω.re) (x : ℂ) :
    ∑' n : ℤ, Complex.exp (-(n + x) ^ 2 * ω) = (π / ω) ^ (1 / 2 : ℂ) *
      (1 + 2 * ∑' n : ℕ, Complex.exp (-((n + 1 : ℕ) : ℂ) ^ 2 * π ^ 2 / ω) *
        Complex.cos (2 * ((n + 1 : ℕ) : ℂ) * π * x)) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hω0 : ω ≠ 0 := fun h => by rw [h, Complex.zero_re] at hω; exact lt_irrefl 0 hω
  set a : ℂ := ω / π
  have ha : 0 < a.re := by
    simp only [a, Complex.div_ofReal_re]; exact div_pos hω Real.pi_pos
  set b : ℂ := -ω * x / π
  have hM := Complex.tsum_exp_neg_quadratic ha b
  set τ : ℂ := Complex.I * π / ω
  have hτ : 0 < τ.im := by
    simp only [τ, mul_div_assoc, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_add, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul]
    rw [zero_div, add_zero]
    exact mul_pos Real.pi_pos (div_pos hω (Complex.normSq_pos.mpr hω0))
  have hθ := (summable_jacobiTheta₂_term_iff x τ).mpr hτ
  -- the left side is `e^{−ωx²}` times the Mathlib series
  have hL : ∑' n : ℤ, Complex.exp (-(n + x) ^ 2 * ω) =
      Complex.exp (-ω * x ^ 2) * ∑' n : ℤ, Complex.exp (-π * a * n ^ 2 + 2 * π * b * n) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [← Complex.exp_add]
    congr 1
    simp only [a, b]
    field_simp
    ring
  have hR : Complex.exp (-ω * x ^ 2) *
      ∑' n : ℤ, Complex.exp (-π / a * (n + Complex.I * b) ^ 2) =
      ∑' n : ℤ, jacobiTheta₂_term n x τ := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [jacobiTheta₂_term, ← Complex.exp_add]
    congr 1
    simp only [a, b, τ]
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  have harg : a.arg ≠ π := fun h => by
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith
  have hsqrt : 1 / a ^ (1 / 2 : ℂ) = (π / ω) ^ (1 / 2 : ℂ) := by
    rw [show (π : ℂ) / ω = a⁻¹ by simp only [a, inv_div], Complex.inv_cpow a _ harg, one_div]
  rw [hL, hM, ← mul_assoc, mul_comm (Complex.exp _), mul_assoc, hR, hsqrt]
  congr 1
  -- fold the theta series over `±n`
  have h := hθ.hasSum.nat_add_neg
  have hpair : ∀ n : ℕ, jacobiTheta₂_term n x τ + jacobiTheta₂_term (-n) x τ =
      2 * (Complex.exp (-(n : ℂ) ^ 2 * π ^ 2 / ω) * Complex.cos (2 * (n : ℂ) * π * x)) :=
    fun n => by
      simp only [jacobiTheta₂_term, Complex.cos]
      have e1 : 2 * π * Complex.I * ((n : ℤ) : ℂ) * x + π * Complex.I * ((n : ℤ) : ℂ) ^ 2 * τ =
          -(n : ℂ) ^ 2 * π ^ 2 / ω + 2 * (n : ℂ) * π * x * Complex.I := by
        simp only [τ]; push_cast; field_simp; ring_nf; simp only [Complex.I_sq]; ring
      have e2 : 2 * π * Complex.I * ((-(n : ℤ) : ℤ) : ℂ) * x +
          π * Complex.I * ((-(n : ℤ) : ℤ) : ℂ) ^ 2 * τ =
          -(n : ℂ) ^ 2 * π ^ 2 / ω + -(2 * (n : ℂ) * π * x) * Complex.I := by
        simp only [τ]; push_cast; field_simp; ring_nf; simp only [Complex.I_sq]; ring
      rw [e1, e2, Complex.exp_add, Complex.exp_add]
      ring
  simp only [hpair] at h
  have h0 : jacobiTheta₂_term 0 x τ = 1 := by simp [jacobiTheta₂_term]
  rw [h0] at h
  have h1 := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.range_one, Finset.sum_singleton] at h1
  rw [show (2 : ℂ) * (Complex.exp (-((0 : ℕ) : ℂ) ^ 2 * π ^ 2 / ω) *
    Complex.cos (2 * ((0 : ℕ) : ℂ) * π * x)) = 2 by simp] at h1
  have h2 := h1.tsum_eq
  rw [tsum_mul_left] at h2
  push_cast at h2 ⊢
  linear_combination -h2

/-! ### The period-one Dirichlet kernel and Jordan's test -/

/-- `Dₖ(y) = 1 + 2 ∑_{k=1}^K cos(2πky)`. -/
noncomputable def dirichlet1 (K : ℕ) (y : ℝ) : ℝ := 2 * halfDirichlet K (2 * π * y)

theorem continuous_dirichlet1 (K : ℕ) : Continuous (dirichlet1 K) := by
  unfold dirichlet1
  exact continuous_const.mul
    ((continuous_halfDirichlet K).comp (continuous_const.mul continuous_id))

theorem dirichlet1_mul_sin (K : ℕ) (y : ℝ) :
    dirichlet1 K y * Real.sin (π * y) = Real.sin ((2 * K + 1) * π * y) := by
  have h := two_mul_halfDirichlet_mul_sin K (2 * π * y)
  rw [show 2 * π * y / 2 = π * y by ring,
    show ((K : ℝ) + 1 / 2) * (2 * π * y) = (2 * K + 1) * π * y by ring] at h
  rw [dirichlet1, ← h]

theorem abs_dirichlet1_le (K : ℕ) (y : ℝ) : |dirichlet1 K y| ≤ 2 * K + 1 := by
  unfold dirichlet1 halfDirichlet
  have : |∑ n ∈ Finset.range K, Real.cos ((n + 1 : ℕ) * (2 * π * y))| ≤ K := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ Finset.range K, |Real.cos ((n + 1 : ℕ) * (2 * π * y))| ≤
          ∑ _n ∈ Finset.range K, (1 : ℝ) := Finset.sum_le_sum fun n _ => Real.abs_cos_le_one _
      _ = K := by simp
  rw [abs_le] at this ⊢
  constructor <;> linarith [this.1, this.2]

theorem dirichlet1_add_nat (K n : ℕ) (y : ℝ) : dirichlet1 K (n + y) = dirichlet1 K y := by
  unfold dirichlet1
  rw [show 2 * π * ((n : ℝ) + y) = 2 * π * y + n * (2 * π) by ring]
  congr 1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, show 2 * π * y + ((n : ℝ) + 1) * (2 * π) =
      (2 * π * y + n * (2 * π)) + 2 * π by ring, halfDirichlet_periodic, ih]

theorem dirichlet1_neg (K : ℕ) (y : ℝ) : dirichlet1 K (-y) = dirichlet1 K y := by
  unfold dirichlet1
  rw [mul_neg, halfDirichlet_neg]

theorem integral_dirichlet1_half (K : ℕ) : ∫ y in (0 : ℝ)..(1 / 2), dirichlet1 K y = 1 / 2 := by
  unfold dirichlet1
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun s => halfDirichlet K s)
      (by positivity : (2 * π : ℝ) ≠ 0), mul_zero, show 2 * π * (1 / 2) = π by ring,
    integral_halfDirichlet, smul_eq_mul]
  field_simp

/-- The partial integrals of the Dirichlet kernel are uniformly bounded on `[0, ½]`. -/
theorem abs_integral_dirichlet1_le (K : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) : |∫ y in a..b, dirichlet1 K y| ≤ 2 := by
  have hπ := Real.pi_pos
  set M : ℝ := 2 * K + 1
  have hM : 1 ≤ M := by simp only [M]; have := (K.cast_nonneg : (0 : ℝ) ≤ K); linarith
  set t := max a (min b (1 / M))
  have hat : a ≤ t := le_max_left _ _
  have htb : t ≤ b := max_le hab (min_le_left _ _)
  have hDint : ∀ c d, IntervalIntegrable (dirichlet1 K) volume c d := fun c d =>
    (continuous_dirichlet1 K).intervalIntegrable c d
  rw [← intervalIntegral.integral_add_adjacent_intervals (hDint a t) (hDint t b)]
  -- the piece `[a, t]`, where `|D| ≤ M` and `t − a ≤ 1/M`
  have h1 : |∫ y in a..t, dirichlet1 K y| ≤ 1 := by
    have hlen : t - a ≤ 1 / M := by
      rcases le_total a (min b (1 / M)) with h | h
      · show max a (min b (1 / M)) - a ≤ 1 / M
        rw [max_eq_right h]; linarith [min_le_right b (1 / M)]
      · show max a (min b (1 / M)) - a ≤ 1 / M
        rw [max_eq_left h, sub_self]; positivity
    calc |∫ y in a..t, dirichlet1 K y| ≤ M * |t - a| := by
          have := intervalIntegral.norm_integral_le_of_norm_le_const
            (f := dirichlet1 K) (C := M) (a := a) (b := t) fun y _ => by
              rw [Real.norm_eq_abs]; exact abs_dirichlet1_le K y
          simpa [Real.norm_eq_abs] using this
      _ ≤ M * (1 / M) := by
          rw [abs_of_nonneg (by linarith)]; exact mul_le_mul_of_nonneg_left hlen (by linarith)
      _ = 1 := by field_simp
  -- the piece `[t, b]`, by the second mean value theorem
  have h2 : |∫ y in t..b, dirichlet1 K y| ≤ 1 := by
    rcases eq_or_lt_of_le htb with heq | hlt
    · rw [heq, intervalIntegral.integral_same, abs_zero]; exact zero_le_one
    have ht1 : 1 / M ≤ t := by
      have : min b (1 / M) = 1 / M := by
        by_contra hne
        have hmin : min b (1 / M) = b := (min_choice b (1 / M)).resolve_right hne
        have : t = b := le_antisymm htb (hmin ▸ le_max_right a (min b (1 / M)))
        exact lt_irrefl _ (this ▸ hlt)
      rw [← this]; exact le_max_right _ _
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
    have hsinpos : ∀ y ∈ Icc t b, 0 < Real.sin (π * y) := fun y hy =>
      Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hy.1]) (by nlinarith [hy.2])
    have hcongr : ∫ y in t..b, dirichlet1 K y =
        ∫ y in t..b, (1 / Real.sin (π * y)) • Real.sin (M * π * y) := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [Set.uIcc_of_le htb] at hy
      have hs := (hsinpos y hy).ne'
      simp only [smul_eq_mul, M]
      rw [← dirichlet1_mul_sin]
      field_simp
    have hanti : AntitoneOn (fun y => 1 / Real.sin (π * y)) (Icc t b) := fun y hy z hz hyz => by
      simp only
      refine one_div_le_one_div_of_le (hsinpos y hy) (Real.sin_le_sin_of_le_of_le_pi_div_two
        (by nlinarith [hy.1]) (by nlinarith [hz.2]) (by nlinarith))
    obtain ⟨ξ, hξ, hbound⟩ := exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn
      htb (one_div_pos.mpr (hsinpos b ⟨htb, le_rfl⟩)).le hanti
      ((by fun_prop : Continuous fun y => Real.sin (M * π * y)).intervalIntegrable t b)
    rw [hcongr, ← Real.norm_eq_abs]
    refine hbound.trans ?_
    have hsin_t : 2 / M ≤ Real.sin (π * t) := by
      have := Real.mul_le_sin (x := π * t) (by positivity) (by nlinarith)
      calc 2 / M = 2 * (1 / M) := by ring
        _ ≤ 2 * t := by linarith
        _ = 2 / π * (π * t) := by field_simp
        _ ≤ _ := this
    have hcos : ‖∫ y in t..ξ, Real.sin (M * π * y)‖ ≤ 2 / (M * π) := by
      have hc : (M * π) ≠ 0 := by positivity
      rw [intervalIntegral.integral_comp_mul_left (fun y => Real.sin y) hc, integral_sin,
        smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos (by positivity : 0 < M * π),
        inv_mul_eq_div]
      exact div_le_div_of_nonneg_right (by
        rw [abs_le]; constructor <;> linarith [Real.neg_one_le_cos (M * π * t),
          Real.cos_le_one (M * π * t), Real.neg_one_le_cos (M * π * ξ),
          Real.cos_le_one (M * π * ξ)]) (by positivity)
    have hs0 : 0 < Real.sin (π * t) := hsinpos t ⟨le_rfl, htb⟩
    calc 1 / Real.sin (π * t) * ‖∫ y in t..ξ, Real.sin (M * π * y)‖
        ≤ 1 / Real.sin (π * t) * (2 / (M * π)) :=
          mul_le_mul_of_nonneg_left hcos (by positivity)
      _ ≤ M / 2 * (2 / (M * π)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [one_div_le (by positivity) (by positivity)]
          calc 1 / (M / 2) = 2 / M := by field_simp
            _ ≤ _ := hsin_t
      _ = 1 / π := by field_simp
      _ ≤ 1 := by rw [div_le_one hπ]; linarith [Real.one_le_pi_div_two]
  calc |(∫ y in a..t, dirichlet1 K y) + ∫ y in t..b, dirichlet1 K y|
      ≤ |∫ y in a..t, dirichlet1 K y| + |∫ y in t..b, dirichlet1 K y| := abs_add_le _ _
    _ ≤ 2 := by linarith

/-- The Riemann–Lebesgue lemma for `∫ g(y) sin(λy) dy`, `g` real. -/
theorem tendsto_integral_mul_sin_real {g : ℝ → ℝ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) :
    Tendsto (fun l : ℝ => ∫ y in a..b, g y * Real.sin (l * y)) atTop (𝓝 0) := by
  have h := dlmf_1_8_10 (fun y => (g y : ℂ)) a b
  have hc := (Complex.continuous_im.tendsto 0).comp h
  rw [Complex.zero_im] at hc
  refine hc.congr fun l => ?_
  simp only [Function.comp_apply]
  have hint : IntervalIntegrable (fun y => (g y : ℂ) * Complex.exp (l * y * Complex.I))
      volume a b :=
    (show IntervalIntegrable (fun y => (g y : ℂ)) volume a b from
      ⟨hg.1.ofReal, hg.2.ofReal⟩).mul_continuousOn
      (by fun_prop : Continuous fun y : ℝ => Complex.exp (l * y * Complex.I)).continuousOn
  rw [← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
  refine intervalIntegral.integral_congr fun y _ => ?_
  simp only [Complex.imCLM_apply, exp_mul_I_eq, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.I_re,
    Complex.I_im]
  ring

theorem mem_nhdsGT_zero_of_pos {c : ℝ} (hc : 0 < c) {s : Set ℝ} (hs : Ioo 0 c ⊆ s) :
    s ∈ 𝓝[>] (0 : ℝ) :=
  mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨c, hc, hs⟩

/-- **Jordan's test**, monotone case: for nondecreasing `h` with right limit `L` at `0`,
`∫₀^{1/2} h Dₖ → L/2`. -/
theorem tendsto_integral_monotone_mul_dirichlet1 {h : ℝ → ℝ} (hmono : Monotone h) {L : ℝ}
    (hL : Tendsto h (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun K : ℕ => ∫ y in (0 : ℝ)..(1 / 2), h y * dirichlet1 K y) atTop (𝓝 (L / 2)) := by
  have hπ := Real.pi_pos
  have hDint : ∀ K c d, IntervalIntegrable (dirichlet1 K) volume c d := fun K c d =>
    (continuous_dirichlet1 K).intervalIntegrable c d
  have hhint : ∀ c d, IntervalIntegrable (fun y => h y - L) volume c d := fun c d =>
    hmono.intervalIntegrable.sub intervalIntegrable_const
  have hge : ∀ y, 0 < y → L ≤ h y := fun y hy => le_of_tendsto hL (by
    filter_upwards [mem_nhdsGT_zero_of_pos hy (subset_refl _)] with z hz
    exact hmono hz.2.le)
  have hsub : ∀ K : ℕ, (∫ y in (0 : ℝ)..(1 / 2), h y * dirichlet1 K y) - L / 2 =
      ∫ y in (0 : ℝ)..(1 / 2), (h y - L) * dirichlet1 K y := fun K => by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub
      (hmono.intervalIntegrable.mul_continuousOn (continuous_dirichlet1 K).continuousOn)
      ((hDint K _ _).const_mul L), intervalIntegral.integral_const_mul, integral_dirichlet1_half]
    ring
  rw [← tendsto_sub_nhds_zero_iff]
  simp_rw [hsub]
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / 4
  have hε' : 0 < ε' := by positivity
  obtain ⟨η, hη0, hη1, hηε⟩ : ∃ η, 0 < η ∧ η ≤ 1 / 2 ∧ h η - L ≤ ε' := by
    have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), h y < L + ε' := hL.eventually (gt_mem_nhds (by linarith))
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
    refine ⟨min (u / 2) (1 / 2), lt_min (by linarith [show (0 : ℝ) < u from hu]) (by norm_num),
      min_le_right _ _, ?_⟩
    have := hsub (show min (u / 2) (1 / 2) ∈ Ioo 0 u from
      ⟨lt_min (by linarith [show (0 : ℝ) < u from hu]) (by norm_num),
        (min_le_left _ _).trans_lt (by linarith [show (0 : ℝ) < u from hu])⟩)
    simp only [Set.mem_ofPred_eq] at this
    linarith
  -- the part near `0`: second mean value theorem
  have hnear : ∀ K : ℕ, |∫ y in (0 : ℝ)..η, (h y - L) * dirichlet1 K y| ≤ 2 * ε' := fun K => by
    set φ : ℝ → ℝ := fun y => max (h y - L) 0
    have hcongr : ∫ y in (0 : ℝ)..η, (h y - L) * dirichlet1 K y =
        ∫ y in (0 : ℝ)..η, φ y • dirichlet1 K y := by
      refine intervalIntegral.integral_congr_ae (ae_of_all _ fun y hy => ?_)
      rw [Set.uIoc_of_le hη0.le] at hy
      simp only [φ, smul_eq_mul, max_eq_left (sub_nonneg.mpr (hge y hy.1))]
    obtain ⟨ξ, hξ, hb⟩ := exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_monotoneOn
      (f := φ) hη0.le (le_max_right _ _ : (0 : ℝ) ≤ φ 0)
      (fun y _ z _ hyz => by
        simp only [φ]; exact max_le_max (sub_le_sub_right (hmono hyz) L) le_rfl) (hDint K 0 η)
    rw [hcongr, ← Real.norm_eq_abs]
    refine hb.trans ?_
    have h1 : φ η ≤ ε' := max_le hηε hε'.le
    have h2 : ‖∫ y in ξ..η, dirichlet1 K y‖ ≤ 2 := by
      rw [Real.norm_eq_abs]; exact abs_integral_dirichlet1_le K hξ.1 hξ.2 hη1
    calc φ η * ‖∫ y in ξ..η, dirichlet1 K y‖ ≤ ε' * 2 :=
          mul_le_mul h1 h2 (norm_nonneg _) hε'.le
      _ = 2 * ε' := by ring
  -- the part away from `0`: Riemann–Lebesgue
  have hfar : Tendsto (fun K : ℕ => ∫ y in η..(1 / 2), (h y - L) * dirichlet1 K y) atTop
      (𝓝 0) := by
    have hsinpos : ∀ y ∈ uIcc η (1 / 2), 0 < Real.sin (π * y) := fun y hy => by
      rw [Set.uIcc_of_le hη1] at hy
      exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hy.1]) (by nlinarith [hy.2])
    have hg : IntervalIntegrable (fun y => (h y - L) * (1 / Real.sin (π * y))) volume η (1 / 2) :=
      (hhint η (1 / 2)).mul_continuousOn (ContinuousOn.div continuousOn_const
        (by fun_prop) fun y hy => (hsinpos y hy).ne')
    have hlam : Tendsto (fun K : ℕ => (2 * K + 1) * π) atTop atTop :=
      Tendsto.atTop_mul_const hπ (tendsto_atTop_add_const_right _ _
        (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos))
    refine ((tendsto_integral_mul_sin_real hg).comp hlam).congr fun K => ?_
    simp only [Function.comp_apply]
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hs := (hsinpos y hy).ne'
    rw [← dirichlet1_mul_sin]
    field_simp
  have hεe : ε' = ε / 4 := rfl
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hfar) ε' hε'
  refine ⟨N, fun K hK => ?_⟩
  have h3 := hN K hK
  rw [Real.dist_eq, sub_zero] at h3 ⊢
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((hhint 0 η).mul_continuousOn (continuous_dirichlet1 K).continuousOn)
    ((hhint η (1 / 2)).mul_continuousOn (continuous_dirichlet1 K).continuousOn)]
  calc |(∫ y in (0 : ℝ)..η, (h y - L) * dirichlet1 K y) +
        ∫ y in η..(1 / 2), (h y - L) * dirichlet1 K y|
      ≤ |∫ y in (0 : ℝ)..η, (h y - L) * dirichlet1 K y| +
          |∫ y in η..(1 / 2), (h y - L) * dirichlet1 K y| := abs_add_le _ _
    _ < ε := by linarith [hnear K]

/-- The clamp of `y` to `[0, ½]`. -/
noncomputable def clampHalf (y : ℝ) : ℝ := max 0 (min y (1 / 2))

theorem clampHalf_mem (y : ℝ) : clampHalf y ∈ Icc (0 : ℝ) (1 / 2) :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

theorem clampHalf_mono : Monotone clampHalf := fun _ _ h => max_le_max le_rfl (min_le_min h le_rfl)

theorem clampHalf_of_mem {y : ℝ} (hy : y ∈ Icc (0 : ℝ) (1 / 2)) : clampHalf y = y := by
  simp only [clampHalf]; rw [min_eq_left hy.2, max_eq_right hy.1]

/-- **Jordan's test** on `[0, ½]`: for `g` of bounded variation on `[0, ½]` and continuous at `0`,
`∫₀^{1/2} g Dₖ → g(0)/2`. -/
theorem tendsto_integral_bv_mul_dirichlet1 {g : ℝ → ℝ}
    (hg : BoundedVariationOn g (Icc 0 (1 / 2))) (hc : ContinuousWithinAt g (Icc 0 (1 / 2)) 0) :
    Tendsto (fun K : ℕ => ∫ y in (0 : ℝ)..(1 / 2), g y * dirichlet1 K y) atTop (𝓝 (g 0 / 2)) := by
  set s : Set ℝ := Icc 0 (1 / 2)
  have hs0 : (0 : ℝ) ∈ s := ⟨le_rfl, by norm_num⟩
  have hloc := hg.locallyBoundedVariationOn
  set P := variationOnFromTo g s 0
  set Q := variationOnFromTo g s 0 - g
  have hP : MonotoneOn P s := variationOnFromTo.monotoneOn hloc hs0
  have hQ : MonotoneOn Q s := variationOnFromTo.sub_self_monotoneOn hloc hs0
  set P' := fun y => P (clampHalf y)
  set Q' := fun y => Q (clampHalf y)
  have hP' : Monotone P' := fun y z hyz =>
    hP (clampHalf_mem y) (clampHalf_mem z) (clampHalf_mono hyz)
  have hQ' : Monotone Q' := fun y z hyz =>
    hQ (clampHalf_mem y) (clampHalf_mem z) (clampHalf_mono hyz)
  have hLP := hP'.tendsto_nhdsGT 0
  have hLQ := hQ'.tendsto_nhdsGT 0
  have hJP := tendsto_integral_monotone_mul_dirichlet1 hP' hLP
  have hJQ := tendsto_integral_monotone_mul_dirichlet1 hQ' hLQ
  have hgPQ : ∀ y ∈ s, g y = P' y - Q' y := fun y hy => by
    show g y = P (clampHalf y) - (P (clampHalf y) - g (clampHalf y))
    rw [clampHalf_of_mem hy]; ring
  have hlim : sInf (P' '' Ioi 0) - sInf (Q' '' Ioi 0) = g 0 := by
    have hs_mem : s ∈ 𝓝[>] (0 : ℝ) := mem_nhdsGT_zero_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
      (Ioo_subset_Icc_self)
    have h1 : Tendsto g (𝓝[>] 0) (𝓝 (sInf (P' '' Ioi 0) - sInf (Q' '' Ioi 0))) :=
      (hLP.sub hLQ).congr' (by
        filter_upwards [hs_mem] with y hy
        exact (hgPQ y hy).symm)
    have h2 : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := hc.tendsto.mono_left (nhdsWithin_le_of_mem hs_mem)
    exact tendsto_nhds_unique h1 h2
  have hint : ∀ K : ℕ, ∫ y in (0 : ℝ)..(1 / 2), g y * dirichlet1 K y =
      (∫ y in (0 : ℝ)..(1 / 2), P' y * dirichlet1 K y) -
        ∫ y in (0 : ℝ)..(1 / 2), Q' y * dirichlet1 K y := fun K => by
    rw [← intervalIntegral.integral_sub
      (hP'.intervalIntegrable.mul_continuousOn (continuous_dirichlet1 K).continuousOn)
      (hQ'.intervalIntegrable.mul_continuousOn (continuous_dirichlet1 K).continuousOn)]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hy
    rw [hgPQ y hy]
    ring
  simp_rw [hint]
  rw [← hlim, sub_div]
  exact hJP.sub hJQ

/-- A bound on `∫₀^{1/2} g Dₖ`, uniform in `K`. -/
theorem abs_integral_bv_mul_dirichlet1_le {g : ℝ → ℝ} (hg : BoundedVariationOn g (Icc 0 (1 / 2)))
    (K : ℕ) : |∫ y in (0 : ℝ)..(1 / 2), g y * dirichlet1 K y| ≤
      |g 0| / 2 + 6 * (eVariationOn g (Icc 0 (1 / 2))).toReal := by
  set s : Set ℝ := Icc 0 (1 / 2)
  have hs0 : (0 : ℝ) ∈ s := ⟨le_rfl, by norm_num⟩
  have hs1 : (1 / 2 : ℝ) ∈ s := ⟨by norm_num, le_rfl⟩
  have hloc := hg.locallyBoundedVariationOn
  set V := (eVariationOn g s).toReal
  set P := variationOnFromTo g s 0
  set Q : ℝ → ℝ := fun y => P y - g y + g 0
  have hP : MonotoneOn P s := variationOnFromTo.monotoneOn hloc hs0
  have hQ : MonotoneOn Q s := fun y hy z hz hyz => by
    have := variationOnFromTo.sub_self_monotoneOn hloc hs0 hy hz hyz
    simp only [Pi.sub_apply] at this
    simp only [Q]; linarith
  have hP0 : P 0 = 0 := variationOnFromTo.self g s 0
  have hQ0 : Q 0 = 0 := by simp [Q, hP0]
  have hP1 : P (1 / 2) = V := by
    simp only [P, V, variationOnFromTo.eq_of_le g s (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [show s ∩ Icc 0 (1 / 2) = s from inter_self s]
  have hQ1 : Q (1 / 2) ≤ 2 * V := by
    simp only [Q, hP1]
    have := hg.sub_le hs0 hs1
    linarith
  have hDint : ∀ c d, IntervalIntegrable (dirichlet1 K) volume c d := fun c d =>
    (continuous_dirichlet1 K).intervalIntegrable c d
  have hPint : IntervalIntegrable (fun y => P y * dirichlet1 K y) volume 0 (1 / 2) := by
    have := MonotoneOn.intervalIntegrable (μ := volume)
      (hP.mono (Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)).subset)
    exact this.mul_continuousOn (continuous_dirichlet1 K).continuousOn
  have hQint : IntervalIntegrable (fun y => Q y * dirichlet1 K y) volume 0 (1 / 2) := by
    have := MonotoneOn.intervalIntegrable (μ := volume)
      (hQ.mono (Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)).subset)
    exact this.mul_continuousOn (continuous_dirichlet1 K).continuousOn
  have hsplit : ∫ y in (0 : ℝ)..(1 / 2), g y * dirichlet1 K y = g 0 * (1 / 2) +
      (∫ y in (0 : ℝ)..(1 / 2), P y * dirichlet1 K y) -
        ∫ y in (0 : ℝ)..(1 / 2), Q y * dirichlet1 K y := by
    have hc : ∫ y in (0 : ℝ)..(1 / 2), g 0 * dirichlet1 K y = g 0 * (1 / 2) := by
      rw [intervalIntegral.integral_const_mul, integral_dirichlet1_half]
    rw [← hc, ← intervalIntegral.integral_add ((hDint _ _).const_mul _) hPint,
      ← intervalIntegral.integral_sub (((hDint _ _).const_mul _).add hPint) hQint]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [Q]
    ring
  have hbound : ∀ R : ℝ → ℝ, MonotoneOn R s → R 0 = 0 →
      |∫ y in (0 : ℝ)..(1 / 2), R y * dirichlet1 K y| ≤ R (1 / 2) * 2 := fun R hR hR0 => by
    obtain ⟨ξ, hξ, hb⟩ := exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_monotoneOn
      (by norm_num : (0 : ℝ) ≤ 1 / 2) hR0.ge hR (hDint 0 (1 / 2))
    rw [← Real.norm_eq_abs]
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (hR0 ▸ hR hs0 hs1 (by norm_num)))
    rw [Real.norm_eq_abs]
    exact abs_integral_dirichlet1_le K hξ.1 hξ.2 le_rfl
  have h1 := hbound P hP hP0
  have h2 := hbound Q hQ hQ0
  rw [hsplit]
  calc |g 0 * (1 / 2) + (∫ y in (0 : ℝ)..(1 / 2), P y * dirichlet1 K y) -
        ∫ y in (0 : ℝ)..(1 / 2), Q y * dirichlet1 K y|
      ≤ |g 0 * (1 / 2)| + |∫ y in (0 : ℝ)..(1 / 2), P y * dirichlet1 K y| +
          |∫ y in (0 : ℝ)..(1 / 2), Q y * dirichlet1 K y| := by
        refine (abs_sub _ _).trans ?_
        linarith [abs_add_le (g 0 * (1 / 2)) (∫ y in (0 : ℝ)..(1 / 2), P y * dirichlet1 K y)]
    _ ≤ |g 0| / 2 + 6 * V := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        rw [hP1] at h1
        linarith

/-! ### 1.8.15 -/

section Formula1815

variable {f : ℝ → ℝ} (hc : ContinuousOn f (Ici 0)) (hbv : BoundedVariationOn f (Ici 0))
  (hi : IntegrableOn f (Ici 0))

include hbv in
theorem bv_Icc_nat (n : ℕ) : BoundedVariationOn f (Icc (n : ℝ) (n + 1)) :=
  hbv.mono fun _ hx => (Nat.cast_nonneg n).trans hx.1

include hi in
theorem intervalIntegrable_of_Ici {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable f volume a b :=
  (hi.mono_set fun _ hx => (le_min ha hb).trans hx.1).intervalIntegrable

include hbv in
/-- The variations over `[n, n+1]` are summable. -/
theorem summable_eVariation_Icc :
    Summable fun n : ℕ => (eVariationOn f (Icc (n : ℝ) (n + 1))).toReal := by
  refine summable_of_sum_range_le (c := (eVariationOn f (Ici 0)).toReal)
    (fun n => ENNReal.toReal_nonneg) fun N => ?_
  have hsum := eVariationOn.sum' f (I := fun n : ℕ => (n : ℝ)) Nat.mono_cast (n := N)
  push_cast at hsum
  rw [← ENNReal.toReal_sum fun i _ => bv_Icc_nat hbv i, hsum]
  exact ENNReal.toReal_mono hbv (eVariationOn.mono f fun x hx => hx.1)

include hi in
theorem summable_integral_abs_Icc :
    Summable fun n : ℕ => ∫ t in (n : ℝ)..(n + 1), |f t| := by
  have hIoi : IntegrableOn f (Ioi 0) := hi.mono_set Ioi_subset_Ici_self
  refine summable_of_sum_range_le (c := ∫ t in Ioi 0, |f t|)
    (fun n => intervalIntegral.integral_nonneg (by linarith) fun _ _ => abs_nonneg _) fun N => ?_
  have hint : ∀ k < N, IntervalIntegrable (fun t => |f t|) volume (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
    fun k _ => (intervalIntegrable_of_Ici hi (by positivity) (by positivity)).abs
  have h := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ)) hint
  push_cast at h
  rw [h, intervalIntegral.integral_of_le (by positivity)]
  exact setIntegral_mono_set hIoi.abs (ae_of_all _ fun _ => abs_nonneg _)
    (Eventually.of_forall fun x hx => hx.1)

include hi hbv in
theorem abs_le_integral_add_variation (n : ℕ) :
    |f n| ≤ (∫ t in (n : ℝ)..(n + 1), |f t|) + (eVariationOn f (Icc (n : ℝ) (n + 1))).toReal := by
  set W := (eVariationOn f (Icc (n : ℝ) (n + 1))).toReal
  have hfi := intervalIntegrable_of_Ici hi (Nat.cast_nonneg n) (by positivity : (0 : ℝ) ≤ n + 1)
  have hpt : ∀ t ∈ Icc (n : ℝ) (n + 1), |f n| ≤ |f t| + W := fun t ht => by
    have := (bv_Icc_nat hbv n).dist_le ⟨le_rfl, by linarith⟩ ht
    rw [Real.dist_eq] at this
    linarith [abs_sub_abs_le_abs_sub (f n) (f t)]
  calc |f n| = ∫ _ in (n : ℝ)..(n + 1), |f n| := by simp
    _ ≤ ∫ t in (n : ℝ)..(n + 1), (|f t| + W) :=
        intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
          (hfi.abs.add intervalIntegrable_const) hpt
    _ = _ := by rw [intervalIntegral.integral_add hfi.abs intervalIntegrable_const]; simp

include hi hbv in
theorem summable_abs_nat : Summable fun n : ℕ => |f n| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (abs_le_integral_add_variation hbv hi)
    ((summable_integral_abs_Icc hi).add (summable_eVariation_Icc hbv))

include hi in
/-- The piece over `[n, n+1]`, folded onto `[0, ½]` from both ends. -/
theorem integral_piece_eq (n K : ℕ) :
    ∫ x in (n : ℝ)..(n + 1), f x * dirichlet1 K x =
      (∫ y in (0 : ℝ)..(1 / 2), f (n + y) * dirichlet1 K y) +
        ∫ y in (0 : ℝ)..(1 / 2), f (n + 1 - y) * dirichlet1 K y := by
  have hD := continuous_dirichlet1 K
  have hint : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      IntervalIntegrable (fun x => f x * dirichlet1 K x) volume a b := fun a b ha hb =>
    (intervalIntegrable_of_Ici hi ha hb).mul_continuousOn hD.continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (n : ℝ) + 1 / 2)
    (hint _ _ (by positivity) (by positivity)) (hint _ _ (by positivity) (by positivity))]
  congr 1
  · have h := intervalIntegral.integral_comp_add_left (fun x => f x * dirichlet1 K x) (n : ℝ)
      (a := 0) (b := 1 / 2)
    rw [add_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [dirichlet1_add_nat]
  · have h := intervalIntegral.integral_comp_sub_left (fun x => f x * dirichlet1 K x)
      ((n : ℝ) + 1) (a := 0) (b := 1 / 2)
    rw [sub_zero, show (n : ℝ) + 1 - 1 / 2 = n + 1 / 2 by ring] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [show (n : ℝ) + 1 - y = ((n + 1 : ℕ) : ℝ) + -y by push_cast; ring, dirichlet1_add_nat,
      dirichlet1_neg]

include hbv in
theorem bv_left (n : ℕ) : BoundedVariationOn (fun y => f (n + y)) (Icc 0 (1 / 2)) :=
  ne_top_of_le_ne_top (bv_Icc_nat hbv n)
    (eVariationOn.comp_le_of_monotoneOn f (fun y => (n : ℝ) + y)
      (fun _ _ _ _ h => by simpa using h) fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩)

include hbv in
theorem bv_right (n : ℕ) : BoundedVariationOn (fun y => f (n + 1 - y)) (Icc 0 (1 / 2)) :=
  ne_top_of_le_ne_top (bv_Icc_nat hbv n)
    (eVariationOn.comp_le_of_antitoneOn f (fun y => (n : ℝ) + 1 - y)
      (fun _ _ _ _ h => by simp only; linarith) fun y hy =>
        ⟨by linarith [hy.2], by linarith [hy.1]⟩)

include hbv in
theorem variation_left_le (n : ℕ) :
    (eVariationOn (fun y => f (n + y)) (Icc 0 (1 / 2))).toReal ≤
      (eVariationOn f (Icc (n : ℝ) (n + 1))).toReal :=
  ENNReal.toReal_mono (bv_Icc_nat hbv n)
    (eVariationOn.comp_le_of_monotoneOn f (fun y => (n : ℝ) + y)
      (fun _ _ _ _ h => by simpa using h) fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩)

include hbv in
theorem variation_right_le (n : ℕ) :
    (eVariationOn (fun y => f (n + 1 - y)) (Icc 0 (1 / 2))).toReal ≤
      (eVariationOn f (Icc (n : ℝ) (n + 1))).toReal :=
  ENNReal.toReal_mono (bv_Icc_nat hbv n)
    (eVariationOn.comp_le_of_antitoneOn f (fun y => (n : ℝ) + 1 - y)
      (fun _ _ _ _ h => by simp only; linarith) fun y hy =>
        ⟨by linarith [hy.2], by linarith [hy.1]⟩)

include hc in
theorem continuousWithinAt_left (n : ℕ) :
    ContinuousWithinAt (fun y => f (n + y)) (Icc 0 (1 / 2)) 0 := by
  have h := hc (n : ℝ) (Set.mem_Ici.mpr (Nat.cast_nonneg n))
  rw [← add_zero (n : ℝ)] at h
  exact h.comp (continuous_const.add continuous_id).continuousWithinAt
    fun y hy => show (0 : ℝ) ≤ n + y by linarith [hy.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

include hc in
theorem continuousWithinAt_right (n : ℕ) :
    ContinuousWithinAt (fun y => f (n + 1 - y)) (Icc 0 (1 / 2)) 0 := by
  have h := hc ((n : ℝ) + 1) (Set.mem_Ici.mpr (by positivity))
  rw [← sub_zero ((n : ℝ) + 1)] at h
  exact h.comp (continuous_const.sub continuous_id).continuousWithinAt
    fun y hy => show (0 : ℝ) ≤ n + 1 - y by
      linarith [hy.2, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

include hc hbv hi in
theorem tendsto_piece (n : ℕ) :
    Tendsto (fun K : ℕ => ∫ x in (n : ℝ)..(n + 1), f x * dirichlet1 K x) atTop
      (𝓝 (f n / 2 + f (n + 1) / 2)) := by
  have h1 := tendsto_integral_bv_mul_dirichlet1 (bv_left hbv n) (continuousWithinAt_left hc n)
  have h2 := tendsto_integral_bv_mul_dirichlet1 (bv_right hbv n) (continuousWithinAt_right hc n)
  simp only [add_zero, sub_zero] at h1 h2
  exact (h1.add h2).congr fun K => (integral_piece_eq hi n K).symm

include hbv hi in
theorem abs_piece_le (K n : ℕ) :
    |∫ x in (n : ℝ)..(n + 1), f x * dirichlet1 K x| ≤
      |f n| / 2 + |f (n + 1)| / 2 + 12 * (eVariationOn f (Icc (n : ℝ) (n + 1))).toReal := by
  have h1 := abs_integral_bv_mul_dirichlet1_le (bv_left hbv n) K
  have h2 := abs_integral_bv_mul_dirichlet1_le (bv_right hbv n) K
  have v1 := variation_left_le hbv n
  have v2 := variation_right_le hbv n
  simp only [add_zero, sub_zero] at h1 h2
  rw [integral_piece_eq hi n K]
  refine (abs_add_le _ _).trans ?_
  linarith

include hi in
theorem integrableOn_mul_dirichlet1 (K : ℕ) :
    IntegrableOn (fun x => f x * dirichlet1 K x) (Ioi 0) := by
  have hIoi : IntegrableOn f (Ioi 0) := hi.mono_set Ioi_subset_Ici_self
  refine Integrable.mono' (hIoi.norm.mul_const (2 * K + 1))
    (hIoi.aestronglyMeasurable.mul (continuous_dirichlet1 K).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [norm_mul, Real.norm_eq_abs (dirichlet1 K x)]
  exact mul_le_mul_of_nonneg_left (abs_dirichlet1_le K x) (norm_nonneg _)

include hi in
theorem hasSum_pieces {K : ℕ}
    (hs : Summable fun n : ℕ => ∫ x in (n : ℝ)..(n + 1), f x * dirichlet1 K x) :
    ∑' n : ℕ, ∫ x in (n : ℝ)..(n + 1), f x * dirichlet1 K x =
      ∫ x in Ioi 0, f x * dirichlet1 K x := by
  have h1 := hs.hasSum.tendsto_sum_nat
  have h2 := intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_mul_dirichlet1 hi K)
    tendsto_natCast_atTop_atTop
  have h3 : ∀ N : ℕ, ∑ n ∈ Finset.range N, ∫ x in (n : ℝ)..(n + 1), f x * dirichlet1 K x =
      ∫ x in (0 : ℝ)..(N : ℝ), f x * dirichlet1 K x := fun N => by
    have := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ)) (f := fun x => f x * dirichlet1 K x) (n := N) fun k _ =>
        (intervalIntegrable_of_Ici hi (by positivity) (by positivity)).mul_continuousOn
          (continuous_dirichlet1 K).continuousOn
    push_cast at this
    exact this
  simp_rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

include hi in
theorem integral_mul_dirichlet1_eq (K : ℕ) :
    ∫ x in Ioi 0, f x * dirichlet1 K x = (∫ x in Ioi 0, f x) +
      2 * ∑ k ∈ Finset.range K, ∫ x in Ioi 0, f x * Real.cos (2 * π * (k + 1) * x) := by
  have hIoi : IntegrableOn f (Ioi 0) := hi.mono_set Ioi_subset_Ici_self
  have hcos : ∀ k : ℕ, IntegrableOn (fun x => f x * Real.cos (2 * π * (k + 1) * x)) (Ioi 0) :=
    fun k => Integrable.mono' hIoi.norm
      (hIoi.aestronglyMeasurable.mul (by fun_prop : Continuous fun x : ℝ =>
        Real.cos (2 * π * (k + 1) * x)).aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [norm_mul, Real.norm_eq_abs (Real.cos _)]
        exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _))
  have e : ∀ x, f x * dirichlet1 K x =
      f x + 2 * ∑ k ∈ Finset.range K, f x * Real.cos (2 * π * (k + 1) * x) := fun x => by
    have hs : ∑ n ∈ Finset.range K, Real.cos (((n + 1 : ℕ) : ℝ) * (2 * π * x)) =
        ∑ k ∈ Finset.range K, Real.cos (2 * π * (k + 1) * x) :=
      Finset.sum_congr rfl fun k _ => by congr 1; push_cast; ring
    rw [dirichlet1, halfDirichlet, hs, ← Finset.mul_sum]
    ring
  simp_rw [e]
  rw [integral_add hIoi ((integrable_finsetSum _ fun k _ => hcos k).const_mul 2),
    integral_const_mul, integral_finsetSum _ fun k _ => hcos k]

include hc hbv hi in
/-- **DLMF 1.8.15** (Poisson's summation formula, alternative form): for `f` continuous, of bounded
variation and integrable on `[0, ∞)`, the series `∑ f(n)` converges and
`½f(0) + ∑_{n ≥ 1} f(n) = ∫₀^∞ f + 2 ∑_{n ≥ 1} ∫₀^∞ f(x) cos(2πnx) dx`, the series on the right
converging (conditionally).  DLMF's hypothesis `f(x) → 0` follows from the others. -/
theorem dlmf_1_8_15 :
    Summable (fun n : ℕ => f (n + 1)) ∧
      Tendsto (fun N : ℕ => (∫ x in Ioi 0, f x) +
        2 * ∑ k ∈ Finset.range N, ∫ x in Ioi 0, f x * Real.cos (2 * π * (k + 1) * x)) atTop
        (𝓝 (f 0 / 2 + ∑' n : ℕ, f (n + 1))) := by
  have hsf := summable_abs_nat hbv hi
  have hsf' : Summable fun n : ℕ => f n := hsf.of_abs
  have hsf1 : Summable fun n : ℕ => f (n + 1) := by
    simpa using (summable_nat_add_iff 1).mpr hsf'
  refine ⟨hsf1, ?_⟩
  have hbsum : Summable fun n : ℕ => |f n| / 2 + |f (n + 1)| / 2 +
      12 * (eVariationOn f (Icc (n : ℝ) (n + 1))).toReal := by
    have h1 : Summable fun n : ℕ => |f (n + 1)| := by
      simpa using (summable_nat_add_iff 1).mpr hsf
    exact ((hsf.div_const 2).add (h1.div_const 2)).add ((summable_eVariation_Icc hbv).mul_left 12)
  have hT := tendsto_tsum_of_dominated_convergence hbsum (tendsto_piece hc hbv hi)
    (Eventually.of_forall fun K n => by
      rw [Real.norm_eq_abs]; exact abs_piece_le hbv hi K n)
  have hvalue : ∑' n : ℕ, (f n / 2 + f (n + 1) / 2) = f 0 / 2 + ∑' n : ℕ, f (n + 1) := by
    rw [(hsf'.div_const 2).tsum_add (hsf1.div_const 2), tsum_div_const, tsum_div_const,
      hsf'.tsum_eq_zero_add]
    push_cast
    ring
  rw [← hvalue]
  refine hT.congr fun K => ?_
  rw [hasSum_pieces hi (Summable.of_norm_bounded hbsum fun n => by
    rw [Real.norm_eq_abs]; exact abs_piece_le hbv hi K n), integral_mul_dirichlet1_eq hi K]

end Formula1815

end Azurite.DLMF
