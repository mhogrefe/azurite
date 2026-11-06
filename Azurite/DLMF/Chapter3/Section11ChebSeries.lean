/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section11Chebyshev
import Azurite.DLMF.Chapter3.Section11Minimax
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# DLMF §3.11(ii): Chebyshev-series expansions

Formalizations of the series parts of <https://dlmf.nist.gov/3.11.ii>, by reduction to the Fourier
series of `θ ↦ f(cos θ)` (§1.8).

* 3.11.10 `chebCoeff` (`cₙ = (2/π) ∫₀^π f(cos θ) cos(nθ) dθ`); `fourierA_cheb` (`cₙ` is the Fourier
  cosine coefficient of `f(cos θ)`, the sine coefficients vanish).
* 3.11.11 `dlmf_3_11_11` (uniform convergence on `[−1, 1]` for `f` continuously differentiable on
  `[−1, 1]`), `dlmf_3_11_11_hasSum` (pointwise); `summable_abs_chebCoeff` (the `cₙ` are absolutely
  summable, by Parseval for the derivative of `f(cos θ)`).
* "if `f ∈ C^∞[−1, 1]`, then the convergence of (3.11.11) is usually very rapid; compare (1.8.7)":
  `dlmf_3_11_ii_smooth` (`cₙ = o(n^{−m})` for `f ∈ C^m[−1, 1]`) and `dlmf_3_11_ii_smooth_all`.
* 3.11.12 `dlmf_3_11_12` (rescaling to `[a, b]`).
* 3.11.13 `dlmf_3_11_13`: "the right-hand side enjoys exactly those properties concerning its
  maxima and minima that are required for the minimax approximation": if `εₙ` is exactly
  `d T_{n+1}((2x − a − b)/(b − a))` on `[a, b]`, then `pₙ` is the minimax polynomial and the
  minimax error is `|d|` (via `dlmf_3_11_i_sufficient` at the extrema of `T_{n+1}`).
* 3.11.14 `dlmf_3_11_14` (Powell's bound): the remainder after truncating at the `(n + 1)`th term
  is at most `(1 + Lₙ)` times the error of any polynomial of degree `≤ n`, and
  `dlmf_3_11_14_minimax` with the minimax error; `cheb_tail_hasSum` identifies the remainder with
  the tail `∑_{k ≥ n+1} c_k T_k(x)` of 3.11.14. Ingredients: the truncated Chebyshev series is the
  Fourier partial sum of `f(cos θ)` (`chebPartialSum_cos_eq`), hence the Dirichlet-kernel bound
  `|Sₙh| ≤ Lₙ max|h|` (`chebPartialSum_bound`), and it reproduces polynomials of degree `≤ n`
  (`chebPartialSum_poly`, from `∫₀^π cos^k θ cos(mθ) dθ = 0` for `k < m`).
* `lebesgueConst_zero` (`L₀ = 1`).

The monotonicity of `Lₙ` and the value `L₁₀₀₀ = 4.07…`: `Section11Lebesgue.lean`,
`Section11LebesgueNum.lean`.
-/

open Polynomial Polynomial.Chebyshev Real Finset MeasureTheory Filter Topology Set

namespace Azurite.DLMF

/-! ### 3.11.10 and the link with Fourier series -/

/-- **DLMF 3.11.10**: `cₙ = (2/π) ∫₀^π f(cos θ) cos(nθ) dθ`. -/
noncomputable def chebCoeff (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  2 / π * ∫ θ in (0 : ℝ)..π, f (Real.cos θ) * Real.cos (n * θ)

theorem dlmf_3_11_10 (f : ℝ → ℝ) (n : ℕ) :
    chebCoeff f n = 2 / π * ∫ θ in (0 : ℝ)..π, f (Real.cos θ) * Real.cos (n * θ) := rfl

theorem cos_mem_Icc (t : ℝ) : Real.cos t ∈ Icc (-1 : ℝ) 1 := ⟨neg_one_le_cos t, cos_le_one t⟩

/-- The integral of an even continuous function over `[−a, a]` is twice that over `[0, a]`. -/
theorem integral_even_symm {φ : ℝ → ℝ} (hφ : ∀ x, φ (-x) = φ x) (hc : Continuous φ) (a : ℝ) :
    ∫ x in (-a)..a, φ x = 2 * ∫ x in (0 : ℝ)..a, φ x := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := a) φ
  simp only [neg_zero, hφ] at h
  rw [← h]
  ring

theorem continuous_comp_cos {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) :
    Continuous fun t => f (Real.cos t) :=
  hf.comp_continuous continuous_cos cos_mem_Icc

/-- `cₙ` is the Fourier cosine coefficient `aₙ` of `θ ↦ f(cos θ)`. -/
theorem fourierA_cheb {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) (n : ℕ) :
    fourierA (fun θ => (f (Real.cos θ) : ℂ)) n = chebCoeff f n := by
  have hφc : Continuous fun x => f (Real.cos x) * Real.cos (n * x) :=
    (continuous_comp_cos hf).mul (by fun_prop)
  have hφe : ∀ x, (fun x => f (Real.cos x) * Real.cos (n * x)) (-x) =
      (fun x => f (Real.cos x) * Real.cos (n * x)) x := fun x => by
    simp only [Real.cos_neg, mul_neg]
  rw [fourierA]
  have e : (∫ x in (-π)..π, (f (Real.cos x) : ℂ) * (Real.cos (n * x) : ℂ)) =
      ((∫ x in (-π)..π, f (Real.cos x) * Real.cos (n * x) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    push_cast
    rfl
  rw [e, integral_even_symm hφe hφc, chebCoeff, Complex.real_smul]
  push_cast
  ring

theorem cheb_even (f : ℝ → ℝ) (x : ℝ) :
    (fun θ => (f (Real.cos θ) : ℂ)) (-x) = (fun θ => (f (Real.cos θ) : ℂ)) x := by
  simp only [Real.cos_neg]

/-- The Fourier sine coefficients of `f(cos θ)` vanish. -/
theorem fourierB_cheb (f : ℝ → ℝ) (k : ℕ) : fourierB (fun θ => (f (Real.cos θ) : ℂ)) k = 0 :=
  dlmf_1_8_i_even (f := fun θ => ((f (Real.cos θ) : ℝ) : ℂ)) (cheb_even f) k

theorem cheb_periodic (f : ℝ → ℝ) :
    Function.Periodic (fun θ => (f (Real.cos θ) : ℂ)) (2 * π) := fun t => by
  simp only [Real.cos_add_two_pi]

/-- The truncated Chebyshev series at `cos θ` is the Fourier partial sum of `f(cos θ)`. -/
theorem chebPartialSum_cos_eq {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) (n : ℕ)
    (θ : ℝ) : ((chebPartialSum (chebCoeff f) n (Real.cos θ) : ℝ) : ℂ) =
      fourierPartialSum (fun t => (f (Real.cos t) : ℂ)) n θ := by
  simp only [chebPartialSum, fourierPartialSum, fourierA_cheb hf, fourierB_cheb, zero_mul,
    add_zero, T_real_cos]
  push_cast
  rfl

/-! ### 3.11.11: uniform convergence -/

/-- For `f` continuously differentiable on `[−1, 1]`, the complex Fourier coefficients of
`f(cos θ)` are absolutely summable. -/
theorem summable_fourierC_cheb {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Icc (-1) 1)) :
    Summable (fourierC fun θ => (f (Real.cos θ) : ℂ)) := by
  set g : ℝ → ℂ := fun θ => (f (Real.cos θ) : ℂ)
  have h1 : ContDiff ℝ 1 (f ∘ Real.cos) :=
    contDiffOn_univ.mp (hf.comp contDiff_cos.contDiffOn fun x _ => cos_mem_Icc x)
  have hg : ContDiff ℝ 1 g := Complex.ofRealCLM.contDiff.comp h1
  have hper : Function.Periodic g (2 * π) := cheb_periodic f
  have hP := (dlmf_1_8_6 (memLp_of_continuous (hg.continuous_deriv le_rfl))).summable
  have hsq : Summable fun n : ℤ => 1 / (n : ℝ) ^ 2 := Real.summable_one_div_int_pow.mpr one_lt_two
  refine Summable.of_norm_bounded_eventually ((hP.add hsq).div_const 2) ?_
  filter_upwards [eventually_cofinite_ne 0] with n hn
  have h2 := fourierC_deriv hper hg n
  have hnI : (n : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hn) Complex.I_ne_zero
  have heq : fourierC g n = fourierC (deriv g) n / (n * Complex.I) := by
    rw [h2]; field_simp
  rw [heq, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast]
  have := two_mul_le_add_sq ‖fourierC (deriv g) n‖ (1 / |(n : ℝ)|)
  rw [div_pow, one_pow, sq_abs] at this
  rw [div_eq_mul_one_div]
  linarith

/-- The Chebyshev coefficients of a continuously differentiable `f` are absolutely summable. -/
theorem summable_abs_chebCoeff {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Icc (-1) 1)) :
    Summable fun n => |chebCoeff f n| := by
  have hs := (summable_fourierC_cheb hf).norm
  have h1 := hs.comp_injective (Nat.cast_injective (R := ℤ))
  have h2 := hs.comp_injective (i := fun n : ℕ => -(n : ℤ)) (fun a b h => by simpa using h)
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => ?_) (h1.add h2)
  have hcont : IntervalIntegrable (fun θ => (f (Real.cos θ) : ℂ)) volume (-π) π :=
    (Complex.continuous_ofReal.comp (continuous_comp_cos hf.continuousOn)).intervalIntegrable _ _
  have e : |chebCoeff f n| = ‖(chebCoeff f n : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [e, ← fourierA_cheb hf.continuousOn, fourierA_eq_add hcont]
  exact norm_add_le _ _

/-- **DLMF 3.11.11**, pointwise: `f(x) = ½c₀ + ∑_{n ≥ 1} cₙ Tₙ(x)` on `[−1, 1]`. -/
theorem dlmf_3_11_11_hasSum {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Icc (-1) 1)) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun n => chebCoeff f (n + 1) * (T ℝ (n + 1 : ℕ)).eval x) (f x - chebCoeff f 0 / 2) := by
  set g : ℝ → ℂ := fun θ => (f (Real.cos θ) : ℂ)
  have hgc : Continuous g := Complex.continuous_ofReal.comp (continuous_comp_cos hf.continuousOn)
  have h := dlmf_1_8_1 (cheb_periodic f) hgc (summable_fourierC_cheb hf) (arccos x)
  simp only [fourierA_cheb hf.continuousOn, fourierB_cheb, zero_mul, add_zero,
    cos_arccos hx.1 hx.2] at h
  rw [← Complex.hasSum_ofReal]
  convert h using 1
  · funext n
    rw [dlmf_3_11_6 _ hx]
    push_cast
    rfl
  · push_cast
    rfl

/-- **DLMF 3.11.11**: for `f` continuously differentiable on `[−1, 1]`, the Chebyshev series
converges uniformly on `[−1, 1]`. -/
theorem dlmf_3_11_11 {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Icc (-1) 1)) :
    TendstoUniformlyOn (fun N x => chebPartialSum (chebCoeff f) N x) f atTop (Icc (-1) 1) := by
  have habs : Summable fun n => |chebCoeff f (n + 1)| :=
    (summable_nat_add_iff 1).mpr (summable_abs_chebCoeff hf)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have ht := tendsto_sum_nat_add fun n => |chebCoeff f (n + 1)|
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with N hN x hx
  set u : ℕ → ℝ := fun n => chebCoeff f (n + 1) * (T ℝ (n + 1 : ℕ)).eval x
  have hs := dlmf_3_11_11_hasSum hf hx
  have hu : ∀ n, |u n| ≤ |chebCoeff f (n + 1)| := fun n => by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (abs_eval_T_real_le_one _ (abs_le.mpr ⟨hx.1, hx.2⟩))
  have hsplit := hs.summable.sum_add_tsum_nat_add N
  rw [hs.tsum_eq] at hsplit
  have hS2 : Summable fun k => |chebCoeff f (k + N + 1)| := (summable_nat_add_iff N).mpr habs
  have huN : ∀ k, |u (k + N)| ≤ |chebCoeff f (k + N + 1)| := fun k => hu (k + N)
  have htail : Summable fun k => |u (k + N)| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) huN hS2
  have hb : |∑' k, u (k + N)| ≤ ∑' k, |chebCoeff f (k + N + 1)| := by
    have h0 : |∑' k, u (k + N)| ≤ ∑' k, |u (k + N)| := by
      simpa only [Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm (f := fun k => u (k + N))
          (by simpa only [Real.norm_eq_abs] using htail)
    exact h0.trans (Summable.tsum_le_tsum huN htail hS2)
  rw [Real.dist_eq, chebPartialSum]
  have : f x - (chebCoeff f 0 / 2 + ∑ k ∈ range N, u k) = ∑' k, u (k + N) := by linarith
  rw [this]
  exact lt_of_le_of_lt hb hN

/-- The remainder in 3.11.14 is the tail of 3.11.11. -/
theorem cheb_tail_hasSum {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Icc (-1) 1)) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (n : ℕ) :
    HasSum (fun k => chebCoeff f (k + n + 1) * (T ℝ (k + n + 1 : ℕ)).eval x)
      (f x - chebPartialSum (chebCoeff f) n x) := by
  have h := (hasSum_nat_add_iff' n).mpr (dlmf_3_11_11_hasSum hf hx)
  convert h using 1
  rw [chebPartialSum]
  ring

/-! ### Smooth functions -/

theorem periodic_iteratedDeriv_complex {g : ℝ → ℂ} {c : ℝ} (hper : Function.Periodic g c) (k : ℕ) :
    Function.Periodic (iteratedDeriv k g) c := by
  induction k with
  | zero => simpa using hper
  | succ k ih => rw [iteratedDeriv_succ]; exact periodic_deriv ih

/-- **DLMF §3.11(ii)**, "if `f ∈ C^∞[−1, 1]`, then the convergence of (3.11.11) is usually very
rapid; compare (1.8.7)": for `f ∈ C^m[−1, 1]`, `cₙ = o(n^{−m})`. -/
theorem dlmf_3_11_ii_smooth {f : ℝ → ℝ} (m : ℕ) (hf : ContDiffOn ℝ m f (Icc (-1) 1)) :
    (fun n : ℕ => chebCoeff f n) =o[atTop] (fun n => ((n : ℝ) ^ m)⁻¹) := by
  set g : ℝ → ℂ := fun θ => (f (Real.cos θ) : ℂ)
  have h1 : ContDiff ℝ m (f ∘ Real.cos) :=
    contDiffOn_univ.mp (hf.comp contDiff_cos.contDiffOn fun x _ => cos_mem_Icc x)
  have hg : ContDiff ℝ m g := Complex.ofRealCLM.contDiff.comp h1
  have hper : Function.Periodic g (2 * π) := cheb_periodic f
  have h := dlmf_1_8_7 (m := m) (fun k => iteratedDeriv k g)
    (fun k _ => periodic_iteratedDeriv_complex hper k)
    (fun k hk => hg.continuous_iteratedDeriv k (by exact_mod_cast hk.le))
    (fun k hk x => by
      rw [iteratedDeriv_succ]
      exact ((hg.differentiable_iteratedDeriv k (by exact_mod_cast hk)) x).hasDerivAt
        |>.hasDerivWithinAt)
    ((hg.continuous_iteratedDeriv m le_rfl).intervalIntegrable _ _)
  have h0 := h.1
  simp only [iteratedDeriv_zero] at h0
  rw [← Asymptotics.isLittleO_norm_left]
  have h0' := h0.norm_left
  convert h0' using 2 with n
  rw [fourierA_cheb hf.continuousOn, Complex.norm_real]

/-- **DLMF §3.11(ii)**: for `f ∈ C^∞[−1, 1]`, `cₙ = o(n^{−m})` for every `m`. -/
theorem dlmf_3_11_ii_smooth_all {f : ℝ → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Icc (-1) 1))
    (m : ℕ) : (fun n : ℕ => chebCoeff f n) =o[atTop] (fun n => ((n : ℝ) ^ m)⁻¹) :=
  dlmf_3_11_ii_smooth m (hf.of_le (by exact_mod_cast le_top))

/-! ### 3.11.12: general intervals -/

theorem affine_mapsTo {a b : ℝ} (hab : a < b) :
    MapsTo (fun t : ℝ => ((b - a) * t + a + b) / 2) (Icc (-1) 1) (Icc a b) := fun t ht => by
  have h1 := mul_le_mul_of_nonneg_left ht.1 (sub_nonneg.mpr hab.le)
  have h2 := mul_le_mul_of_nonneg_left ht.2 (sub_nonneg.mpr hab.le)
  constructor <;> simp only at * <;> linarith

theorem rescale_mem {a b : ℝ} (hab : a < b) {x : ℝ} (hx : x ∈ Icc a b) :
    (2 * x - a - b) / (b - a) ∈ Icc (-1 : ℝ) 1 := by
  have hba : 0 < b - a := sub_pos.mpr hab
  constructor
  · rw [le_div_iff₀ hba]; linarith [hx.1]
  · rw [div_le_iff₀ hba]; linarith [hx.2]

theorem affine_rescale {a b : ℝ} (hab : a < b) (x : ℝ) :
    ((b - a) * ((2 * x - a - b) / (b - a)) + a + b) / 2 = x := by
  have hba : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  field_simp
  ring

/-- **DLMF 3.11.12**: on `[a, b]`, `f(x) = ∑'_{n=0}^∞ dₙ Tₙ((2x − a − b)/(b − a))` uniformly, with
`dₙ` the coefficients 3.11.10 of `t ↦ f(((b − a)t + a + b)/2)`. -/
theorem dlmf_3_11_12 {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    TendstoUniformlyOn (fun N x => chebPartialSum
      (chebCoeff fun t => f (((b - a) * t + a + b) / 2)) N ((2 * x - a - b) / (b - a)))
      f atTop (Icc a b) := by
  have hF : ContDiffOn ℝ 1 (fun t => f (((b - a) * t + a + b) / 2)) (Icc (-1) 1) :=
    hf.comp (by fun_prop : ContDiff ℝ 1 fun t : ℝ => ((b - a) * t + a + b) / 2).contDiffOn
      (affine_mapsTo hab)
  have h := (dlmf_3_11_11 hF).comp fun x : ℝ => (2 * x - a - b) / (b - a)
  refine (h.mono fun x hx => rescale_mem hab hx).congr_right fun x _ => ?_
  simp only [Function.comp_apply, affine_rescale hab]

/-! ### 3.11.13: the equioscillation of `T_{n+1}` -/

/-- **DLMF 3.11.13**: if `εₙ(x) = d T_{n+1}((2x − a − b)/(b − a))` exactly on `[a, b]`, then the
right-hand side has exactly the extremal properties required by §3.11(i): `pₙ` is the minimax
polynomial, with minimax error `|d|`. -/
theorem dlmf_3_11_13 {a b : ℝ} (hab : a < b) (f : C(Icc a b, ℝ)) {n : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ n) (d : ℝ)
    (hf : ∀ x : Icc a b, f x - p.eval (x : ℝ) =
      d * (T ℝ (n + 1 : ℕ)).eval ((2 * x - a - b) / (b - a))) :
    IsMinimax f n p ∧ minimaxErr f p = |d| := by
  have hba : 0 < b - a := sub_pos.mpr hab
  -- the extrema of `T_{n+1}`, in increasing order
  set y : Fin (n + 2) → ℝ := fun j => ((b - a) * node (n + 1) (n + 1 - j) + a + b) / 2 with hy
  have hymem : ∀ j, y j ∈ Icc a b := fun j => affine_mapsTo hab node_mem_Icc
  have hresc : ∀ j, (2 * y j - a - b) / (b - a) = node (n + 1) (n + 1 - j) := fun j => by
    simp only [hy]; field_simp; ring
  have hval : ∀ j : Fin (n + 2), f ⟨y j, hymem j⟩ - p.eval (y j) = d * (-1) ^ (n + 1 - (j : ℕ)) :=
    fun j => by
      rw [hf ⟨y j, hymem j⟩]
      simp only
      rw [hresc, eval_T_real_node (Finset.mem_Iic.mpr (by omega))]
  have hmono : StrictMono y := fun i j hij => by
    simp only [hy]
    have hl := node_lt (n := n + 1) (i := n + 1 - (j : ℕ)) (j := n + 1 - (i : ℕ)) (by omega)
      (by have : (i : ℕ) < j := hij; omega)
    have := mul_lt_mul_of_pos_left hl hba
    linarith
  have herr : minimaxErr f p = |d| := by
    apply le_antisymm
    · refine (ContinuousMap.norm_le _ (abs_nonneg d)).mpr fun x => ?_
      simp only [ContinuousMap.sub_apply, polyOn_apply, Real.norm_eq_abs, hf x, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg d)
        (abs_eval_T_real_le_one _ (abs_le.mpr (rescale_mem hab x.2)))
    · have := abs_err_le f p ⟨y 0, hymem 0⟩
      rw [hval 0, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one] at this
      exact this
  refine ⟨dlmf_3_11_i_sufficient f hp (x := fun j => ⟨y j, hymem j⟩) hmono (fun j => ?_)
    (fun j => ?_), herr⟩
  · rw [hval j, herr, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
  · have h1 := hval j.succ
    have h2 := hval j.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
    rw [h1, h2, show n + 1 - (j : ℕ) = (n + 1 - ((j : ℕ) + 1)) + 1 by omega, pow_succ]
    ring

/-! ### 3.11.14: Powell's bound -/

/-- `∫₀^π cos^k θ cos(mθ) dθ = 0` for `k < m`. -/
theorem integral_cos_pow_mul_cos {k m : ℕ} (h : k < m) :
    ∫ θ in (0 : ℝ)..π, Real.cos θ ^ k * Real.cos (m * θ) = 0 := by
  induction k generalizing m with
  | zero =>
    have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [pow_zero, one_mul]
    rw [intervalIntegral.integral_comp_mul_left (fun t => Real.cos t) hm, integral_cos]
    simp [Real.sin_nat_mul_pi]
  | succ k ih =>
    have e : ∀ θ : ℝ, Real.cos θ ^ (k + 1) * Real.cos (m * θ) =
        1 / 2 * (Real.cos θ ^ k * Real.cos ((m + 1 : ℕ) * θ)) +
          1 / 2 * (Real.cos θ ^ k * Real.cos ((m - 1 : ℕ) * θ)) := fun θ => by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one, add_mul, sub_mul, one_mul,
        Real.cos_add, Real.cos_sub]
      ring
    rw [intervalIntegral.integral_congr fun θ _ => e θ,
      intervalIntegral.integral_add ((by fun_prop : Continuous fun θ : ℝ =>
        1 / 2 * (Real.cos θ ^ k * Real.cos ((m + 1 : ℕ) * θ))).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun θ : ℝ =>
        1 / 2 * (Real.cos θ ^ k * Real.cos ((m - 1 : ℕ) * θ))).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      ih (by omega), ih (by omega)]
    ring

/-- The Chebyshev coefficients `c_m` of a polynomial of degree `≤ n` vanish for `m > n`. -/
theorem chebCoeff_poly_eq_zero {q : ℝ[X]} {n m : ℕ} (hq : q.natDegree ≤ n) (hm : n < m) :
    chebCoeff (fun x => q.eval x) m = 0 := by
  rw [chebCoeff]
  have e : ∀ θ : ℝ, q.eval (Real.cos θ) * Real.cos (m * θ) =
      ∑ k ∈ range (n + 1), q.coeff k * (Real.cos θ ^ k * Real.cos (m * θ)) := fun θ => by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hq), sum_mul]
    exact sum_congr rfl fun _ _ => by ring
  rw [intervalIntegral.integral_congr fun θ _ => e θ, intervalIntegral.integral_finsetSum
    fun k _ => (by fun_prop : Continuous fun θ : ℝ =>
      q.coeff k * (Real.cos θ ^ k * Real.cos (m * θ))).intervalIntegrable _ _]
  rw [sum_eq_zero fun k hk => by
    rw [intervalIntegral.integral_const_mul,
      integral_cos_pow_mul_cos (by have := mem_range.mp hk; omega), mul_zero], mul_zero]

/-- The truncated Chebyshev series reproduces polynomials of degree `≤ n`. -/
theorem chebPartialSum_poly {q : ℝ[X]} {n : ℕ} (hq : q.natDegree ≤ n) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) : chebPartialSum (chebCoeff fun x => q.eval x) n x = q.eval x := by
  have hC : ContDiffOn ℝ 1 (fun x => q.eval x) (Icc (-1) 1) := (contDiff_aeval q 1).contDiffOn
  have hs := dlmf_3_11_11_hasSum hC hx
  have h2 : HasSum (fun k => chebCoeff (fun x => q.eval x) (k + 1) * (T ℝ (k + 1 : ℕ)).eval x)
      (∑ k ∈ range n, chebCoeff (fun x => q.eval x) (k + 1) * (T ℝ (k + 1 : ℕ)).eval x) :=
    hasSum_sum_of_ne_finset_zero fun k hk => by
      rw [chebCoeff_poly_eq_zero hq (by simp at hk; omega), zero_mul]
  have := hs.unique h2
  rw [chebPartialSum]
  linarith

theorem chebCoeff_sub {f h : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1))
    (hh : ContinuousOn h (Icc (-1) 1)) (n : ℕ) :
    chebCoeff (fun x => f x - h x) n = chebCoeff f n - chebCoeff h n := by
  simp only [chebCoeff]
  have hi1 : IntervalIntegrable (fun θ => f (Real.cos θ) * Real.cos (n * θ)) volume 0 π :=
    ((continuous_comp_cos hf).mul (by fun_prop)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ => h (Real.cos θ) * Real.cos (n * θ)) volume 0 π :=
    ((continuous_comp_cos hh).mul (by fun_prop)).intervalIntegrable _ _
  rw [← mul_sub, ← intervalIntegral.integral_sub hi1 hi2]
  congr 1
  exact intervalIntegral.integral_congr fun θ _ => by ring

theorem chebPartialSum_sub (c c' : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    chebPartialSum (fun k => c k - c' k) n x = chebPartialSum c n x - chebPartialSum c' n x := by
  simp only [chebPartialSum, sub_mul, sum_sub_distrib]
  ring

/-- The Dirichlet-kernel bound `|Sₙh(x)| ≤ Lₙ max|h|` on `[−1, 1]`. -/
theorem chebPartialSum_bound {h : ℝ → ℝ} (hh : ContinuousOn h (Icc (-1) 1)) {E : ℝ}
    (hE : ∀ x ∈ Icc (-1 : ℝ) 1, |h x| ≤ E) (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |chebPartialSum (chebCoeff h) n x| ≤ lebesgueConst n * E := by
  set g : ℝ → ℂ := fun t => (h (Real.cos t) : ℂ)
  have hgc : Continuous g := Complex.continuous_ofReal.comp (continuous_comp_cos hh)
  have hπ := pi_pos
  set θ := arccos x
  have hxθ : Real.cos θ = x := cos_arccos hx.1 hx.2
  have e1 : chebPartialSum (chebCoeff h) n x = chebPartialSum (chebCoeff h) n (Real.cos θ) := by
    rw [hxθ]
  have e2 : |chebPartialSum (chebCoeff h) n (Real.cos θ)| =
      ‖((chebPartialSum (chebCoeff h) n (Real.cos θ) : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [e1, e2, chebPartialSum_cos_eq hh,
    fourierPartialSum_eq_fold (cheb_periodic h) (hgc.intervalIntegrable _ _), norm_smul,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
  have hH : Continuous (halfDirichlet n) := continuous_halfDirichlet n
  have hle : ‖∫ s in (0 : ℝ)..π, (g (θ + s) + g (θ - s)) * (halfDirichlet n s : ℂ)‖ ≤
      ∫ s in (0 : ℝ)..π, 2 * E * |halfDirichlet n s| := by
    refine intervalIntegral.norm_integral_le_of_norm_le hπ.le
      (Eventually.of_forall fun s _ => ?_)
      ((continuous_const.mul hH.abs).intervalIntegrable _ _)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : ‖g (θ + s) + g (θ - s)‖ ≤ 2 * E := by
      refine (norm_add_le _ _).trans ?_
      simp only [g, Complex.norm_real, Real.norm_eq_abs]
      linarith [hE _ (cos_mem_Icc (θ + s)), hE _ (cos_mem_Icc (θ - s))]
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hL : ∫ s in (0 : ℝ)..π, 2 * E * |halfDirichlet n s| = π * lebesgueConst n * E := by
    have e2 : ∫ s in (0 : ℝ)..π, 2 * E * |halfDirichlet n s| =
        E * ∫ s in (0 : ℝ)..π, |Real.sin ((n + 1 / 2) * s)| / Real.sin (s / 2) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => ?_)
      rw [uIoc_of_le hπ.le] at hs
      have hsin : 0 < Real.sin (s / 2) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) (by linarith [hs.2])
      rw [← two_mul_halfDirichlet_mul_sin, abs_mul, abs_mul, abs_of_pos hsin, abs_two]
      field_simp
    rw [e2, lebesgueConst]
    field_simp
  calc 1 / π * ‖∫ s in (0 : ℝ)..π, (g (θ + s) + g (θ - s)) * (halfDirichlet n s : ℂ)‖
      ≤ 1 / π * (π * lebesgueConst n * E) := by gcongr; exact hle.trans hL.le
    _ = lebesgueConst n * E := by field_simp

/-- Powell's bound on `[−1, 1]`: if `|f − q| ≤ E` on `[−1, 1]` with `deg q ≤ n`, then the remainder
of the truncated Chebyshev series is at most `(1 + Lₙ) E`. -/
theorem powell_bound {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) {n : ℕ} {q : ℝ[X]}
    (hq : q.natDegree ≤ n) {E : ℝ} (hE : ∀ x ∈ Icc (-1 : ℝ) 1, |f x - q.eval x| ≤ E) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    |f x - chebPartialSum (chebCoeff f) n x| ≤ (1 + lebesgueConst n) * E := by
  set h : ℝ → ℝ := fun y => f y - q.eval y with hhdef
  have hqc : ContinuousOn (fun y => q.eval y) (Icc (-1) 1) := q.continuous.continuousOn
  have hh : ContinuousOn h (Icc (-1) 1) := hf.sub hqc
  have hS : chebPartialSum (chebCoeff f) n x = chebPartialSum (chebCoeff h) n x + q.eval x := by
    have e : chebCoeff h = fun k => chebCoeff f k - chebCoeff (fun y => q.eval y) k :=
      funext (chebCoeff_sub hf hqc)
    rw [e, chebPartialSum_sub, chebPartialSum_poly hq hx]
    ring
  have hb := chebPartialSum_bound hh hE n hx
  have hx' : |h x| ≤ E := hE x hx
  rw [hS]
  calc |f x - (chebPartialSum (chebCoeff h) n x + q.eval x)|
      = |h x - chebPartialSum (chebCoeff h) n x| := by simp only [h]; ring_nf
    _ ≤ |h x| + |chebPartialSum (chebCoeff h) n x| := abs_sub _ _
    _ ≤ (1 + lebesgueConst n) * E := by linarith

/-- **DLMF 3.11.14** (Powell): on `[a, b]`, if `|f − p| ≤ E` with `deg p ≤ n`, then the remainder
`|f(x) − ∑'_{k=0}^n d_k T_k((2x − a − b)/(b − a))|` is at most `(1 + Lₙ) E`. -/
theorem dlmf_3_11_14 {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) {E : ℝ}
    (hE : ∀ x ∈ Icc a b, |f x - p.eval x| ≤ E) {x : ℝ} (hx : x ∈ Icc a b) :
    |f x - chebPartialSum (chebCoeff fun t => f (((b - a) * t + a + b) / 2)) n
      ((2 * x - a - b) / (b - a))| ≤ (1 + lebesgueConst n) * E := by
  set r : ℝ[X] := C ((b - a) / 2) * X + C ((a + b) / 2)
  have hr : ∀ t, r.eval t = ((b - a) * t + a + b) / 2 := fun t => by
    simp only [r, eval_add, eval_mul, eval_C, eval_X]; ring
  have hq : (p.comp r).natDegree ≤ n := by
    refine (natDegree_comp_le).trans ?_
    have : r.natDegree ≤ 1 := natDegree_linear_le
    calc p.natDegree * r.natDegree ≤ n * 1 := Nat.mul_le_mul hp this
      _ = n := mul_one n
  have hF : ContinuousOn (fun t => f (((b - a) * t + a + b) / 2)) (Icc (-1) 1) :=
    hf.comp (by fun_prop : Continuous fun t : ℝ => ((b - a) * t + a + b) / 2).continuousOn
      (affine_mapsTo hab)
  have h := powell_bound hF hq (E := E) (fun t ht => by
    rw [eval_comp, hr]; exact hE _ (affine_mapsTo hab ht)) (rescale_mem hab hx)
  rwa [affine_rescale hab] at h

/-- **DLMF 3.11.14** with the minimax polynomial: the remainder of the truncated Chebyshev series
is at most `1 + Lₙ` times the maximum error of the minimax polynomial `pₙ`. -/
theorem dlmf_3_11_14_minimax {a b : ℝ} (hab : a < b) (f : C(Icc a b, ℝ)) {n : ℕ} {p : ℝ[X]}
    (hp : IsMinimax f n p) (x : Icc a b) :
    |f x - chebPartialSum (chebCoeff fun t => IccExtend hab.le f (((b - a) * t + a + b) / 2)) n
      ((2 * x - a - b) / (b - a))| ≤ (1 + lebesgueConst n) * minimaxErr f p := by
  have hfc : ContinuousOn (IccExtend hab.le f) (Icc a b) :=
    (f.continuous.Icc_extend' (h := hab.le)).continuousOn
  have h := dlmf_3_11_14 hab hfc hp.1 (E := minimaxErr f p)
    (fun y hy => by rw [IccExtend_of_mem hab.le f hy]; exact abs_err_le f p ⟨y, hy⟩) x.2
  rwa [IccExtend_val] at h

/-- **DLMF §3.11(ii)**: `L₀ = 1`. -/
theorem lebesgueConst_zero : lebesgueConst 0 = 1 := by
  have hπ := pi_pos
  have h : ∫ t in (0 : ℝ)..π, |Real.sin ((((0 : ℕ) : ℝ) + 1 / 2) * t)| / Real.sin (t / 2) =
      ∫ _ in (0 : ℝ)..π, (1 : ℝ) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hπ.le] at ht
    have hsin : 0 < Real.sin (t / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2])
    rw [show (((0 : ℕ) : ℝ) + 1 / 2) * t = t / 2 by push_cast; ring, abs_of_pos hsin,
      div_self hsin.ne']
  rw [lebesgueConst, h, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  field_simp

end Azurite.DLMF
