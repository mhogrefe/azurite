/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section15
import Azurite.DLMF.Chapter1.Section8
import Azurite.DLMF.Chapter1.Section9
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# DLMF §1.15(iii): Summability of Fourier series

Formalizations of <https://dlmf.nist.gov/1.15#iii>. Functions are `2π`-periodic `f : ℝ → ℂ`,
integrable on `[0, 2π]`, with coefficients `fourierF` (1.15.19).

* Poisson kernel `diskPoisson` (1.15.12–1.15.14). `dlmf_1_15_12` splits the bilateral geometric
  series, `dlmf_1_15_13` integrates it termwise, and `dlmf_1_15_14` is the uniform decay on
  `[δ, 2π − δ]`.
* Fejér kernel `fejerK` (1.15.15–1.15.17). `fejerK_eq_sum` writes it as the average of the
  Dirichlet kernels `2Dₘ` of §1.8 (away from `θ ∈ 2πℤ`). This gives `dlmf_1_15_16` and
  `dlmf_1_15_17`.
* Abel means `abelMean` (1.15.18) and the Poisson integral `dlmf_1_15_20` (termwise integration).
  Cesàro means `cesaroMeanF`, `fourierSym` (1.15.21–1.15.22) and the Fejér integral `dlmf_1_15_23`.
* 1.15.24 (`dlmf_1_15_24_abel` with `r → 1−`, `dlmf_1_15_24_cesaro`; uniform versions for
  continuous `f`). These follow from one approximate-identity theorem (`tendsto_kernel_mean`,
  `tendstoUniformly_kernel_mean`) for even, periodic, bounded kernels `k ≥ 0` of mean 1 that tend
  to `0` uniformly on each `[δ, π]`. The proof folds the integral onto `[0, π]`
  (`integral_kernel_eq`) and uses the estimate `norm_integral_kernel_le`.
* Real `f` (1.15.25–1.15.28). `fourierG` is analytic in the unit disk (`dlmf_1_15_27`), with
  `A(r, θ) = ℜ G(re^{iθ})` (`dlmf_1_15_iii_re`) and `ℑ G` given by 1.15.28 (`dlmf_1_15_28`).
  Hence `A`
  is harmonic in polar coordinates (`dlmf_1_15_iii_harmonic`, from 1.9.27).
-/

open Set Filter Topology MeasureTheory Complex Finset
open scoped Real Interval

namespace Azurite.DLMF

/-! ### The Poisson kernel (1.15.12–1.15.14) -/

/-- The Poisson kernel `P(r, θ) = (1 − r²)/(1 − 2r cos θ + r²)`. -/
noncomputable def diskPoisson (r θ : ℝ) : ℝ := (1 - r ^ 2) / (1 - 2 * r * Real.cos θ + r ^ 2)

theorem diskPoisson_den_pos {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (θ : ℝ) :
    0 < 1 - 2 * r * Real.cos θ + r ^ 2 := by
  nlinarith [Real.cos_le_one θ, sq_nonneg (1 - r)]

/-- **DLMF (1.15.12)**: `P(r, θ) = ∑_{n ∈ ℤ} r^{|n|} e^{inθ}` (`0 ≤ r < 1`). -/
theorem dlmf_1_15_12 {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (θ : ℝ) :
    HasSum (fun n : ℤ => (r : ℂ) ^ n.natAbs * cexp (n * θ * I)) (diskPoisson r θ : ℂ) := by
  set z : ℂ := r * cexp (θ * I)
  set w : ℂ := r * cexp (-(θ * I))
  have hz : ‖z‖ < 1 := by
    simp only [z, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, norm_exp_ofReal_mul_I,
      mul_one]; exact h1
  have hw : ‖w‖ < 1 := by
    have : w = r * cexp (((-θ : ℝ) : ℂ) * I) := by simp only [w]; push_cast; ring_nf
    rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, norm_exp_ofReal_mul_I,
      mul_one]; exact h1
  have hA : HasSum (fun n : ℕ => (r : ℂ) ^ (n : ℤ).natAbs * cexp ((n : ℤ) * θ * I)) (1 - z)⁻¹ := by
    refine (hasSum_geometric_of_norm_lt_one hz).congr_fun fun n => ?_
    simp only [z, Int.natAbs_natCast, mul_pow, ← Complex.exp_nat_mul]
    push_cast; ring_nf
  have hB : HasSum (fun n : ℕ => (r : ℂ) ^ (-((n : ℤ) + 1)).natAbs *
      cexp ((-((n : ℤ) + 1) : ℤ) * θ * I)) (w * (1 - w)⁻¹) := by
    refine ((hasSum_geometric_of_norm_lt_one hw).mul_left w).congr_fun fun n => ?_
    have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    simp only [w, this, mul_pow, ← Complex.exp_nat_mul]
    rw [pow_succ, show cexp ((((-((n : ℤ) + 1)) : ℤ) : ℂ) * θ * I) =
      cexp (-(θ * I)) * cexp (n * -(θ * I)) by rw [← Complex.exp_add]; push_cast; ring_nf]
    ring
  have h := HasSum.of_nat_of_neg_add_one
    (f := fun n : ℤ => (r : ℂ) ^ n.natAbs * cexp (n * θ * I)) hA hB
  suffices key : ((diskPoisson r θ : ℝ) : ℂ) = (1 - z)⁻¹ + w * (1 - w)⁻¹ by rw [key]; exact h
  have hzw : z * w = (r : ℂ) ^ 2 := by
    simp only [z, w]; rw [mul_mul_mul_comm, ← Complex.exp_add]; simp; ring
  have hzw' : z + w = 2 * r * Complex.cos θ := by
    simp only [z, w]; rw [Complex.cos]; ring_nf
  have h1z : 1 - z ≠ 0 := fun e => by
    have : z = 1 := by linear_combination -e
    rw [this, norm_one] at hz; exact lt_irrefl _ hz
  have h1w : 1 - w ≠ 0 := fun e => by
    have : w = 1 := by linear_combination -e
    rw [this, norm_one] at hw; exact lt_irrefl _ hw
  have hden : ((1 - 2 * r * Real.cos θ + r ^ 2 : ℝ) : ℂ) = (1 - z) * (1 - w) := by
    push_cast; linear_combination hzw' - hzw
  rw [diskPoisson, ofReal_div, hden, eq_comm, ← sub_eq_zero]
  have e : (1 - z)⁻¹ + w * (1 - w)⁻¹ - ((1 - r ^ 2 : ℝ) : ℂ) / ((1 - z) * (1 - w)) =
      ((1 - w) + w * (1 - z) - ((1 - r ^ 2 : ℝ) : ℂ)) / ((1 - z) * (1 - w)) := by
    field_simp
  rw [e, div_eq_zero_iff]
  left
  push_cast
  linear_combination (-1 : ℂ) * hzw

theorem summable_pow_natAbs {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun n : ℤ => r ^ n.natAbs := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using summable_geometric_of_lt_one h0 h1
  · refine ((summable_geometric_of_lt_one h0 h1).mul_left r).congr fun n => ?_
    have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    simp only [this, pow_succ]; ring

theorem diskPoisson_neg (r θ : ℝ) : diskPoisson r (-θ) = diskPoisson r θ := by
  simp [diskPoisson, Real.cos_neg]

theorem diskPoisson_nonneg {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (θ : ℝ) : 0 ≤ diskPoisson r θ :=
  div_nonneg (by nlinarith) (diskPoisson_den_pos h0 h1 θ).le

theorem diskPoisson_periodic (r : ℝ) : Function.Periodic (diskPoisson r) (2 * π) := fun θ => by
  simp [diskPoisson, Real.cos_add_two_pi]

theorem continuous_diskPoisson {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : Continuous (diskPoisson r) :=
  continuous_const.div (by fun_prop) fun θ => (diskPoisson_den_pos h0 h1 θ).ne'

theorem diskPoisson_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (θ : ℝ) :
    diskPoisson r θ ≤ (1 + r) / (1 - r) := by
  have hd := diskPoisson_den_pos h0 h1 θ
  rw [diskPoisson, div_le_div_iff₀ hd (by linarith)]
  nlinarith [Real.cos_le_one θ, sq_nonneg (1 - r)]

/-! ### Fourier coefficients and Abel means (1.15.18–1.15.20) -/

/-- **DLMF (1.15.19)**: `F(n) = (1/(2π)) ∫_0^{2π} f(t) e^{−int} dt`. -/
noncomputable def fourierF (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ t in (0 : ℝ)..2 * π, f t * cexp (-(n * t * I))

/-- **DLMF (1.15.18)**: the Abel means `A(r, θ) = ∑_{n ∈ ℤ} r^{|n|} F(n) e^{inθ}`. -/
noncomputable def abelMean (f : ℝ → ℂ) (r θ : ℝ) : ℂ :=
  ∑' n : ℤ, (r : ℂ) ^ n.natAbs * fourierF f n * cexp (n * θ * I)

theorem two_pi_pos : (0 : ℝ) < 2 * π := by positivity

theorem norm_fourierF_le {f : ℝ → ℂ} (n : ℤ) :
    ‖fourierF f n‖ ≤ 1 / (2 * π) * ∫ t in (0 : ℝ)..2 * π, ‖f t‖ := by
  rw [fourierF, norm_mul, show ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) by
    rw [norm_div, norm_one, show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg two_pi_pos.le] ]
  refine mul_le_mul_of_nonneg_left ((intervalIntegral.norm_integral_le_integral_norm
    two_pi_pos.le).trans (le_of_eq ?_)) (by positivity)
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [norm_mul, show -((n : ℂ) * t * I) = ((-(n * t) : ℝ) : ℂ) * I by push_cast; ring,
    norm_exp_ofReal_mul_I, mul_one]

/-- **DLMF (1.15.20)**: `A(r, θ) = (1/(2π)) ∫_0^{2π} P(r, θ − t) f(t) dt` (`0 ≤ r < 1`, `f`
integrable on `[0, 2π]`). -/
theorem dlmf_1_15_20 {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 (2 * π)) {r : ℝ}
    (h0 : 0 ≤ r) (h1 : r < 1) (θ : ℝ) :
    abelMean f r θ = (1 / (2 * π) : ℂ) *
      ∫ t in (0 : ℝ)..2 * π, (diskPoisson r (θ - t) : ℂ) * f t := by
  have hfI : IntegrableOn f (Ioc 0 (2 * π)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).mp hf
  set G : ℤ → ℝ → ℂ := fun n t => (r : ℂ) ^ n.natAbs * cexp (n * θ * I) *
    (f t * cexp (-(n * t * I)))
  have hterm : ∀ n t, ‖G n t‖ = r ^ n.natAbs * ‖f t‖ := fun n t => by
    simp only [G, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg h0]
    rw [show (n : ℂ) * θ * I = ((n * θ : ℝ) : ℂ) * I by push_cast; ring,
      show -((n : ℂ) * t * I) = ((-(n * t) : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, norm_exp_ofReal_mul_I]
    ring
  have hGi : ∀ n, Integrable (G n) (volume.restrict (Ioc 0 (2 * π))) := fun n => by
    refine (hfI.norm.const_mul (r ^ n.natAbs)).mono' ?_ (ae_of_all _ fun t => (hterm n t).le)
    show AEStronglyMeasurable (fun t => ((r : ℂ) ^ n.natAbs * cexp (n * θ * I)) *
      (f t * cexp (-(n * t * I)))) _
    exact aestronglyMeasurable_const.mul (hfI.aestronglyMeasurable.mul
      (by fun_prop : Continuous fun t : ℝ => cexp (-(n * t * I))).aestronglyMeasurable)
  have hGs : Summable fun n => ∫ t, ‖G n t‖ ∂(volume.restrict (Ioc 0 (2 * π))) := by
    simp_rw [hterm, integral_const_mul]
    exact (summable_pow_natAbs h0 h1).mul_right _
  have hsum := integral_tsum_of_summable_integral_norm hGi hGs
  have hpt : ∀ t, (diskPoisson r (θ - t) : ℂ) * f t = ∑' n, G n t := fun t => by
    rw [(dlmf_1_15_12 h0 h1 (θ - t)).tsum_eq.symm, ← tsum_mul_right]
    congr 1; funext n
    simp only [G]
    rw [show (n : ℂ) * ((θ - t : ℝ) : ℂ) * I = n * θ * I + -(n * t * I) by push_cast; ring,
      Complex.exp_add]
    ring
  rw [intervalIntegral.integral_of_le two_pi_pos.le]
  simp_rw [hpt]
  rw [← hsum, abelMean, ← tsum_mul_left]
  congr 1; funext n
  simp only [G]
  rw [integral_const_mul, fourierF, intervalIntegral.integral_of_le two_pi_pos.le]
  ring

theorem fourierF_one (n : ℤ) : fourierF (fun _ => 1) n = if n = 0 then 1 else 0 := by
  rw [fourierF]
  split_ifs with hn
  · subst hn; simp; field_simp
  · have hc : -((n : ℂ) * I) ≠ 0 := by simp [hn, I_ne_zero]
    have e : ∀ t : ℝ, (1 : ℂ) * cexp (-(n * t * I)) = cexp (-((n : ℂ) * I) * t) := fun t => by
      ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    push_cast
    rw [show -((n : ℂ) * I) * (2 * π) = ((-n : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I]
    simp

/-- **DLMF (1.15.13)**: `(1/(2π)) ∫_0^{2π} P(r, θ) dθ = 1` (`0 ≤ r < 1`). -/
theorem dlmf_1_15_13 {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    1 / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, diskPoisson r θ = 1 := by
  have h := dlmf_1_15_20 (f := fun _ => (1 : ℂ)) intervalIntegrable_const h0 h1 0
  rw [abelMean, tsum_eq_single 0 (fun n hn => by simp [fourierF_one, hn])] at h
  simp only [fourierF_one, ite_true, Int.natAbs_zero, pow_zero, Int.cast_zero, zero_mul,
    Complex.exp_zero, mul_one, zero_sub] at h
  simp_rw [diskPoisson_neg] at h
  rw [intervalIntegral.integral_ofReal] at h
  apply ofReal_injective
  push_cast
  linear_combination -h

theorem sin_half_le {δ θ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (hθ : θ ∈ Icc δ (2 * π - δ)) :
    Real.sin (δ / 2) ≤ Real.sin (θ / 2) := by
  rcases le_or_gt (θ / 2) (π / 2) with h | h
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h (by linarith [hθ.1])
  · rw [← Real.sin_pi_sub (θ / 2)]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith)
      (by linarith [hθ.2])

theorem sin_half_pos {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) : 0 < Real.sin (δ / 2) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

/-- **DLMF (1.15.14)**: `P(r, θ) → 0` as `r → 1−`, uniformly for `θ ∈ [δ, 2π − δ]`
(`0 < δ < π`). -/
theorem dlmf_1_15_14 {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    TendstoUniformlyOn diskPoisson (fun _ => 0) (𝓝[<] 1) (Icc δ (2 * π - δ)) := by
  set s := Real.sin (δ / 2)
  have hs := sin_half_pos hδ hδπ
  have hbound : ∀ r ∈ Ico (1 / 2 : ℝ) 1, ∀ θ ∈ Icc δ (2 * π - δ),
      0 ≤ diskPoisson r θ ∧ diskPoisson r θ ≤ (1 - r ^ 2) / (2 * s ^ 2) := fun r hr θ hθ => by
    have h0 : 0 ≤ r := by linarith [hr.1]
    refine ⟨diskPoisson_nonneg h0 hr.2 θ, ?_⟩
    have hsθ := sin_half_le hδ hδπ hθ
    have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have := Real.cos_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at this
      nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
    have hd := diskPoisson_den_pos h0 hr.2 θ
    rw [diskPoisson, div_le_div_iff₀ hd (by positivity)]
    have : 2 * s ^ 2 ≤ 1 - 2 * r * Real.cos θ + r ^ 2 := by
      rw [hcos]
      have : s ^ 2 ≤ Real.sin (θ / 2) ^ 2 := pow_le_pow_left₀ hs.le hsθ 2
      nlinarith [sq_nonneg (1 - r), hr.1]
    exact mul_le_mul_of_nonneg_left this (by nlinarith [hr.2])
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hc : Tendsto (fun r : ℝ => (1 - r ^ 2) / (2 * s ^ 2)) (𝓝[<] 1) (𝓝 0) := by
    have := ((by fun_prop : Continuous fun r : ℝ => (1 - r ^ 2) / (2 * s ^ 2)).tendsto 1)
    simp only [one_pow, sub_self, zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds
  filter_upwards [(tendsto_order.1 hc).2 ε hε, Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)]
    with r hr hr' θ hθ
  obtain ⟨b0, b1⟩ := hbound r ⟨hr'.1.le, hr'.2⟩ θ hθ
  rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_of_nonneg b0]
  exact b1.trans_lt hr

/-! ### The Fejér kernel (1.15.15–1.15.17) -/

/-- **DLMF (1.15.15)**: the Fejér kernel `Kₙ(θ) = (1/(n+1)) (sin(½(n+1)θ)/sin(½θ))²`. -/
noncomputable def fejerK (n : ℕ) (θ : ℝ) : ℝ :=
  1 / (n + 1) * (Real.sin ((n + 1) * θ / 2) / Real.sin (θ / 2)) ^ 2

theorem fejerK_nonneg (n : ℕ) (θ : ℝ) : 0 ≤ fejerK n θ := by
  unfold fejerK; positivity

theorem fejerK_neg (n : ℕ) (θ : ℝ) : fejerK n (-θ) = fejerK n θ := by
  simp only [fejerK, mul_neg, neg_div, Real.sin_neg, div_neg, neg_neg]

theorem fejerK_periodic (n : ℕ) : Function.Periodic (fejerK n) (2 * π) := fun θ => by
  simp only [fejerK]
  have h1 : (n + 1 : ℝ) * (θ + 2 * π) / 2 = (n + 1) * θ / 2 + ((n + 1 : ℕ) : ℝ) * π := by
    push_cast; ring
  have h2 : (θ + 2 * π) / 2 = θ / 2 + ((1 : ℕ) : ℝ) * π := by push_cast; ring
  rw [h1, h2, Real.sin_add_nat_mul_pi, Real.sin_add_nat_mul_pi, div_pow, div_pow, mul_pow,
    mul_pow, ← pow_mul, ← pow_mul, Even.neg_one_pow (n := (n + 1) * 2) ⟨n + 1, by ring⟩,
    Even.neg_one_pow (n := 1 * 2) ⟨1, by ring⟩, one_mul, one_mul]

theorem abs_sin_nat_mul_le (n : ℕ) (y : ℝ) : |Real.sin (n * y)| ≤ n * |Real.sin y| := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    rw [add_mul, one_mul, Real.sin_add]
    calc |Real.sin (n * y) * Real.cos y + Real.cos (n * y) * Real.sin y| ≤
        |Real.sin (n * y)| * 1 + 1 * |Real.sin y| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
      _ ≤ n * |Real.sin y| + |Real.sin y| := by linarith
      _ = (n + 1) * |Real.sin y| := by ring

theorem fejerK_le (n : ℕ) (θ : ℝ) : fejerK n θ ≤ n + 1 := by
  rcases eq_or_ne (Real.sin (θ / 2)) 0 with h | h
  · simp [fejerK, h]; positivity
  have hb : |Real.sin ((n + 1) * θ / 2)| ≤ (n + 1) * |Real.sin (θ / 2)| := by
    have := abs_sin_nat_mul_le (n + 1) (θ / 2)
    push_cast at this; rwa [show (n + 1 : ℝ) * (θ / 2) = (n + 1) * θ / 2 by ring] at this
  have hs : 0 < |Real.sin (θ / 2)| := abs_pos.mpr h
  rw [fejerK, div_pow, ← sq_abs, ← sq_abs (Real.sin (θ / 2))]
  have h2 : |Real.sin ((n + 1) * θ / 2)| ^ 2 ≤ ((n + 1) * |Real.sin (θ / 2)|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [mul_pow] at h2
  have h3 : |Real.sin ((n + 1) * θ / 2)| ^ 2 / |Real.sin (θ / 2)| ^ 2 ≤ (n + 1) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  calc 1 / ((n : ℝ) + 1) * (|Real.sin ((n + 1) * θ / 2)| ^ 2 / |Real.sin (θ / 2)| ^ 2) ≤
      1 / ((n : ℝ) + 1) * (n + 1) ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = n + 1 := by field_simp

theorem measurable_fejerK (n : ℕ) : Measurable (fejerK n) := by
  unfold fejerK; fun_prop

/-- `∑_{k=−m}^{m} e^{ikx} = 2 Dₘ(x)` (`halfDirichlet` of §1.8). -/
theorem sum_Icc_cexp (m : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.Icc (-(m : ℤ)) m, cexp (k * x * I) = ((2 * halfDirichlet m x : ℝ) : ℂ) := by
  induction m with
  | zero => simp [halfDirichlet]
  | succ m ih =>
    have e : Finset.Icc (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ) =
        insert (-((m + 1 : ℕ) : ℤ)) (insert ((m + 1 : ℕ) : ℤ) (Finset.Icc (-(m : ℤ)) m)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [e, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; push_cast; omega), ih, halfDirichlet,
      halfDirichlet, Finset.sum_range_succ]
    push_cast
    rw [show ((m : ℂ) + 1) * x = (((m + 1) * x : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos]
    rw [ofReal_cos, Complex.cos]
    push_cast
    ring_nf

theorem sum_sin_mul_sin (n : ℕ) (x : ℝ) :
    ∑ m ∈ Finset.range (n + 1), Real.sin ((m + 1 / 2) * x) * Real.sin (x / 2) =
      Real.sin ((n + 1) * x / 2) ^ 2 := by
  have key : ∀ m : ℕ, Real.sin ((m + 1 / 2) * x) * Real.sin (x / 2) =
      (Real.cos (m * x) - Real.cos ((m + 1) * x)) / 2 := fun m => by
    rw [Real.cos_sub_cos]
    rw [show (m * x + (m + 1) * x) / 2 = (m + 1 / 2) * x by ring,
      show (m * x - (m + 1) * x) / 2 = -(x / 2) by ring, Real.sin_neg]
    ring
  simp_rw [key]
  rw [Real.sin_sq_eq_half_sub, show 2 * ((n + 1) * x / 2) = (n + 1) * x by ring]
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring_nf

/-- `Kₙ(x) = (1/(n+1)) ∑_{m=0}^{n} 2Dₘ(x)` where `sin(x/2) ≠ 0`. -/
theorem fejerK_eq_sum {n : ℕ} {x : ℝ} (hx : Real.sin (x / 2) ≠ 0) :
    fejerK n x = 1 / (n + 1) * ∑ m ∈ Finset.range (n + 1), 2 * halfDirichlet m x := by
  rw [fejerK, div_pow, ← sum_sin_mul_sin]
  congr 1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← two_mul_halfDirichlet_mul_sin]
  field_simp

theorem integral_two_halfDirichlet (m : ℕ) :
    ∫ x in (0 : ℝ)..2 * π, 2 * halfDirichlet m x = 2 * π := by
  have hc : ∀ j : ℕ, ∫ x in (0 : ℝ)..2 * π, Real.cos ((j + 1 : ℕ) * x) = 0 := fun j => by
    have hj : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hj, integral_cos,
      mul_zero, Real.sin_zero, sub_zero, show ((j + 1 : ℕ) : ℝ) * (2 * π) =
        ((2 * (j + 1) : ℕ) : ℝ) * π by push_cast; ring, Real.sin_nat_mul_pi, smul_zero]
  simp only [halfDirichlet]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const
    ((by fun_prop : Continuous fun x : ℝ => ∑ n ∈ Finset.range m,
      Real.cos ((n + 1 : ℕ) * x)).intervalIntegrable _ _), intervalIntegral.integral_finsetSum
    fun j _ => (by fun_prop : Continuous fun x : ℝ => Real.cos ((j + 1 : ℕ) * x)).intervalIntegrable
      _ _]
  simp only [hc, Finset.sum_const_zero, add_zero, intervalIntegral.integral_const, smul_eq_mul,
    sub_zero]
  ring

theorem ae_sin_half_ne_zero (θ : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), Real.sin ((θ - t) / 2) ≠ 0 := by
  have hS : (Set.range fun k : ℤ => θ - 2 * π * k).Countable := Set.countable_range _
  filter_upwards [hS.ae_notMem volume] with t ht h
  apply ht
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
  exact ⟨k, by linarith⟩

/-- **DLMF (1.15.16)**: `(1/(2π)) ∫_0^{2π} Kₙ(θ) dθ = 1`. -/
theorem dlmf_1_15_16 (n : ℕ) : 1 / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, fejerK n θ = 1 := by
  have e : ∫ θ in (0 : ℝ)..2 * π, fejerK n θ =
      ∫ θ in (0 : ℝ)..2 * π, 1 / (n + 1) * ∑ m ∈ Finset.range (n + 1), 2 * halfDirichlet m θ := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_sin_half_ne_zero 0] with t ht _
    rw [zero_sub, neg_div, Real.sin_neg, neg_ne_zero] at ht
    exact fejerK_eq_sum ht
  rw [e, intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum fun m _ =>
    (show Continuous fun x : ℝ => 2 * halfDirichlet m x from
      continuous_const.mul (continuous_halfDirichlet m)).intervalIntegrable _ _]
  simp_rw [integral_two_halfDirichlet]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  field_simp

/-- **DLMF (1.15.17)**: `Kₙ(θ) → 0` as `n → ∞`, uniformly for `θ ∈ [δ, 2π − δ]`
(`0 < δ < π`). -/
theorem dlmf_1_15_17 {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    TendstoUniformlyOn fejerK (fun _ => 0) atTop (Icc δ (2 * π - δ)) := by
  set s := Real.sin (δ / 2)
  have hs := sin_half_pos hδ hδπ
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hc : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * (1 / s ^ 2)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (1 / s ^ 2)
    rwa [zero_mul] at this
  filter_upwards [(tendsto_order.1 hc).2 ε hε] with n hn θ hθ
  have hsθ := sin_half_le hδ hδπ hθ
  rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_of_nonneg (fejerK_nonneg n θ)]
  refine lt_of_le_of_lt ?_ hn
  rw [fejerK]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [div_pow, div_le_div_iff₀ (pow_pos (hs.trans_le hsθ) 2) (by positivity), one_mul]
  have h1 : Real.sin ((n + 1) * θ / 2) ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]; exact Real.abs_sin_le_one _
  have h2 : s ^ 2 ≤ Real.sin (θ / 2) ^ 2 := pow_le_pow_left₀ hs.le hsθ 2
  nlinarith [sq_nonneg (Real.sin ((n + 1) * θ / 2)), sq_nonneg s]

/-! ### Cesàro means (1.15.21–1.15.23) -/

/-- **DLMF (1.15.22)**: `sₙ(θ) = ∑_{k=−n}^{n} F(k) e^{ikθ}`. -/
noncomputable def fourierSym (f : ℝ → ℂ) (n : ℕ) (θ : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(n : ℤ)) n, fourierF f k * cexp (k * θ * I)

/-- **DLMF (1.15.21)**: the Cesàro means `σₙ(θ) = (s₀(θ) + ⋯ + sₙ(θ))/(n + 1)`. -/
noncomputable def cesaroMeanF (f : ℝ → ℂ) (n : ℕ) (θ : ℝ) : ℂ :=
  (∑ m ∈ Finset.range (n + 1), fourierSym f m θ) / (n + 1)

theorem fourierSym_eq_integral {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 (2 * π)) (m : ℕ)
    (θ : ℝ) : fourierSym f m θ = (1 / (2 * π) : ℂ) *
      ∫ t in (0 : ℝ)..2 * π, ((2 * halfDirichlet m (θ - t) : ℝ) : ℂ) * f t := by
  have hi : ∀ k : ℤ, IntervalIntegrable (fun t => cexp (k * θ * I) * (f t * cexp (-(k * t * I))))
      volume 0 (2 * π) := fun k =>
    (hf.mul_continuousOn (by fun_prop : Continuous fun t : ℝ => cexp (-(k * t * I))).continuousOn
      ).const_mul _
  simp_rw [← sum_Icc_cexp]
  rw [fourierSym]
  have e : ∀ t, (∑ k ∈ Finset.Icc (-(m : ℤ)) m, cexp (k * ((θ - t : ℝ) : ℂ) * I)) * f t =
      ∑ k ∈ Finset.Icc (-(m : ℤ)) m, cexp (k * θ * I) * (f t * cexp (-(k * t * I))) := fun t => by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (k : ℂ) * ((θ - t : ℝ) : ℂ) * I = k * θ * I + -(k * t * I) by push_cast; ring,
      Complex.exp_add]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum fun k _ => hi k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul, fourierF]
  ring

/-- **DLMF (1.15.23)**: `σₙ(θ) = (1/(2π)) ∫_0^{2π} Kₙ(θ − t) f(t) dt` (`f` integrable on
`[0, 2π]`). -/
theorem dlmf_1_15_23 {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 (2 * π)) (n : ℕ)
    (θ : ℝ) : cesaroMeanF f n θ = (1 / (2 * π) : ℂ) *
      ∫ t in (0 : ℝ)..2 * π, (fejerK n (θ - t) : ℂ) * f t := by
  have hi : ∀ m : ℕ, IntervalIntegrable (fun t => ((2 * halfDirichlet m (θ - t) : ℝ) : ℂ) * f t)
      volume 0 (2 * π) := fun m =>
    hf.continuousOn_mul (continuous_ofReal.comp (continuous_const.mul
      ((continuous_halfDirichlet m).comp (continuous_const.sub continuous_id)))).continuousOn
  rw [cesaroMeanF]
  simp_rw [fourierSym_eq_integral hf]
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum fun m _ => hi m, mul_div_assoc,
    ← intervalIntegral.integral_div]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_sin_half_ne_zero θ] with t ht _
  rw [fejerK_eq_sum ht, ← Finset.sum_mul]
  push_cast
  field_simp

/-! ### Approximate identities and convergence (1.15.24) -/

theorem intervalIntegrable_kernel_mul {k : ℝ → ℝ} {C : ℝ} (hkm : Measurable k)
    (hk0 : ∀ x, 0 ≤ k x) (hkC : ∀ x, k x ≤ C) {g : ℝ → ℂ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun u => (k u : ℂ) * g u) volume a b :=
  (hg.norm.const_mul C).mono_fun'
    (show AEStronglyMeasurable (fun u => (k u : ℂ) * g u) _ from
      (continuous_ofReal.measurable.comp hkm).aestronglyMeasurable.mul hg.def'.aestronglyMeasurable)
    (ae_of_all _ fun u => by
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hk0 u)]
      exact mul_le_mul_of_nonneg_right (hkC u) (norm_nonneg _))

/-- For an even `2π`-periodic kernel `k`,
`∫_0^{2π} k(θ − t) f(t) dt = ∫_0^π k(u)(f(θ+u) + f(θ−u)) du`
(`f` `2π`-periodic and integrable). -/
theorem integral_kernel_eq {k : ℝ → ℝ} {C : ℝ} (hkm : Measurable k) (hk0 : ∀ x, 0 ≤ k x)
    (hkC : ∀ x, k x ≤ C) (hkp : Function.Periodic k (2 * π)) (hke : ∀ x, k (-x) = k x)
    {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π)) (hf : IntervalIntegrable f volume 0 (2 * π))
    (θ : ℝ) :
    ∫ t in (0 : ℝ)..2 * π, (k (θ - t) : ℂ) * f t =
      ∫ u in (0 : ℝ)..π, (k u : ℂ) * (f (θ + u) + f (θ - u)) := by
  have hfa : ∀ a b, IntervalIntegrable f volume a b := fun a b =>
    hper.intervalIntegrable two_pi_pos.ne' (t := 0) (by simpa using hf) a b
  set g : ℝ → ℂ := fun u => (k u : ℂ) * f (θ - u)
  have hgp : Function.Periodic g (2 * π) := fun u => by
    simp only [g, hkp u, show θ - (u + 2 * π) = θ - u - 2 * π by ring, hper.sub_eq]
  have hgi : ∀ a b, IntervalIntegrable g volume a b := fun a b =>
    intervalIntegrable_kernel_mul hkm hk0 hkC ((hfa (θ - b) (θ - a)).comp_sub_left θ |>.symm
      |> fun h => by simpa [sub_sub_cancel] using h)
  have h1 : ∫ t in (0 : ℝ)..2 * π, (k (θ - t) : ℂ) * f t = ∫ u in θ - 2 * π..θ, g u := by
    have := intervalIntegral.integral_comp_sub_left (fun u => g u) θ (a := 0) (b := 2 * π)
    simp only [sub_zero, g, sub_sub_cancel] at this
    exact this
  have h2 := hgp.intervalIntegral_add_eq (θ - 2 * π) (-π)
  rw [show θ - 2 * π + 2 * π = θ by ring, show -π + 2 * π = π by ring] at h2
  rw [h1, h2, ← intervalIntegral.integral_add_adjacent_intervals (hgi (-π) 0) (hgi 0 π)]
  have hneg : ∫ u in (-π)..0, g u = ∫ u in (0 : ℝ)..π, (k u : ℂ) * f (θ + u) := by
    rw [← neg_zero, ← intervalIntegral.integral_comp_neg]
    simp only [g, hke, sub_neg_eq_add, neg_zero]
  rw [hneg, ← intervalIntegral.integral_add]
  · refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [g]; ring
  · exact intervalIntegrable_kernel_mul hkm hk0 hkC
      ((hfa (θ + 0) (θ + π)).comp_add_left θ |> fun h => by simpa using h)
  · exact hgi 0 π

theorem integral_half_kernel {k : ℝ → ℝ} {C : ℝ} (hkm : Measurable k) (hk0 : ∀ x, 0 ≤ k x)
    (hkC : ∀ x, k x ≤ C) (hkp : Function.Periodic k (2 * π)) (hke : ∀ x, k (-x) = k x)
    (hk1 : ∫ x in (0 : ℝ)..2 * π, k x = 2 * π) : ∫ x in (0 : ℝ)..π, k x = π := by
  have h := integral_kernel_eq hkm hk0 hkC hkp hke (f := fun _ => (1 : ℂ))
    (fun _ => rfl) intervalIntegrable_const 0
  simp only [zero_sub, hke, mul_one] at h
  rw [intervalIntegral.integral_ofReal, show ∫ u in (0 : ℝ)..π, (k u : ℂ) * (1 + 1) =
    ∫ u in (0 : ℝ)..π, ((2 * k u : ℝ) : ℂ) by congr 1; funext u; push_cast; ring,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul, hk1] at h
  have := ofReal_injective h
  linarith

/-- The core estimate: if `|h| ≤ e` on `(0, δ]` and `k ≤ η` on `[δ, π]`, then
`|∫_0^π k h| ≤ eπ + η ∫_0^π |h|` (for `k ≥ 0` with `∫_0^π k = π`). -/
theorem norm_integral_kernel_le {k : ℝ → ℝ} {C : ℝ} (hkm : Measurable k) (hk0 : ∀ x, 0 ≤ k x)
    (hkC : ∀ x, k x ≤ C) (hkπ : ∫ x in (0 : ℝ)..π, k x = π) {h : ℝ → ℂ}
    (hh : IntervalIntegrable h volume 0 π) {δ e η : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) (he : 0 ≤ e)
    (hη : 0 ≤ η) (hhe : ∀ u ∈ Ioc 0 δ, ‖h u‖ ≤ e) (hkη : ∀ u ∈ Icc δ π, k u ≤ η) :
    ‖∫ u in (0 : ℝ)..π, (k u : ℂ) * h u‖ ≤ e * π + η * ∫ u in (0 : ℝ)..π, ‖h u‖ := by
  have hki : ∀ a b, IntervalIntegrable k volume a b := fun a b =>
    (intervalIntegrable_const (c := C)).mono_fun' hkm.aestronglyMeasurable
      (ae_of_all _ fun x => by
        show ‖k x‖ ≤ C
        rw [Real.norm_of_nonneg (hk0 x)]; exact hkC x)
  have hkh : ∀ a b, a ≤ b → 0 ≤ a → b ≤ π →
      IntervalIntegrable (fun u => k u * ‖h u‖) volume a b := fun a b hab ha hb => by
    have := intervalIntegrable_kernel_mul hkm hk0 hkC (hh.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le Real.pi_pos.le]; exact Icc_subset_Icc ha hb))
    refine this.norm.congr fun u _ => ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hk0 u)]
  calc ‖∫ u in (0 : ℝ)..π, (k u : ℂ) * h u‖ ≤ ∫ u in (0 : ℝ)..π, ‖(k u : ℂ) * h u‖ :=
        intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le
    _ = ∫ u in (0 : ℝ)..π, k u * ‖h u‖ := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hk0 u)]
    _ = (∫ u in (0 : ℝ)..δ, k u * ‖h u‖) + ∫ u in δ..π, k u * ‖h u‖ :=
        (intervalIntegral.integral_add_adjacent_intervals (hkh 0 δ hδ.le le_rfl hδπ)
          (hkh δ π hδπ hδ.le le_rfl)).symm
    _ ≤ (∫ u in (0 : ℝ)..δ, k u * e) + ∫ u in δ..π, η * ‖h u‖ := by
        gcongr
        · exact intervalIntegral.integral_mono_on_of_le_Ioo hδ.le (hkh 0 δ hδ.le le_rfl hδπ)
            ((hki 0 δ).mul_const e) fun u hu =>
              mul_le_mul_of_nonneg_left (hhe u ⟨hu.1, hu.2.le⟩) (hk0 u)
        · exact intervalIntegral.integral_mono_on hδπ (hkh δ π hδπ hδ.le le_rfl)
            ((hh.norm.mono_set (by
              rw [uIcc_of_le hδπ, uIcc_of_le Real.pi_pos.le]; exact Icc_subset_Icc hδ.le le_rfl)
              ).const_mul η) fun u hu =>
              mul_le_mul_of_nonneg_right (hkη u hu) (norm_nonneg _)
    _ ≤ e * π + η * ∫ u in (0 : ℝ)..π, ‖h u‖ := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
        have h1 : (∫ u in (0 : ℝ)..δ, k u) ≤ π := by
          rw [← hkπ]
          exact intervalIntegral.integral_mono_interval le_rfl hδ.le hδπ
            (ae_of_all _ fun x => hk0 x) (hki 0 π)
        have h2 : (∫ u in δ..π, ‖h u‖) ≤ ∫ u in (0 : ℝ)..π, ‖h u‖ :=
          intervalIntegral.integral_mono_interval hδ.le hδπ le_rfl
            (ae_of_all _ fun x => norm_nonneg _) hh.norm
        nlinarith [mul_le_mul_of_nonneg_left h1 he, mul_le_mul_of_nonneg_left h2 hη]

/-- The mean `(1/(2π)) ∫_0^{2π} k(θ − t) f(t) dt` minus `(L₁ + L₂)/2`, folded onto `[0, π]`. -/
theorem kernel_mean_sub {k : ℝ → ℝ} {C : ℝ} (hkm : Measurable k) (hk0 : ∀ x, 0 ≤ k x)
    (hkC : ∀ x, k x ≤ C) (hkp : Function.Periodic k (2 * π)) (hke : ∀ x, k (-x) = k x)
    (hk1 : ∫ x in (0 : ℝ)..2 * π, k x = 2 * π) {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hf : IntervalIntegrable f volume 0 (2 * π)) (θ : ℝ) (L₁ L₂ : ℂ) :
    (1 / (2 * π) : ℂ) * (∫ t in (0 : ℝ)..2 * π, (k (θ - t) : ℂ) * f t) - (L₁ + L₂) / 2 =
      (1 / (2 * π) : ℂ) * ∫ u in (0 : ℝ)..π, (k u : ℂ) * (f (θ + u) + f (θ - u) - (L₁ + L₂)) := by
  have hfa : ∀ a b, IntervalIntegrable f volume a b := fun a b =>
    hper.intervalIntegrable two_pi_pos.ne' (t := 0) (by simpa using hf) a b
  have hkπ := integral_half_kernel hkm hk0 hkC hkp hke hk1
  have hA : IntervalIntegrable (fun u => f (θ + u)) volume 0 π := by
    have := (hfa (θ + 0) (θ + π)).comp_add_left θ; simpa using this
  have hB : IntervalIntegrable (fun u => f (θ - u)) volume 0 π := by
    have := (hfa (θ - π) θ).comp_sub_left θ
    simp only [sub_sub_cancel, sub_self] at this; exact this.symm
  have hi1 : IntervalIntegrable (fun u => (k u : ℂ) * (f (θ + u) + f (θ - u))) volume 0 π :=
    intervalIntegrable_kernel_mul hkm hk0 hkC (hA.add hB)
  have hi2 : IntervalIntegrable (fun u => (k u : ℂ) * (L₁ + L₂)) volume 0 π :=
    intervalIntegrable_kernel_mul hkm hk0 hkC intervalIntegrable_const
  rw [integral_kernel_eq hkm hk0 hkC hkp hke hper hf θ]
  have e : ∫ u in (0 : ℝ)..π, (k u : ℂ) * (f (θ + u) + f (θ - u) - (L₁ + L₂)) =
      (∫ u in (0 : ℝ)..π, (k u : ℂ) * (f (θ + u) + f (θ - u))) -
        ∫ u in (0 : ℝ)..π, (k u : ℂ) * (L₁ + L₂) := by
    rw [← intervalIntegral.integral_sub hi1 hi2]; congr 1; funext u; ring
  rw [e, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, hkπ]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- **Approximate identity, pointwise.** Let `kλ ≥ 0` be even, `2π`-periodic, measurable and bounded
with `(1/(2π)) ∫_0^{2π} kλ = 1`, and `kλ → 0` uniformly on each `[δ, π]`. If `f` is
`2π`-periodic and
integrable and `f(θ±)` exist, then `(1/(2π)) ∫_0^{2π} kλ(θ − t) f(t) dt → ½(f(θ+) + f(θ−))`. -/
theorem tendsto_kernel_mean {ι : Type*} {l : Filter ι} {k : ι → ℝ → ℝ}
    (hkm : ∀ i, Measurable (k i)) (hkp : ∀ i, Function.Periodic (k i) (2 * π))
    (hke : ∀ i x, k i (-x) = k i x) (hk0 : ∀ᶠ i in l, ∀ x, 0 ≤ k i x)
    (hkb : ∀ᶠ i in l, ∃ C, ∀ x, k i x ≤ C)
    (hk1 : ∀ᶠ i in l, ∫ x in (0 : ℝ)..2 * π, k i x = 2 * π)
    (hku : ∀ δ, 0 < δ → δ < π → ∀ η, 0 < η → ∀ᶠ i in l, ∀ x ∈ Icc δ π, k i x ≤ η)
    {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π)) (hf : IntervalIntegrable f volume 0 (2 * π))
    {θ : ℝ} {Lp Lm : ℂ} (hp : Tendsto f (𝓝[>] θ) (𝓝 Lp)) (hm : Tendsto f (𝓝[<] θ) (𝓝 Lm)) :
    Tendsto (fun i => (1 / (2 * π) : ℂ) * ∫ t in (0 : ℝ)..2 * π, (k i (θ - t) : ℂ) * f t) l
      (𝓝 ((Lp + Lm) / 2)) := by
  have hfa : ∀ a b, IntervalIntegrable f volume a b := fun a b =>
    hper.intervalIntegrable two_pi_pos.ne' (t := 0) (by simpa using hf) a b
  set h : ℝ → ℂ := fun u => f (θ + u) + f (θ - u) - (Lp + Lm)
  have hA : IntervalIntegrable (fun u => f (θ + u)) volume 0 π := by
    have := (hfa (θ + 0) (θ + π)).comp_add_left θ; simpa using this
  have hB : IntervalIntegrable (fun u => f (θ - u)) volume 0 π := by
    have := (hfa (θ - π) θ).comp_sub_left θ
    simp only [sub_sub_cancel, sub_self] at this; exact this.symm
  have hh : IntervalIntegrable h volume 0 π := (hA.add hB).sub intervalIntegrable_const
  have hh0 : Tendsto h (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => θ + u) (𝓝[>] 0) (𝓝[>] θ) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := ((show Continuous fun u : ℝ => θ + u by fun_prop).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with u hu; simp only [Set.mem_Ioi]; linarith [hu.out]
    have h2 : Tendsto (fun u : ℝ => θ - u) (𝓝[>] 0) (𝓝[<] θ) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := ((show Continuous fun u : ℝ => θ - u by fun_prop).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with u hu; simp only [Set.mem_Iio]; linarith [hu.out]
    have := ((hp.comp h1).add (hm.comp h2)).sub_const (Lp + Lm)
    simpa [h] using this
  set H := ∫ u in (0 : ℝ)..π, ‖h u‖
  have hH : 0 ≤ H := intervalIntegral.integral_nonneg Real.pi_pos.le fun u _ => norm_nonneg _
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ₀, hδ₀, hδh⟩ := Metric.tendsto_nhdsWithin_nhds.mp hh0 (ε / 2) (by positivity)
  set δ := min (δ₀ / 2) (π / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδπ : δ < π := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  have hhe : ∀ u ∈ Ioc 0 δ, ‖h u‖ ≤ ε / 2 := fun u hu => by
    have := hδh hu.1 (by rw [dist_zero_right, Real.norm_of_nonneg hu.1.le]
                         linarith [hu.2, min_le_left (δ₀ / 2) (π / 2)])
    rw [dist_zero_right] at this; exact this.le
  set η := ε / (H + 1)
  have hη : 0 < η := by positivity
  filter_upwards [hk0, hkb, hk1, hku δ hδ hδπ η hη] with i hi0 hib hi1 hiu
  obtain ⟨C, hC⟩ := hib
  rw [dist_eq_norm, kernel_mean_sub (hkm i) hi0 hC (hkp i) (hke i) hi1 hper hf θ Lp Lm]
  have hb := norm_integral_kernel_le (hkm i) hi0 hC (integral_half_kernel (hkm i) hi0 hC (hkp i)
    (hke i) hi1) hh hδ hδπ.le (by positivity) hη.le hhe hiu
  rw [norm_mul, show ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) by
    rw [norm_div, norm_one, show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg two_pi_pos.le] ]
  have hηH : η * H < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
  calc 1 / (2 * π) * ‖∫ u in (0 : ℝ)..π, (k i u : ℂ) * h u‖ ≤
      1 / (2 * π) * (ε / 2 * π + η * H) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ < ε := by
        rw [mul_add, show 1 / (2 * π) * (ε / 2 * π) = ε / 4 by field_simp; ring]
        have : 1 / (2 * π) * (η * H) < ε / 2 := by
          rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ two_pi_pos]
          nlinarith [Real.two_le_pi]
        linarith

/-- A continuous `2π`-periodic `f` is uniformly continuous. -/
theorem periodic_uniform_cont {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π)) (hc : Continuous f)
    {e : ℝ} (he : 0 < e) : ∃ δ > 0, ∀ θ u : ℝ, |u| < δ → ‖f (θ + u) - f θ‖ < e := by
  have hK := (isCompact_Icc (a := -(2 * π)) (b := 4 * π)).uniformContinuousOn_of_continuous
    hc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hK
  obtain ⟨δ, hδ, hδK⟩ := hK e he
  refine ⟨min δ (2 * π), lt_min hδ two_pi_pos, fun θ u hu => ?_⟩
  set n := toIcoDiv two_pi_pos 0 θ
  have hmem := sub_toIcoDiv_zsmul_mem_Ico two_pi_pos 0 θ
  set θ' := θ - n • (2 * π)
  have h1 : f θ = f θ' := (hper.sub_zsmul_eq n).symm
  have h2 : f (θ + u) = f (θ' + u) := by
    rw [show θ' + u = θ + u - n • (2 * π) by simp only [θ']; ring, hper.sub_zsmul_eq n]
  have hu' := abs_lt.mp (hu.trans_le (min_le_right _ _))
  rw [h1, h2, ← dist_eq_norm]
  refine hδK (θ' + u) ⟨by linarith [hmem.1], by linarith [hmem.2]⟩ θ'
    ⟨by linarith [hmem.1], by linarith [hmem.2]⟩ ?_
  rw [Real.dist_eq, add_sub_cancel_left]
  exact hu.trans_le (min_le_left _ _)

/-- **Approximate identity, uniform.** Under the kernel hypotheses of `tendsto_kernel_mean`, for
continuous `2π`-periodic `f` the means converge to `f` uniformly. -/
theorem tendstoUniformly_kernel_mean {ι : Type*} {l : Filter ι} {k : ι → ℝ → ℝ}
    (hkm : ∀ i, Measurable (k i)) (hkp : ∀ i, Function.Periodic (k i) (2 * π))
    (hke : ∀ i x, k i (-x) = k i x) (hk0 : ∀ᶠ i in l, ∀ x, 0 ≤ k i x)
    (hkb : ∀ᶠ i in l, ∃ C, ∀ x, k i x ≤ C)
    (hk1 : ∀ᶠ i in l, ∫ x in (0 : ℝ)..2 * π, k i x = 2 * π)
    (hku : ∀ δ, 0 < δ → δ < π → ∀ η, 0 < η → ∀ᶠ i in l, ∀ x ∈ Icc δ π, k i x ≤ η)
    {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π)) (hc : Continuous f) {G : ι → ℝ → ℂ}
    (hG : ∀ᶠ i in l, ∀ θ, G i θ =
      (1 / (2 * π) : ℂ) * ∫ t in (0 : ℝ)..2 * π, (k i (θ - t) : ℂ) * f t) :
    TendstoUniformly G f l := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    (hper.isBounded_of_continuous two_pi_pos.ne' hc)
  have hM' : ∀ x, ‖f x‖ ≤ M := fun x => hM _ ⟨x, rfl⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM' 0)
  have hf : IntervalIntegrable f volume 0 (2 * π) := hc.intervalIntegrable _ _
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ₀, hδ₀, hδf⟩ := periodic_uniform_cont hper hc (e := ε / 4) (by positivity)
  set δ := min (δ₀ / 2) (π / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδπ : δ < π := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  set η := ε / (4 * M * π + 1)
  have hη : 0 < η := by positivity
  filter_upwards [hk0, hkb, hk1, hku δ hδ hδπ η hη, hG] with i hi0 hib hi1 hiu hiG θ
  obtain ⟨C, hC⟩ := hib
  set h : ℝ → ℂ := fun u => f (θ + u) + f (θ - u) - (f θ + f θ)
  have hh : IntervalIntegrable h volume 0 π :=
    (by fun_prop : Continuous h).intervalIntegrable _ _
  have hhe : ∀ u ∈ Ioc 0 δ, ‖h u‖ ≤ ε / 2 := fun u hu => by
    have hu1 : |u| < δ₀ := by
      rw [abs_of_pos hu.1]; linarith [hu.2, min_le_left (δ₀ / 2) (π / 2)]
    have hu2 : |-u| < δ₀ := by rwa [abs_neg]
    have a1 := hδf θ u hu1
    have a2 := hδf θ (-u) hu2
    rw [← sub_eq_add_neg] at a2
    calc ‖h u‖ = ‖(f (θ + u) - f θ) + (f (θ - u) - f θ)‖ := by congr 1; simp only [h]; ring
      _ ≤ ‖f (θ + u) - f θ‖ + ‖f (θ - u) - f θ‖ := norm_add_le _ _
      _ ≤ ε / 2 := by linarith
  have hHb : ∫ u in (0 : ℝ)..π, ‖h u‖ ≤ 4 * M * π := by
    have : ∫ u in (0 : ℝ)..π, ‖h u‖ ≤ ∫ u in (0 : ℝ)..π, 4 * M :=
      intervalIntegral.integral_mono_on Real.pi_pos.le hh.norm intervalIntegrable_const
        fun u _ => by
          calc ‖h u‖ ≤ ‖f (θ + u)‖ + ‖f (θ - u)‖ + (‖f θ‖ + ‖f θ‖) := by
                simp only [h]
                refine (norm_sub_le _ _).trans ?_
                gcongr
                · exact norm_add_le _ _
                · exact norm_add_le _ _
            _ ≤ 4 * M := by linarith [hM' (θ + u), hM' (θ - u), hM' θ]
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    linarith
  rw [dist_comm, dist_eq_norm, hiG θ, show f θ = (f θ + f θ) / 2 by ring,
    kernel_mean_sub (hkm i) hi0 hC (hkp i) (hke i) hi1 hper hf θ (f θ) (f θ)]
  have hb := norm_integral_kernel_le (hkm i) hi0 hC (integral_half_kernel (hkm i) hi0 hC (hkp i)
    (hke i) hi1) hh hδ hδπ.le (by positivity) hη.le hhe hiu
  rw [norm_mul, show ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) by
    rw [norm_div, norm_one, show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg two_pi_pos.le] ]
  have hηH : η * ∫ u in (0 : ℝ)..π, ‖h u‖ < ε := by
    calc η * ∫ u in (0 : ℝ)..π, ‖h u‖ ≤ η * (4 * M * π) := mul_le_mul_of_nonneg_left hHb hη.le
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
  calc 1 / (2 * π) * ‖∫ u in (0 : ℝ)..π, (k i u : ℂ) * h u‖ ≤
      1 / (2 * π) * (ε / 2 * π + η * ∫ u in (0 : ℝ)..π, ‖h u‖) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ < ε := by
        rw [mul_add, show 1 / (2 * π) * (ε / 2 * π) = ε / 4 by field_simp; ring]
        have : 1 / (2 * π) * (η * ∫ u in (0 : ℝ)..π, ‖h u‖) < ε / 2 := by
          rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ two_pi_pos]
          nlinarith [Real.two_le_pi]
        linarith

/-! ### 1.15.24 for the Abel and Cesàro means -/

theorem diskPoisson_kernel_facts :
    (∀ r, Measurable (diskPoisson r)) ∧ (∀ r, Function.Periodic (diskPoisson r) (2 * π)) ∧
    (∀ r x, diskPoisson r (-x) = diskPoisson r x) ∧
    (∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ x, 0 ≤ diskPoisson r x) ∧
    (∀ᶠ r in 𝓝[<] (1 : ℝ), ∃ C, ∀ x, diskPoisson r x ≤ C) ∧
    (∀ᶠ r in 𝓝[<] (1 : ℝ), ∫ x in (0 : ℝ)..2 * π, diskPoisson r x = 2 * π) ∧
    (∀ δ, 0 < δ → δ < π → ∀ η, 0 < η →
      ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ x ∈ Icc δ π, diskPoisson r x ≤ η) := by
  have hr : ∀ᶠ r in 𝓝[<] (1 : ℝ), r ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT one_pos
  refine ⟨fun r => by unfold diskPoisson; fun_prop, diskPoisson_periodic, diskPoisson_neg,
    hr.mono fun r h => diskPoisson_nonneg h.1.le h.2,
    hr.mono fun r h => ⟨_, diskPoisson_le h.1.le h.2⟩,
    hr.mono fun r h => ?_, fun δ hδ hδπ η hη => ?_⟩
  · have := dlmf_1_15_13 h.1.le h.2
    field_simp at this; linarith
  · have hu := Metric.tendstoUniformlyOn_iff.mp (dlmf_1_15_14 hδ hδπ) η hη
    filter_upwards [hu] with r hr' x hx
    have := hr' x ⟨hx.1, by linarith [hx.2]⟩
    rw [dist_comm, dist_zero_right, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this.le

theorem fejerK_kernel_facts :
    (∀ n, Measurable (fejerK n)) ∧ (∀ n, Function.Periodic (fejerK n) (2 * π)) ∧
    (∀ n x, fejerK n (-x) = fejerK n x) ∧ (∀ᶠ n in atTop, ∀ x, 0 ≤ fejerK n x) ∧
    (∀ᶠ n in atTop, ∃ C, ∀ x, fejerK n x ≤ C) ∧
    (∀ᶠ n in atTop, ∫ x in (0 : ℝ)..2 * π, fejerK n x = 2 * π) ∧
    (∀ δ, 0 < δ → δ < π → ∀ η, 0 < η → ∀ᶠ n in atTop, ∀ x ∈ Icc δ π, fejerK n x ≤ η) := by
  refine ⟨measurable_fejerK, fejerK_periodic, fejerK_neg, Eventually.of_forall fun n =>
    fejerK_nonneg n, Eventually.of_forall fun n => ⟨_, fejerK_le n⟩,
    Eventually.of_forall fun n => ?_, fun δ hδ hδπ η hη => ?_⟩
  · have := dlmf_1_15_16 n
    field_simp at this; linarith
  · have hu := Metric.tendstoUniformlyOn_iff.mp (dlmf_1_15_17 hδ hδπ) η hη
    filter_upwards [hu] with n hn x hx
    have := hn x ⟨hx.1, by linarith [hx.2]⟩
    rw [dist_comm, dist_zero_right, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this.le

/-- **DLMF (1.15.24)**, Abel means: for `f` `2π`-periodic and integrable on `[0, 2π]`,
`A(r, θ) → ½(f(θ+) + f(θ−))` as `r → 1−` wherever both one-sided limits exist. -/
theorem dlmf_1_15_24_abel {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hf : IntervalIntegrable f volume 0 (2 * π)) {θ : ℝ} {Lp Lm : ℂ}
    (hp : Tendsto f (𝓝[>] θ) (𝓝 Lp)) (hm : Tendsto f (𝓝[<] θ) (𝓝 Lm)) :
    Tendsto (fun r => abelMean f r θ) (𝓝[<] 1) (𝓝 ((Lp + Lm) / 2)) := by
  obtain ⟨a, b, c, d, e, g, h⟩ := diskPoisson_kernel_facts
  refine (tendsto_kernel_mean a b c d e g h hper hf hp hm).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT one_pos] with r hr
  exact (dlmf_1_15_20 hf hr.1.le hr.2 θ).symm

/-- **DLMF (1.15.24)**, Cesàro means: `σₙ(θ) → ½(f(θ+) + f(θ−))` as `n → ∞`. -/
theorem dlmf_1_15_24_cesaro {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hf : IntervalIntegrable f volume 0 (2 * π)) {θ : ℝ} {Lp Lm : ℂ}
    (hp : Tendsto f (𝓝[>] θ) (𝓝 Lp)) (hm : Tendsto f (𝓝[<] θ) (𝓝 Lm)) :
    Tendsto (fun n => cesaroMeanF f n θ) atTop (𝓝 ((Lp + Lm) / 2)) := by
  obtain ⟨a, b, c, d, e, g, h⟩ := fejerK_kernel_facts
  refine (tendsto_kernel_mean a b c d e g h hper hf hp hm).congr fun n => ?_
  exact (dlmf_1_15_23 hf n θ).symm

/-- **DLMF §1.15(iii)**: for continuous `2π`-periodic `f`, `A(r, θ) → f(θ)` uniformly. -/
theorem dlmf_1_15_24_abel_uniform {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hc : Continuous f) : TendstoUniformly (fun r θ => abelMean f r θ) f (𝓝[<] 1) := by
  obtain ⟨a, b, c, d, e, g, h⟩ := diskPoisson_kernel_facts
  refine tendstoUniformly_kernel_mean a b c d e g h hper hc ?_
  filter_upwards [Ioo_mem_nhdsLT one_pos] with r hr θ
  exact dlmf_1_15_20 (hc.intervalIntegrable _ _) hr.1.le hr.2 θ

/-- **DLMF §1.15(iii)**: for continuous `2π`-periodic `f`, `σₙ(θ) → f(θ)` uniformly. -/
theorem dlmf_1_15_24_cesaro_uniform {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hc : Continuous f) : TendstoUniformly (fun n θ => cesaroMeanF f n θ) f atTop := by
  obtain ⟨a, b, c, d, e, g, h⟩ := fejerK_kernel_facts
  refine tendstoUniformly_kernel_mean a b c d e g h hper hc (Eventually.of_forall fun n θ => ?_)
  exact dlmf_1_15_23 (hc.intervalIntegrable _ _) n θ

/-! ### The analytic function `G` (1.15.25–1.15.28) -/

/-- **DLMF (1.15.26)–(1.15.27)**: `G(z) = F(0) + 2 ∑_{n=1}^{∞} F(n) zⁿ`. -/
noncomputable def fourierG (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  fourierF f 0 + 2 * ∑' n : ℕ, fourierF f (n + 1) * z ^ (n + 1)

theorem summable_fourierF_mul_pow (f : ℝ → ℂ) {z : ℂ} {ρ : ℝ} (hz : ‖z‖ ≤ ρ) (hρ : ρ < 1) :
    Summable fun n : ℕ => fourierF f (n + 1) * z ^ (n + 1) := by
  set B := 1 / (2 * π) * ∫ t in (0 : ℝ)..2 * π, ‖f t‖
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hz
  refine Summable.of_norm_bounded (((summable_geometric_of_lt_one hρ0 hρ).mul_left (B * ρ)))
    fun n => ?_
  rw [norm_mul, norm_pow]
  calc ‖fourierF f (n + 1)‖ * ‖z‖ ^ (n + 1) ≤ B * ρ ^ (n + 1) :=
        mul_le_mul (by exact_mod_cast norm_fourierF_le (f := f) ((n : ℤ) + 1))
          (pow_le_pow_left₀ (norm_nonneg _) hz _) (by positivity)
          ((norm_nonneg _).trans (norm_fourierF_le 0))
    _ = B * ρ * ρ ^ n := by ring

/-- **DLMF (1.15.27)**: `G` is analytic in the unit disk. -/
theorem dlmf_1_15_27 (f : ℝ → ℂ) : DifferentiableOn ℂ (fourierG f) (Metric.ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz
  set ρ := (‖z‖ + 1) / 2
  have hzρ : ‖z‖ < ρ := by simp only [ρ]; linarith
  have hρ1 : ρ < 1 := by simp only [ρ]; linarith
  set B := 1 / (2 * π) * ∫ t in (0 : ℝ)..2 * π, ‖f t‖
  have hd : DifferentiableOn ℂ (fun w => ∑' n : ℕ, fourierF f (n + 1) * w ^ (n + 1))
      (Metric.ball 0 ρ) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (u := fun n : ℕ => B * ρ ^ (n + 1))
      ((summable_geometric_of_lt_one (by positivity) hρ1).mul_left (B * ρ) |>.congr
        fun n => by ring) (fun n => (by fun_prop : Differentiable ℂ fun w : ℂ =>
          fourierF f (n + 1) * w ^ (n + 1)).differentiableOn) Metric.isOpen_ball
      fun n w hw => ?_
    rw [mem_ball_zero_iff] at hw
    rw [norm_mul, norm_pow]
    exact mul_le_mul (by exact_mod_cast norm_fourierF_le (f := f) ((n : ℤ) + 1))
      (pow_le_pow_left₀ (norm_nonneg _) hw.le _) (by positivity)
      ((norm_nonneg _).trans (norm_fourierF_le 0))
  have hza : DifferentiableAt ℂ (fun w => ∑' n : ℕ, fourierF f (n + 1) * w ^ (n + 1)) z :=
    hd.differentiableAt (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hzρ))
  exact ((hza.const_mul 2).const_add _).differentiableWithinAt

theorem fourierF_neg_ofReal (f : ℝ → ℝ) (n : ℤ) :
    fourierF (fun t => (f t : ℂ)) (-n) = (starRingEnd ℂ) (fourierF (fun t => (f t : ℂ)) n) := by
  simp only [fourierF, map_mul, intervalIntegral.integral_of_le two_pi_pos.le]
  rw [← integral_conj]
  congr 1
  · simp [map_ofNat]
  · congr 1; funext t
    rw [map_mul, conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp [map_neg, map_mul, conj_ofReal, conj_I]

theorem fourierF_zero_ofReal (f : ℝ → ℝ) :
    fourierF (fun t => (f t : ℂ)) 0 = ((fourierF (fun t => (f t : ℂ)) 0).re : ℂ) := by
  have h := fourierF_neg_ofReal f 0
  rw [neg_zero] at h
  exact (Complex.conj_eq_iff_re.mp h.symm).symm

theorem abel_term_split (f : ℝ → ℂ) {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (θ : ℝ) :
    Summable fun n : ℤ => (r : ℂ) ^ n.natAbs * fourierF f n * cexp (n * θ * I) := by
  set B := 1 / (2 * π) * ∫ t in (0 : ℝ)..2 * π, ‖f t‖
  refine Summable.of_norm_bounded ((summable_pow_natAbs h0 h1).mul_left B) fun n => ?_
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg h0,
    show (n : ℂ) * θ * I = ((n * θ : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I,
    mul_one, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_fourierF_le n) (by positivity)

theorem abel_term_pos (f : ℝ → ℂ) (r θ : ℝ) (n : ℕ) :
    (r : ℂ) ^ ((n + 1 : ℕ) : ℤ).natAbs * fourierF f ((n + 1 : ℕ) : ℤ) *
      cexp (((n + 1 : ℕ) : ℤ) * θ * I) = fourierF f (n + 1) * (r * cexp (θ * I)) ^ (n + 1) := by
  rw [Int.natAbs_natCast, mul_pow, ← Complex.exp_nat_mul]
  push_cast; ring_nf

/-- **DLMF §1.15(iii)**: for real `f`, the Abel sum is the real part of `G`:
`A(r, θ) = u = ℜ G(re^{iθ})` (`0 ≤ r < 1`). -/
theorem dlmf_1_15_iii_re (f : ℝ → ℝ) {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (θ : ℝ) :
    abelMean (fun t => (f t : ℂ)) r θ =
      ((fourierG (fun t => (f t : ℂ)) (r * cexp (θ * I))).re : ℂ) := by
  set g : ℝ → ℂ := fun t => (f t : ℂ)
  set a : ℤ → ℂ := fun n => (r : ℂ) ^ n.natAbs * fourierF g n * cexp (n * θ * I)
  have hs := abel_term_split g h0 h1 θ
  set z : ℂ := r * cexp (θ * I)
  have hz : ‖z‖ ≤ r := by
    simp only [z, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, norm_exp_ofReal_mul_I,
      mul_one, le_refl]
  have hS := summable_fourierF_mul_pow g hz h1
  set S := ∑' n : ℕ, fourierF g (n + 1) * z ^ (n + 1)
  have hpos : ∀ n : ℕ, a ((n + 1 : ℕ) : ℤ) = fourierF g (n + 1) * z ^ (n + 1) := fun n =>
    abel_term_pos g r θ n
  have hneg : ∀ n : ℕ, a (-((n : ℤ) + 1)) = (starRingEnd ℂ) (fourierF g (n + 1) * z ^ (n + 1)) :=
    fun n => by
      rw [← hpos]
      simp only [a, g, map_mul, map_pow, conj_ofReal, ← Complex.exp_conj]
      rw [show (-((n : ℤ) + 1)) = -(((n + 1 : ℕ) : ℤ)) by push_cast; ring, fourierF_neg_ofReal,
        Int.natAbs_neg]
      congr 2
      simp only [conj_I, map_intCast]
      push_cast
      ring
  have h1' : Summable fun n : ℕ => a n := hs.comp_injective Nat.cast_injective
  have h2' : Summable fun n : ℕ => a (-((n : ℤ) + 1)) :=
    hs.comp_injective fun m n h => by simpa using h
  rw [abelMean, tsum_of_nat_of_neg_add_one h1' h2', h1'.tsum_eq_zero_add]
  simp only [hneg]
  rw [← conj_tsum, show (∑' n : ℕ, a ((n + 1 : ℕ) : ℤ)) = S from tsum_congr hpos]
  have ha0 : a ((0 : ℕ) : ℤ) = fourierF g 0 := by simp [a]
  rw [ha0, add_assoc, Complex.add_conj, fourierG, show (∑' n : ℕ, fourierF g (n + 1) *
    z ^ (n + 1)) = S from rfl]
  have hF0 := fourierF_zero_ofReal f
  simp only [g] at hF0 ⊢
  rw [hF0]
  simp only [add_re, ofReal_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
  push_cast
  ring

/-- **DLMF (1.15.28)**: for real `f`,
`v = ℑ G(re^{iθ}) = −∑_{n ∈ ℤ} i (sign n) F(n) r^{|n|} e^{inθ}`. -/
theorem dlmf_1_15_28 (f : ℝ → ℝ) {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (θ : ℝ) :
    ((fourierG (fun t => (f t : ℂ)) (r * cexp (θ * I))).im : ℂ) =
      -∑' n : ℤ, I * (Int.sign n : ℂ) * fourierF (fun t => (f t : ℂ)) n * (r : ℂ) ^ n.natAbs *
        cexp (n * θ * I) := by
  set g : ℝ → ℂ := fun t => (f t : ℂ)
  set a : ℤ → ℂ := fun n => (r : ℂ) ^ n.natAbs * fourierF g n * cexp (n * θ * I)
  have hs := abel_term_split g h0 h1 θ
  set z : ℂ := r * cexp (θ * I)
  have hpos : ∀ n : ℕ, a ((n + 1 : ℕ) : ℤ) = fourierF g (n + 1) * z ^ (n + 1) := fun n =>
    abel_term_pos g r θ n
  have hneg : ∀ n : ℕ, a (-((n : ℤ) + 1)) = (starRingEnd ℂ) (fourierF g (n + 1) * z ^ (n + 1)) :=
    fun n => by
      rw [← hpos]
      simp only [a, g, map_mul, map_pow, conj_ofReal, ← Complex.exp_conj]
      rw [show (-((n : ℤ) + 1)) = -(((n + 1 : ℕ) : ℤ)) by push_cast; ring, fourierF_neg_ofReal,
        Int.natAbs_neg]
      congr 2
      simp only [conj_I, map_intCast]
      push_cast
      ring
  set b : ℤ → ℂ := fun n => I * (Int.sign n : ℂ) * fourierF g n * (r : ℂ) ^ n.natAbs *
    cexp (n * θ * I)
  have hb : ∀ n, b n = I * (Int.sign n : ℂ) * a n := fun n => by simp only [a, b]; ring
  have hbs : Summable b := by
    refine Summable.of_norm_bounded hs.norm fun n => ?_
    rw [hb, norm_mul, norm_mul, norm_I, one_mul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rcases Int.sign_trichotomy n with h | h | h <;> simp [h]
  have hS : Summable fun n : ℕ => fourierF g (n + 1) * z ^ (n + 1) := by
    have hz : ‖z‖ ≤ r := by
      simp only [z, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, norm_exp_ofReal_mul_I,
        mul_one, le_refl]
    exact summable_fourierF_mul_pow g hz h1
  set S := ∑' n : ℕ, fourierF g (n + 1) * z ^ (n + 1)
  have h1' : Summable fun n : ℕ => b n := hbs.comp_injective Nat.cast_injective
  have h2' : Summable fun n : ℕ => b (-((n : ℤ) + 1)) :=
    hbs.comp_injective fun m n h => by simpa using h
  have hpos' : ∀ n : ℕ, b ((n + 1 : ℕ) : ℤ) = I * (fourierF g (n + 1) * z ^ (n + 1)) := fun n => by
    rw [hb, hpos]
    have : Int.sign ((n + 1 : ℕ) : ℤ) = 1 := Int.sign_eq_one_of_pos (by omega)
    rw [this]; push_cast; ring
  have hneg' : ∀ n : ℕ, b (-((n : ℤ) + 1)) =
      -I * (starRingEnd ℂ) (fourierF g (n + 1) * z ^ (n + 1)) := fun n => by
    rw [hb, hneg]
    have : Int.sign (-((n : ℤ) + 1)) = -1 := Int.sign_eq_neg_one_of_neg (by omega)
    rw [this]; push_cast; ring
  rw [tsum_of_nat_of_neg_add_one h1' h2', h1'.tsum_eq_zero_add]
  simp only [hneg', hpos']
  rw [tsum_mul_left, tsum_mul_left, ← conj_tsum]
  have hb0 : b ((0 : ℕ) : ℤ) = 0 := by simp [b]
  rw [hb0, zero_add, fourierG]
  rw [show (∑' n : ℕ, fourierF g (n + 1) * z ^ (n + 1)) = S from rfl]
  have hsc : S - (starRingEnd ℂ) S = ((2 * S.im : ℝ) : ℂ) * I := Complex.sub_conj S
  have hF0 := fourierF_zero_ofReal f
  simp only [g] at hF0 ⊢
  rw [hF0]
  simp only [add_im, ofReal_im, mul_im, re_ofNat, im_ofNat, zero_mul, add_zero, zero_add]
  push_cast at hsc ⊢
  linear_combination I * hsc + (2 * (S.im : ℂ)) * I_sq

/-- **DLMF §1.15(iii)**: for real `f`, `A(r, θ)` is harmonic in polar coordinates (1.9.27):
`∂²A/∂r² + (1/r) ∂A/∂r + (1/r²) ∂²A/∂θ² = 0` for `0 < r < 1`. -/
theorem dlmf_1_15_iii_harmonic (f : ℝ → ℝ) {r : ℝ} (h0 : 0 < r) (h1 : r < 1) (θ : ℝ) :
    deriv (fun ρ => deriv (fun ρ' => (abelMean (fun t => (f t : ℂ)) ρ' θ).re) ρ) r +
        1 / r * deriv (fun ρ => (abelMean (fun t => (f t : ℂ)) ρ θ).re) r +
        1 / r ^ 2 * deriv (fun φ => deriv (fun φ' =>
          (abelMean (fun t => (f t : ℂ)) r φ').re) φ) θ = 0 := by
  set g : ℝ → ℂ := fun t => (f t : ℂ)
  have hz : ((r : ℂ) * cexp (θ * I)) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0.le,
      norm_exp_ofReal_mul_I, mul_one]; exact h1
  have hH := (dlmf_1_9_27 Metric.isOpen_ball (dlmf_1_15_27 g) h0 hz).1
  have hre : ∀ ρ φ : ℝ, 0 ≤ ρ → ρ < 1 → (abelMean g ρ φ).re = (fourierG g (ρ * cexp (φ * I))).re :=
    fun ρ φ hρ0 hρ1 => by rw [dlmf_1_15_iii_re f hρ0 hρ1 φ, ofReal_re]
  have hev : (fun ρ' => (abelMean g ρ' θ).re) =ᶠ[𝓝 r]
      fun ρ' => (fourierG g (ρ' * cexp (θ * I))).re := by
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < r from h0) h1] with ρ hρ
    exact hre ρ θ hρ.1.le hρ.2
  have hφ : (fun φ' : ℝ => (abelMean g r φ').re) =
      fun φ' : ℝ => (fourierG g (r * cexp (φ' * I))).re :=
    funext fun φ => hre r φ h0.le h1
  rw [hev.deriv.deriv_eq, hev.deriv_eq, hφ]
  exact hH

/-! ### Defining equations -/

theorem dlmf_1_15_15 (n : ℕ) (θ : ℝ) :
    fejerK n θ = 1 / (n + 1) * (Real.sin ((n + 1) * θ / 2) / Real.sin (θ / 2)) ^ 2 := rfl

theorem dlmf_1_15_18 (f : ℝ → ℂ) (r θ : ℝ) :
    abelMean f r θ = ∑' n : ℤ, (r : ℂ) ^ n.natAbs * fourierF f n * cexp (n * θ * I) := rfl

theorem dlmf_1_15_19 (f : ℝ → ℂ) (n : ℤ) :
    fourierF f n = (1 / (2 * π) : ℂ) * ∫ t in (0 : ℝ)..2 * π, f t * cexp (-(n * t * I)) := rfl

theorem dlmf_1_15_21 (f : ℝ → ℂ) (n : ℕ) (θ : ℝ) :
    cesaroMeanF f n θ = (∑ m ∈ Finset.range (n + 1), fourierSym f m θ) / (n + 1) := rfl

theorem dlmf_1_15_22 (f : ℝ → ℂ) (n : ℕ) (θ : ℝ) :
    fourierSym f n θ = ∑ k ∈ Finset.Icc (-(n : ℤ)) n, fourierF f k * cexp (k * θ * I) := rfl

theorem dlmf_1_15_26 (f : ℝ → ℂ) (z : ℂ) :
    fourierG f z = fourierF f 0 + 2 * ∑' n : ℕ, fourierF f (n + 1) * z ^ (n + 1) := rfl

end Azurite.DLMF
