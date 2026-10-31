/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section8Poisson
import Azurite.DLMF.Chapter1.Section16
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# DLMF §1.17(iii): Series representations of the Dirac delta

https://dlmf.nist.gov/1.17.iii

* 1.17.17: the Fourier summation formula of §1.8 for continuous `2π`-periodic `φ` with summable
  coefficients (`dlmf_1_8_3`).
* 1.17.18: the series `∑ₖ e^{ik(x−a)}` diverges. It is not summable (`dlmf_1_17_18_not_summable`),
  and its symmetric partial sums do not converge for any `x − a` (`dlmf_1_17_18_not_tendsto`).
* 1.17.20: `dirichletDelta n y = (1/(2π)) ∑_{k=−n}^{n} e^{iky} = Dₙ(y)/π`, with §1.8's
  `halfDirichlet` (`dirichletDelta_eq`), and the closed form `sin((n+½)y)/(2π sin(½y))`.
* 1.17.19: `∫_{−π}^{π} δₙ(x − a) φ(x) dx` is the `n`th Fourier partial sum at `a`
  (`integral_dirichletDelta_mul`). It tends to `φ(a)` under Dirichlet's conditions 1.8.11
  (`dlmf_1_17_19_dirichlet`, `dlmf_1_17_19` for `φ` differentiable at `a`).
* **DLMF error**: DLMF asserts 1.17.19 for every continuous `2π`-periodic `φ`. That is false
  (`dlmf_1_17_19_counterexample`). The functionals `F ↦ ∫ δₙ F` on `C(ℝ/2πℤ, ℂ)`
  (`dirichletFunctional`) have norms at least `Lₙ/2 − 1` (`le_norm_dirichletFunctional`, with
  test functions `Dₙ/(|Dₙ| + 1)`). The Lebesgue constants `Lₙ ∼ (4/π²) ln n` of 1.8.9 are
  unbounded, so by Banach–Steinhaus some continuous periodic `φ` has unbounded integrals at
  `a = 0`.
* 1.17.21: the formal `2π`-periodic delta is, as a distribution on `ℝ`, the Dirac comb. For every
  test function `φ`, `∫ δₙ(x − a) φ(x) dx → ∑ₘ φ(a + 2πm)` (`dlmf_1_17_21`), by Poisson's
  summation formula 1.8.14.
* 1.17.22–1.17.25 (Legendre, Laguerre, Hermite, spherical harmonics) are deferred to the chapters
  defining those functions.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real ContDiff

namespace Azurite.DLMF

/-! ### The Fourier summation formula (1.17.17) -/

/-- DLMF 1.17.17, the Fourier summation formula of §1.8 (1.8.3–1.8.4): for continuous
`2π`-periodic `φ` with summable Fourier coefficients,
`(1/(2π)) ∑ₖ e^{−ika} ∫_{−π}^{π} φ(x) e^{ikx} dx = φ(a)`. -/
theorem dlmf_1_17_17 {φ : ℝ → ℂ} (hper : Function.Periodic φ (2 * π)) (hc : Continuous φ)
    (hs : Summable (fourierC φ)) (a : ℝ) :
    HasSum (fun k : ℤ => ((2 * π : ℝ) : ℂ)⁻¹ *
      (cexp (-(I * k * a)) * ∫ x in (-π)..π, φ x * cexp (I * k * x))) (φ a) := by
  have h := dlmf_1_8_3 hper hc hs a
  rw [← (Equiv.neg ℤ).hasSum_iff] at h
  convert h using 1
  funext k
  simp only [Function.comp, Equiv.neg_apply, fourierC, Complex.real_smul]
  have e : ∫ x in (-π)..π, φ x * cexp (-(((-k : ℤ) : ℂ) * x * I)) =
      ∫ x in (-π)..π, φ x * cexp (I * k * x) :=
    intervalIntegral.integral_congr fun x _ => by push_cast; ring_nf
  rw [e]
  push_cast
  ring_nf

/-! ### The Dirichlet kernel (1.17.18–1.17.20) -/

/-- DLMF 1.17.20: `δₙ(y) = (1/(2π)) ∑_{k=−n}^{n} e^{iky}`. -/
noncomputable def dirichletDelta (n : ℕ) (y : ℝ) : ℂ :=
  ((2 * π : ℝ) : ℂ)⁻¹ * ∑ k ∈ Finset.Icc (-(n : ℤ)) n, cexp (I * k * y)

theorem halfDirichlet_succ (n : ℕ) (s : ℝ) :
    halfDirichlet (n + 1) s = halfDirichlet n s + Real.cos ((n + 1 : ℕ) * s) := by
  simp only [halfDirichlet, Finset.sum_range_succ]; ring

theorem sum_Icc_cexp_eq_halfDirichlet (n : ℕ) (y : ℝ) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n, cexp (I * k * y) = ((2 * halfDirichlet n y : ℝ) : ℂ) := by
  induction n with
  | zero => simp [halfDirichlet]
  | succ n ih =>
    have hset : Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) =
        insert (-((n : ℤ) + 1)) (insert ((n : ℤ) + 1) (Finset.Icc (-(n : ℤ)) n)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    have h1 : ((n : ℤ) + 1) ∉ Finset.Icc (-(n : ℤ)) n := by simp
    have h2 : -((n : ℤ) + 1) ∉ insert ((n : ℤ) + 1) (Finset.Icc (-(n : ℤ)) n) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hset, Finset.sum_insert h2, Finset.sum_insert h1, ih, halfDirichlet_succ]
    have hc := Complex.two_cos (((n + 1 : ℕ) : ℝ) * y : ℝ)
    push_cast at hc ⊢
    rw [show I * (-((n : ℂ) + 1)) * y = -(((n : ℂ) + 1) * y) * I by ring,
      show I * ((n : ℂ) + 1) * y = ((n : ℂ) + 1) * y * I by ring]
    linear_combination -hc

/-- `δₙ(y) = (1/π) Dₙ(y)` with `Dₙ(y) = ½ + ∑_{k=1}^n cos(ky)` (§1.8(ii)). -/
theorem dirichletDelta_eq (n : ℕ) (y : ℝ) :
    dirichletDelta n y = ((halfDirichlet n y / π : ℝ) : ℂ) := by
  rw [dirichletDelta, sum_Icc_cexp_eq_halfDirichlet]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  push_cast
  field_simp

/-- DLMF 1.17.20: `δₙ(y) = sin((n + ½)y) / (2π sin(½y))`. -/
theorem dlmf_1_17_20 (n : ℕ) {y : ℝ} (hy : Real.sin (y / 2) ≠ 0) :
    dirichletDelta n y = ((Real.sin ((n + 1 / 2) * y) / (2 * π * Real.sin (y / 2)) : ℝ) : ℂ) := by
  rw [dirichletDelta_eq, ← two_mul_halfDirichlet_mul_sin]
  congr 1
  have := Real.pi_pos
  field_simp

theorem norm_cexp_I_mul (k y : ℝ) : ‖cexp (I * k * y)‖ = 1 := by
  rw [show I * (k : ℂ) * y = ((k * y : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- DLMF §1.17(iii): the series `∑ₖ e^{ik(x−a)}` of 1.17.18 does not converge: it is not summable,
its terms having modulus `1`. -/
theorem dlmf_1_17_18_not_summable (y : ℝ) : ¬ Summable fun k : ℤ => cexp (I * k * y) := by
  intro h
  have h0 := h.tendsto_cofinite_zero.norm
  have h1 : (fun k : ℤ => ‖cexp (I * k * y)‖) = fun _ => (1 : ℝ) :=
    funext fun k => by exact_mod_cast norm_cexp_I_mul k y
  rw [h1, norm_zero] at h0
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h0)

/-- DLMF §1.17(iii): nor do its symmetric partial sums `∑_{k=−n}^{n} e^{iky}` converge, for any
`y`. -/
theorem dlmf_1_17_18_not_tendsto (y : ℝ) (L : ℂ) :
    ¬ Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc (-(n : ℤ)) n, cexp (I * k * y)) atTop (𝓝 L) := by
  intro h
  simp_rw [sum_Icc_cexp_eq_halfDirichlet] at h
  have hr := (Complex.continuous_re.tendsto L).comp h
  simp only [Function.comp_def, ofReal_re] at hr
  have hd := (hr.comp (tendsto_add_atTop_nat 1)).sub hr
  rw [sub_self] at hd
  have hcos : Tendsto (fun n : ℕ => Real.cos ((n + 1 : ℕ) * y)) atTop (𝓝 0) := by
    have := hd.const_mul (1 / 2)
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp, halfDirichlet_succ]
    ring
  have h2 : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [id]; omega) tendsto_id
  have hA := hcos.comp h2
  have hB := ((hcos.pow 2).const_mul 2).sub_const 1
  have e : ∀ n : ℕ, (fun n : ℕ => Real.cos ((n + 1 : ℕ) * y)) (2 * n + 1) =
      2 * Real.cos ((n + 1 : ℕ) * y) ^ 2 - 1 := fun n => by
    simp only
    rw [show ((2 * n + 1 + 1 : ℕ) : ℝ) * y = 2 * (((n + 1 : ℕ) : ℝ) * y) by
      push_cast; ring, Real.cos_two_mul]
  simp only [Function.comp_def, e] at hA
  have := tendsto_nhds_unique hA hB
  norm_num at this

/-! ### 1.17.19 -/

/-- `∫_{−π}^{π} δₙ(x − a) φ(x) dx` is the `n`th partial sum of the Fourier series of `φ` at `a`. -/
theorem integral_dirichletDelta_mul {φ : ℝ → ℂ} (hφ : IntervalIntegrable φ volume (-π) π)
    (n : ℕ) (a : ℝ) :
    ∫ x in (-π)..π, dirichletDelta n (x - a) * φ x = fourierPartialSum φ n a := by
  rw [fourierPartialSum_eq_integral hφ, Complex.real_smul,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [dirichletDelta_eq]
  push_cast
  ring

/-- DLMF 1.17.19, under the hypotheses of Dirichlet's theorem 1.8.11: for `2π`-periodic `φ`,
integrable on a period, with one-sided (generalized) derivatives at `a`,
`∫_{−π}^{π} δₙ(x − a) φ(x) dx → ½φ(a−) + ½φ(a+)`. -/
theorem dlmf_1_17_19_dirichlet {φ : ℝ → ℂ} (hper : Function.Periodic φ (2 * π))
    (hφ : IntervalIntegrable φ volume (-π) π) {a : ℝ} {fL fR dL dR : ℂ}
    (hL : Tendsto (fun h : ℝ => (φ (a + h) - fL) / h) (𝓝[<] 0) (𝓝 dL))
    (hR : Tendsto (fun h : ℝ => (φ (a + h) - fR) / h) (𝓝[>] 0) (𝓝 dR)) :
    Tendsto (fun n : ℕ => ∫ x in (-π)..π, dirichletDelta n (x - a) * φ x) atTop
      (𝓝 (fL / 2 + fR / 2)) := by
  simp_rw [integral_dirichletDelta_mul hφ]
  exact dlmf_1_8_11 hper hφ hL hR

/-- DLMF 1.17.19 for continuous `2π`-periodic `φ` differentiable at `a`. -/
theorem dlmf_1_17_19 {φ : ℝ → ℂ} (hper : Function.Periodic φ (2 * π)) (hc : Continuous φ)
    {a : ℝ} (hd : DifferentiableAt ℝ φ a) :
    Tendsto (fun n : ℕ => ∫ x in (-π)..π, dirichletDelta n (x - a) * φ x) atTop (𝓝 (φ a)) := by
  have hs := hasDerivAt_iff_tendsto_slope_zero.mp hd.hasDerivAt
  have hs' : Tendsto (fun h : ℝ => (φ (a + h) - φ a) / h) (𝓝[≠] 0) (𝓝 (deriv φ a)) :=
    hs.congr fun h => by rw [Complex.real_smul, ofReal_inv, div_eq_inv_mul]
  have h := dlmf_1_17_19_dirichlet hper (hc.intervalIntegrable _ _)
    (hs'.mono_left (nhdsWithin_mono _ fun h (hh : h < 0) => hh.ne))
    (hs'.mono_left (nhdsWithin_mono _ fun h (hh : 0 < h) => hh.ne'))
  rwa [add_halves] at h

/-! ### Continuity of `φ` is not enough for 1.17.19 -/

theorem abs_halfDirichlet_le (n : ℕ) (s : ℝ) : |halfDirichlet n s| ≤ n + 1 / 2 := by
  have h := abs_dirichlet1_le n (s / (2 * π))
  have hπ := Real.pi_pos
  rw [dirichlet1, show 2 * π * (s / (2 * π)) = s by field_simp, abs_mul, abs_two] at h
  linarith

theorem continuous_dirichletDelta (n : ℕ) : Continuous (dirichletDelta n) := by
  rw [show dirichletDelta n = fun y => ((halfDirichlet n y / π : ℝ) : ℂ) from
    funext (dirichletDelta_eq n)]
  exact Complex.continuous_ofReal.comp ((continuous_halfDirichlet n).div_const π)

theorem intervalIntegrable_dirichletDelta_mul (n : ℕ) (F : C(AddCircle (2 * π), ℂ)) :
    IntervalIntegrable (fun x : ℝ => dirichletDelta n x * F x) volume (-π) π :=
  ((continuous_dirichletDelta n).mul (F.continuous.comp continuous_quotient_mk')).intervalIntegrable
    _ _

/-- The functional `F ↦ ∫_{−π}^{π} δₙ(x) F(x) dx` on the Banach space `C(ℝ/2πℤ, ℂ)`. -/
noncomputable def dirichletFunctional (n : ℕ) : C(AddCircle (2 * π), ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun F => ∫ x in (-π)..π, dirichletDelta n x * F x
      map_add' := fun F G => by
        simp only [ContinuousMap.add_apply, mul_add]
        exact intervalIntegral.integral_add (intervalIntegrable_dirichletDelta_mul n F)
          (intervalIntegrable_dirichletDelta_mul n G)
      map_smul' := fun c F => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        funext x
        ring }
    ((n + 1 / 2) / π * (2 * π)) fun F => by
      have hπ := Real.pi_pos
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := -π) (b := π) (C := (n + 1 / 2) / π * ‖F‖)
        (f := fun x : ℝ => dirichletDelta n x * F x) fun x _ => by
          rw [norm_mul, dirichletDelta_eq, Complex.norm_real, Real.norm_eq_abs, abs_div,
            abs_of_pos hπ]
          gcongr
          · exact abs_halfDirichlet_le n x
          · exact F.norm_coe_le_norm _
      rw [show |π - -π| = 2 * π by rw [abs_of_pos (by linarith)]; ring] at h
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      linarith

theorem dirichletFunctional_apply (n : ℕ) (F : C(AddCircle (2 * π), ℂ)) :
    dirichletFunctional n F = ∫ x in (-π)..π, dirichletDelta n x * F x := rfl

/-- `∫_0^π |Dₙ| = (π/2) Lₙ` with the Lebesgue constant `Lₙ` of 1.8.8. -/
theorem integral_abs_halfDirichlet (n : ℕ) :
    ∫ t in (0 : ℝ)..π, |halfDirichlet n t| = π / 2 * lebesgueConst n := by
  have hπ := Real.pi_pos
  rw [lebesgueConst, ← mul_assoc, show π / 2 * (1 / π) = 1 / 2 by field_simp,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
  rw [uIoc_of_le hπ.le] at ht
  have hs : 0 < Real.sin (t / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2])
  have h := two_mul_halfDirichlet_mul_sin n t
  rw [← h, abs_mul, abs_mul, abs_of_pos hs, abs_two]
  field_simp

theorem le_norm_dirichletFunctional (n : ℕ) :
    lebesgueConst n / 2 - 1 ≤ ‖dirichletFunctional n‖ := by
  have hπ := Real.pi_pos
  set D := halfDirichlet n with hD
  have hDc : Continuous D := continuous_halfDirichlet n
  set g : ℝ → ℝ := fun x => D x / (|D x| + 1)
  have hgc : Continuous g := hDc.div (hDc.abs.add continuous_const) fun x => by positivity
  have hgp : Function.Periodic (fun x => ((g x : ℝ) : ℂ)) (2 * π) := fun x => by
    simp only [g, D, halfDirichlet_periodic n x]
  let ψ : C(AddCircle (2 * π), ℂ) :=
    ⟨hgp.lift, (Complex.continuous_ofReal.comp hgc).quotient_liftOn' _⟩
  have hψ : ∀ x : ℝ, ψ x = ((g x : ℝ) : ℂ) := fun x => rfl
  have hψn : ‖ψ‖ ≤ 1 := by
    refine (ContinuousMap.norm_le _ zero_le_one).mpr fun p => ?_
    induction p using QuotientAddGroup.induction_on with
    | H x =>
      rw [hψ, Complex.norm_real, Real.norm_eq_abs, abs_div,
        abs_of_pos (by positivity : 0 < |D x| + 1)]
      exact (div_le_one (by positivity)).mpr (by linarith)
  set k : ℝ → ℝ := fun x => D x ^ 2 / (|D x| + 1)
  have hkc : Continuous k := (hDc.pow 2).div (hDc.abs.add continuous_const) fun x => by positivity
  have hval : dirichletFunctional n ψ = ((1 / π * ∫ x in (-π)..π, k x : ℝ) : ℂ) := by
    rw [dirichletFunctional_apply, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hψ, dirichletDelta_eq, g, k]
    push_cast
    ring
  have hk0 : ∀ x, 0 ≤ k x := fun x => by positivity
  have hsplit : ∫ x in (-π)..π, k x = (∫ x in (-π)..0, k x) + ∫ x in (0 : ℝ)..π, k x :=
    (intervalIntegral.integral_add_adjacent_intervals (hkc.intervalIntegrable _ _)
      (hkc.intervalIntegrable _ _)).symm
  have hneg : 0 ≤ ∫ x in (-π)..0, k x :=
    intervalIntegral.integral_nonneg (by linarith) fun x _ => hk0 x
  have hmono : ∫ x in (0 : ℝ)..π, (|D x| - 1) ≤ ∫ x in (0 : ℝ)..π, k x := by
    refine intervalIntegral.integral_mono_on hπ.le
      ((hDc.abs.sub continuous_const).intervalIntegrable _ _) (hkc.intervalIntegrable _ _)
      fun x _ => ?_
    simp only [k]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_abs (D x)]
  rw [intervalIntegral.integral_sub (hDc.abs.intervalIntegrable _ _) intervalIntegrable_const,
    integral_abs_halfDirichlet, intervalIntegral.integral_const, smul_eq_mul, mul_one,
    sub_zero] at hmono
  have hge : lebesgueConst n / 2 - 1 ≤ 1 / π * ∫ x in (-π)..π, k x := by
    rw [hsplit]
    have : lebesgueConst n / 2 - 1 = 1 / π * (π / 2 * lebesgueConst n - π) := by
      field_simp
    rw [this]
    gcongr
    linarith
  calc lebesgueConst n / 2 - 1 ≤ 1 / π * ∫ x in (-π)..π, k x := hge
    _ = ‖dirichletFunctional n ψ‖ := by
      rw [hval, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (by positivity)
        (intervalIntegral.integral_nonneg (by linarith) fun x _ => hk0 x))]
    _ ≤ ‖dirichletFunctional n‖ * ‖ψ‖ := (dirichletFunctional n).le_opNorm ψ
    _ ≤ ‖dirichletFunctional n‖ := mul_le_of_le_one_right (norm_nonneg _) hψn

theorem tendsto_lebesgueConst_atTop : Tendsto lebesgueConst atTop atTop := by
  have hπ := Real.pi_pos
  have hv : Tendsto (fun n : ℕ => 4 / π ^ 2 * Real.log n) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)
  exact dlmf_1_8_9.symm.tendsto_atTop hv

/-- **DLMF error in 1.17.19–1.17.20**: continuity and `2π`-periodicity of `φ` do not suffice.
`∫_{−π}^{π} δₙ(x − a) φ(x) dx` is the `n`th Fourier partial sum of `φ` at `a`, and since the norms
of these functionals on `C(ℝ/2πℤ)` grow like the Lebesgue constants `Lₙ ∼ (4/π²) ln n`, the
Banach–Steinhaus theorem gives a continuous `2π`-periodic `φ` for which the integrals at `a = 0`
are unbounded, so 1.17.19 fails. -/
theorem dlmf_1_17_19_counterexample :
    ∃ φ : ℝ → ℂ, Continuous φ ∧ Function.Periodic φ (2 * π) ∧
      ¬ Tendsto (fun n : ℕ => ∫ x in (-π)..π, dirichletDelta n (x - 0) * φ x) atTop
        (𝓝 (φ 0)) := by
  by_contra hcon
  push Not at hcon
  have hbd : ∀ F : C(AddCircle (2 * π), ℂ), ∃ C, ∀ n, ‖dirichletFunctional n F‖ ≤ C := by
    intro F
    have h := hcon (fun x => F x) (F.continuous.comp continuous_quotient_mk')
      (fun x => by simp only [AddCircle.coe_add_period])
    simp only [sub_zero] at h
    obtain ⟨C, hC⟩ := h.norm.bddAbove_range
    exact ⟨C, fun n => hC ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hbd
  obtain ⟨n, hn⟩ := (tendsto_lebesgueConst_atTop.eventually_gt_atTop (2 * C + 2)).exists
  have := le_norm_dirichletFunctional n
  linarith [hC n]

/-! ### The `2π`-periodic delta (1.17.21) -/

theorem tendsto_finset_Icc_int : Tendsto (fun n : ℕ => Finset.Icc (-(n : ℤ)) n) atTop atTop :=
  tendsto_atTop_finset_of_monotone
    (fun m n hmn => Finset.Icc_subset_Icc (by omega) (by omega))
    fun k => ⟨k.natAbs, by simp only [Finset.mem_Icc]; omega⟩

theorem sum_Icc_neg_index (n : ℕ) (g : ℤ → ℂ) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n, g (-k) = ∑ k ∈ Finset.Icc (-(n : ℤ)) n, g k :=
  Finset.sum_nbij' (fun k => -k) (fun k => -k)
    (fun k hk => by simp only [Finset.mem_Icc] at hk ⊢; omega)
    (fun k hk => by simp only [Finset.mem_Icc] at hk ⊢; omega)
    (fun k _ => neg_neg k) (fun k _ => neg_neg k) (fun k _ => rfl)

/-- DLMF 1.17.21, the formal `2π`-periodic representation `δ(x − a) = (1/(2π)) ∑ₖ e^{ik(x−a)}`,
as distributions on `ℝ`: the `2π`-periodic delta is the Dirac comb `∑ₘ δ(x − a − 2πm)`. For every
test function `φ`, `∑ₘ φ(a + 2πm)` converges and
`∫ δₙ(x − a) φ(x) dx → ∑ₘ φ(a + 2πm)`. The proof is Poisson's summation formula 1.8.14. -/
theorem dlmf_1_17_21 {φ : ℝ → ℂ} (hφ : IsTestFunction univ φ) (a : ℝ) :
    Summable (fun m : ℤ => φ (a + 2 * π * m)) ∧
      Tendsto (fun n : ℕ => ∫ x, dirichletDelta n (x - a) * φ x) atTop
        (𝓝 (∑' m : ℤ, φ (a + 2 * π * m))) := by
  have hπ := Real.pi_pos
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  set f : ℝ → ℂ := fun t => φ (2 * π * t)
  have hfs : ContDiff ℝ ∞ f := hφ.1.comp (contDiff_const.mul contDiff_id)
  have hfc : HasCompactSupport f := by
    have := hφ.2.1.comp_smul h2π
    simpa [smul_eq_mul] using this
  have hfi : Integrable f := hfs.continuous.integrable_of_hasCompactSupport hfc
  have hd1 := (contDiff_infty_iff_deriv.mp hfs).2
  have hd2 := (contDiff_infty_iff_deriv.mp hd1).2
  have hf''i : Integrable (deriv (deriv f)) :=
    hd2.continuous.integrable_of_hasCompactSupport hfc.deriv.deriv
  obtain ⟨hs1, hs2, heq⟩ := dlmf_1_8_14 (hfs.of_le (by exact_mod_cast natCast_le_infty 2)) hfi hf''i
    (a / (2 * π))
  have hx : ∀ m : ℤ, f (a / (2 * π) + m) = φ (a + 2 * π * m) := fun m => by
    simp only [f]; congr 1; field_simp
  simp only [hx] at hs1 heq
  refine ⟨hs1, ?_⟩
  rw [heq]
  -- the Poisson terms
  set T : ℤ → ℂ := fun k => cexp (2 * π * I * k * (a / (2 * π) : ℝ)) *
    ∫ t, f t * cexp (-2 * π * I * k * t)
  have hT : ∀ k : ℤ, T k =
      ((2 * π : ℝ) : ℂ)⁻¹ * (cexp (I * k * a) * ∫ y, φ y * cexp (-(I * k * y))) := fun k => by
    simp only [T, f]
    have hc := Measure.integral_comp_mul_left (fun y : ℝ => φ y * cexp (-(I * k * y))) (2 * π)
    have e : ∫ t : ℝ, φ (2 * π * t) * cexp (-2 * π * I * k * t) =
        ∫ t : ℝ, φ (2 * π * t) * cexp (-(I * k * ((2 * π * t : ℝ) : ℂ))) :=
      integral_congr_ae (ae_of_all _ fun t => by push_cast; ring_nf)
    rw [e, hc, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹), Complex.real_smul]
    have : (2 * π * I * k * ((a / (2 * π) : ℝ) : ℂ)) = I * k * a := by
      push_cast; field_simp
    rw [this]
    push_cast
    ring
  have hlim := (hs2.hasSum.comp tendsto_finset_Icc_int)
  refine hlim.congr fun n => ?_
  simp only [Function.comp]
  -- the integral as a finite sum
  have hφi : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have hint : ∀ k : ℤ, Integrable fun x : ℝ => ((2 * π : ℝ) : ℂ)⁻¹ *
      (cexp (I * k * (x - a)) * φ x) := fun k =>
    (hφi.bdd_mul (c := 1) (by fun_prop) (ae_of_all _ fun x => by
      rw [show I * (k : ℂ) * ((x : ℂ) - a) = ((k * (x - a) : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I])).const_mul _
  have e : (fun x => dirichletDelta n (x - a) * φ x) = fun x : ℝ =>
      ∑ k ∈ Finset.Icc (-(n : ℤ)) n, ((2 * π : ℝ) : ℂ)⁻¹ * (cexp (I * k * (x - a)) * φ x) := by
    funext x
    rw [dirichletDelta, mul_assoc, Finset.sum_mul, Finset.mul_sum]
    push_cast
    rfl
  rw [e, integral_finsetSum _ fun k _ => hint k, ← sum_Icc_neg_index]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hT, integral_const_mul, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [mul_left_comm, ← Complex.exp_add, mul_comm]
  congr 2
  push_cast
  ring

end Azurite.DLMF
