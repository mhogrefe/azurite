/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14StieltjesAbel
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# DLMF §1.15(iv): Definitions for integrals

Formalizations of <https://dlmf.nist.gov/1.15#iv>.

* `IntegralConverges f L`: `∫_{−∞}^{∞} f` converges to `L` in the sense of 1.4.22: `f` is
  integrable on bounded intervals and both `∫_0^∞ f` and `∫_{−∞}^0 f` converge as improper
  integrals (`integralConverges_of_integrable` for Lebesgue integrable `f`).
* `IntegralAbelSum` (1.15.29–1.15.30). The integrals `∫_{−∞}^{∞} e^{−ε|t|} f(t) dt` are taken as
  convergent improper integrals. A convergent `∫ f` need not be absolutely convergent, and then
  `e^{−ε|t|} f` need not be Lebesgue integrable: `eᵗ sin(e^{2t})` with `ε < 1` is an example.
  `dlmf_1_15_30` covers the Lebesgue integrable case.
* `IntegralCesaroSum` (1.15.31–1.15.32).
* Regularity (`dlmf_1_15_iv`): a convergent `∫_{−∞}^{∞} f = L` is Abel and Cesàro summable to `L`.
  On each half line, integration by parts against the primitive `P` (`integral_mul_eq_primitive`
  of §1.14(vi)) gives `∫_0^R (1 − t/R) g = (1/R) ∫_0^R P` and
  `∫_0^R e^{−εt} g = e^{−εR} P(R) + ∫_0^R P(u) ε e^{−εu} du`. The averages of `P` then tend to
  `P(∞)` (`tendsto_average_of_tendsto`, `tendsto_abel_weight`).
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real

namespace Azurite.DLMF

/-! ### Definitions -/

/-- `∫_{−∞}^{∞} f(t) dt` converges to `L` (as in 1.4.22): `f` is integrable on bounded intervals,
`∫_0^b f → L₁` as `b → ∞`, `∫_a^0 f → L₂` as `a → −∞`, and `L = L₁ + L₂`. -/
def IntegralConverges (f : ℝ → ℂ) (L : ℂ) : Prop :=
  (∀ a b, IntervalIntegrable f volume a b) ∧ ∃ L₁ L₂ : ℂ,
    Tendsto (fun b => ∫ t in (0 : ℝ)..b, f t) atTop (𝓝 L₁) ∧
    Tendsto (fun a => ∫ t in a..(0 : ℝ), f t) atBot (𝓝 L₂) ∧ L = L₁ + L₂

/-- **DLMF (1.15.29)–(1.15.30)**, Abel summability of an integral:
`∫_{−∞}^{∞} e^{−ε|t|} f(t) dt` converges for every `ε > 0` (to `A(ε)`) and `A(ε) → L` as
`ε → 0+`. -/
def IntegralAbelSum (f : ℝ → ℂ) (L : ℂ) : Prop :=
  ∃ A : ℝ → ℂ, (∀ ε > 0, IntegralConverges (fun t => (Real.exp (-(ε * |t|)) : ℂ) * f t) (A ε)) ∧
    Tendsto A (𝓝[>] 0) (𝓝 L)

/-- **DLMF (1.15.31)–(1.15.32)**, Cesàro `(C,1)` summability of an integral:
`∫_{−R}^{R} (1 − |t|/R) f(t) dt → L` as `R → ∞`. -/
def IntegralCesaroSum (f : ℝ → ℂ) (L : ℂ) : Prop :=
  (∀ a b, IntervalIntegrable f volume a b) ∧
    Tendsto (fun R : ℝ => ∫ t in -R..R, ((1 - |t| / R : ℝ) : ℂ) * f t) atTop (𝓝 L)

/-- A Lebesgue integrable `f` has a convergent integral, equal to `∫ f`. -/
theorem integralConverges_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    IntegralConverges f (∫ t, f t) := by
  refine ⟨fun a b => hf.intervalIntegrable, ∫ t in Ioi 0, f t, ∫ t in Iic 0, f t,
    intervalIntegral_tendsto_integral_Ioi 0 hf.integrableOn tendsto_id,
    intervalIntegral_tendsto_integral_Iic 0 hf.integrableOn tendsto_id, ?_⟩
  rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl).symm measurableSet_Iic hf.integrableOn
    hf.integrableOn, Ioi_union_Iic, Measure.restrict_univ]

/-! ### One-sided tools on `[0, ∞)` -/

section OneSided

variable {g : ℝ → ℂ} {L₁ : ℂ}

theorem continuous_primitive_zero (hg : ∀ a b, IntervalIntegrable g volume a b) :
    Continuous fun u => ∫ t in (0 : ℝ)..u, g t :=
  intervalIntegral.continuous_primitive hg 0

theorem exists_bound_primitive (hg : ∀ a b, IntervalIntegrable g volume a b)
    (hL : Tendsto (fun b => ∫ t in (0 : ℝ)..b, g t) atTop (𝓝 L₁)) :
    ∃ B, 0 ≤ B ∧ ∀ u, 0 ≤ u → ‖∫ t in (0 : ℝ)..u, g t‖ ≤ B := by
  obtain ⟨B, hB⟩ := exists_bound_of_tendsto_integral (fun R _ => hg 0 R) hL
  exact ⟨max B 0, le_max_right _ _, fun u hu => (hB u hu).trans (le_max_left _ _)⟩

/-- `(1/R) ∫_0^R P → L₁` when `P(u) → L₁` (Cesàro means of a continuous function). -/
theorem tendsto_average_of_tendsto {P : ℝ → ℂ} (hP : Continuous P)
    (hL : Tendsto P atTop (𝓝 L₁)) :
    Tendsto (fun R : ℝ => (1 / R : ℂ) * ∫ u in (0 : ℝ)..R, P u) atTop (𝓝 L₁) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨S, hS⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hL) (ε / 2) (by positivity))
  set S' := max S 0
  set C := ‖∫ u in (0 : ℝ)..S', (P u - L₁)‖
  have hev : ∀ᶠ R : ℝ in atTop, C / R < ε / 2 := by
    have := (tendsto_const_nhds (x := C)).div_atTop tendsto_id
    exact (tendsto_order.1 this).2 _ (by positivity)
  filter_upwards [hev, eventually_gt_atTop S'] with R hR hRS
  have hR0 : 0 < R := lt_of_le_of_lt (le_max_right _ _) hRS
  have hi : ∀ a b, IntervalIntegrable (fun u => P u - L₁) volume a b := fun a b =>
    (hP.sub continuous_const).intervalIntegrable a b
  have e : (1 / R : ℂ) * (∫ u in (0 : ℝ)..R, P u) - L₁ =
      (1 / R : ℂ) * ((∫ u in (0 : ℝ)..S', (P u - L₁)) + ∫ u in S'..R, (P u - L₁)) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi 0 S') (hi S' R),
      intervalIntegral.integral_sub (hP.intervalIntegrable 0 R) intervalIntegrable_const,
      intervalIntegral.integral_const, Complex.real_smul, sub_zero]
    have : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR0.ne'
    field_simp
  have h2 : ‖∫ u in S'..R, (P u - L₁)‖ ≤ ε / 2 * |R - S'| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => by
      rw [uIoc_of_le hRS.le] at hu
      rw [← dist_eq_norm]
      exact (hS u ((le_max_left _ _).trans hu.1.le)).le
  rw [dist_eq_norm, e, norm_mul, show ‖(1 / R : ℂ)‖ = 1 / R by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg hR0.le] ]
  have hS'R : |R - S'| ≤ R := by
    rw [abs_of_pos (by linarith)]; linarith [le_max_right S 0]
  calc 1 / R * ‖(∫ u in (0 : ℝ)..S', (P u - L₁)) + ∫ u in S'..R, (P u - L₁)‖ ≤
      1 / R * (C + ε / 2 * R) := by
        refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (by positivity)
        exact add_le_add le_rfl (h2.trans (mul_le_mul_of_nonneg_left hS'R (by positivity)))
    _ = C / R + ε / 2 := by field_simp
    _ < ε := by linarith

/-- One-sided Cesàro: `∫_0^R (1 − t/R) g(t) dt → L₁` when `∫_0^R g → L₁`. -/
theorem tendsto_cesaro_halfline (hg : ∀ a b, IntervalIntegrable g volume a b)
    (hL : Tendsto (fun b => ∫ t in (0 : ℝ)..b, g t) atTop (𝓝 L₁)) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, ((1 - t / R : ℝ) : ℂ) * g t) atTop (𝓝 L₁) := by
  refine (tendsto_average_of_tendsto (continuous_primitive_zero hg) hL).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  have h := integral_mul_eq_primitive (g := g) (h := fun t => ((1 - t / R : ℝ) : ℂ))
    (h' := fun _ => ((-(1 / R) : ℝ) : ℂ)) hR.le (hg 0 R)
    (fun t _ => by
      have := ((hasDerivAt_id t).div_const R).const_sub 1 |>.ofReal_comp
      simpa using this)
    continuousOn_const
  rw [show ∫ t in (0 : ℝ)..R, ((1 - t / R : ℝ) : ℂ) * g t =
    ∫ t in (0 : ℝ)..R, g t * ((1 - t / R : ℝ) : ℂ) by congr 1; funext t; ring, h,
    intervalIntegral.integral_mul_const]
  have : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  simp only [div_self hR.ne', sub_self, ofReal_zero, mul_zero, zero_sub]
  push_cast
  field_simp

end OneSided

section OneSidedAbel

variable {g : ℝ → ℂ} {L₁ : ℂ}

theorem integral_exp_weight {ε : ℝ} (hε : 0 < ε) :
    ∫ u in Ioi (0 : ℝ), ε * Real.exp (-(ε * u)) = 1 := by
  rw [integral_const_mul]
  have := integral_exp_mul_Ioi (a := -ε) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, neg_mul] at this
  rw [this]; field_simp

theorem integrableOn_exp_weight {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun u : ℝ => ε * Real.exp (-(ε * u))) (Ioi 0) := by
  have := (exp_neg_integrableOn_Ioi 0 hε).const_mul ε
  simp only [neg_mul] at this
  exact this

theorem integrableOn_primitive_mul_weight (hg : ∀ a b, IntervalIntegrable g volume a b)
    (hL : Tendsto (fun b => ∫ t in (0 : ℝ)..b, g t) atTop (𝓝 L₁)) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun u => (∫ t in (0 : ℝ)..u, g t) * ((ε * Real.exp (-(ε * u)) : ℝ) : ℂ))
      (Ioi 0) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_primitive hg hL
  refine ((integrableOn_exp_weight hε).const_mul B).mono'
    (((continuous_primitive_zero hg).mul (by fun_prop)).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right (hB u (le_of_lt hu)) (by positivity)

/-- One-sided Abel, fixed `ε > 0`: `∫_0^R e^{−εt} g(t) dt → ∫_0^∞ P(u) ε e^{−εu} du` with
`P(u) = ∫_0^u g`. -/
theorem tendsto_abel_halfline (hg : ∀ a b, IntervalIntegrable g volume a b)
    (hL : Tendsto (fun b => ∫ t in (0 : ℝ)..b, g t) atTop (𝓝 L₁)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, (Real.exp (-(ε * t)) : ℂ) * g t) atTop
      (𝓝 (∫ u in Ioi (0 : ℝ), (∫ t in (0 : ℝ)..u, g t) *
        ((ε * Real.exp (-(ε * u)) : ℝ) : ℂ))) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_primitive hg hL
  have hbd : Tendsto (fun R : ℝ => (∫ t in (0 : ℝ)..R, g t) * (Real.exp (-(ε * R)) : ℂ)) atTop
      (𝓝 0) := by
    have hz := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_id.const_mul_atTop hε))).const_mul B
    rw [mul_zero] at hz
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_ge_atTop 0] with R hR
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_right (hB R hR) (Real.exp_pos _).le
  have hI := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_primitive_mul_weight hg hL hε) tendsto_id
  have := hbd.add hI
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  have h := integral_mul_eq_primitive (g := g) (h := fun t => (Real.exp (-(ε * t)) : ℂ))
    (h' := fun t => ((-(ε * Real.exp (-(ε * t))) : ℝ) : ℂ)) hR (hg 0 R)
    (fun t _ => by
      have := (((hasDerivAt_id t).const_mul ε).neg.exp).ofReal_comp
      simp only [id, Pi.neg_apply] at this
      refine this.congr_deriv ?_
      push_cast; ring)
    (by fun_prop)
  rw [show ∫ t in (0 : ℝ)..R, (Real.exp (-(ε * t)) : ℂ) * g t =
    ∫ t in (0 : ℝ)..R, g t * (Real.exp (-(ε * t)) : ℂ) by congr 1; funext t; ring, h]
  simp only [id]
  rw [sub_eq_add_neg, ← intervalIntegral.integral_neg]
  congr 1
  refine intervalIntegral.integral_congr fun u _ => ?_
  push_cast; ring

/-- One-sided Abel limit: `∫_0^∞ P(u) ε e^{−εu} du → L₁` as `ε → 0+`. -/
theorem tendsto_abel_weight (hg : ∀ a b, IntervalIntegrable g volume a b)
    (hL : Tendsto (fun b => ∫ t in (0 : ℝ)..b, g t) atTop (𝓝 L₁)) :
    Tendsto (fun ε : ℝ => ∫ u in Ioi (0 : ℝ), (∫ t in (0 : ℝ)..u, g t) *
      ((ε * Real.exp (-(ε * u)) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 L₁) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_primitive hg hL
  set K := B + ‖L₁‖
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨S₀, hS⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hL) (η / 2) (by positivity))
  set S := max S₀ 0
  have hS0 : 0 ≤ S := le_max_right _ _
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * (K * S) < η / 2 := by
    have : Tendsto (fun ε : ℝ => ε * (K * S)) (𝓝[>] 0) (𝓝 0) := by
      have h := ((show Continuous fun ε : ℝ => ε * (K * S) by fun_prop).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using h
    exact (tendsto_order.1 this).2 _ (by positivity)
  filter_upwards [hev, self_mem_nhdsWithin] with ε hεS hε
  have hε0 : (0 : ℝ) < ε := hε
  have hw := integral_exp_weight hε0
  have hwI := integrableOn_exp_weight hε0
  have hPI := integrableOn_primitive_mul_weight hg hL hε0
  have hL1I : IntegrableOn (fun u : ℝ => L₁ * ((ε * Real.exp (-(ε * u)) : ℝ) : ℂ)) (Ioi 0) :=
    (hwI.ofReal (𝕜 := ℂ)).const_mul L₁
  have e : (∫ u in Ioi (0 : ℝ), (∫ t in (0 : ℝ)..u, g t) * ((ε * Real.exp (-(ε * u)) : ℝ) : ℂ))
      - L₁ = ∫ u in Ioi (0 : ℝ), ((∫ t in (0 : ℝ)..u, g t) - L₁) *
        ((ε * Real.exp (-(ε * u)) : ℝ) : ℂ) := by
    have hL1 : ∫ u in Ioi (0 : ℝ), L₁ * ((ε * Real.exp (-(ε * u)) : ℝ) : ℂ) = L₁ := by
      rw [integral_const_mul, integral_complex_ofReal, hw, ofReal_one, mul_one]
    conv_lhs => rw [← hL1]
    rw [← integral_sub hPI hL1I]
    congr 1; funext u; ring
  rw [dist_eq_norm, e]
  set F : ℝ → ℝ := fun u => ‖((∫ t in (0 : ℝ)..u, g t) - L₁) *
    ((ε * Real.exp (-(ε * u)) : ℝ) : ℂ)‖
  have hFI : IntegrableOn F (Ioi 0) :=
    (IntegrableOn.congr_fun (hPI.sub hL1I)
      (fun u _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi).norm
  have hF0 : ∀ u, 0 ≤ F u := fun u => norm_nonneg _
  have hFe : ∀ u, 0 < u → F u = ‖(∫ t in (0 : ℝ)..u, g t) - L₁‖ * (ε * Real.exp (-(ε * u))) :=
    fun u _ => by
      simp only [F]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hsplit : ∫ u in Ioi (0 : ℝ), F u = (∫ u in Ioc 0 S, F u) + ∫ u in Ioi S, F u := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hFI.mono_set Ioc_subset_Ioi_self)
      (hFI.mono_set (Ioi_subset_Ioi hS0)), Ioc_union_Ioi_eq_Ioi hS0]
  have h1 : ∫ u in Ioc 0 S, F u ≤ ε * K * S := by
    have := setIntegral_mono_on (hFI.mono_set Ioc_subset_Ioi_self)
      (integrableOn_const (s := Ioc 0 S) (C := ε * K) (by simp)) measurableSet_Ioc fun u hu => by
        rw [hFe u hu.1]
        have hK : ‖(∫ t in (0 : ℝ)..u, g t) - L₁‖ ≤ K := by
          have := norm_sub_le (∫ t in (0 : ℝ)..u, g t) L₁
          linarith [hB u hu.1.le]
        have hw1 : ε * Real.exp (-(ε * u)) ≤ ε := by
          have := Real.exp_le_one_iff.mpr (by nlinarith [hu.1] : -(ε * u) ≤ 0)
          nlinarith
        calc ‖(∫ t in (0 : ℝ)..u, g t) - L₁‖ * (ε * Real.exp (-(ε * u))) ≤ K * ε :=
              mul_le_mul hK hw1 (by positivity) (by positivity)
          _ = ε * K := by ring
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hS0, sub_zero, smul_eq_mul] at this
    linarith
  have h2 : ∫ u in Ioi S, F u ≤ η / 2 := by
    have hm := setIntegral_mono_on (hFI.mono_set (Ioi_subset_Ioi hS0))
      ((hwI.mono_set (Ioi_subset_Ioi hS0)).const_mul (η / 2)) measurableSet_Ioi fun u hu => by
        have hu0 : 0 < u := lt_of_le_of_lt hS0 hu
        rw [hFe u hu0]
        exact mul_le_mul_of_nonneg_right
          (by rw [← dist_eq_norm]; exact (hS u ((le_max_left _ _).trans (le_of_lt hu))).le)
          (by positivity)
    rw [integral_const_mul] at hm
    have hw' : ∫ u in Ioi S, ε * Real.exp (-(ε * u)) ≤ 1 := by
      rw [← hw]
      exact setIntegral_mono_set hwI (ae_of_all _ fun u => by positivity)
        (Ioi_subset_Ioi hS0).eventuallyLE
    nlinarith
  refine (norm_integral_le_integral_norm _).trans_lt ?_
  show ∫ u in Ioi (0 : ℝ), F u < η
  rw [hsplit]
  nlinarith

end OneSidedAbel

/-! ### Regularity -/

theorem intervalIntegrable_comp_neg {f : ℝ → ℂ} (hf : ∀ a b, IntervalIntegrable f volume a b)
    (a b : ℝ) : IntervalIntegrable (fun t => f (-t)) volume a b := by
  have := (IntervalIntegrable.iff_comp_neg (f := f) (a := -a) (b := -b)).mp (hf (-a) (-b))
  simpa only [neg_neg] using this

theorem tendsto_neg_half {f : ℝ → ℂ} {L₂ : ℂ}
    (h : Tendsto (fun a => ∫ t in a..(0 : ℝ), f t) atBot (𝓝 L₂)) :
    Tendsto (fun b => ∫ t in (0 : ℝ)..b, f (-t)) atTop (𝓝 L₂) := by
  refine (h.comp tendsto_neg_atTop_atBot).congr fun b => ?_
  simp only [Function.comp, intervalIntegral.integral_comp_neg, neg_zero]

/-- **DLMF §1.15(iv)**: if `∫_{−∞}^{∞} f(t) dt` converges to `L`, the integral is Abel and Cesàro
summable to `L`. -/
theorem dlmf_1_15_iv {f : ℝ → ℂ} {L : ℂ} (hf : IntegralConverges f L) :
    IntegralAbelSum f L ∧ IntegralCesaroSum f L := by
  obtain ⟨hloc, L₁, L₂, h₁, h₂, rfl⟩ := hf
  have hloc' := intervalIntegrable_comp_neg hloc
  have h₂' := tendsto_neg_half h₂
  refine ⟨?_, hloc, ?_⟩
  · set Ap : ℝ → ℂ := fun ε => ∫ u in Ioi (0 : ℝ), (∫ t in (0 : ℝ)..u, f t) *
      ((ε * Real.exp (-(ε * u)) : ℝ) : ℂ)
    set Am : ℝ → ℂ := fun ε => ∫ u in Ioi (0 : ℝ), (∫ t in (0 : ℝ)..u, f (-t)) *
      ((ε * Real.exp (-(ε * u)) : ℝ) : ℂ)
    refine ⟨fun ε => Ap ε + Am ε, fun ε hε => ?_,
      (tendsto_abel_weight hloc h₁).add (tendsto_abel_weight hloc' h₂')⟩
    set F : ℝ → ℂ := fun t => ((Real.exp (-(ε * |t|)) : ℝ) : ℂ) * f t
    refine ⟨fun a b => (hloc a b).continuousOn_mul (by fun_prop : Continuous fun t : ℝ =>
      ((Real.exp (-(ε * |t|)) : ℝ) : ℂ)).continuousOn, Ap ε, Am ε, ?_, ?_, rfl⟩
    · refine (tendsto_abel_halfline hloc h₁ hε).congr' ?_
      filter_upwards [eventually_ge_atTop 0] with b hb
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hb] at ht
      simp only [F, abs_of_nonneg ht.1]
    · refine ((tendsto_abel_halfline hloc' h₂' hε).comp tendsto_neg_atBot_atTop).congr' ?_
      filter_upwards [eventually_le_atBot 0] with a ha
      have h := intervalIntegral.integral_comp_neg (fun t => F t) (a := 0) (b := -a)
      simp only [neg_neg, neg_zero] at h
      simp only [Function.comp]
      rw [← h]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le (by linarith)] at ht
      simp only [F, abs_neg, abs_of_nonneg ht.1]
  · have hP := tendsto_cesaro_halfline hloc h₁
    have hM := tendsto_cesaro_halfline hloc' h₂'
    rw [add_comm L₁ L₂]
    refine (hM.add hP).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    have hw : ∀ a b, IntervalIntegrable (fun t => ((1 - |t| / R : ℝ) : ℂ) * f t) volume a b :=
      fun a b => (hloc a b).continuousOn_mul (by fun_prop : Continuous fun t : ℝ =>
        ((1 - |t| / R : ℝ) : ℂ)).continuousOn
    rw [← intervalIntegral.integral_add_adjacent_intervals (hw (-R) 0) (hw 0 R)]
    congr 1
    · have h := intervalIntegral.integral_comp_neg
        (fun t => ((1 - |t| / R : ℝ) : ℂ) * f t) (a := 0) (b := R)
      simp only [neg_zero, abs_neg] at h
      rw [← h]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hR.le] at ht
      simp only [abs_of_nonneg ht.1]
    · refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hR.le] at ht
      simp only [abs_of_nonneg ht.1]

/-- In particular a Lebesgue integrable `f` is Abel and Cesàro summable to `∫ f`. -/
theorem dlmf_1_15_iv_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    IntegralAbelSum f (∫ t, f t) ∧ IntegralCesaroSum f (∫ t, f t) :=
  dlmf_1_15_iv (integralConverges_of_integrable hf)

/-- **DLMF (1.15.30)** for Lebesgue integrable `e^{−ε|t|} f`: the Abel integrals are the Lebesgue
integrals `∫ e^{−ε|t|} f(t) dt`. -/
theorem dlmf_1_15_30 {f : ℝ → ℂ} {L : ℂ}
    (hf : ∀ ε > 0, Integrable fun t => (Real.exp (-(ε * |t|)) : ℂ) * f t)
    (hL : Tendsto (fun ε => ∫ t, (Real.exp (-(ε * |t|)) : ℂ) * f t) (𝓝[>] 0) (𝓝 L)) :
    IntegralAbelSum f L :=
  ⟨fun ε => ∫ t, (Real.exp (-(ε * |t|)) : ℂ) * f t,
    fun ε hε => integralConverges_of_integrable (hf ε hε), hL⟩

/-- **DLMF (1.15.32)**. -/
theorem dlmf_1_15_32 {f : ℝ → ℂ} {L : ℂ} :
    IntegralCesaroSum f L ↔ (∀ a b, IntervalIntegrable f volume a b) ∧
      Tendsto (fun R : ℝ => ∫ t in -R..R, ((1 - |t| / R : ℝ) : ℂ) * f t) atTop (𝓝 L) := Iff.rfl

end Azurite.DLMF
