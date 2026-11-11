/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section8
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# DLMF §5.9(i): integral representations of `Γ` (part 1)

Formalizations of <https://dlmf.nist.gov/5.9>, equations 5.9.1 and 5.9.3.

* The Laplace transform of `t^{a−1}` at a complex point:
  `∫₀^∞ t^{a−1} e^{−zt} dt = Γ(a) z^{−a}`, `ℜa > 0`, `ℜz > 0` (`integral_cpow_mul_cexp_neg`).
  Mathlib has it for real `z > 0`; both sides are analytic in `z` on the right half-plane
  (`hasDerivAt_laplace_cpow`, differentiation under the integral sign), so the identity theorem
  (`eqOn_of_eq_on_pos_reals`) extends it.
* 5.9.1, `(1/μ) Γ(ν/μ) z^{−ν/μ} = ∫₀^∞ e^{−zt^μ} t^{ν−1} dt` (`dlmf_5_9_1`), by the substitution
  `u = t^μ`.
* 5.9.3, `c^{−z} Γ(z) = ∫_{−∞}^{∞} |t|^{2z−1} e^{−ct²} dt` (`dlmf_5_9_3`), from 5.9.1 with
  `μ = 2` and evenness.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-- Identity theorem along the positive reals: two functions analytic on a preconnected open set
containing `1` that agree at every positive real of that set agree on it. -/
theorem eqOn_of_eq_on_pos_reals {f g : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) (hU : IsPreconnected U) (hU1 : IsOpen U) (h1 : (1 : ℂ) ∈ U)
    (h : ∀ x : ℝ, 0 < x → (x : ℂ) ∈ U → f x = g x) : EqOn f g U := by
  refine hf.eqOn_of_preconnected_of_frequently_eq hg hU h1 ?_
  have hlim : Tendsto (fun j : ℕ => (((1 : ℝ) + 1 / ((j : ℝ) + 1) : ℝ) : ℂ)) atTop
      (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun j => ?_⟩
    · have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
      rw [add_zero] at h0
      have := (continuous_ofReal.tendsto 1).comp h0
      rw [ofReal_one] at this
      exact this
    · intro h
      have := ofReal_injective (h.trans ofReal_one.symm)
      have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith
  have hev : ∀ᶠ j : ℕ in atTop, (((1 : ℝ) + 1 / ((j : ℝ) + 1) : ℝ) : ℂ) ∈ U :=
    ((continuous_ofReal.tendsto 1).comp
      (by
        have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
        rw [add_zero] at h0
        exact h0)).eventually (by rw [ofReal_one]; exact hU1.mem_nhds h1)
  refine hlim.frequently (hev.mono fun j hj => ?_).frequently
  exact h _ (by positivity) hj

/-- `‖t^{a−1} e^{−zt}‖ = t^{ℜa−1} e^{−ℜz t}` for `t > 0`. -/
theorem norm_cpow_mul_cexp_neg {t : ℝ} (ht : 0 < t) (a z : ℂ) :
    ‖(t : ℂ) ^ (a - 1) * cexp (-(z * t))‖ = t ^ (a.re - 1) * Real.exp (-(z.re * t)) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  simp

theorem integrableOn_rpow_mul_exp_neg_mul {s b : ℝ} (hs : -1 < s) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ s * Real.exp (-(b * t))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow hs one_pos hb
  refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul]

theorem integrableOn_cpow_sub_one_mul_cexp_neg {a z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * cexp (-(z * t))) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_rpow_mul_exp_neg_mul (s := a.re - 1) (by linarith) hz)
    ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    refine ContinuousAt.continuousWithinAt ?_
    have : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht
    have hc : ContinuousAt (fun t : ℝ => (t : ℂ)) t := continuous_ofReal.continuousAt
    exact (hc.cpow continuousAt_const this).mul (by fun_prop)
  · rw [norm_cpow_mul_cexp_neg ht]

/-- The Laplace transform of `t^{a−1}` is differentiable in `z` on the right half-plane. -/
theorem hasDerivAt_laplace_cpow {a : ℂ} (ha : 0 < a.re) {z₀ : ℂ} (hz : 0 < z₀.re) :
    HasDerivAt (fun z : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) * cexp (-(z * t)))
      (∫ t in Ioi (0 : ℝ), -((t : ℂ) ^ (a + 1 - 1) * cexp (-(z₀ * t)))) z₀ := by
  set ε := z₀.re / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hre : ∀ z ∈ Metric.ball z₀ ε, ε < z.re := fun z hz' => by
    have := (Complex.abs_re_le_norm (z - z₀)).trans_lt (by rwa [← dist_eq_norm])
    rw [sub_re, abs_lt] at this
    linarith [this.1]
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (a - 1) * cexp (-(z * t)))
      (volume.restrict (Ioi 0)) := fun z => by
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    refine ContinuousAt.continuousWithinAt ?_
    have : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht
    have hc : ContinuousAt (fun t : ℝ => (t : ℂ)) t := continuous_ofReal.continuousAt
    exact (hc.cpow continuousAt_const this).mul (by fun_prop)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun z (t : ℝ) => (t : ℂ) ^ (a - 1) * cexp (-(z * t)))
    (F' := fun z (t : ℝ) => -((t : ℂ) ^ (a + 1 - 1) * cexp (-(z * t))))
    (bound := fun t => t ^ ((a + 1).re - 1) * Real.exp (-(ε * t))) (x₀ := z₀)
    (Metric.ball_mem_nhds z₀ hε) (Eventually.of_forall hmeas)
    (integrableOn_cpow_sub_one_mul_cexp_neg ha hz)
    (by
      have := (integrableOn_cpow_sub_one_mul_cexp_neg (a := a + 1) (by simp; linarith) hz).neg
      exact this.aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht z hz' => by
      rw [norm_neg, norm_cpow_mul_cexp_neg ht]
      have := hre z hz'
      have ht' : (0 : ℝ) < t := ht
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg ht'.le _)
      nlinarith))
    (integrableOn_rpow_mul_exp_neg_mul (by simp; linarith) hε)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht z _ => by
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
      have h1 : HasDerivAt (fun z : ℂ => -(z * t)) (-(t : ℂ)) z := by
        have := ((hasDerivAt_id z).mul_const (t : ℂ)).neg
        exact this.congr_deriv (by simp)
      refine (h1.cexp.const_mul ((t : ℂ) ^ (a - 1))).congr_deriv ?_
      rw [show a + 1 - 1 = (a - 1) + 1 by ring, cpow_add _ _ ht0, cpow_one]
      ring))
  exact key.2

/-- The Laplace transform of `t^{a−1}` at a complex point:
`∫₀^∞ t^{a−1} e^{−zt} dt = Γ(a) z^{−a}` (`ℜa > 0`, `ℜz > 0`). -/
theorem integral_cpow_mul_cexp_neg {a z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) * cexp (-(z * t)) = Gamma a * z ^ (-a) := by
  set U : Set ℂ := {w | 0 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hF : AnalyticOnNhd ℂ (fun z : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) * cexp (-(z * t)))
      U :=
    DifferentiableOn.analyticOnNhd (fun _ hw =>
      (hasDerivAt_laplace_cpow ha hw).differentiableAt.differentiableWithinAt) hUo
  have hG : AnalyticOnNhd ℂ (fun z : ℂ => Gamma a * z ^ (-a)) U :=
    DifferentiableOn.analyticOnNhd (fun w hw => by
      have : w ∈ slitPlane := Or.inl hw
      exact ((differentiableAt_id.cpow_const this).const_mul _).differentiableWithinAt) hUo
  refine eqOn_of_eq_on_pos_reals hF hG (convex_halfSpace_re_gt 0).isPreconnected hUo
    (by simp [hU]) (fun x hx _ => ?_) hz
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi ha hx, one_div,
    inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne), cpow_neg]
  ring

/-- `(x^μ)^w = x^{μw}` for `x > 0`. -/
theorem ofReal_rpow_cpow_eq {x : ℝ} (hx : 0 < x) (μ : ℝ) (w : ℂ) :
    ((x ^ μ : ℝ) : ℂ) ^ w = (x : ℂ) ^ ((μ : ℂ) * w) := by
  have h1 : ((x ^ μ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx μ).ne'
  have h2 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [cpow_def_of_ne_zero h1, cpow_def_of_ne_zero h2, ← ofReal_log (Real.rpow_nonneg hx.le μ),
    Real.log_rpow hx, ← ofReal_log hx.le]
  push_cast
  ring_nf

/-- **DLMF 5.9.1**: `(1/μ) Γ(ν/μ) / z^{ν/μ} = ∫₀^∞ e^{−zt^μ} t^{ν−1} dt` (`ℜν > 0`, `μ > 0`,
`ℜz > 0`, principal powers). -/
theorem dlmf_5_9_1 {ν z : ℂ} {μ : ℝ} (hν : 0 < ν.re) (hμ : 0 < μ) (hz : 0 < z.re) :
    1 / (μ : ℂ) * Gamma (ν / μ) * (1 / z ^ (ν / μ)) =
      ∫ t in Ioi (0 : ℝ), cexp (-(z * ((t ^ μ : ℝ) : ℂ))) * (t : ℂ) ^ (ν - 1) := by
  have hμ0 : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hμ.ne'
  have ha : 0 < (ν / μ).re := by
    rw [show ν / (μ : ℂ) = ν * ((μ⁻¹ : ℝ) : ℂ) by push_cast; ring, re_mul_ofReal]
    exact mul_pos hν (inv_pos.mpr hμ)
  have h := integral_cpow_mul_cexp_neg ha hz
  rw [← integral_comp_rpow_Ioi _ hμ.ne'] at h
  have e : ∫ t in Ioi (0 : ℝ), cexp (-(z * ((t ^ μ : ℝ) : ℂ))) * (t : ℂ) ^ (ν - 1) =
      1 / (μ : ℂ) * ∫ x in Ioi (0 : ℝ), (|μ| * x ^ (μ - 1)) •
        (((x ^ μ : ℝ) : ℂ) ^ (ν / μ - 1) * cexp (-(z * ((x ^ μ : ℝ) : ℂ)))) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx' : (0 : ℝ) < x := hx
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx'.ne'
    rw [real_smul, ofReal_mul, abs_of_pos hμ, ofReal_rpow_cpow_eq hx',
      Complex.ofReal_cpow hx'.le (μ - 1)]
    have e1 : (x : ℂ) ^ (((μ - 1 : ℝ) : ℂ)) * (x : ℂ) ^ ((μ : ℂ) * (ν / μ - 1)) =
        (x : ℂ) ^ (ν - 1) := by
      rw [← cpow_add _ _ hx0]
      congr 1
      field_simp
      push_cast
      ring
    calc cexp (-(z * ((x ^ μ : ℝ) : ℂ))) * (x : ℂ) ^ (ν - 1)
        = 1 / (μ : ℂ) * ((μ : ℂ) * ((x : ℂ) ^ (((μ - 1 : ℝ) : ℂ)) *
            (x : ℂ) ^ ((μ : ℂ) * (ν / μ - 1))) * cexp (-(z * ((x ^ μ : ℝ) : ℂ)))) := by
          rw [e1]; field_simp
      _ = _ := by ring
  rw [e, h, cpow_neg, one_div (z ^ (ν / μ))]
  ring

/-- `∫_{−∞}^{∞} f(|t|) dt = 2 ∫₀^∞ f(t) dt` for complex-valued `f` integrable on `(0, ∞)`. -/
theorem integral_comp_abs_complex {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) :
    ∫ x, f |x| = 2 * ∫ x in Ioi (0 : ℝ), f x := by
  have eq : ∫ (x : ℝ) in Ioi 0, f |x| = ∫ (x : ℝ) in Ioi 0, f x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
    rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
  have hf' : IntegrableOn (fun x => f |x|) (Ioi 0) :=
    hf.congr_fun (fun x hx => by rw [abs_of_pos (by exact hx)]) measurableSet_Ioi
  have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf'
  calc
    _ = (∫ x in Iic 0, f |x|) + ∫ x in Ioi 0, f |x| := by
      rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi int_Iic hf',
        Iic_union_Ioi, Measure.restrict_univ]
    _ = 2 * ∫ x in Ioi 0, f x := by
      rw [two_mul, eq]
      congr 1
      rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
      refine setIntegral_congr_fun measurableSet_Iic (fun _ hx => ?_)
      rw [abs_eq_neg_self.mpr (by exact hx)]

theorem integrableOn_dlmf_5_9_1 {ν z : ℂ} {μ : ℝ} (hν : 0 < ν.re) (hμ : 0 < μ) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => cexp (-(z * ((t ^ μ : ℝ) : ℂ))) * (t : ℂ) ^ (ν - 1)) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_rpow_mul_exp_neg_mul_rpow (s := ν.re - 1) (by linarith)
    hμ hz)) ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    refine ContinuousAt.continuousWithinAt ?_
    have : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht
    have hc : ContinuousAt (fun t : ℝ => (t : ℂ)) t := continuous_ofReal.continuousAt
    have hr : ContinuousAt (fun t : ℝ => t ^ μ) t :=
      Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht))
    exact ((continuous_exp.continuousAt.comp
      (((continuous_ofReal.continuousAt.comp hr).const_mul z).neg)).mul
      (hc.cpow continuousAt_const this))
  · have ht' : (0 : ℝ) < t := ht
    rw [norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos ht']
    simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, sub_re, one_re]
    rw [mul_comm]
    exact le_of_eq (by ring_nf)

/-- **DLMF 5.9.3**: `c^{−z} Γ(z) = ∫_{−∞}^{∞} |t|^{2z−1} e^{−ct²} dt` (`c > 0`, `ℜz > 0`). -/
theorem dlmf_5_9_3 {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : 0 < z.re) :
    (c : ℂ) ^ (-z) * Gamma z = ∫ t : ℝ, ((|t| : ℝ) : ℂ) ^ (2 * z - 1) * cexp (-(c * t ^ 2)) := by
  have hc' : 0 < ((c : ℂ)).re := by simpa using hc
  have h1 := dlmf_5_9_1 (ν := 2 * z) (μ := 2) (by simp; linarith) two_pos hc'
  have hfun : ∀ t : ℝ, ((|t| : ℝ) : ℂ) ^ (2 * z - 1) * cexp (-(c * t ^ 2)) =
      (fun x : ℝ => cexp (-((c : ℂ) * ((x ^ (2 : ℝ) : ℝ) : ℂ))) * (x : ℂ) ^ (2 * z - 1)) |t| := by
    intro t
    simp only
    rw [Real.rpow_two, sq_abs, mul_comm]
    push_cast
    rfl
  simp_rw [hfun]
  have hint : IntegrableOn
      (fun x : ℝ => cexp (-((c : ℂ) * ((x ^ (2 : ℝ) : ℝ) : ℂ))) * (x : ℂ) ^ (2 * z - 1)) (Ioi 0) :=
    integrableOn_dlmf_5_9_1 (by simp; linarith) two_pos hc'
  rw [integral_comp_abs_complex hint, ← h1]
  rw [show (2 * z) / ((2 : ℝ) : ℂ) = z by push_cast; field_simp, cpow_neg]
  push_cast
  field_simp

end Azurite.DLMF
