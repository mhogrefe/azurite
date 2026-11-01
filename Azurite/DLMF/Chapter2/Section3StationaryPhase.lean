/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section3Watson
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.Convex

/-!
# DLMF §2.3(iv): the method of stationary phase, Watson-type lemma (2.3.20)

* `integral_rpow_mul_cexp_neg_complex`: `∫₀^∞ t^{α−1} e^{−zt} dt = Γ(α) z^{−α}` for `ℜz > 0`
  (Mathlib has real `z`), by analytic continuation (`analyticOnNhd_integral_rpow_mul_cexp`).
* `fourier_cutoff_model`: with the smooth cutoff `spCutoff` (`1` on `(−∞, 1]`, `0` on `[2, ∞)`),
  `∫₀^∞ e^{ixt} t^{α−1} χ(t) dt = e^{iπα/2} Γ(α) x^{−α} + O(x^{−M})` for every `M > α`: the
  damped integrals `e^{−(ε−ix)t}` are computed exactly, the tail `t^{α−1}(1 − χ)` is
  `O(x^{−M})` by `M` integrations by parts (`spTail_ibp_iter`), and `ε → 0+`.
* `fourier_remainder`: `∫₀^∞ e^{ixt} R(t) dt = O(x^{−β})` when `R⁽ᵏ⁾(t) = O(t^{β−1−k})` near `0`
  (`k ≤ K`, `K > β`) and the integrals converge uniformly at `∞`: split at `t = 1/x` and
  integrate by parts from there (`fourierIoi_iter` of §2.3(i)).
* `dlmf_2_3_20`: the Fourier analog of Watson's lemma; "the expansion 2.3.7 is infinitely
  differentiable" is the hypothesis that each `q⁽ᵏ⁾` has the termwise differentiated expansion.
-/

open Set Filter Topology Asymptotics Complex MeasureTheory
open scoped ContDiff

namespace Azurite.DLMF

/-! ### `∫₀^∞ t^{α−1} e^{−zt} dt = Γ(α) z^{−α}` for complex `z` -/

theorem norm_ofReal_rpow_mul_cexp {α : ℝ} {s : ℂ} {t : ℝ} (ht : 0 < t) :
    ‖((t ^ (α - 1) : ℝ) : ℂ) * cexp (-(s * t))‖ = t ^ (α - 1) * Real.exp (-s.re * t ^ (1 : ℝ)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),
    Complex.norm_exp, Real.rpow_one]
  simp

theorem integrableOn_rpow_mul_cexp_neg {α : ℝ} (hα : 0 < α) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => ((t ^ (α - 1) : ℝ) : ℂ) * cexp (-(s * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < α - 1) one_pos hs
  refine Integrable.mono' h ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
    (norm_ofReal_rpow_mul_cexp ht).le)
  exact ((Complex.measurable_ofReal.comp (measurable_id.pow_const _)).mul
    (by fun_prop : Measurable fun t : ℝ => cexp (-(s * t)))).aestronglyMeasurable

/-- The function `s ↦ ∫₀^∞ t^{α−1} e^{−st} dt` is analytic on `ℜs > 0`. -/
theorem analyticOnNhd_integral_rpow_mul_cexp {α : ℝ} (hα : 0 < α) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∫ t in Ioi 0, ((t ^ (α - 1) : ℝ) : ℂ) * cexp (-(s * t)))
      {s | 0 < s.re} := by
  refine DifferentiableOn.analyticOnNhd (fun s₀ hs₀ => ?_)
    (isOpen_lt continuous_const continuous_re)
  have hs₀' : 0 < s₀.re := hs₀
  set δ := s₀.re / 2
  have hδ : 0 < δ := half_pos hs₀'
  have hball : ∀ s ∈ Metric.ball s₀ δ, δ < s.re := fun s hs => by
    have h1 : |s.re - s₀.re| < δ := by
      calc |s.re - s₀.re| = |(s - s₀).re| := by rw [sub_re]
        _ ≤ ‖s - s₀‖ := abs_re_le_norm _
        _ < δ := by rwa [← dist_eq_norm]
    have := (abs_lt.mp h1).1
    simp only [δ] at this ⊢
    linarith
  have hbound := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < α) one_pos hδ
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun s t => ((t ^ (α - 1) : ℝ) : ℂ) * cexp (-(s * t)))
    (F' := fun s t => ((t ^ (α - 1) : ℝ) : ℂ) * (cexp (-(s * t)) * (-(t : ℂ))))
    (bound := fun t => t ^ α * Real.exp (-δ * t ^ (1 : ℝ)))
    (Metric.ball_mem_nhds s₀ hδ)
    (Eventually.of_forall fun s => ((Complex.measurable_ofReal.comp
      (measurable_id.pow_const _)).mul (by fun_prop : Measurable fun t : ℝ =>
        cexp (-(s * t)))).aestronglyMeasurable)
    (integrableOn_rpow_mul_cexp_neg hα hs₀')
    (((Complex.measurable_ofReal.comp (measurable_id.pow_const _)).mul
      (by fun_prop : Measurable fun t : ℝ => cexp (-(s₀ * t)) * (-(t : ℂ)))).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht s hs => by
      have ht0 : 0 < t := ht
      rw [← mul_assoc, norm_mul, norm_ofReal_rpow_mul_cexp ht0, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg ht0.le, Real.rpow_one]
      calc t ^ (α - 1) * Real.exp (-s.re * t) * t = t ^ α * Real.exp (-s.re * t) := by
            rw [mul_right_comm, ← Real.rpow_add_one ht0.ne', sub_add_cancel]
        _ ≤ t ^ α * Real.exp (-δ * t) := by
            gcongr
            nlinarith [hball s hs])
    hbound
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t _ s _ => by
      have h0 : HasDerivAt (fun y : ℂ => -(y * t)) (-(t : ℂ)) s := by
        have h1 := ((hasDerivAt_id s).mul_const (t : ℂ)).neg
        simp only [id, one_mul] at h1
        exact h1
      exact h0.cexp.const_mul (((t ^ (α - 1) : ℝ) : ℂ)))
  exact key.2.differentiableAt.differentiableWithinAt

/-- `∫₀^∞ t^{α−1} e^{−st} dt = Γ(α) s^{−α}` for `ℜs > 0` (Mathlib has real `s`). -/
theorem integral_rpow_mul_cexp_neg_complex {α : ℝ} (hα : 0 < α) {s : ℂ} (hs : 0 < s.re) :
    ∫ t in Ioi 0, ((t ^ (α - 1) : ℝ) : ℂ) * cexp (-(s * t)) =
      (1 / s) ^ (α : ℂ) * Complex.Gamma α := by
  set U := {s : ℂ | 0 < s.re}
  have hG : AnalyticOnNhd ℂ (fun s : ℂ => (1 / s) ^ (α : ℂ) * Complex.Gamma α) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
      (isOpen_lt continuous_const continuous_re)
    have hz' : 0 < z.re := hz
    have hz0 : z ≠ 0 := fun h => by rw [h] at hz'; simp at hz'
    have hslit : 1 / z ∈ slitPlane := by
      left
      rw [one_div, inv_re]
      exact div_pos hz' (normSq_pos.mpr hz0)
    exact ((((differentiableAt_id.inv hz0).congr_of_eventuallyEq
      (Eventually.of_forall fun w => by simp [one_div])).cpow_const hslit).mul_const
      _).differentiableWithinAt
  have hEq := (analyticOnNhd_integral_rpow_mul_cexp hα).eqOn_of_preconnected_of_frequently_eq hG
    (convex_halfSpace_re_gt 0).isPreconnected (show (1 : ℂ) ∈ U by simp [U]) ?_
  · exact hEq hs
  -- agreement on the positive reals
  have hreal : ∀ r : ℝ, 0 < r → ∫ t in Ioi 0, ((t ^ (α - 1) : ℝ) : ℂ) * cexp (-((r : ℂ) * t)) =
      (1 / (r : ℂ)) ^ (α : ℂ) * Complex.Gamma α := fun r hr => by
    rw [← integral_cpow_mul_exp_neg_mul_Ioi (by simpa using hα) hr]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [ofReal_cpow (le_of_lt ht)]
    push_cast
    rfl
  set u : ℕ → ℂ := fun n => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hu : Tendsto u atTop (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
      rw [add_zero] at h
      have h2 := (Complex.continuous_ofReal.tendsto 1).comp h
      rw [Complex.ofReal_one] at h2
      exact h2
    · simp only [u, mem_compl_iff, mem_singleton_iff]
      rw [← Complex.ofReal_one, Complex.ofReal_inj]
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  refine hu.frequently (Frequently.of_forall fun n => ?_)
  exact hreal _ (by positivity)

/-- `(i/x)^α = e^{iπα/2} x^{−α}` for `x > 0`. -/
theorem one_div_neg_I_mul_cpow {x : ℝ} (hx : 0 < x) (α : ℝ) :
    (1 / (-(I * x))) ^ (α : ℂ) = cexp (α * (Real.pi : ℂ) * I / 2) * ((x ^ (-α) : ℝ) : ℂ) := by
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have e : 1 / (-(I * x)) = I * ((x⁻¹ : ℝ) : ℂ) := by
    push_cast; field_simp; rw [I_sq]
  have hx' : 0 < x⁻¹ := inv_pos.mpr hx
  rw [e, cpow_def_of_ne_zero (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx'.ne')),
    log_mul_ofReal _ hx' _ I_ne_zero, log_I, Real.log_inv, Real.rpow_neg hx.le,
    Real.rpow_def_of_pos hx, ofReal_inv, ofReal_exp, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ### A smooth cutoff and the model integrals -/

/-- A smooth cutoff, `1` on `(−∞, 1]` and `0` on `[2, ∞)`. -/
noncomputable def spCutoff (t : ℝ) : ℝ := 1 - Real.smoothTransition (t - 1)

theorem spCutoff_contDiff : ContDiff ℝ ∞ spCutoff :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem spCutoff_eq_one {t : ℝ} (ht : t ≤ 1) : spCutoff t = 1 := by
  rw [spCutoff, Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

theorem spCutoff_eq_zero {t : ℝ} (ht : 2 ≤ t) : spCutoff t = 0 := by
  rw [spCutoff, Real.smoothTransition.one_of_one_le (by linarith), sub_self]

theorem spCutoff_nonneg (t : ℝ) : 0 ≤ spCutoff t :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

theorem spCutoff_le_one (t : ℝ) : spCutoff t ≤ 1 :=
  sub_le_self _ (Real.smoothTransition.nonneg _)

/-- The tail `t^{α−1}(1 − χ(t))`, smooth on `ℝ` and `0` on `(−∞, 1]`. -/
noncomputable def spTail (α : ℝ) (t : ℝ) : ℝ := t ^ (α - 1) * Real.smoothTransition (t - 1)

theorem spTail_eq_zero {α t : ℝ} (ht : t ≤ 1) : spTail α t = 0 := by
  rw [spTail, Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero]

theorem spTail_eq_rpow {α t : ℝ} (ht : 2 ≤ t) : spTail α t = t ^ (α - 1) := by
  rw [spTail, Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem spTail_contDiff (α : ℝ) : ContDiff ℝ ∞ (spTail α) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge t 1 with h | h
  · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with u hu
    exact spTail_eq_zero (le_of_lt hu)
  · exact (Real.contDiffAt_rpow_const_of_ne (by linarith)).mul
      (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt

theorem spTail_add (α t : ℝ) : t ^ (α - 1) * spCutoff t + spTail α t = t ^ (α - 1) := by
  rw [spCutoff, spTail]; ring

theorem iteratedDeriv_spTail_of_lt_one {α t : ℝ} (ht : t < 1) (k : ℕ) :
    iteratedDeriv k (spTail α) t = 0 := by
  have h : spTail α =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact spTail_eq_zero (le_of_lt hu)
  rw [h.iteratedDeriv_eq]
  rcases k with _ | k
  · simp
  · simp

theorem iteratedDeriv_rpow_real {r t : ℝ} (k : ℕ) :
    iteratedDeriv k (fun u : ℝ => u ^ r) t = (descPochhammer ℝ k).eval r * t ^ (r - k) := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]

theorem iteratedDeriv_spTail_of_gt_two {α t : ℝ} (ht : 2 < t) (k : ℕ) :
    iteratedDeriv k (spTail α) t = (descPochhammer ℝ k).eval (α - 1) * t ^ (α - 1 - k) := by
  have h : spTail α =ᶠ[𝓝 t] fun u => u ^ (α - 1) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact spTail_eq_rpow (le_of_lt hu)
  rw [h.iteratedDeriv_eq, iteratedDeriv_rpow_real]

/-- Polynomial growth of the derivatives of the tail. -/
theorem iteratedDeriv_spTail_bound (α : ℝ) (k : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ t, 0 ≤ t → ‖iteratedDeriv k (spTail α) t‖ ≤ B * (1 + t) ^ (Nat.ceil α) := by
  have hc : Continuous (iteratedDeriv k (spTail α)) :=
    (spTail_contDiff α).continuous_iteratedDeriv k (by exact_mod_cast le_top)
  obtain ⟨B₁, hB₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hc.continuousOn
  set D := |(descPochhammer ℝ k).eval (α - 1)|
  refine ⟨max B₁ D, le_max_of_le_right (abs_nonneg _), fun t ht => ?_⟩
  have h1 : (1 : ℝ) ≤ (1 + t) ^ (Nat.ceil α) := one_le_pow₀ (by linarith)
  rcases le_or_gt t 2 with h | h
  · calc _ ≤ B₁ := hB₁ t ⟨ht, h⟩
      _ ≤ max B₁ D * 1 := by rw [mul_one]; exact le_max_left _ _
      _ ≤ _ := by gcongr
  · rw [iteratedDeriv_spTail_of_gt_two h, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg
      (Real.rpow_nonneg ht _)]
    have h2 : t ^ (α - 1 - k) ≤ (1 + t) ^ (Nat.ceil α) := by
      calc t ^ (α - 1 - k) ≤ t ^ ((Nat.ceil α : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by
              have := Nat.le_ceil α; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
        _ = t ^ (Nat.ceil α) := Real.rpow_natCast _ _
        _ ≤ _ := pow_le_pow_left₀ ht (by linarith) _
    calc D * t ^ (α - 1 - k) ≤ max B₁ D * (1 + t) ^ (Nat.ceil α) :=
          mul_le_mul (le_max_right _ _) h2 (Real.rpow_nonneg ht _)
            (le_max_of_le_right (abs_nonneg _))
      _ = _ := rfl

theorem norm_cexp_neg_mul' (z : ℂ) (t : ℝ) : ‖cexp (-(z * t))‖ = Real.exp (-(z.re * t)) := by
  rw [Complex.norm_exp]; simp

theorem hasDerivAt_iteratedDeriv_spTail (α : ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (iteratedDeriv k (spTail α)) (iteratedDeriv (k + 1) (spTail α) t) t := by
  have hlt : ((k : ℕ) : WithTop ℕ∞) < ∞ := by exact_mod_cast ENat.natCast_lt_top k
  have h := ((spTail_contDiff α).differentiable_iteratedDeriv k hlt t).hasDerivAt
  rwa [← iteratedDeriv_succ] at h

/-- One integration by parts against `e^{−zt}`, `ℜz > 0`. -/
theorem spTail_ibp (α : ℝ) {z : ℂ} (hz : 0 < z.re) (k : ℕ) :
    ∫ t : ℝ in Ioi 0, cexp (-(z * t)) * ((iteratedDeriv k (spTail α) t : ℝ) : ℂ) =
      (1 / z) *
        ∫ t : ℝ in Ioi 0, cexp (-(z * t)) * ((iteratedDeriv (k + 1) (spTail α) t : ℝ) : ℂ) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  set m := Nat.ceil α
  obtain ⟨B, hB0, hB⟩ := iteratedDeriv_spTail_bound α k
  obtain ⟨B', hB0', hB'⟩ := iteratedDeriv_spTail_bound α (k + 1)
  have hint : ∀ j B, (∀ t, 0 ≤ t → ‖iteratedDeriv j (spTail α) t‖ ≤ B * (1 + t) ^ m) →
      IntegrableOn (fun t : ℝ => cexp (-(z * t)) * ((iteratedDeriv j (spTail α) t : ℝ) : ℂ))
        (Ioi 0) := fun j B hB => by
    have hc : Continuous (iteratedDeriv j (spTail α)) :=
      (spTail_contDiff α).continuous_iteratedDeriv j (by exact_mod_cast le_top)
    refine Integrable.mono' ((integrableOn_one_add_pow_mul_exp_neg m hz).const_mul B)
      ((by fun_prop : Continuous fun t : ℝ => cexp (-(z * t))).mul
        (continuous_ofReal.comp hc)).aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    rw [norm_mul, norm_cexp_neg_mul', Complex.norm_real]
    calc Real.exp (-(z.re * t)) * ‖iteratedDeriv j (spTail α) t‖ ≤
        Real.exp (-(z.re * t)) * (B * (1 + t) ^ m) := by gcongr; exact hB t (le_of_lt ht)
      _ = _ := by ring
  set v : ℝ → ℂ := fun t => -cexp (-(z * t)) / z with hvdef
  have hv : ∀ t : ℝ, HasDerivAt v (cexp (-(z * t))) t := fun t => by
    have h0 : HasDerivAt (fun y : ℝ => -(z * y)) (-z) t := by
      have h1 := ((hasDerivAt_id t).ofReal_comp.const_mul z).neg
      convert h1 using 1
      · ext y; simp
      · simp
    have h2 := h0.cexp.neg.div_const z
    convert h2 using 1
    field_simp
  have hu : ∀ t : ℝ, HasDerivAt (fun t => ((iteratedDeriv k (spTail α) t : ℝ) : ℂ))
      ((iteratedDeriv (k + 1) (spTail α) t : ℝ) : ℂ) t := fun t =>
    (hasDerivAt_iteratedDeriv_spTail α k t).ofReal_comp
  have huv' : IntegrableOn ((fun t => ((iteratedDeriv k (spTail α) t : ℝ) : ℂ)) *
      fun t : ℝ => cexp (-(z * t))) (Ioi 0) :=
    (hint k B hB).congr_fun (fun t _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi
  have hu'v : IntegrableOn ((fun t => ((iteratedDeriv (k + 1) (spTail α) t : ℝ) : ℂ)) * v)
      (Ioi 0) :=
    IntegrableOn.congr_fun ((hint (k + 1) B' hB').const_mul (-(1 / z)))
      (fun t _ => by simp only [Pi.mul_apply, hvdef]; ring) measurableSet_Ioi
  have hzero : Tendsto ((fun t => ((iteratedDeriv k (spTail α) t : ℝ) : ℂ)) * v) (𝓝[>] 0)
      (𝓝 0) := by
    have h := (((hu 0).continuousAt.mul (hv 0).continuousAt).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simp only [Pi.mul_apply] at h
    rwa [iteratedDeriv_spTail_of_lt_one zero_lt_one, ofReal_zero, zero_mul] at h
  have hinf : Tendsto ((fun t => ((iteratedDeriv k (spTail α) t : ℝ) : ℂ)) * v) atTop
      (𝓝 0) := by
    have h := (tendsto_one_add_pow_mul_exp_neg m hz).const_mul (B / ‖z‖)
    rw [mul_zero] at h
    refine squeeze_zero_norm' ?_ h
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [Pi.mul_apply, norm_mul, hvdef, norm_div, norm_neg, norm_cexp_neg_mul', Complex.norm_real]
    calc ‖iteratedDeriv k (spTail α) t‖ * (Real.exp (-(z.re * t)) / ‖z‖) ≤
        (B * (1 + t) ^ m) * (Real.exp (-(z.re * t)) / ‖z‖) := by gcongr; exact hB t ht
      _ = _ := by ring
  have key := integral_Ioi_mul_deriv_eq_deriv_mul (fun t _ => hu t) (fun t _ => hv t) huv'
    hu'v hzero hinf
  have e1 : ∫ t : ℝ in Ioi 0, cexp (-(z * t)) * ((iteratedDeriv k (spTail α) t : ℝ) : ℂ) =
      ∫ t in Ioi 0, ((iteratedDeriv k (spTail α) t : ℝ) : ℂ) * cexp (-(z * t)) := by
    simp_rw [mul_comm (cexp _)]
  rw [e1, key, sub_zero, zero_sub, hvdef, ← integral_const_mul, ← integral_neg]
  congr 1
  ext t
  ring

theorem spTail_ibp_iter (α : ℝ) {z : ℂ} (hz : 0 < z.re) (M : ℕ) :
    ∫ t : ℝ in Ioi 0, cexp (-(z * t)) * ((spTail α t : ℝ) : ℂ) =
      (1 / z) ^ M *
        ∫ t : ℝ in Ioi 0, cexp (-(z * t)) * ((iteratedDeriv M (spTail α) t : ℝ) : ℂ) := by
  induction M with
  | zero => simp
  | succ M ih => rw [ih, spTail_ibp α hz M, pow_succ]; ring

theorem integrableOn_norm_iteratedDeriv_spTail {α : ℝ} {M : ℕ} (hM : α < M) :
    IntegrableOn (fun t => ‖iteratedDeriv M (spTail α) t‖) (Ioi 0) := by
  have hc : Continuous (iteratedDeriv M (spTail α)) :=
    (spTail_contDiff α).continuous_iteratedDeriv M (by exact_mod_cast le_top)
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 2)]
  refine IntegrableOn.union ((hc.norm.continuousOn.integrableOn_Icc).mono_set
    Ioc_subset_Icc_self) ?_
  have h := (integrableOn_Ioi_rpow_of_lt (by linarith : α - 1 - M < -1)
    (by norm_num : (0 : ℝ) < 2)).const_mul |(descPochhammer ℝ M).eval (α - 1)|
  refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
  have ht' : (2 : ℝ) < t := ht
  rw [iteratedDeriv_spTail_of_gt_two ht', norm_mul, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]

theorem integrableOn_rpow_mul_spCutoff {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun t : ℝ => t ^ (α - 1) * spCutoff t) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 2)]
  refine IntegrableOn.union ?_ ?_
  · have h := (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < α - 1)
      (a := 0) (b := 2))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h
    refine Integrable.mono' h ((measurable_id.pow_const _).mul
      spCutoff_contDiff.continuous.measurable).aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _)
      (spCutoff_nonneg t))]
    exact mul_le_of_le_one_right (Real.rpow_nonneg ht0.le _) (spCutoff_le_one t)
  · refine (integrableOn_zero).congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht' : (2 : ℝ) < t := ht
    simp [spCutoff_eq_zero ht'.le]

/-- The model integral: `∫₀^∞ e^{ixt} t^{α−1} χ(t) dt = e^{iπα/2} Γ(α) x^{−α} + O(x^{−M})` for
every `M > α`. -/
theorem fourier_cutoff_model {α : ℝ} (hα : 0 < α) {M : ℕ} (hM : α < M) :
    ∃ C, ∀ x : ℝ, 0 < x →
      ‖(∫ t : ℝ in Ioi 0, cexp (I * x * t) * ((t ^ (α - 1) * spCutoff t : ℝ) : ℂ)) -
        cexp (α * (Real.pi : ℂ) * I / 2) * Complex.Gamma α * ((x ^ (-α) : ℝ) : ℂ)‖ ≤
        C * x ^ (-(M : ℝ)) := by
  set GM := ∫ t in Ioi 0, ‖iteratedDeriv M (spTail α) t‖
  refine ⟨GM, fun x hx => ?_⟩
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  set z : ℝ → ℂ := fun ε => (ε : ℂ) - I * x with hzdef
  have hzre : ∀ ε, (z ε).re = ε := fun ε => by simp [hzdef]
  set A : ℝ → ℂ := fun ε => ∫ t : ℝ in Ioi 0, cexp (-(z ε * t)) *
    ((t ^ (α - 1) * spCutoff t : ℝ) : ℂ) with hAdef
  set T : ℝ → ℂ := fun ε => ∫ t : ℝ in Ioi 0, cexp (-(z ε * t)) * ((spTail α t : ℝ) : ℂ)
    with hTdef
  have hbd := integrableOn_rpow_mul_spCutoff hα
  have hAint : ∀ ε, 0 ≤ ε → IntegrableOn (fun t : ℝ => cexp (-(z ε * t)) *
      ((t ^ (α - 1) * spCutoff t : ℝ) : ℂ)) (Ioi 0) := fun ε hε => by
    refine Integrable.mono' hbd ((by fun_prop : Continuous fun t : ℝ =>
      cexp (-(z ε * t))).measurable.mul (continuous_ofReal.measurable.comp
        ((measurable_id.pow_const _).mul
          spCutoff_contDiff.continuous.measurable))).aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    have ht0 : 0 < t := ht
    rw [norm_mul, norm_cexp_neg_mul', hzre, Complex.norm_real, Real.norm_of_nonneg
      (mul_nonneg (Real.rpow_nonneg ht0.le _) (spCutoff_nonneg t))]
    exact mul_le_of_le_one_left (mul_nonneg (Real.rpow_nonneg ht0.le _) (spCutoff_nonneg t))
      (Real.exp_le_one_iff.mpr (by nlinarith))
  -- `A + T = Γ(α) z^{−α}`
  have hsplit : ∀ ε, 0 < ε → A ε + T ε = (1 / z ε) ^ (α : ℂ) * Complex.Gamma α := fun ε hε => by
    have hfull := integrableOn_rpow_mul_cexp_neg hα (s := z ε) (by rw [hzre]; exact hε)
    have hTint : IntegrableOn (fun t : ℝ => cexp (-(z ε * t)) * ((spTail α t : ℝ) : ℂ))
        (Ioi 0) := by
      refine (hfull.sub (hAint ε hε.le)).congr_fun (fun t _ => ?_) measurableSet_Ioi
      have hs : spTail α t = t ^ (α - 1) - t ^ (α - 1) * spCutoff t := by
        linarith [spTail_add α t]
      simp only [Pi.sub_apply]
      rw [hs]
      push_cast
      ring
    rw [← integral_rpow_mul_cexp_neg_complex hα (by rw [hzre]; exact hε), hAdef, hTdef,
      ← integral_add (hAint ε hε.le) hTint]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have hs : spTail α t = t ^ (α - 1) - t ^ (α - 1) * spCutoff t := by
      linarith [spTail_add α t]
    rw [hs]
    push_cast
    ring
  -- the bound on `T`
  have hT : ∀ ε, 0 < ε → ‖T ε‖ ≤ GM * x ^ (-(M : ℝ)) := fun ε hε => by
    have hzr : 0 < (z ε).re := by rw [hzre]; exact hε
    rw [hTdef]
    simp only
    rw [spTail_ibp_iter α hzr M, norm_mul, norm_pow, norm_div, norm_one, mul_comm]
    have hz : x ≤ ‖z ε‖ := by
      have := abs_im_le_norm (z ε)
      simp only [hzdef, sub_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_mul, one_mul,
        zero_sub, zero_add, abs_neg, abs_of_pos hx] at this
      exact this
    have hpow : (1 / ‖z ε‖) ^ M ≤ x ^ (-(M : ℝ)) := by
      rw [Real.rpow_neg hx.le, Real.rpow_natCast, ← one_div, one_div_pow]
      exact one_div_le_one_div_of_le (pow_pos hx M) (pow_le_pow_left₀ hx.le hz M)
    refine mul_le_mul ?_ hpow (by positivity) (integral_nonneg fun _ => norm_nonneg _)
    refine norm_integral_le_of_norm_le (integrableOn_norm_iteratedDeriv_spTail hM)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    rw [norm_mul, norm_cexp_neg_mul', hzre, Complex.norm_real]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (Real.exp_le_one_iff.mpr (by have : (0 : ℝ) < t := ht; nlinarith))
  -- the limits as `ε → 0+`
  have hA : Tendsto A (𝓝[>] 0) (𝓝 (∫ t : ℝ in Ioi 0, cexp (I * x * t) *
      ((t ^ (α - 1) * spCutoff t : ℝ) : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => t ^ (α - 1) * spCutoff t)
      ?_ ?_ hbd ?_
    · exact Eventually.of_forall fun ε => ((by fun_prop : Continuous fun t : ℝ =>
        cexp (-(z ε * t))).measurable.mul (continuous_ofReal.measurable.comp
          ((measurable_id.pow_const _).mul
            spCutoff_contDiff.continuous.measurable))).aestronglyMeasurable.restrict
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := ht
      have hε' : (0 : ℝ) < ε := hε
      rw [norm_mul, norm_cexp_neg_mul', hzre, Complex.norm_real, Real.norm_of_nonneg
        (mul_nonneg (Real.rpow_nonneg ht0.le _) (spCutoff_nonneg t))]
      exact mul_le_of_le_one_left (mul_nonneg (Real.rpow_nonneg ht0.le _) (spCutoff_nonneg t))
        (Real.exp_le_one_iff.mpr (by nlinarith))
    · refine Eventually.of_forall fun t => ?_
      have hc : Continuous fun ε : ℝ => cexp (-(z ε * t)) * ((t ^ (α - 1) * spCutoff t : ℝ) : ℂ) :=
        by rw [hzdef]; fun_prop
      have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      convert h using 2
      simp only [hzdef, ofReal_zero, zero_sub]
      ring_nf
  have hslit : 1 / (-(I * (x : ℂ))) ∈ slitPlane := by
    right
    have : 1 / (-(I * (x : ℂ))) = I * ((x⁻¹ : ℝ) : ℂ) := by
      push_cast; field_simp; rw [I_sq]
    rw [this]
    simp [hx.ne']
  have hG : Tendsto (fun ε => (1 / z ε) ^ (α : ℂ) * Complex.Gamma α) (𝓝[>] 0)
      (𝓝 ((1 / (-(I * (x : ℂ)))) ^ (α : ℂ) * Complex.Gamma α)) := by
    have hz0 : z 0 = -(I * x) := by simp [hzdef]
    have hc : ContinuousAt (fun ε => 1 / z ε) 0 := by
      refine (continuousAt_const.div (by rw [hzdef]; fun_prop) ?_)
      rw [hz0]; exact neg_ne_zero.mpr (mul_ne_zero I_ne_zero hxc)
    have h1 : ContinuousAt (fun ε => (1 / z ε) ^ (α : ℂ)) 0 := by
      have h2 := continuousAt_cpow_const (b := (α : ℂ)) (show 1 / z 0 ∈ slitPlane by
        rw [hz0]; exact hslit)
      exact h2.comp (f := fun ε => 1 / z ε) hc
    have h3 := ((h1.mul (continuousAt_const (y := Complex.Gamma α))).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simp only [Pi.mul_apply, hz0] at h3
    exact h3
  have hlim : Tendsto T (𝓝[>] 0) (𝓝 ((1 / (-(I * (x : ℂ)))) ^ (α : ℂ) * Complex.Gamma α -
      ∫ t : ℝ in Ioi 0, cexp (I * x * t) * ((t ^ (α - 1) * spCutoff t : ℝ) : ℂ))) := by
    refine (hG.sub hA).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← hsplit ε hε]
    ring
  have hle := le_of_tendsto hlim.norm (by
    filter_upwards [self_mem_nhdsWithin] with ε hε using hT ε hε)
  rw [norm_sub_rev, one_div_neg_I_mul_cpow hx] at hle
  calc _ = ‖(∫ t : ℝ in Ioi 0, cexp (I * x * t) * ((t ^ (α - 1) * spCutoff t : ℝ) : ℂ)) -
        cexp (α * (Real.pi : ℂ) * I / 2) * ((x ^ (-α) : ℝ) : ℂ) * Complex.Gamma α‖ := by
        ring_nf
    _ ≤ _ := hle

/-! ### The remainder near `0` -/

theorem intervalIntegrable_exp_mul_of_contDiffOn {R : ℝ → ℂ} (hR : ContDiffOn ℝ ∞ R (Ioi 0))
    (k : ℕ) (x : ℝ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (fun t => cexp (I * x * t) * iteratedDeriv k R t) volume u v := by
  refine ContinuousOn.intervalIntegrable ?_
  refine ((by fun_prop : Continuous fun t : ℝ => cexp (I * x * t)).continuousOn).mul ?_
  refine (continuousOn_iteratedDeriv_of_contDiffOn isOpen_Ioi hR k).mono fun t ht => ?_
  rcases le_total u v with h | h
  · rw [uIcc_of_le h] at ht; exact hu.trans_le ht.1
  · rw [uIcc_of_ge h] at ht; exact hv.trans_le ht.1

/-- Moving the base point of a uniformly convergent improper integral. -/
theorem tendstoUniformlyOn_base_change {R : ℝ → ℂ} (hR : ContDiffOn ℝ ∞ R (Ioi 0)) {k : ℕ}
    {X₀ : ℝ} {g : ℝ → ℂ}
    (hg : TendstoUniformlyOn (fun T (x : ℝ) => ∫ t in (1 : ℝ)..T,
      cexp (I * x * t) * iteratedDeriv k R t) g atTop (Ici X₀)) {δ : ℝ} (hδ : 0 < δ) :
    TendstoUniformlyOn (fun T (x : ℝ) => ∫ t in δ..T, cexp (I * x * t) * iteratedDeriv k R t)
      (fun x => (∫ t in δ..1, cexp (I * x * t) * iteratedDeriv k R t) + g x) atTop
      (Ici X₀) := by
  rw [Metric.tendstoUniformlyOn_iff] at hg ⊢
  intro ε hε
  filter_upwards [hg ε hε, eventually_ge_atTop 1] with T hT hT1 x hx
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_exp_mul_of_contDiffOn hR k x hδ one_pos)
    (intervalIntegrable_exp_mul_of_contDiffOn hR k x (u := 1) (v := T) one_pos (by linarith)),
    dist_add_left]
  exact hT x hx

/-- **The remainder estimate**: if `|R⁽ᵏ⁾(t)| ≤ C t^{β−1−k}` on `(0, b]` for `k ≤ K`, `K > β`,
and each `∫ e^{ixt} R⁽ˢ⁾` converges at `∞` uniformly for large `x`, then
`∫₀^∞ e^{ixt} R(t) dt = O(x^{−β})`. -/
theorem fourier_remainder {R : ℝ → ℂ} {β : ℝ} (hβ : 0 < β) {K : ℕ} (hK : β < K)
    (hR : ContDiffOn ℝ ∞ R (Ioi 0)) {b C : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hbd : ∀ k ≤ K, ∀ t ∈ Ioc 0 b, ‖iteratedDeriv k R t‖ ≤ C * t ^ (β - 1 - k))
    (hunif : ∀ s, ∃ X₀ : ℝ, ∃ g : ℝ → ℂ, TendstoUniformlyOn (fun T (x : ℝ) =>
      ∫ t in (1 : ℝ)..T, cexp (I * x * t) * iteratedDeriv s R t) g atTop (Ici X₀)) :
    ∃ X C', ∀ x, X ≤ x → ‖fourierIoiIntegral R 0 x‖ ≤ C' * x ^ (-β) := by
  choose X₀ g hg using hunif
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hbd 0 (Nat.zero_le _) b ⟨hb, le_rfl⟩)
    exact (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hb _)).mp h
  obtain ⟨BK, hBK⟩ := fourierIoi_bounded (q := R) (a := 1) hg K
  set J := ∫ t in b..1, ‖iteratedDeriv K R t‖
  have hJ : 0 ≤ J := intervalIntegral.integral_nonneg hb1 fun _ _ => norm_nonneg _
  set X := 1 / b + ∑ s ∈ Finset.range (K + 1), |X₀ s| + 1
  have hsum0 : 0 ≤ ∑ s ∈ Finset.range (K + 1), |X₀ s| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hXs : ∀ s ≤ K, X₀ s ≤ X := fun s hs => by
    have h1 : |X₀ s| ≤ ∑ s ∈ Finset.range (K + 1), |X₀ s| :=
      Finset.single_le_sum (f := fun s => |X₀ s|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega))
    have := le_abs_self (X₀ s)
    have : 0 ≤ 1 / b := by positivity
    linarith
  have hBK0 : 0 ≤ BK := (norm_nonneg _).trans (hBK X (hXs K le_rfl))
  refine ⟨X, C / β + K * C + C / (K - β) + J + BK, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := by
    have : 0 < 1 / b := by positivity
    linarith
  have hx0 : 0 < x := by linarith
  have hxb : 1 / b ≤ x := by linarith
  set δ := 1 / x with hδdef
  have hδ : 0 < δ := by positivity
  have hδb : δ ≤ b := by
    rw [hδdef, div_le_iff₀ hx0]
    have := (div_le_iff₀ hb).mp hxb
    linarith
  have hδ1 : δ ≤ 1 := hδb.trans hb1
  have hpow : ∀ r : ℝ, δ ^ r = x ^ (-r) := fun r => by
    rw [hδdef, one_div, Real.inv_rpow hx0.le, Real.rpow_neg hx0.le]
  -- the half-line expansion from `δ`
  have hgδ := fun s => tendstoUniformlyOn_base_change hR (hg s) hδ
  have hiter := fourierIoi_iter isOpen_Ioi (fun t ht => hδ.trans_le ht) hR hgδ K hx0
    fun s hs => (hXs s hs).trans hx
  -- the value of the improper integral
  have hint0 : IntervalIntegrable R volume 0 δ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le]
    have hp := (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < β - 1)
      (a := 0) (b := δ)).const_mul C
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le] at hp
    refine Integrable.mono' hp (((continuousOn_iteratedDeriv_of_contDiffOn isOpen_Ioi hR 0).mono
      fun t ht => ht.1).aestronglyMeasurable measurableSet_Ioc |>.congr ?_)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
    · exact Eventually.of_forall fun t => by simp
    · have h := hbd 0 (Nat.zero_le _) t ⟨ht.1, ht.2.trans hδb⟩
      simpa using h
  have hval : fourierIoiIntegral R 0 x = (∫ t in (0 : ℝ)..δ, cexp (I * x * t) * R t) +
      (fun y : ℝ => (∫ t in δ..1, cexp (I * y * t) * iteratedDeriv 0 R t) + g 0 y) x := by
    have h := ((hgδ 0).tendsto_at (show x ∈ Ici (X₀ 0) from (hXs 0 (Nat.zero_le _)).trans hx))
    have h2 : Tendsto (fun T => ∫ t in (0 : ℝ)..T, cexp (I * x * t) * R t) atTop
        (𝓝 ((∫ t in (0 : ℝ)..δ, cexp (I * x * t) * R t) +
          (fun y : ℝ => (∫ t in δ..1, cexp (I * y * t) * iteratedDeriv 0 R t) + g 0 y) x)) := by
      refine (h.const_add _).congr' ?_
      filter_upwards [eventually_ge_atTop δ] with T hT
      simp only [iteratedDeriv_zero]
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hint0.continuousOn_mul (by fun_prop))
        (by simpa using intervalIntegrable_exp_mul_of_contDiffOn hR 0 x hδ (hδ.trans_le hT))]
    exact h2.limUnder_eq
  rw [hval]
  beta_reduce
  rw [hiter]
  -- the three bounds
  have hA : ‖∫ t in (0 : ℝ)..δ, cexp (I * x * t) * R t‖ ≤ C / β * x ^ (-β) := by
    calc _ ≤ ∫ t in (0 : ℝ)..δ, C * t ^ (β - 1) := by
          refine intervalIntegral.norm_integral_le_of_norm_le hδ.le
            (ae_of_all _ fun t ht => ?_) (intervalIntegral.intervalIntegrable_rpow'
              (by linarith) |>.const_mul C)
          rw [norm_mul, show I * (x : ℂ) * t = ((x * t : ℝ) : ℂ) * I by push_cast; ring,
            norm_exp_ofReal_mul_I, one_mul]
          have h := hbd 0 (Nat.zero_le _) t ⟨ht.1, ht.2.trans hδb⟩
          simpa using h
      _ = C / β * x ^ (-β) := by
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
            sub_add_cancel, Real.zero_rpow hβ.ne', sub_zero, hpow]
          ring
  have hB : ∀ s < K, ‖fourierTermIoi R δ s x‖ ≤ C * x ^ (-β) := fun s hs => by
    rw [fourierTermIoi, norm_mul, norm_mul, norm_pow, norm_div, norm_I, Complex.norm_real,
      Real.norm_of_nonneg hx0.le, show I * (δ : ℂ) * x = ((δ * x : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, one_mul]
    have h := hbd s hs.le δ ⟨hδ, hδb⟩
    rw [hpow] at h
    calc (1 / x) ^ (s + 1) * ‖iteratedDeriv s R δ‖ ≤ (1 / x) ^ (s + 1) *
          (C * x ^ (-(β - 1 - s))) := by gcongr
      _ = C * x ^ (-β) := by
          rw [one_div_pow, ← Real.rpow_natCast, one_div, ← Real.rpow_neg hx0.le, mul_left_comm,
            ← Real.rpow_add hx0]
          congr 2
          push_cast
          ring
  have hgK : ‖(∫ t in δ..1, cexp (I * x * t) * iteratedDeriv K R t) + g K x‖ ≤
      C / (K - β) * x ^ (K - β) + J + BK := by
    refine (norm_add_le _ _).trans (add_le_add ?_ (hBK x ((hXs K le_rfl).trans hx)))
    refine (norm_integral_exp_mul_le hδ1).trans ?_
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := b)
      ((continuousOn_iteratedDeriv_of_contDiffOn isOpen_Ioi hR K).norm.mono (fun t ht => by
        rw [uIcc_of_le hδb] at ht; exact hδ.trans_le ht.1) |>.intervalIntegrable)
      ((continuousOn_iteratedDeriv_of_contDiffOn isOpen_Ioi hR K).norm.mono (fun t ht => by
        rw [uIcc_of_le hb1] at ht; exact hb.trans_le ht.1) |>.intervalIntegrable)]
    refine add_le_add ?_ le_rfl
    calc _ ≤ ∫ t in δ..b, C * t ^ (β - 1 - K) := by
          refine intervalIntegral.integral_mono_on hδb
            ((continuousOn_iteratedDeriv_of_contDiffOn isOpen_Ioi hR K).norm.mono (fun t ht => by
              rw [uIcc_of_le hδb] at ht; exact hδ.trans_le ht.1) |>.intervalIntegrable)
            ((intervalIntegral.intervalIntegrable_rpow (Or.inr (by
              rw [uIcc_of_le hδb]; exact fun h => absurd h.1 (not_le.mpr hδ)))).const_mul C)
            fun t ht => hbd K le_rfl t ⟨hδ.trans_le ht.1, ht.2⟩
      _ = C * ((b ^ (β - K) - δ ^ (β - K)) / (β - K)) := by
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, by
            rw [uIcc_of_le hδb]; exact fun h => absurd h.1 (not_le.mpr hδ)⟩)]
          congr 2 <;> ring_nf
      _ ≤ C / (K - β) * x ^ (K - β) := by
          rw [hpow, show -(β - K) = K - β by ring]
          have hKβ : 0 < K - β := by linarith
          have hb0 : 0 ≤ b ^ (β - K) := Real.rpow_nonneg hb.le _
          rw [show b ^ (β - K) - x ^ (K - β) = -(x ^ (K - β) - b ^ (β - K)) by ring,
            show β - (K : ℝ) = -(K - β) by ring, neg_div_neg_eq]
          rw [div_mul_eq_mul_div, mul_div_assoc]
          gcongr
          have := Real.rpow_nonneg hb.le (-((K : ℝ) - β))
          linarith
  -- assemble
  have hxK : ‖(I / (x : ℂ)) ^ K‖ = x ^ (-(K : ℝ)) := by
    rw [norm_pow, norm_div, norm_I, Complex.norm_real, Real.norm_of_nonneg hx0.le,
      Real.rpow_neg hx0.le, Real.rpow_natCast, one_div_pow, one_div]
  have hxKβ : x ^ (-(K : ℝ)) ≤ x ^ (-β) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hxK' : x ^ (-(K : ℝ)) * x ^ (K - β) = x ^ (-β) := by
    rw [← Real.rpow_add hx0]; ring_nf
  calc _ ≤ ‖∫ t in (0 : ℝ)..δ, cexp (I * x * t) * R t‖ +
        (∑ s ∈ Finset.range K, ‖fourierTermIoi R δ s x‖ +
          ‖(I / (x : ℂ)) ^ K‖ *
            ‖(∫ t in δ..1, cexp (I * x * t) * iteratedDeriv K R t) + g K x‖) := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_add_le _ _).trans
          (add_le_add (norm_sum_le _ _) (norm_mul _ _).le)))
    _ ≤ C / β * x ^ (-β) + (∑ s ∈ Finset.range K, C * x ^ (-β) +
          x ^ (-(K : ℝ)) * (C / (K - β) * x ^ (K - β) + J + BK)) := by
        rw [hxK]
        gcongr with s hs
        · exact hB s (Finset.mem_range.mp hs)
    _ ≤ C / β * x ^ (-β) + (K * (C * x ^ (-β)) +
          (C / (K - β) * x ^ (-β) + (J + BK) * x ^ (-β))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        gcongr
        calc x ^ (-(K : ℝ)) * (C / (K - β) * x ^ (K - β) + J + BK) =
            C / (K - β) * (x ^ (-(K : ℝ)) * x ^ (K - β)) + x ^ (-(K : ℝ)) * (J + BK) := by ring
          _ ≤ _ := by
            rw [hxK', mul_comm (x ^ (-(K : ℝ)))]
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hxKβ (by linarith))
    _ = _ := by ring

/-! ### Derivatives of power sums -/

/-- The `k`-th derivative of `∑ cₛ tʳˢ` (`t > 0`). -/
noncomputable def powSumDeriv (F : Finset ℕ) (c : ℕ → ℂ) (r : ℕ → ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  ∑ s ∈ F, c s * (((descPochhammer ℝ k).eval (r s) : ℝ) : ℂ) * ((t ^ (r s - k) : ℝ) : ℂ)

theorem hasDerivAt_powSumDeriv (F : Finset ℕ) (c : ℕ → ℂ) (r : ℕ → ℝ) (k : ℕ) {t : ℝ}
    (ht : 0 < t) : HasDerivAt (powSumDeriv F c r k) (powSumDeriv F c r (k + 1) t) t := by
  unfold powSumDeriv
  refine HasDerivAt.fun_sum fun s _ => ?_
  have h := ((Real.hasDerivAt_rpow_const (p := r s - k) (Or.inl ht.ne')).ofReal_comp).const_mul
    (c s * (((descPochhammer ℝ k).eval (r s) : ℝ) : ℂ))
  convert h using 1
  rw [descPochhammer_succ_eval]
  push_cast
  ring_nf

theorem iteratedDeriv_sub_powSum {q : ℝ → ℂ} (hq : ContDiffOn ℝ ∞ q (Ioi 0)) (F : Finset ℕ)
    (c : ℕ → ℂ) (r : ℕ → ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv k (fun u => q u - powSumDeriv F c r 0 u) t =
      iteratedDeriv k q t - powSumDeriv F c r k t := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    have hev : iteratedDeriv k (fun u => q u - powSumDeriv F c r 0 u) =ᶠ[𝓝 t]
        fun u => iteratedDeriv k q u - powSumDeriv F c r k u := by
      filter_upwards [Ioi_mem_nhds ht] with u hu using ih hu
    rw [iteratedDeriv_succ, hev.deriv_eq]
    exact ((hasDerivAt_iteratedDeriv_of_contDiffOn isOpen_Ioi hq k ht).sub
      (hasDerivAt_powSumDeriv F c r k ht)).deriv

/-! ### Watson's lemma for Fourier integrals (2.3.20) -/

theorem intervalIntegrable_exp_mul_of_bound {g : ℝ → ℂ} (hg : ContinuousOn g (Ioi 0))
    {b₀ C e : ℝ} (hb₀ : 0 < b₀) (he : -1 < e) (hbd : ∀ t ∈ Ioc 0 b₀, ‖g t‖ ≤ C * t ^ e)
    (x : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => cexp (I * x * t) * g t) volume 0 T := by
  have h0 : IntervalIntegrable g volume 0 b₀ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb₀.le]
    have hp := (intervalIntegral.intervalIntegrable_rpow' he (a := 0) (b := b₀)).const_mul C
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb₀.le] at hp
    exact Integrable.mono' hp ((hg.mono fun t ht => ht.1).aestronglyMeasurable measurableSet_Ioc)
      (ae_restrict_of_forall_mem measurableSet_Ioc hbd)
  have h1 : IntervalIntegrable g volume 0 T := by
    rcases le_or_gt b₀ T with h | h
    · refine h0.trans (hg.mono fun t ht => ?_).intervalIntegrable
      rw [uIcc_of_le h] at ht; exact hb₀.trans_le ht.1
    · exact h0.mono_set (by rw [uIcc_of_le hT, uIcc_of_le hb₀.le]; exact Icc_subset_Icc_right h.le)
  exact h1.continuousOn_mul (by fun_prop)

/-- **DLMF 2.3.20**: if `q` is infinitely differentiable on `(0, ∞)`, has the expansion 2.3.7
(`q(t) ∼ ∑ aₛ t^{(s+λ−μ)/μ}` as `t → 0+`), and this expansion is infinitely differentiable
(`q⁽ᵏ⁾` has the termwise differentiated expansion), and each `∫ e^{ixt} q⁽ˢ⁾(t) dt` converges at
`∞` uniformly for large `x`, then
`∫₀^∞ e^{ixt} q(t) dt ∼ ∑ e^{(s+λ)πi/(2μ)} Γ((s+λ)/μ) aₛ x^{−(s+λ)/μ}` as `x → +∞`. -/
theorem dlmf_2_3_20 {q : ℝ → ℂ} {a : ℕ → ℂ} {lam μ : ℝ} (hlam : 0 < lam) (hμ : 0 < μ)
    (hq : ContDiffOn ℝ ∞ q (Ioi 0))
    (hexp : ∀ k : ℕ, IsGenAsympExpansionDLMF (𝓝[>] 0)
      (fun s t => ((t ^ (((s : ℝ) + lam - μ) / μ - k) : ℝ) : ℂ)) (iteratedDeriv k q)
      (fun s t => a s * (((descPochhammer ℝ k).eval (((s : ℝ) + lam - μ) / μ) : ℝ) : ℂ) *
        ((t ^ (((s : ℝ) + lam - μ) / μ - k) : ℝ) : ℂ)))
    (hunif : ∀ s, ∃ X₀ : ℝ, ∃ g : ℝ → ℂ, TendstoUniformlyOn (fun T (x : ℝ) =>
      ∫ t in (1 : ℝ)..T, cexp (I * x * t) * iteratedDeriv s q t) g atTop (Ici X₀)) :
    IsGenAsympExpansionDLMF atTop (fun s x => ((x ^ (-watsonExp lam μ s) : ℝ) : ℂ))
      (fourierIoiIntegral q 0)
      (fun s x => cexp ((((s : ℝ) + lam) * Real.pi / (2 * μ) : ℝ) * I) *
        (Real.Gamma (watsonExp lam μ s) : ℂ) * a s * ((x ^ (-watsonExp lam μ s) : ℝ) : ℂ)) := by
  set α := watsonExp lam μ with hαdef
  have hαp := watsonExp_pos hlam hμ
  refine ⟨?_, fun n => ?_⟩
  · simpa only [mul_one] using isAsympScale_rpow_neg_mul (one_div_pos.mpr hμ)
      (watsonExp_succ (lam := lam) hμ) (w := fun _ => (1 : ℂ))
      (Eventually.of_forall fun _ => one_ne_zero)
  set r : ℕ → ℝ := fun s => α s - 1 with hrdef
  set K := Nat.ceil (α n) + 1 with hKdef
  have hK : α n < K := by
    have := Nat.le_ceil (α n); rw [hKdef]; push_cast; linarith
  -- bounds from the differentiated expansions
  have hbk : ∀ k : ℕ, ∃ b C, 0 < b ∧ b ≤ 1 ∧ ∀ t ∈ Ioc 0 b,
      ‖iteratedDeriv k q t - powSumDeriv (Finset.range n) a r k t‖ ≤
        C * t ^ (α n - 1 - k) := fun k => by
    obtain ⟨b, C, hb, hb1, h⟩ := exists_bound_of_isBigODLMF_nhdsGT ((hexp k).2 n)
      (fun t ht => ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht _).ne') zero_lt_one
    refine ⟨b, C, hb, hb1, fun t ht => ?_⟩
    have h1 := h t ht
    simp only [watsonExp_sub_one hμ, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)] at h1
    exact h1
  choose bf Cf hbf hbf1 hbfb using hbk
  set b := min ((Finset.range (K + 1)).inf' ⟨0, by simp⟩ bf) (1 / 2) with hbdef
  have hb : 0 < b := lt_min ((Finset.lt_inf'_iff _).mpr fun k _ => hbf k) (by norm_num)
  have hbk' : ∀ k ≤ K, b ≤ bf k := fun k hk =>
    (min_le_left _ _).trans (Finset.inf'_le _ (Finset.mem_range.mpr (by omega)))
  have hb2 : b ≤ 1 / 2 := min_le_right _ _
  set C := ∑ k ∈ Finset.range (K + 1), |Cf k|
  have hCk : ∀ k ≤ K, Cf k ≤ C := fun k hk =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun k => |Cf k|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega)))
  -- the models and the remainder
  set m : ℕ → ℝ → ℂ := fun s t => ((t ^ (r s) * spCutoff t : ℝ) : ℂ) with hmdef
  set R : ℝ → ℂ := fun t => q t - ∑ s ∈ Finset.range n, a s * m s t with hRdef
  have hmc : ∀ s, ContDiffOn ℝ ∞ (m s) (Ioi 0) := fun s =>
    ofRealCLM.contDiff.comp_contDiffOn (fun t ht =>
      ((Real.contDiffAt_rpow_const_of_ne (ne_of_gt ht)).mul
        spCutoff_contDiff.contDiffAt).contDiffWithinAt)
  have hR : ContDiffOn ℝ ∞ R (Ioi 0) :=
    hq.sub (ContDiffOn.sum fun s _ => contDiffOn_const.mul (hmc s))
  have hRnear : ∀ t, 0 < t → t < 1 →
      R =ᶠ[𝓝 t] fun u => q u - powSumDeriv (Finset.range n) a r 0 u := fun t _ ht1 => by
    filter_upwards [Iio_mem_nhds ht1] with u hu
    simp only [hRdef, hmdef, powSumDeriv, spCutoff_eq_one (le_of_lt hu)]
    simp
  have hbd : ∀ k ≤ K, ∀ t ∈ Ioc 0 b, ‖iteratedDeriv k R t‖ ≤ C * t ^ (α n - 1 - k) := by
    intro k hk t ht
    have ht1 : t < 1 := by linarith [ht.2]
    rw [(hRnear t ht.1 ht1).iteratedDeriv_eq, iteratedDeriv_sub_powSum hq _ a r k ht.1]
    refine (hbfb k t ⟨ht.1, ht.2.trans (hbk' k hk)⟩).trans ?_
    exact mul_le_mul_of_nonneg_right (hCk k hk) (Real.rpow_nonneg ht.1.le _)
  have hfar : ∀ k t, 2 < t → iteratedDeriv k R t = iteratedDeriv k q t := fun k t ht => by
    refine Filter.EventuallyEq.iteratedDeriv_eq k ?_
    filter_upwards [Ioi_mem_nhds ht] with u hu
    simp [hRdef, hmdef, spCutoff_eq_zero (le_of_lt hu)]
  have hunifR : ∀ s, ∃ X₀ : ℝ, ∃ g : ℝ → ℂ, TendstoUniformlyOn (fun T (x : ℝ) =>
      ∫ t in (1 : ℝ)..T, cexp (I * x * t) * iteratedDeriv s R t) g atTop (Ici X₀) := by
    intro s
    obtain ⟨X₀, g, hg⟩ := hunif s
    refine ⟨X₀, fun x => (∫ t in (1 : ℝ)..3, cexp (I * x * t) * iteratedDeriv s R t) -
      (∫ t in (1 : ℝ)..3, cexp (I * x * t) * iteratedDeriv s q t) + g x, ?_⟩
    rw [Metric.tendstoUniformlyOn_iff] at hg ⊢
    intro ε hε
    filter_upwards [hg ε hε, eventually_ge_atTop 3] with T hT hT3 x hx
    have e1 := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_exp_mul_of_contDiffOn hR s x (u := 1) (v := 3) one_pos (by norm_num))
      (intervalIntegrable_exp_mul_of_contDiffOn hR s x (u := 3) (v := T) (by norm_num)
        (by linarith))
    have e2 := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_exp_mul_of_contDiffOn hq s x (u := 1) (v := 3) one_pos (by norm_num))
      (intervalIntegrable_exp_mul_of_contDiffOn hq s x (u := 3) (v := T) (by norm_num)
        (by linarith))
    have e3 : ∫ t in (3 : ℝ)..T, cexp (I * x * t) * iteratedDeriv s R t =
        ∫ t in (3 : ℝ)..T, cexp (I * x * t) * iteratedDeriv s q t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hT3] at ht
      rw [hfar s t (by linarith [ht.1])]
    show dist ((∫ t in (1 : ℝ)..3, cexp (I * x * t) * iteratedDeriv s R t) -
      (∫ t in (1 : ℝ)..3, cexp (I * x * t) * iteratedDeriv s q t) + g x)
      (∫ t in (1 : ℝ)..T, cexp (I * x * t) * iteratedDeriv s R t) < ε
    have h := hT x hx
    rw [← e2] at h
    rw [← e1, e3]
    convert h using 1
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    ring
  obtain ⟨XR, CR, hRem⟩ := fourier_remainder (hαp n) hK hR hb (hb2.trans (by norm_num)) hbd
    hunifR
  -- the models
  have hmod : ∀ s, ∃ Cm : ℝ, s < n → ∀ x : ℝ, 0 < x →
      ‖(∫ t : ℝ in Ioi 0, cexp (I * x * t) * m s t) -
        cexp (α s * (Real.pi : ℂ) * I / 2) * Complex.Gamma (α s) * ((x ^ (-α s) : ℝ) : ℂ)‖ ≤
        Cm * x ^ (-(K : ℝ)) := fun s => by
    by_cases hs : s < n
    · have hsK : α s < K := (watsonExp_mono hμ hs.le).trans_lt hK
      obtain ⟨Cm, hCm⟩ := fourier_cutoff_model (hαp s) hsK
      exact ⟨Cm, fun _ => hCm⟩
    · exact ⟨0, fun h => absurd h hs⟩
  choose Cm hCm using hmod
  -- integrability near `0`
  obtain ⟨b₀, C₀, hb₀, -, h₀⟩ := exists_bound_of_isBigODLMF_nhdsGT ((hexp 0).2 0)
    (fun t ht => ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht _).ne') zero_lt_one
  have hq0 : ∀ t ∈ Ioc 0 b₀, ‖q t‖ ≤ C₀ * t ^ (α 0 - 1) := fun t ht => by
    have h := h₀ t ht
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, iteratedDeriv_zero,
      watsonExp_sub_one hμ, Nat.cast_zero, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)] at h
    convert h using 3
    rw [hαdef, ← watsonExp_sub_one hμ 0]
    simp
  have hqint : ∀ (x T : ℝ), 0 ≤ T →
      IntervalIntegrable (fun t => cexp (I * x * t) * q t) volume 0 T :=
    fun x T hT => intervalIntegrable_exp_mul_of_bound hq.continuousOn hb₀
      (by linarith [hαp 0]) hq0 x hT
  have hmint : ∀ (s : ℕ) (x T : ℝ), 0 ≤ T →
      IntervalIntegrable (fun t => cexp (I * x * t) * m s t) volume 0 T := fun s x T hT => by
    have hr : -1 < r s := by simp only [hrdef]; linarith [hαp s]
    refine intervalIntegrable_exp_mul_of_bound (C := 1) (hmc s).continuousOn one_pos hr
      (fun t ht => ?_) x hT
    rw [hmdef]; simp only
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _)
      (spCutoff_nonneg t)), one_mul]
    exact mul_le_of_le_one_right (Real.rpow_nonneg ht.1.le _) (spCutoff_le_one t)
  have hmIoi : ∀ (s : ℕ) (x : ℝ),
      IntegrableOn (fun t : ℝ => cexp (I * x * t) * m s t) (Ioi 0) := fun s x => by
    refine Integrable.mono' (integrableOn_rpow_mul_spCutoff (hαp s))
      (((by fun_prop : Continuous fun t : ℝ => cexp (I * x * t)).measurable.mul
        (continuous_ofReal.measurable.comp ((measurable_id.pow_const _).mul
          spCutoff_contDiff.continuous.measurable))).aestronglyMeasurable.restrict)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    have ht0 : 0 < t := ht
    rw [hmdef]; simp only
    rw [norm_mul, show I * (x : ℂ) * t = ((x * t : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_of_nonneg
        (mul_nonneg (Real.rpow_nonneg ht0.le _) (spCutoff_nonneg t))]
  have hmodel_eq : ∀ (s : ℕ) (x T : ℝ), 2 ≤ T → ∫ t in (0 : ℝ)..T, cexp (I * x * t) * m s t =
      ∫ t : ℝ in Ioi 0, cexp (I * x * t) * m s t := fun s x T hT => by
    have hU := setIntegral_union (disjoint_left.mpr fun t h1 h2 => not_lt.mpr h1.2 h2 :
      Disjoint (Ioc (0 : ℝ) T) (Ioi T)) measurableSet_Ioi
      ((hmIoi s x).mono_set (fun t ht => ht.1 : Ioc (0 : ℝ) T ⊆ Ioi 0))
      ((hmIoi s x).mono_set (Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ T)))
    rw [Ioc_union_Ioi_eq_Ioi (by linarith : (0 : ℝ) ≤ T)] at hU
    have hz : ∫ t in Ioi T, cexp (I * x * t) * m s t = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℂ)) fun t ht => by
        have ht' : T < t := ht
        simp [hmdef, spCutoff_eq_zero (by linarith : (2 : ℝ) ≤ t)]]
      simp
    rw [intervalIntegral.integral_of_le (by linarith), hU, hz, add_zero]
  obtain ⟨XR0, gR0, hgR0⟩ := hunifR 0
  set X := max (max XR XR0) 1
  set Cmod := ∑ s ∈ Finset.range n, ‖a s‖ * Cm s
  refine isBigODLMF_of_bound (K := Cmod + CR) ?_ ?_
  · filter_upwards [eventually_ge_atTop X] with x hx
    have hxR : XR ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
    have hxR0 : XR0 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
    have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
    have hx0 : 0 < x := by linarith
    -- the limit for `R`
    have hRint : ∀ T, 0 ≤ T → IntervalIntegrable (fun t => cexp (I * x * t) * R t) volume 0 T :=
      fun T hT => by
        refine ((hqint x T hT).sub (IntervalIntegrable.sum (Finset.range n) fun s _ =>
          (hmint s x T hT).const_mul (a s))).congr (fun t _ => ?_)
        simp only [hRdef]
        rw [mul_sub, Finset.mul_sum, Finset.sum_apply]
        congr 1
        exact Finset.sum_congr rfl fun s _ => by ring
    have hRlim : Tendsto (fun T => ∫ t in (0 : ℝ)..T, cexp (I * x * t) * R t) atTop
        (𝓝 ((∫ t in (0 : ℝ)..1, cexp (I * x * t) * R t) + gR0 x)) := by
      have h := (hgR0.tendsto_at (show x ∈ Ici XR0 from hxR0)).const_add
        (∫ t in (0 : ℝ)..1, cexp (I * x * t) * R t)
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with T hT
      simp only [iteratedDeriv_zero]
      rw [intervalIntegral.integral_add_adjacent_intervals (hRint 1 zero_le_one)
        (intervalIntegrable_exp_mul_of_contDiffOn hR 0 x (u := 1) (v := T) one_pos
          (by linarith) |> fun h => by simpa using h)]
    have hFR : fourierIoiIntegral R 0 x = (∫ t in (0 : ℝ)..1, cexp (I * x * t) * R t) + gR0 x :=
      hRlim.limUnder_eq
    have hFq : fourierIoiIntegral q 0 x = ∑ s ∈ Finset.range n,
        a s * (∫ t : ℝ in Ioi 0, cexp (I * x * t) * m s t) + fourierIoiIntegral R 0 x := by
      refine (((tendsto_const_nhds (x := ∑ s ∈ Finset.range n,
        a s * (∫ t : ℝ in Ioi 0, cexp (I * x * t) * m s t))).add hRlim).congr' ?_).limUnder_eq
        |>.trans (by rw [hFR])
      filter_upwards [eventually_ge_atTop 2] with T hT
      have hT0 : (0 : ℝ) ≤ T := by linarith
      have e : ∫ t in (0 : ℝ)..T, cexp (I * x * t) * q t =
          ∫ t in (0 : ℝ)..T, ((∑ s ∈ Finset.range n, a s * (cexp (I * x * t) * m s t)) +
            cexp (I * x * t) * R t) := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        have h1 : ∑ s ∈ Finset.range n, a s * (cexp (I * x * t) * m s t) =
            cexp (I * x * t) * ∑ s ∈ Finset.range n, a s * m s t := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
        simp only [hRdef]
        rw [h1]
        ring
      have hsumint : IntervalIntegrable (fun t => ∑ s ∈ Finset.range n,
          a s * (cexp (I * x * t) * m s t)) volume 0 T := by
        have h := IntervalIntegrable.sum (Finset.range n) fun s _ =>
          (hmint s x T hT0).const_mul (a s)
        rwa [Finset.sum_fn] at h
      symm
      rw [e, intervalIntegral.integral_add hsumint (hRint T hT0),
        intervalIntegral.integral_finsetSum fun s _ => (hmint s x T hT0).const_mul (a s)]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [intervalIntegral.integral_const_mul, hmodel_eq s x T hT]
    -- the bound
    have hterm : ∀ s ∈ Finset.range n, cexp ((((s : ℝ) + lam) * Real.pi / (2 * μ) : ℝ) * I) *
        (Real.Gamma (α s) : ℂ) * a s * ((x ^ (-α s) : ℝ) : ℂ) =
        a s * (cexp (α s * (Real.pi : ℂ) * I / 2) * Complex.Gamma (α s) *
          ((x ^ (-α s) : ℝ) : ℂ)) := fun s _ => by
      rw [Complex.Gamma_ofReal]
      have : ((((s : ℝ) + lam) * Real.pi / (2 * μ) : ℝ) : ℂ) * I =
          (α s : ℂ) * (Real.pi : ℂ) * I / 2 := by
        rw [hαdef, watsonExp]; push_cast; field_simp
      rw [this]; ring
    have hφ : ‖((x ^ (-α n) : ℝ) : ℂ)‖ = x ^ (-α n) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    have hxK : x ^ (-(K : ℝ)) ≤ x ^ (-α n) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    rw [hFq, Finset.sum_congr rfl hterm, hφ]
    calc _ = ‖∑ s ∈ Finset.range n, a s * ((∫ t : ℝ in Ioi 0, cexp (I * x * t) * m s t) -
          cexp (α s * (Real.pi : ℂ) * I / 2) * Complex.Gamma (α s) * ((x ^ (-α s) : ℝ) : ℂ)) +
          fourierIoiIntegral R 0 x‖ := by
          have h1 : ∑ s ∈ Finset.range n, a s *
              ((∫ t : ℝ in Ioi 0, cexp (I * x * t) * m s t) -
                cexp (α s * (Real.pi : ℂ) * I / 2) * Complex.Gamma (α s) *
                  ((x ^ (-α s) : ℝ) : ℂ)) = (∑ s ∈ Finset.range n,
                a s * (∫ t : ℝ in Ioi 0, cexp (I * x * t) * m s t)) - ∑ s ∈ Finset.range n,
                a s * (cexp (α s * (Real.pi : ℂ) * I / 2) * Complex.Gamma (α s) *
                  ((x ^ (-α s) : ℝ) : ℂ)) := by
            rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun s _ => by ring
          rw [h1]
          congr 1
          ring
      _ ≤ ∑ s ∈ Finset.range n, ‖a s‖ * (Cm s * x ^ (-(K : ℝ))) + CR * x ^ (-α n) := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun s hs => ?_)) (hRem x hxR))
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hCm s (Finset.mem_range.mp hs) x hx0) (norm_nonneg _)
      _ ≤ ∑ s ∈ Finset.range n, ‖a s‖ * (Cm s * x ^ (-α n)) + CR * x ^ (-α n) := by
          gcongr with s hs
          have := (norm_nonneg _).trans (hCm s (Finset.mem_range.mp hs) x hx0)
          have hpos : 0 ≤ Cm s := by
            have h2 : 0 < x ^ (-(K : ℝ)) := Real.rpow_pos_of_pos hx0 _
            exact (mul_nonneg_iff_of_pos_right h2).mp this
          exact hpos
      _ = _ := by
          rw [add_mul, Finset.sum_mul]; congr 1
          exact Finset.sum_congr rfl fun s _ => by ring
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx _).ne'

end Azurite.DLMF
