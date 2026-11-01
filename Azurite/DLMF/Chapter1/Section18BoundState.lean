/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18Hermite
import Azurite.DLMF.Chapter1.Section16
import Azurite.DLMF.Chapter1.Section14HilbertDense

/-!
# DLMF §1.18(viii), Example 1: bound states in one dimension

https://dlmf.nist.gov/1.18.viii

DLMF's claim, after Simon (1976, Thm 2.5), is that `−d²/dx² + q` on `ℝ` has a negative eigenvalue
whenever `q < 0` on some interval and `∫ q ≤ 0`. For continuous compactly supported `q`, it is
proven in `Section18Simon` by a shooting argument. (Simon also assumes `∫ (1 + x²)|q| < ∞`,
which DLMF omits.) This file has two complementary parts:

* The δ-well `q = −αδ(x − a)`: `ψ(x) = e^{−α|x−a|/2}` (`wellFun`) satisfies
  `−ψ″ − αδ_a ψ = −(α²/4)ψ` in the sense of distributions (`dlmf_1_18_viii_delta_well`, by two
  integrations by parts on each side of `a`). For `α > 0`, `ψ ∈ L²` (`memLp_wellFun`) and the
  eigenvalue `−α²/4` is negative (`delta_well_eigenvalue_neg`).
* The variational core of Simon's theorem: for integrable `q` with `∫ q < 0`, the Gaussians
  `ψ_ε = e^{−εx²}` (`trialFun`) have negative energy `∫ |ψ_ε′|² + ∫ q ψ_ε² < 0` for small `ε`
  (`dlmf_1_18_viii_trial`). The kinetic term is `√(2ε) ∫ u² e^{−u²}` (`kinetic_trialFun`), and the
  potential term tends to `∫ q`. The two-dimensional analog is not formalized.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real ContDiff

namespace Azurite.DLMF

/-! ### The δ-well `q = −α δ(x − a)` -/

/-- The bound state `ψ(x) = e^{−α|x−a|/2}` of the δ-well. -/
noncomputable def wellFun (α a x : ℝ) : ℝ := Real.exp (-(α / 2 * |x - a|))

/-- `e^{c(x − a)}`, cast to `ℂ`. -/
noncomputable def expShift (c a x : ℝ) : ℂ := ((Real.exp (c * (x - a)) : ℝ) : ℂ)

theorem hasDerivAt_expShift (c a x : ℝ) :
    HasDerivAt (expShift c a) ((c : ℂ) * expShift c a x) x := by
  have h : HasDerivAt (fun y : ℝ => Real.exp (c * (y - a))) (Real.exp (c * (x - a)) * c) x :=
    ((Real.hasDerivAt_exp _).comp x (((hasDerivAt_id x).sub_const a).const_mul c)).congr_deriv
      (by simp)
  exact h.ofReal_comp.congr_deriv (by simp only [expShift]; push_cast; ring)

theorem testFun_derivs {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (x : ℝ) :
    HasDerivAt φ (deriv φ x) x ∧ HasDerivAt (deriv φ) (deriv (deriv φ) x) x := by
  have h1 := contDiff_infty_iff_deriv.mp hφ
  have h2 := contDiff_infty_iff_deriv.mp h1.2
  exact ⟨(h1.1 x).hasDerivAt, (h2.1 x).hasDerivAt⟩

/-- Two integrations by parts against `e^{c(x−a)}` on `[s, t]`. -/
theorem integral_expShift_mul_deriv_deriv {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (c a s t : ℝ) :
    ∫ x in s..t, expShift c a x * deriv (deriv φ) x =
      expShift c a t * deriv φ t - expShift c a s * deriv φ s -
        ((c : ℂ) * expShift c a t * φ t - (c : ℂ) * expShift c a s * φ s) +
          (c : ℂ) ^ 2 * ∫ x in s..t, expShift c a x * φ x := by
  have hd := testFun_derivs hφ
  have hc1 : Continuous (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2.continuous
  have hc2 : Continuous (deriv (deriv φ)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hφ).2).2.continuous
  have hE : Continuous (expShift c a) := by unfold expShift; fun_prop
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := s) (b := t)
    (u := expShift c a) (u' := fun x => (c : ℂ) * expShift c a x) (v := deriv φ)
    (v' := deriv (deriv φ)) (fun x _ => hasDerivAt_expShift c a x) (fun x _ => (hd x).2)
    ((continuous_const.mul hE).intervalIntegrable _ _) (hc2.intervalIntegrable _ _)
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := s) (b := t)
    (u := fun x => (c : ℂ) * expShift c a x) (u' := fun x => (c : ℂ) * ((c : ℂ) * expShift c a x))
    (v := φ) (v' := deriv φ) (fun x _ => (hasDerivAt_expShift c a x).const_mul (c : ℂ))
    (fun x _ => (hd x).1) ((continuous_const.mul (continuous_const.mul hE)).intervalIntegrable _ _)
    (hc1.intervalIntegrable _ _)
  rw [h1, h2]
  have e : ∫ x in s..t, (c : ℂ) * ((c : ℂ) * expShift c a x) * φ x =
      (c : ℂ) ^ 2 * ∫ x in s..t, expShift c a x * φ x := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  rw [e]
  ring

theorem exists_radius_testFunction {φ : ℝ → ℂ} (hφ : IsTestFunction univ φ) (a : ℝ) :
    ∃ R, |a| < R ∧ ∀ x, R ≤ |x| → φ x = 0 ∧ deriv φ x = 0 ∧ deriv (deriv φ) x = 0 := by
  obtain ⟨r, hr⟩ := hφ.2.1.isCompact.isBounded.subset_ball 0
  refine ⟨max r (|a| + 1), by
    have := le_max_right r (|a| + 1); linarith, fun x hx => ?_⟩
  have hx' : x ∉ tsupport φ := fun h => by
    have := hr h
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at this
    linarith [le_max_left r (|a| + 1)]
  refine ⟨image_eq_zero_of_notMem_tsupport hx', image_eq_zero_of_notMem_tsupport
    fun h => hx' (tsupport_deriv_subset h), image_eq_zero_of_notMem_tsupport
    fun h => hx' (tsupport_deriv_subset (tsupport_deriv_subset h))⟩

/-- DLMF §1.18(viii), Example 1: the δ-well `q = −αδ(x − a)`, `α > 0`, has the `L²` eigenfunction
`ψ(x) = e^{−α|x−a|/2}` with negative eigenvalue `−α²/4`: in the sense of distributions,
`−ψ″ − αδ_a ψ = −(α²/4) ψ` (with `ψ(a) = 1`), i.e. for every test function `φ`,
`∫ ψ φ″ = (α²/4) ∫ ψ φ − α φ(a)`. -/
theorem dlmf_1_18_viii_delta_well (α a : ℝ) {φ : ℝ → ℂ}
    (hφ : IsTestFunction univ φ) :
    ∫ x, (wellFun α a x : ℂ) * deriv (deriv φ) x =
      ((α ^ 2 / 4 : ℝ) : ℂ) * (∫ x, (wellFun α a x : ℂ) * φ x) - α * φ a := by
  obtain ⟨R, hRa, hR⟩ := exists_radius_testFunction hφ a
  have hR0 : 0 < R := (abs_nonneg a).trans_lt hRa
  have haR : a < R := (le_abs_self a).trans_lt hRa
  have hRa' : -R < a := by linarith [neg_abs_le a]
  have hwc : Continuous fun x => (wellFun α a x : ℂ) := by unfold wellFun; fun_prop
  have hc0 : Continuous φ := hφ.1.continuous
  have hc2 : Continuous (deriv (deriv φ)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hφ.1).2).2.continuous
  -- reduce to `[−R, R]`
  have hsupp : ∀ g : ℝ → ℂ, (∀ x, R ≤ |x| → g x = 0) →
      ∫ x, (wellFun α a x : ℂ) * g x = ∫ x in (-R)..R, (wellFun α a x : ℂ) * g x := fun g hg => by
    refine (intervalIntegral.integral_eq_integral_of_support_subset fun x hx => ?_).symm
    by_contra h
    rw [mem_Ioc, not_and_or, not_lt, not_le] at h
    apply hx
    have : R ≤ |x| := by
      rcases h with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    simp [hg x this]
  rw [hsupp _ fun x hx => (hR x hx).2.2, hsupp _ fun x hx => (hR x hx).1,
    ← intervalIntegral.integral_add_adjacent_intervals (b := a)
      (f := fun x => (wellFun α a x : ℂ) * deriv (deriv φ) x)
      ((hwc.mul hc2).intervalIntegrable _ _) ((hwc.mul hc2).intervalIntegrable _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (b := a)
      (f := fun x => (wellFun α a x : ℂ) * φ x)
      ((hwc.mul hc0).intervalIntegrable _ _) ((hwc.mul hc0).intervalIntegrable _ _)]
  -- on each side `ψ` is an exponential
  have hL : ∀ x ∈ uIcc (-R) a, (wellFun α a x : ℂ) = expShift (α / 2) a x := fun x hx => by
    rw [uIcc_of_le hRa'.le] at hx
    simp only [wellFun, expShift, abs_of_nonpos (sub_nonpos.mpr hx.2)]
    congr 2; ring
  have hRt : ∀ x ∈ uIcc a R, (wellFun α a x : ℂ) = expShift (-(α / 2)) a x := fun x hx => by
    rw [uIcc_of_le haR.le] at hx
    simp only [wellFun, expShift, abs_of_nonneg (sub_nonneg.mpr hx.1)]
    congr 2; ring
  have i1 : ∫ x in (-R)..a, (wellFun α a x : ℂ) * deriv (deriv φ) x =
      ∫ x in (-R)..a, expShift (α / 2) a x * deriv (deriv φ) x :=
    intervalIntegral.integral_congr fun x hx => by simp only [hL x hx]
  have i2 : ∫ x in a..R, (wellFun α a x : ℂ) * deriv (deriv φ) x =
      ∫ x in a..R, expShift (-(α / 2)) a x * deriv (deriv φ) x :=
    intervalIntegral.integral_congr fun x hx => by simp only [hRt x hx]
  have i3 : ∫ x in (-R)..a, (wellFun α a x : ℂ) * φ x =
      ∫ x in (-R)..a, expShift (α / 2) a x * φ x :=
    intervalIntegral.integral_congr fun x hx => by simp only [hL x hx]
  have i4 : ∫ x in a..R, (wellFun α a x : ℂ) * φ x =
      ∫ x in a..R, expShift (-(α / 2)) a x * φ x :=
    intervalIntegral.integral_congr fun x hx => by simp only [hRt x hx]
  rw [i1, i2, i3, i4, integral_expShift_mul_deriv_deriv hφ.1,
    integral_expShift_mul_deriv_deriv hφ.1]
  have hRR := hR R (by rw [abs_of_pos hR0])
  have hmR := hR (-R) (by rw [abs_neg, abs_of_pos hR0])
  have he : ∀ c, expShift c a a = 1 := fun c => by simp [expShift]
  rw [hRR.1, hRR.2.1, hmR.1, hmR.2.1, he, he]
  push_cast
  ring

theorem memLp_wellFun {α : ℝ} (hα : 0 < α) (a : ℝ) :
    MemLp (fun x => (wellFun α a x : ℂ)) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm (by unfold wellFun; fun_prop)).mpr ?_
  have h := (integrable_exp_neg_abs hα).comp_sub_right a
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [wellFun, Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Real.exp_nat_mul]
  congr 1
  push_cast; ring

/-- The eigenvalue `−α²/4` of the δ-well is negative, below the continuous spectrum `[0, ∞)`. -/
theorem delta_well_eigenvalue_neg {α : ℝ} (hα : 0 < α) : -(α ^ 2 / 4) < 0 := by
  have := sq_pos_of_pos hα
  linarith

/-! ### Variational core of Simon's theorem -/

/-- The Gaussian trial functions `ψ_ε(x) = e^{−εx²}`. -/
noncomputable def trialFun (ε x : ℝ) : ℝ := Real.exp (-(ε * x ^ 2))

theorem hasDerivAt_trialFun (ε x : ℝ) :
    HasDerivAt (trialFun ε) (-(2 * ε * x) * trialFun ε x) x := by
  have h := ((hasDerivAt_pow 2 x).const_mul ε).neg.exp
  refine h.congr_deriv ?_
  simp only [trialFun, Pi.neg_apply]
  ring

theorem kinetic_trialFun {ε : ℝ} (hε : 0 < ε) :
    ∫ x, (deriv (trialFun ε) x) ^ 2 = √(2 * ε) * ∫ u, u ^ 2 * Real.exp (-u ^ 2) := by
  set c := √(2 * ε)
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc2 : c ^ 2 = 2 * ε := Real.sq_sqrt (by positivity)
  have e : ∀ x, (deriv (trialFun ε) x) ^ 2 = c ^ 2 * ((c * x) ^ 2 * Real.exp (-(c * x) ^ 2)) :=
    fun x => by
      have hsq : Real.exp (-(ε * x ^ 2)) ^ 2 = Real.exp (-(2 * ε * x ^ 2)) := by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf
      rw [(hasDerivAt_trialFun ε x).deriv, show (c * x) ^ 2 = 2 * ε * x ^ 2 by
        rw [mul_pow, hc2], hc2, trialFun, mul_pow, hsq]
      ring
  simp_rw [e]
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (fun u => u ^ 2 * Real.exp (-u ^ 2)) c, abs_of_pos (inv_pos.mpr hc), smul_eq_mul]
  field_simp

theorem tendsto_kinetic_trialFun :
    Tendsto (fun ε => ∫ x, (deriv (trialFun ε) x) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun ε : ℝ => √(2 * ε) * ∫ u, u ^ 2 * Real.exp (-u ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    have hs : Tendsto (fun ε : ℝ => √(2 * ε)) (𝓝 0) (𝓝 0) := by
      have h0 : Tendsto (fun ε : ℝ => √(2 * ε)) (𝓝 0) (𝓝 (√(2 * 0))) :=
        (Real.continuous_sqrt.comp (continuous_const.mul continuous_id)).tendsto 0
      rwa [mul_zero, Real.sqrt_zero] at h0
    have := hs.mul_const (∫ u, u ^ 2 * Real.exp (-u ^ 2))
    rw [zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (kinetic_trialFun hε).symm

theorem tendsto_potential_trialFun {q : ℝ → ℝ} (hq : Integrable q) :
    Tendsto (fun ε => ∫ x, q x * trialFun ε x ^ 2) (𝓝[>] 0) (𝓝 (∫ x, q x)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖q x‖)
    (Eventually.of_forall fun ε => hq.aestronglyMeasurable.mul
      (by simp only [trialFun]; fun_prop :
        Continuous fun x => trialFun ε x ^ 2).aestronglyMeasurable)
    ?_ hq.norm (ae_of_all _ fun x => ?_)
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine ae_of_all _ fun x => ?_
    rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ trialFun ε x ^ 2)]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [trialFun, ← Real.exp_nat_mul]
    exact Real.exp_le_one_iff.mpr (by push_cast; nlinarith [sq_nonneg x])
  · have h : Tendsto (fun ε : ℝ => q x * trialFun ε x ^ 2) (𝓝 0) (𝓝 (q x * trialFun 0 x ^ 2)) :=
      ((by simp only [trialFun]; fun_prop :
        Continuous fun ε : ℝ => q x * trialFun ε x ^ 2).tendsto 0)
    simpa [trialFun] using h.mono_left nhdsWithin_le_nhds

/-- DLMF §1.18(viii), Example 1, the variational core of Simon's theorem: if `q` is integrable
with `∫ q < 0`, the energy form of `ℒ = −d²/dx² + q` is negative on a Gaussian:
`∫ |ψ_ε′|² + ∫ q |ψ_ε|² < 0` for `ψ_ε = e^{−εx²}` with small `ε > 0`. So `ℒ` is not
nonnegative and its spectrum extends below the continuous spectrum `[0, ∞)`. -/
theorem dlmf_1_18_viii_trial {q : ℝ → ℝ} (hq : Integrable q) (hneg : ∫ x, q x < 0) :
    ∃ ε > 0, (∫ x, (deriv (trialFun ε) x) ^ 2) + ∫ x, q x * trialFun ε x ^ 2 < 0 := by
  have h := tendsto_kinetic_trialFun.add (tendsto_potential_trialFun hq)
  rw [zero_add] at h
  obtain ⟨ε, hε1, hε2⟩ := ((h.eventually (gt_mem_nhds hneg)).and self_mem_nhdsWithin).exists
  exact ⟨ε, hε2, hε1⟩

end Azurite.DLMF
