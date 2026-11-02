/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section8CaseI
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# DLMF §2.8(iii): Case II: Simple Turning Point, 2.8.14–2.8.21

For `d²W/dξ² = (u² ξ + ψ(ξ)) W` (2.8.14) on an interval `(α₁, α₂) ∋ 0`:

* 2.8.17 (`regB`, `dlmf_2_8_17_pos`, `dlmf_2_8_17_neg`): DLMF's two-sided formula
  `B(ξ) = (2ξ^{1/2})^{−1} ∫_0^ξ g(v) v^{−1/2} dv` (`ξ > 0`) and its mirror (`ξ < 0`) is the single
  function `B(ξ) = ∫_0^1 g(ξσ²) dσ`, which is `C^∞` through the turning point (`regPhi_smooth`) and
  is the solution of `B + 2ξB′ = g` regular at `0` (`regB_ode`).
* 2.8.18 (`caseIIA`, `caseIIB`, `dlmf_2_8_18`): for `ψ ∈ C^∞` the coefficients `A_s`, `B_s` are
  `C^∞` and satisfy `B_s + 2ξB_s′ = ψA_s − A_s″`, `2A_{s+1}′ = −B_s″ + ψB_s`.
* 2.8.15–2.8.16 as formal expansions (`CaseIIData.dlmf_2_8_15_formal`): for any solution of Airy's
  equation (`Ai` or `Bi`), the truncated expansion satisfies 2.8.14 up to the single residual
  `u^{2−2n}(A″_{n−1} − ψA_{n−1}) Ai(u^{2/3}ξ)`.
* 2.8.20–2.8.21 (`envAi`, `envBi`, `envAi_envBi_continuous`): the envelopes are continuous, given
  that `c` is a root of `Ai = Bi` (2.8.19) with `Ai(c) ≥ 0`.

Not formalized: the error terms `O(u^{1−2n})` of 2.8.15–2.8.16 and 2.8.22–2.8.23 (Olver, Ch. 11),
which need the Airy-function theory of DLMF Chapter 9 (Wronskian, asymptotics, modulus and weight
bounds), and the value `c = −0.36604…` of 2.8.19.
-/
open Filter Topology Set MeasureTheory intervalIntegral
open scoped ContDiff

namespace Azurite.DLMF

variable {I : Set ℝ}

/-- `Φ_m(h)(ξ) = ∫_0^1 σ^m h(ξσ²) dσ`. -/
noncomputable def regPhi (m : ℕ) (h : ℝ → ℝ) (ξ : ℝ) : ℝ := ∫ σ in (0 : ℝ)..1, σ ^ m * h (ξ * σ ^ 2)

/-- **DLMF 2.8.17**: `B(ξ) = ∫_0^1 g(ξσ²) dσ`. -/
noncomputable def regB (g : ℝ → ℝ) : ℝ → ℝ := regPhi 0 g

theorem mul_sq_mem (hIc : I.OrdConnected) (h0 : (0 : ℝ) ∈ I) {ξ σ : ℝ} (hξ : ξ ∈ I)
    (hσ : σ ∈ Icc (0 : ℝ) 1) : ξ * σ ^ 2 ∈ I := by
  have hs : σ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨by positivity, by nlinarith [hσ.1, hσ.2]⟩
  refine hIc.uIcc_subset h0 hξ ?_
  rcases le_total 0 ξ with h | h
  · rw [uIcc_of_le h]; exact ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  · rw [uIcc_of_ge h]; exact ⟨by nlinarith [hs.2], by nlinarith [hs.1]⟩

theorem regPhi_cont_integrand {h : ℝ → ℝ} (hIc : I.OrdConnected) (h0 : (0 : ℝ) ∈ I)
    (hc : ContinuousOn h I) (m : ℕ) {ξ : ℝ} (hξ : ξ ∈ I) :
    ContinuousOn (fun σ : ℝ => σ ^ m * h (ξ * σ ^ 2)) (Icc 0 1) :=
  (continuousOn_pow m).mul (hc.comp (continuousOn_const.mul (continuousOn_pow 2))
    fun _ hσ => mul_sq_mem hIc h0 hξ hσ)

/-- `d/dξ Φ_m(h) = Φ_{m+2}(h′)`. -/
theorem regPhi_hasDerivAt (hI : IsOpen I) (hIc : I.OrdConnected) (h0 : (0 : ℝ) ∈ I)
    {h h' : ℝ → ℝ} (hd : ∀ x ∈ I, HasDerivAt h (h' x) x) (hc' : ContinuousOn h' I) (m : ℕ)
    {ξ : ℝ} (hξ : ξ ∈ I) : HasDerivAt (regPhi m h) (regPhi (m + 2) h' ξ) ξ := by
  have hc : ContinuousOn h I := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hI ξ hξ
  have hlo : ξ - ε / 2 ∈ I := hball (by
    rw [Metric.mem_ball, Real.dist_eq, show ξ - ε / 2 - ξ = -(ε / 2) by ring, abs_neg,
      abs_of_pos (by linarith)]; linarith)
  have hhi : ξ + ε / 2 ∈ I := hball (by
    rw [Metric.mem_ball, Real.dist_eq, show ξ + ε / 2 - ξ = ε / 2 by ring,
      abs_of_pos (by linarith)]; linarith)
  set K := Icc (min 0 (ξ - ε / 2)) (max 0 (ξ + ε / 2)) with hK
  have hKI : K ⊆ I := hIc.out (by rcases min_choice 0 (ξ - ε / 2) with h | h <;> rw [h] <;>
    assumption) (by rcases max_choice 0 (ξ + ε / 2) with h | h <;> rw [h] <;> assumption)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc'.mono hKI)
  set s := Metric.ball ξ (ε / 2) with hs
  have hsK : ∀ x ∈ s, ∀ σ ∈ Icc (0 : ℝ) 1, x * σ ^ 2 ∈ K := by
    intro x hx σ hσ
    rw [hs, Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    have h2 : σ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨by positivity, by nlinarith [hσ.1, hσ.2]⟩
    constructor
    · rcases le_total 0 x with h | h
      · exact (min_le_left _ _).trans (by nlinarith [h2.1])
      · exact (min_le_right _ _).trans (by nlinarith [h2.1, h2.2])
    · rcases le_total 0 x with h | h
      · exact le_trans (by nlinarith [h2.1, h2.2]) (le_max_right _ _)
      · exact le_trans (by nlinarith [h2.1]) (le_max_left _ _)
  have hsI : s ⊆ I := fun x hx => hball (Metric.ball_subset_ball (by linarith) hx)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x σ => σ ^ m * h (x * σ ^ 2)) (F' := fun x σ => σ ^ (m + 2) * h' (x * σ ^ 2))
    (μ := volume) (a := 0) (b := 1) (x₀ := ξ) (bound := fun _ => M)
    (Metric.ball_mem_nhds ξ (by linarith : 0 < ε / 2))
    (Filter.eventually_of_mem (Metric.ball_mem_nhds ξ (by linarith : 0 < ε / 2)) fun x hx =>
      ((regPhi_cont_integrand hIc h0 hc m (hsI hx)).mono
        (by rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self)).aestronglyMeasurable
        measurableSet_uIoc)
    ((regPhi_cont_integrand hIc h0 hc m hξ).intervalIntegrable_of_Icc zero_le_one)
    (((regPhi_cont_integrand hIc h0 hc' (m + 2) hξ).mono
      (by rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self)).aestronglyMeasurable
      measurableSet_uIoc)
    (ae_of_all _ fun σ hσ x hx => by
      rw [uIoc_of_le zero_le_one] at hσ
      have hσ' : σ ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hσ
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hσ'.1]
      have h1 : σ ^ (m + 2) ≤ 1 := pow_le_one₀ hσ'.1 hσ'.2
      have h2 := hM _ (hsK x hx σ hσ')
      rw [Real.norm_eq_abs] at h2
      calc σ ^ (m + 2) * |h' (x * σ ^ 2)| ≤ 1 * M :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = M := one_mul M)
    intervalIntegrable_const
    (ae_of_all _ fun σ hσ x hx => by
      rw [uIoc_of_le zero_le_one] at hσ
      have hσ' : σ ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hσ
      have := ((hd _ (hKI (hsK x hx σ hσ'))).comp x ((hasDerivAt_id x).mul_const (σ ^ 2))).const_mul
        (σ ^ m)
      refine this.congr_deriv ?_
      simp only [one_mul]
      ring)
  exact key.2

theorem regPhi_contDiffOn (hI : IsOpen I) (hIc : I.OrdConnected) (h0 : (0 : ℝ) ∈ I) :
    ∀ (k : ℕ) (m : ℕ) (h : ℝ → ℝ), ContDiffOn ℝ ∞ h I → ContDiffOn ℝ k (regPhi m h) I := by
  intro k
  induction k with
  | zero =>
    intro m h hh
    rw [Nat.cast_zero, contDiffOn_zero]
    have hd : ContDiffOn ℝ ∞ (deriv h) I := hh.deriv_of_isOpen hI (m := ∞) (by simp)
    exact fun ξ hξ => (regPhi_hasDerivAt hI hIc h0 (fun x hx =>
      ((hh.differentiableOn (by simp)).differentiableAt (hI.mem_nhds hx)).hasDerivAt)
      hd.continuousOn m hξ).continuousAt.continuousWithinAt
  | succ k ih =>
    intro m h hh
    have hd : ContDiffOn ℝ ∞ (deriv h) I := hh.deriv_of_isOpen hI (m := ∞) (by simp)
    have hder : ∀ ξ ∈ I, HasDerivAt (regPhi m h) (regPhi (m + 2) (deriv h) ξ) ξ :=
      fun ξ hξ => regPhi_hasDerivAt hI hIc h0 (fun x hx =>
        ((hh.differentiableOn (by simp)).differentiableAt (hI.mem_nhds hx)).hasDerivAt)
        hd.continuousOn m hξ
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by norm_cast,
      contDiffOn_succ_iff_deriv_of_isOpen hI]
    refine ⟨fun ξ hξ => (hder ξ hξ).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (ih (m + 2) (deriv h) hd).congr fun ξ hξ => (hder ξ hξ).deriv

/-- `Φ_m(h)` is `C^∞` on `I` when `h` is. -/
theorem regPhi_smooth (hI : IsOpen I) (hIc : I.OrdConnected) (h0 : (0 : ℝ) ∈ I) (m : ℕ)
    {h : ℝ → ℝ} (hh : ContDiffOn ℝ ∞ h I) : ContDiffOn ℝ ∞ (regPhi m h) I :=
  contDiffOn_infty.mpr fun k => regPhi_contDiffOn hI hIc h0 k m h hh

/-- **DLMF 2.8.17**: `B = ∫_0^1 g(ξσ²) dσ` solves `B + 2ξ B′ = g`. -/
theorem regB_ode (hI : IsOpen I) (hIc : I.OrdConnected) (h0 : (0 : ℝ) ∈ I) {g g' : ℝ → ℝ}
    (hd : ∀ x ∈ I, HasDerivAt g (g' x) x) (hc' : ContinuousOn g' I) {ξ : ℝ} (hξ : ξ ∈ I) :
    regB g ξ + 2 * ξ * deriv (regB g) ξ = g ξ := by
  have hc : ContinuousOn g I := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  rw [regB, (regPhi_hasDerivAt hI hIc h0 hd hc' 0 hξ).deriv]
  -- `d/dσ [σ g(ξσ²)] = g(ξσ²) + 2ξ σ² g′(ξσ²)`
  have hFTC := integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (f := fun σ => σ * g (ξ * σ ^ 2))
    (f' := fun σ => σ ^ 0 * g (ξ * σ ^ 2) + 2 * ξ * (σ ^ (0 + 2) * g' (ξ * σ ^ 2)))
    (fun σ hσ => by
      rw [uIcc_of_le zero_le_one] at hσ
      have hσm := mul_sq_mem hIc h0 hξ hσ
      have h1 := (hd _ hσm).comp σ (((hasDerivAt_id σ).pow 2).const_mul ξ)
      refine ((hasDerivAt_id σ).mul h1).congr_deriv ?_
      simp only [id, pow_zero, one_mul, zero_add, Nat.cast_ofNat, Function.comp_apply,
        Pi.pow_apply]
      ring)
    (((regPhi_cont_integrand hIc h0 hc 0 hξ).add
      (continuousOn_const.mul (regPhi_cont_integrand hIc h0 hc' 2 hξ))).intervalIntegrable_of_Icc
      zero_le_one)
  rw [integral_add ((regPhi_cont_integrand hIc h0 hc 0 hξ).intervalIntegrable_of_Icc zero_le_one)
    (((regPhi_cont_integrand hIc h0 hc' 2 hξ).intervalIntegrable_of_Icc
      zero_le_one).const_mul _), intervalIntegral.integral_const_mul] at hFTC
  simp only [one_mul, one_pow, zero_mul, sub_zero, mul_one] at hFTC
  rw [regPhi, regPhi]
  linear_combination hFTC

/-! ### DLMF's two-sided formula -/

/-- **DLMF 2.8.17**, `ξ > 0`: `B(ξ) = (2ξ^{1/2})^{−1} ∫_0^ξ g(v) v^{−1/2} dv`. -/
theorem dlmf_2_8_17_pos (hI : IsOpen I) (hIc : I.OrdConnected) (h0 : (0 : ℝ) ∈ I)
    {g g' : ℝ → ℝ} (hd : ∀ x ∈ I, HasDerivAt g (g' x) x) (hc' : ContinuousOn g' I) {ξ : ℝ}
    (hξ : ξ ∈ I) (hpos : 0 < ξ) :
    regB g ξ = 1 / (2 * Real.sqrt ξ) * ∫ v in (0 : ℝ)..ξ, g v / Real.sqrt v := by
  have hc : ContinuousOn g I := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  set J := I ∩ Ioi 0 with hJ
  have hJo : IsOpen J := hI.inter isOpen_Ioi
  have hJc : J.OrdConnected := hIc.inter ordConnected_Ioi
  have hsub : ∀ y ∈ J, Icc 0 y ⊆ I := fun y hy => hIc.out h0 hy.1
  -- `g(v)/√v` is integrable on `[0, y]`
  have hcont : ∀ y ∈ J, ContinuousOn (fun v => g v / Real.sqrt v) (Ioc 0 y) := fun y hy =>
    (hc.mono fun v hv => hsub y hy (Ioc_subset_Icc_self hv)).div
      Real.continuous_sqrt.continuousOn fun v hv => (Real.sqrt_pos.mpr hv.1).ne'
  have hint : ∀ y ∈ J, IntervalIntegrable (fun v => g v / Real.sqrt v) volume 0 y := by
    intro y hy
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.mono (hsub y hy))
    refine IntervalIntegrable.mono_fun' ((intervalIntegrable_rpow' (r := -(1 / 2))
      (by norm_num)).const_mul M) ?_ ?_
    · rw [uIoc_of_le hy.2.le]
      exact (hcont y hy).aestronglyMeasurable measurableSet_Ioc
    · rw [uIoc_of_le hy.2.le]
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun v hv => ?_)
      have hv0 : 0 < v := hv.1
      show ‖g v / Real.sqrt v‖ ≤ M * v ^ (-(1 / 2 : ℝ))
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.sqrt_pos.mpr hv0), Real.rpow_neg hv0.le,
        ← Real.sqrt_eq_rpow, div_eq_mul_inv]
      have := hM v ⟨hv.1.le, hv.2⟩
      rw [Real.norm_eq_abs] at this
      exact mul_le_mul_of_nonneg_right this (inv_nonneg.mpr (Real.sqrt_nonneg _))
  set G : ℝ → ℝ := fun y => ∫ v in (0 : ℝ)..y, g v / Real.sqrt v with hG
  set H : ℝ → ℝ := fun y => 2 * Real.sqrt y * regB g y with hH
  have hcJ : ContinuousOn (fun v => g v / Real.sqrt v) J :=
    (hc.mono fun v hv => hv.1).div Real.continuous_sqrt.continuousOn fun v hv =>
      (Real.sqrt_pos.mpr hv.2).ne'
  have hGd : ∀ y ∈ J, HasDerivAt G (g y / Real.sqrt y) y := fun y hy =>
    integral_hasDerivAt_right (hint y hy) (hcJ.stronglyMeasurableAtFilter hJo y hy)
      (hcJ.continuousAt (hJo.mem_nhds hy))
  have hHd : ∀ y ∈ J, HasDerivAt H (g y / Real.sqrt y) y := by
    intro y hy
    have hy0 : 0 < y := hy.2
    have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
    have hB := regPhi_hasDerivAt hI hIc h0 hd hc' 0 hy.1
    have hsq := Real.hasDerivAt_sqrt hy0.ne'
    have hode := regB_ode hI hIc h0 hd hc' hy.1
    rw [regB, hB.deriv] at hode
    refine ((hsq.const_mul 2).mul hB).congr_deriv ?_
    have hss : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
    rw [regB] at *
    field_simp
    linear_combination hode + 2 * regPhi (0 + 2) g' y * hss
  have hD : ∀ y ∈ J, HasDerivAt (fun y => H y - G y) 0 y := fun y hy =>
    ((hHd y hy).sub (hGd y hy)).congr_deriv (sub_self _)
  -- the common constant is `0`: both sides are `O(√y)` as `y → 0+`
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.mono (hsub ξ ⟨hξ, hpos⟩))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hpos.le⟩)
  have hsmall : ∀ y, 0 < y → y ≤ ξ → |H y - G y| ≤ 4 * M * Real.sqrt y := by
    intro y hy0 hyξ
    have hyJ : y ∈ J := ⟨hIc.out h0 hξ ⟨hy0.le, hyξ⟩, hy0⟩
    have hGb : |G y| ≤ 2 * M * Real.sqrt y := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le hy0.le (ae_of_all _ fun v hv => ?_)
        ((intervalIntegrable_rpow' (r := -(1 / 2)) (by norm_num)).const_mul M)).trans
        (le_of_eq ?_)
      · have hv0 : 0 < v := hv.1
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.sqrt_pos.mpr hv0), Real.rpow_neg hv0.le,
          ← Real.sqrt_eq_rpow, div_eq_mul_inv]
        have := hM v ⟨hv.1.le, hv.2.trans hyξ⟩
        rw [Real.norm_eq_abs] at this
        exact mul_le_mul_of_nonneg_right this (inv_nonneg.mpr (Real.sqrt_nonneg _))
      · rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num)),
          Real.zero_rpow (by norm_num), Real.sqrt_eq_rpow]
        norm_num
        ring
    have hBb : |regB g y| ≤ M := by
      rw [← Real.norm_eq_abs, regB, regPhi]
      refine (norm_integral_le_of_norm_le_const (C := M) fun σ hσ => ?_).trans (by simp)
      rw [uIoc_of_le zero_le_one] at hσ
      rw [pow_zero, one_mul]
      have h2 : σ ^ 2 ≤ 1 := by nlinarith [hσ.1, hσ.2]
      exact hM _ ⟨by positivity, by nlinarith [hσ.1]⟩
    have hHb : |H y| ≤ 2 * M * Real.sqrt y := by
      rw [hH, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_nonneg (Real.sqrt_nonneg _)]
      nlinarith [Real.sqrt_nonneg y]
    calc |H y - G y| ≤ |H y| + |G y| := abs_sub _ _
      _ ≤ 4 * M * Real.sqrt y := by linarith
  have hconst : ∀ y, 0 < y → y ≤ ξ → H y - G y = H ξ - G ξ := fun y hy0 hyξ =>
    eq_of_hasDerivAt_zero hJc hD ⟨hIc.out h0 hξ ⟨hy0.le, hyξ⟩, hy0⟩ ⟨hξ, hpos⟩
  have hlim : Tendsto (fun y => 4 * M * Real.sqrt y) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).const_mul (4 * M)).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have hzero : |H ξ - G ξ| ≤ 0 := ge_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsGT hpos] with y hy
    rw [← hconst y hy.1 hy.2.le]
    exact hsmall y hy.1 hy.2.le)
  have hHG : H ξ = G ξ := by
    have := abs_nonpos_iff.mp hzero
    linarith
  have hs : 0 < Real.sqrt ξ := Real.sqrt_pos.mpr hpos
  rw [hH, hG] at hHG
  simp only at hHG
  rw [← hHG]
  field_simp

/-- **DLMF 2.8.17**, `ξ < 0`: `B(ξ) = (2(−ξ)^{1/2})^{−1} ∫_ξ^0 g(v) (−v)^{−1/2} dv`. -/
theorem dlmf_2_8_17_neg (hI : IsOpen I) (hIc : I.OrdConnected) (h0 : (0 : ℝ) ∈ I)
    {g g' : ℝ → ℝ} (hd : ∀ x ∈ I, HasDerivAt g (g' x) x) (hc' : ContinuousOn g' I) {ξ : ℝ}
    (hξ : ξ ∈ I) (hneg : ξ < 0) :
    regB g ξ = 1 / (2 * Real.sqrt (-ξ)) * ∫ v in ξ..0, g v / Real.sqrt (-v) := by
  have hI' : IsOpen (Neg.neg ⁻¹' I) := hI.preimage continuous_neg
  have hIc' : (Neg.neg ⁻¹' I).OrdConnected := ⟨fun x hx y hy z hz => hIc.out hy hx ⟨by
    simp only [mem_Icc] at hz; linarith, by simp only [mem_Icc] at hz; linarith⟩⟩
  have h0' : (0 : ℝ) ∈ Neg.neg ⁻¹' I := by simpa using h0
  have hd' : ∀ x ∈ Neg.neg ⁻¹' I, HasDerivAt (fun x => g (-x)) (-g' (-x)) x := fun x hx => by
    have := (hd (-x) hx).comp x (hasDerivAt_neg x)
    convert this using 1 <;> first | rfl | ring
  have hc'' : ContinuousOn (fun x => -g' (-x)) (Neg.neg ⁻¹' I) :=
    (hc'.comp continuous_neg.continuousOn fun x hx => hx).neg
  have := dlmf_2_8_17_pos hI' hIc' h0' hd' hc'' (ξ := -ξ) (by simpa using hξ) (by linarith)
  have hl : regB (fun x => g (-x)) (-ξ) = regB g ξ := by
    simp only [regB, regPhi, neg_mul, neg_neg]
  rw [hl] at this
  rw [this, show (∫ v in (0 : ℝ)..-ξ, g (-v) / Real.sqrt v) =
    ∫ v in ξ..0, g v / Real.sqrt (-v) by
      have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := -ξ)
        (fun w => g w / Real.sqrt (-w))
      simpa using this]

/-! ### 2.8.18: the coefficients `A_s`, `B_s` -/

/-- `B` from `A` by 2.8.17: `B = ∫_0^1 (ψA − A″)(ξσ²) dσ`. -/
noncomputable def caseIIBOf (ψ A : ℝ → ℝ) : ℝ → ℝ :=
  regB fun v => ψ v * A v - deriv (deriv A) v

/-- **DLMF 2.8.17–2.8.18**: `A₀ = 1`, `B_s` by 2.8.17, and
`A_{s+1} = −½ B_s′ + ½ ∫_{x₀}^{ξ} ψ B_s + c_s` (constants of integration arbitrary). -/
noncomputable def caseIIA (ψ : ℝ → ℝ) (x₀ : ℝ) (c : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | s + 1 => fun x => -(1 / 2) * deriv (caseIIBOf ψ (caseIIA ψ x₀ c s)) x +
      1 / 2 * (∫ t in x₀..x, ψ t * caseIIBOf ψ (caseIIA ψ x₀ c s) t) + c s

/-- `B_s` of 2.8.17. -/
noncomputable def caseIIB (ψ : ℝ → ℝ) (x₀ : ℝ) (c : ℕ → ℝ) (s : ℕ) : ℝ → ℝ :=
  caseIIBOf ψ (caseIIA ψ x₀ c s)

theorem caseIIBOf_smooth (hI : IsOpen I) (hIc : I.OrdConnected) (h0 : (0 : ℝ) ∈ I)
    {ψ A : ℝ → ℝ} (hψ : ContDiffOn ℝ ∞ ψ I) (hA : ContDiffOn ℝ ∞ A I) :
    ContDiffOn ℝ ∞ (fun v => ψ v * A v - deriv (deriv A) v) I ∧
      ContDiffOn ℝ ∞ (caseIIBOf ψ A) I := by
  have hg : ContDiffOn ℝ ∞ (fun v => ψ v * A v - deriv (deriv A) v) I :=
    (hψ.mul hA).sub ((hA.deriv_of_isOpen hI (m := ∞) (by simp)).deriv_of_isOpen hI (m := ∞)
      (by simp))
  exact ⟨hg, regPhi_smooth hI hIc h0 0 hg⟩

/-- **DLMF 2.8.17–2.8.18**: for `ψ` of class `C^∞` on `(α₁, α₂) ∋ 0, x₀`, all `A_s`, `B_s` are
`C^∞`, `B_s + 2ξ B_s′ = ψ A_s − A_s″` (2.8.17) and `2 A_{s+1}′ = −B_s″ + ψ B_s` (2.8.18). -/
theorem dlmf_2_8_18 (hI : IsOpen I) (hIc : I.OrdConnected) (h0 : (0 : ℝ) ∈ I) {ψ : ℝ → ℝ}
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (hψ : ContDiffOn ℝ ∞ ψ I) (c : ℕ → ℝ) (s : ℕ) :
    ContDiffOn ℝ ∞ (caseIIA ψ x₀ c s) I ∧ ContDiffOn ℝ ∞ (caseIIB ψ x₀ c s) I ∧
      (∀ x ∈ I, caseIIB ψ x₀ c s x + 2 * x * deriv (caseIIB ψ x₀ c s) x =
        ψ x * caseIIA ψ x₀ c s x - deriv (deriv (caseIIA ψ x₀ c s)) x) ∧
      ∀ x ∈ I, 2 * deriv (caseIIA ψ x₀ c (s + 1)) x =
        -deriv (deriv (caseIIB ψ x₀ c s)) x + ψ x * caseIIB ψ x₀ c s x := by
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hA : ∀ s, ContDiffOn ℝ ∞ (caseIIA ψ x₀ c s) I := by
    intro s
    induction s with
    | zero => exact contDiffOn_const
    | succ s ih =>
      have hB := (caseIIBOf_smooth hI hIc h0 hψ ih).2
      have hd : ContDiffOn ℝ ∞ (deriv (caseIIBOf ψ (caseIIA ψ x₀ c s))) I :=
        hB.deriv_of_isOpen hI (m := ∞) (by simp)
      have hprod : ContDiffOn ℝ ∞ (fun t => ψ t * caseIIBOf ψ (caseIIA ψ x₀ c s) t) I :=
        hψ.mul hB
      have hG : ContDiffOn ℝ ∞
          (fun x => ∫ t in x₀..x, ψ t * caseIIBOf ψ (caseIIA ψ x₀ c s) t) I := by
        rw [contDiffOn_infty_iff_deriv_of_isOpen hI]
        have hGd : ∀ x ∈ I, HasDerivAt
            (fun x => ∫ t in x₀..x, ψ t * caseIIBOf ψ (caseIIA ψ x₀ c s) t)
            (ψ x * caseIIBOf ψ (caseIIA ψ x₀ c s) x) x := fun x hx =>
          integral_hasDerivAt_right
            ((hprod.continuousOn.mono (hIc.uIcc_subset hx₀ hx)).intervalIntegrable)
            (hprod.continuousOn.stronglyMeasurableAtFilter hI x hx)
            (hprod.continuousOn.continuousAt (hI.mem_nhds hx))
        exact ⟨fun x hx => (hGd x hx).differentiableAt.differentiableWithinAt,
          hprod.congr fun x hx => (hGd x hx).deriv⟩
      exact ((contDiffOn_const.mul hd).add (contDiffOn_const.mul hG)).add contDiffOn_const
  obtain ⟨hg, hB⟩ := caseIIBOf_smooth hI hIc h0 hψ (hA s)
  refine ⟨hA s, hB, fun x hx => ?_, fun x hx => ?_⟩
  · have hgd : ContDiffOn ℝ ∞ (deriv fun v => ψ v * caseIIA ψ x₀ c s v -
        deriv (deriv (caseIIA ψ x₀ c s)) v) I := hg.deriv_of_isOpen hI (m := ∞) (by simp)
    exact regB_ode hI hIc h0 (fun v hv => ((hg.differentiableOn hne).differentiableAt
      (hI.mem_nhds hv)).hasDerivAt) hgd.continuousOn hx
  · have hd : ContDiffOn ℝ ∞ (deriv (caseIIB ψ x₀ c s)) I :=
      hB.deriv_of_isOpen hI (m := ∞) (by simp)
    have h1 : HasDerivAt (deriv (caseIIB ψ x₀ c s)) (deriv (deriv (caseIIB ψ x₀ c s)) x) x :=
      ((hd.differentiableOn hne).differentiableAt (hI.mem_nhds hx)).hasDerivAt
    have hprod : ContinuousOn (fun t => ψ t * caseIIB ψ x₀ c s t) I :=
      hψ.continuousOn.mul hB.continuousOn
    have h2 : HasDerivAt (fun x => ∫ t in x₀..x, ψ t * caseIIB ψ x₀ c s t)
        (ψ x * caseIIB ψ x₀ c s x) x :=
      integral_hasDerivAt_right ((hprod.mono (hIc.uIcc_subset hx₀ hx)).intervalIntegrable)
        (hprod.stronglyMeasurableAtFilter hI x hx) (hprod.continuousAt (hI.mem_nhds hx))
    have h3 : HasDerivAt (fun x => -(1 / 2) * deriv (caseIIB ψ x₀ c s) x +
        1 / 2 * (∫ t in x₀..x, ψ t * caseIIB ψ x₀ c s t) + c s)
        (-(1 / 2) * deriv (deriv (caseIIB ψ x₀ c s)) x + 1 / 2 * (ψ x * caseIIB ψ x₀ c s x))
        x := ((h1.const_mul (-(1 / 2))).add (h2.const_mul (1 / 2))).add_const (c s)
    rw [show caseIIA ψ x₀ c (s + 1) = fun x => -(1 / 2) * deriv (caseIIB ψ x₀ c s) x +
      1 / 2 * (∫ t in x₀..x, ψ t * caseIIB ψ x₀ c s t) + c s from rfl, h3.deriv]
    ring

/-! ### The formal expansions 2.8.15–2.8.16 -/

/-- Hypotheses on the coefficients for `n` terms: `A₀ = 1`, derivatives, and the relations
2.8.17 (`B_s + 2ξB_s′ = ψA_s − A_s″`) and 2.8.18 (`2A_{s+1}′ = −B_s″ + ψB_s`) for `s ≤ n − 2`. -/
structure CaseIIData (I : Set ℝ) (ψ : ℝ → ℝ) (A A' A'' B B' B'' : ℕ → ℝ → ℝ) (n : ℕ) :
    Prop where
  A_zero : ∀ x, A 0 x = 1
  A_deriv : ∀ s < n, ∀ x ∈ I, HasDerivAt (A s) (A' s x) x
  A'_deriv : ∀ s < n, ∀ x ∈ I, HasDerivAt (A' s) (A'' s x) x
  B_deriv : ∀ s, s + 1 < n → ∀ x ∈ I, HasDerivAt (B s) (B' s x) x
  B'_deriv : ∀ s, s + 1 < n → ∀ x ∈ I, HasDerivAt (B' s) (B'' s x) x
  Beq : ∀ s, s + 1 < n → ∀ x ∈ I, B s x + 2 * x * B' s x = ψ x * A s x - A'' s x
  Aeq : ∀ s, s + 1 < n → ∀ x ∈ I, 2 * A' (s + 1) x = -B'' s x + ψ x * B s x

/-- `∑_{s<n} A_s/u^{2s}`. -/
noncomputable def sumA (A : ℕ → ℝ → ℝ) (u : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ s ∈ Finset.range n, A s x / u ^ (2 * s)

/-- `∑_{s<n−1} B_s/u^{2s + 4/3}`. -/
noncomputable def sumB (B : ℕ → ℝ → ℝ) (u : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ s ∈ Finset.range (n - 1), B s x / (u ^ (2 * s) * u ^ (4 / 3 : ℝ))

theorem hasDerivAt_sumA {A A' : ℕ → ℝ → ℝ} {u : ℝ} {n : ℕ} {x : ℝ}
    (h : ∀ s < n, HasDerivAt (A s) (A' s x) x) : HasDerivAt (sumA A u n) (sumA A' u n x) x := by
  have := HasDerivAt.fun_sum (u := Finset.range n) (A := fun s y => A s y / u ^ (2 * s))
    (A' := fun s => A' s x / u ^ (2 * s)) fun s hs =>
      (h s (Finset.mem_range.mp hs)).div_const _
  exact this

theorem hasDerivAt_sumB {B B' : ℕ → ℝ → ℝ} {u : ℝ} {n : ℕ} {x : ℝ}
    (h : ∀ s, s + 1 < n → HasDerivAt (B s) (B' s x) x) :
    HasDerivAt (sumB B u n) (sumB B' u n x) x := by
  have := HasDerivAt.fun_sum (u := Finset.range (n - 1))
    (A := fun s y => B s y / (u ^ (2 * s) * u ^ (4 / 3 : ℝ)))
    (A' := fun s => B' s x / (u ^ (2 * s) * u ^ (4 / 3 : ℝ))) fun s hs =>
      (h s (by have := Finset.mem_range.mp hs; omega)).div_const _
  exact this

namespace CaseIIData

variable {ψ : ℝ → ℝ} {A A' A'' B B' B'' : ℕ → ℝ → ℝ} {n : ℕ}
  (D : CaseIIData I ψ A A' A'' B B' B'' n)
include D

/-- The coefficient of `Ai`: `P″ − ψP + u^{4/3}(Q + 2ξQ′) = u^{2−2n}(A″_{n−1} − ψA_{n−1})`. -/
theorem coeff_Ai {u : ℝ} (hu : 0 < u) (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ I) :
    sumA A'' u n x - ψ x * sumA A u n x +
        u ^ (4 / 3 : ℝ) * (sumB B u n x + 2 * x * sumB B' u n x) =
      (A'' (n - 1) x - ψ x * A (n - 1) x) / u ^ (2 * (n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hc : u ^ (4 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hu _).ne'
  simp only [sumA, sumB, Nat.add_sub_cancel, Finset.sum_range_succ]
  have hz : ∀ s ∈ Finset.range m, A'' s x / u ^ (2 * s) - ψ x * (A s x / u ^ (2 * s)) +
      (u ^ (4 / 3 : ℝ) * (B s x / (u ^ (2 * s) * u ^ (4 / 3 : ℝ))) +
        2 * x * (B' s x / (u ^ (2 * s) * u ^ (4 / 3 : ℝ))) * u ^ (4 / 3 : ℝ)) = 0 := by
    intro s hs
    have := D.Beq s (by have := Finset.mem_range.mp hs; omega) x hx
    have hus : u ^ (2 * s) ≠ 0 := pow_ne_zero _ hu.ne'
    field_simp
    linear_combination this
  have hsum := Finset.sum_eq_zero hz
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  have e1 : ∑ i ∈ Finset.range m, 2 * x * (B' i x / (u ^ (2 * i) * u ^ (4 / 3 : ℝ))) *
      u ^ (4 / 3 : ℝ) = u ^ (4 / 3 : ℝ) * (2 * x * ∑ i ∈ Finset.range m,
        B' i x / (u ^ (2 * i) * u ^ (4 / 3 : ℝ))) := by
    rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  linear_combination hsum

/-- The coefficient of `Ai′`: `Q″ − ψQ + 2u^{2/3}P′ = 0`. -/
theorem coeff_Ai' {u : ℝ} (hu : 0 < u) (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ I) :
    sumB B'' u n x - ψ x * sumB B u n x + 2 * u ^ (2 / 3 : ℝ) * sumA A' u n x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hA0 : A' 0 x = 0 := by
    have h := D.A_deriv 0 (by omega) x hx
    rw [show A 0 = fun _ => 1 from funext D.A_zero] at h
    exact h.unique (hasDerivAt_const x 1)
  have hc : (u ^ (2 / 3 : ℝ)) ^ 3 = u ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num
  have h43 : u ^ (4 / 3 : ℝ) = (u ^ (2 / 3 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num
  have hcp : 0 < u ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hu _
  simp only [sumA, sumB, Nat.add_sub_cancel]
  rw [Finset.sum_range_succ', hA0, zero_div, add_zero, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun s hs => ?_
  have := D.Aeq s (by have := Finset.mem_range.mp hs; omega) x hx
  have hus : u ^ (2 * s) ≠ 0 := pow_ne_zero _ hu.ne'
  rw [h43, show 2 * (s + 1) = 2 * s + 2 by ring, pow_add, ← hc]
  field_simp
  linear_combination this

/-- **DLMF 2.8.15–2.8.16** as formal expansions: for any solution `(𝒜, 𝒜′)` of Airy's equation
`𝒜″(t) = t 𝒜(t)` (e.g. `Ai` or `Bi`), the truncated expansion
`W = 𝒜(u^{2/3}ξ) ∑_{s<n} A_s/u^{2s} + 𝒜′(u^{2/3}ξ) ∑_{s<n−1} B_s/u^{2s+4/3}` satisfies
`W″ = (u²ξ + ψ) W + u^{2−2n}(A″_{n−1} − ψA_{n−1}) 𝒜(u^{2/3}ξ)`, so the coefficients 2.8.17–2.8.18
make every term but the last cancel. -/
theorem dlmf_2_8_15_formal (hn : 1 ≤ n) {Ai Ai' : ℝ → ℝ} (hA1 : ∀ t, HasDerivAt Ai (Ai' t) t)
    (hA2 : ∀ t, HasDerivAt Ai' (t * Ai t) t) {u : ℝ} (hu : 0 < u) {x : ℝ} (hx : x ∈ I) :
    HasDerivAt (fun y => Ai (u ^ (2 / 3 : ℝ) * y) * sumA A u n y +
        Ai' (u ^ (2 / 3 : ℝ) * y) * sumB B u n y)
      (Ai (u ^ (2 / 3 : ℝ) * x) * (sumA A' u n x + u ^ (4 / 3 : ℝ) * x * sumB B u n x) +
        Ai' (u ^ (2 / 3 : ℝ) * x) * (u ^ (2 / 3 : ℝ) * sumA A u n x + sumB B' u n x)) x ∧
    HasDerivAt (fun y => Ai (u ^ (2 / 3 : ℝ) * y) *
        (sumA A' u n y + u ^ (4 / 3 : ℝ) * y * sumB B u n y) +
        Ai' (u ^ (2 / 3 : ℝ) * y) * (u ^ (2 / 3 : ℝ) * sumA A u n y + sumB B' u n y))
      ((u ^ 2 * x + ψ x) * (Ai (u ^ (2 / 3 : ℝ) * x) * sumA A u n x +
        Ai' (u ^ (2 / 3 : ℝ) * x) * sumB B u n x) +
        (A'' (n - 1) x - ψ x * A (n - 1) x) / u ^ (2 * (n - 1)) * Ai (u ^ (2 / 3 : ℝ) * x)) x := by
  set c := u ^ (2 / 3 : ℝ) with hc_def
  have hcp : 0 < c := Real.rpow_pos_of_pos hu _
  have hc3 : c ^ 3 = u ^ 2 := by
    rw [hc_def, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num
  have h43 : u ^ (4 / 3 : ℝ) = c ^ 2 := by
    rw [hc_def, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num
  have hl : HasDerivAt (fun y : ℝ => c * y) c x :=
    ((hasDerivAt_id x).const_mul c).congr_deriv (mul_one c)
  have hAi := (hA1 (c * x)).comp x hl
  have hAi' := (hA2 (c * x)).comp x hl
  have hP := hasDerivAt_sumA (u := u) fun s hs => D.A_deriv s hs x hx
  have hP' := hasDerivAt_sumA (u := u) fun s hs => D.A'_deriv s hs x hx
  have hQ := hasDerivAt_sumB (u := u) fun s hs => D.B_deriv s hs x hx
  have hQ' := hasDerivAt_sumB (u := u) fun s hs => D.B'_deriv s hs x hx
  constructor
  · refine ((hAi.mul hP).add (hAi'.mul hQ)).congr_deriv ?_
    simp only [Function.comp_apply]
    rw [h43]
    ring
  · have hd := (hAi.mul (hP'.add ((((hasDerivAt_id x).const_mul (u ^ (4 / 3 : ℝ))).mul hQ)))).add
      (hAi'.mul ((hP.const_mul c).add hQ'))
    refine hd.congr_deriv ?_
    have e1 := D.coeff_Ai hu hn hx
    have e2 := D.coeff_Ai' hu hn hx
    simp only [Function.comp_apply, id, Pi.add_apply, Pi.mul_apply] at hd ⊢
    rw [h43] at e1 ⊢
    rw [← hc_def] at e2
    linear_combination Ai (c * x) * e1 + Ai' (c * x) * e2 + (Ai (c * x) * x * sumA A u n x +
      Ai' (c * x) * x * sumB B u n x) * hc3

end CaseIIData

/-! ### 2.8.19–2.8.21: the envelopes of `Ai`, `Bi` -/

/-- **DLMF 2.8.20–2.8.21**: `envAi(x) = (Ai² + Bi²)^{1/2}` for `x ≤ c`, `√2 Ai(x)` for `x ≥ c`, `c`
the root 2.8.19 of `Ai = Bi` of smallest absolute value. -/
noncomputable def envAi (Ai Bi : ℝ → ℝ) (c x : ℝ) : ℝ :=
  if x ≤ c then Real.sqrt (Ai x ^ 2 + Bi x ^ 2) else Real.sqrt 2 * Ai x

/-- **DLMF 2.8.20–2.8.21**: `envBi(x) = (Ai² + Bi²)^{1/2}` for `x ≤ c`, `√2 Bi(x)` for `x ≥ c`. -/
noncomputable def envBi (Ai Bi : ℝ → ℝ) (c x : ℝ) : ℝ :=
  if x ≤ c then Real.sqrt (Ai x ^ 2 + Bi x ^ 2) else Real.sqrt 2 * Bi x

/-- **DLMF §2.8(iii)**: "these envelopes are continuous functions of `x`" — given that `c` is a
root of 2.8.19 (`Ai(c) = Bi(c)`) at which `Ai(c) ≥ 0`. -/
theorem envAi_envBi_continuous {Ai Bi : ℝ → ℝ} (hA : Continuous Ai) (hB : Continuous Bi) {c : ℝ}
    (hc : Ai c = Bi c) (hpos : 0 ≤ Ai c) :
    Continuous (envAi Ai Bi c) ∧ Continuous (envBi Ai Bi c) := by
  have key : Real.sqrt (Ai c ^ 2 + Bi c ^ 2) = Real.sqrt 2 * Ai c := by
    rw [← hc, show Ai c ^ 2 + Ai c ^ 2 = 2 * Ai c ^ 2 by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq hpos]
  have hs : Continuous fun x => Real.sqrt (Ai x ^ 2 + Bi x ^ 2) :=
    Real.continuous_sqrt.comp ((hA.pow 2).add (hB.pow 2))
  constructor
  · exact hs.if_le (continuous_const.mul hA) continuous_id continuous_const
      fun x hx => by rw [hx]; exact key
  · exact hs.if_le (continuous_const.mul hB) continuous_id continuous_const
      fun x hx => by rw [hx, key, hc]

theorem abs_le_envAi {Ai Bi : ℝ → ℝ} {c x : ℝ} (hx : x ≤ c) :
    |Ai x| ≤ envAi Ai Bi c x ∧ |Bi x| ≤ envBi Ai Bi c x := by
  simp only [envAi, envBi, hx, ↓reduceIte]
  constructor
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (Bi x)])
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (Ai x)])

end Azurite.DLMF
