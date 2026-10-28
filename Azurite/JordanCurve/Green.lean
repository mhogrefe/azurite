/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.JordanCurve.WindingNumber
import Azurite.JordanCurve.CauchyPompeiu
import Azurite.JordanCurve.Interior
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Green's theorem for the winding number

For a closed piecewise-`C¹` curve `c` in `ℂ` (`ClosedPiecewiseC1`) and a `C¹` function
`g : ℂ → ℂ`, `∮_c g dz = 2i ∫ ∂̄g(p) · W_c(p) dA(p)` where `W_c` is the winding number
(`ClosedPiecewiseC1.contourIntegral_eq_integral_dbar` for compactly supported `g`,
`contourIntegral_eq_integral_dbar'` in general via a bump-function cutoff).  Proof: by the
Cauchy–Pompeiu formula, `g(c(t)) c'(t) = −(1/π) ∫ ∂̄g(p) c'(t)/(p − c(t)) dA(p)`; the kernel
is integrable on `[tᵢ, tᵢ₊₁] × ℂ` (`integrable_kernel`: `‖p − c(t)‖⁻¹` is integrable on balls,
uniformly in `t`), so Fubini applies, and `∫ c'(t)/(c(t) − p) dt = 2πi W_c(p)` for `p` off the
curve, which is Lebesgue-null (`volume_curve`).

Real form (`lineIntegralRe_eq_integral`): for `C¹` functions `u v : ℂ → ℝ`,
`∮_c u dx + v dy = ∫ (∂v/∂x − ∂u/∂y)(p) · W_c(p) dA(p)`, the real part of the complex identity
for `g = u − i v`.  Since `W_c = 0` on the unbounded complementary components, for a
*positively oriented* curve (`W_c = 1` on the interior `jordanInterior c a b`, the union of the
bounded components) this is Green's theorem
`∮_c u dx + v dy = ∬_{interior} (∂v/∂x − ∂u/∂y) dA`
(`lineIntegralRe_eq_setIntegral_jordanInterior`); the DLMF 1.6.44 statement in `ℝ × ℝ` is
`Azurite.DLMF.dlmf_1_6_44` (§1.6).
-/

namespace Azurite.JordanCurve

open Set Filter Topology MeasureTheory Complex
open scoped Real

/-- `p ↦ ‖p − w‖⁻¹` is integrable on balls around `w`. -/
theorem integrableOn_inv_norm_sub (w : ℂ) (r : ℝ) :
    IntegrableOn (fun p : ℂ => ‖p - w‖⁻¹) (Metric.ball w r) := by
  have h0 : IntegrableOn (fun p : ℂ => ‖p‖⁻¹) (Metric.ball 0 r) := by
    refine integrableOn_ball_of_norm_le_rpow (f := fun p : ℂ => ‖p‖⁻¹) (C := 1) (α := 1)
      (by rw [Complex.finrank_real_complex]; norm_num)
      (by rw [Complex.finrank_real_complex]; norm_num)
      (ae_of_all _ fun p => by simp [Real.rpow_neg_one])
      continuous_norm.measurable.inv.aestronglyMeasurable
  have h1 := (h0.integrable_indicator Metric.isOpen_ball.measurableSet).comp_sub_right w
  rw [← integrable_indicator_iff Metric.isOpen_ball.measurableSet]
  refine h1.congr (ae_of_all _ fun p => ?_)
  simp only [indicator, Metric.mem_ball, dist_eq_norm, sub_zero]

/-- Translation invariance of the kernel integral over balls. -/
theorem integral_ball_inv_norm_sub (w : ℂ) (r : ℝ) :
    ∫ p in Metric.ball w r, ‖p - w‖⁻¹ = ∫ q in Metric.ball (0 : ℂ) r, ‖q‖⁻¹ := by
  rw [← integral_indicator Metric.isOpen_ball.measurableSet,
    ← integral_indicator Metric.isOpen_ball.measurableSet,
    ← integral_sub_right_eq_self (fun q => (Metric.ball (0 : ℂ) r).indicator (fun q => ‖q‖⁻¹) q) w]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [indicator, Metric.mem_ball, dist_eq_norm, sub_zero]

/-- The planar line integral `∫_c u dx + v dy` along a path `c : ℝ → ℂ`, `x = Re c`,
`y = Im c`. -/
noncomputable def lineIntegralRe (u v : ℂ → ℝ) (c : ℝ → ℂ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, (u (c t) * deriv (fun s => (c s).re) t + v (c t) * deriv (fun s => (c s).im) t)

namespace ClosedPiecewiseC1

variable {c : ℝ → ℂ} {a b : ℝ} (P : ClosedPiecewiseC1 c a b)

/-- Every parameter value lies in some piece. -/
theorem exists_piece {s : ℝ} (hs : s ∈ Icc a b) (hn : 0 < P.n) :
    ∃ i < P.n, s ∈ Icc (P.t i) (P.t (i + 1)) := by
  classical
  have hex : ∃ i, s ≤ P.t (i + 1) := ⟨P.n - 1, by
    rw [Nat.sub_add_cancel hn, P.last]; exact hs.2⟩
  refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · have := Nat.find_min' hex (show s ≤ P.t (P.n - 1 + 1) by
      rw [Nat.sub_add_cancel hn, P.last]; exact hs.2)
    omega
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, P.first]; exact hs.1
    · have := Nat.find_min hex (Nat.sub_lt hpos one_pos)
      rw [Nat.sub_one_add_one hpos.ne'] at this
      exact (not_le.mp this).le

/-- The curve has zero area: it is a finite union of images of segments under `C¹` maps. -/
theorem volume_curve : volume P.curve = 0 := by
  rcases Nat.eq_zero_or_pos P.n with hn | hn
  · have hab : a = b := by
      have h1 := P.first
      have h2 := P.last
      rw [hn] at h2
      exact h1.symm.trans h2
    have : P.curve = {c a} := by
      rw [curve, ← hab, Icc_self, image_singleton]
    rw [this]
    exact measure_singleton _
  have hcover : P.curve ⊆ ⋃ i ∈ Finset.range P.n, P.g i '' Icc (P.t i) (P.t (i + 1)) := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨i, hi, hsi⟩ := P.exists_piece hs hn
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr hi, s, hsi, (P.eqOn i hi hsi).symm⟩
  refine measure_mono_null hcover ((measure_biUnion_null_iff (Finset.range P.n).countable_toSet).mpr
    fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  set S : Set ℂ := {w | w.re ∈ Icc (P.t i) (P.t (i + 1)) ∧ w.im = 0} with hS
  have hS0 : volume S = 0 := by
    have : S = Complex.measurableEquivRealProd ⁻¹' (Icc (P.t i) (P.t (i + 1)) ×ˢ {0}) := by
      ext w; simp [hS, Complex.measurableEquivRealProd_apply]
    rw [this, Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Icc.prod (measurableSet_singleton 0)).nullMeasurableSet,
      Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
  have himg : P.g i '' Icc (P.t i) (P.t (i + 1)) = (fun w : ℂ => P.g i w.re) '' S := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(s : ℂ), ⟨by simpa using hs, ofReal_im s⟩, by simp⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.re, hw.1, rfl⟩
  rw [himg]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (((P.contDiff i hi').differentiable one_ne_zero).comp
      Complex.reCLM.differentiable).differentiableOn
    hS0

/-- `∂̄g` is continuous with compact support for `g` `C¹` with compact support. -/
theorem dbar_continuous_hasCompactSupport {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hsupp : HasCompactSupport g) : Continuous (dbar g) ∧ HasCompactSupport (dbar g) := by
  have hA := hg.continuous_fderiv one_ne_zero
  refine ⟨((hA.clm_apply continuous_const).add (continuous_const.mul
    (hA.clm_apply continuous_const))).div_const 2, (hsupp.fderiv ℝ).mono fun p hp => ?_⟩
  simp only [Function.mem_support] at hp ⊢
  intro h
  apply hp
  simp [dbar, h]

/-- The Fubini kernel `(s, p) ↦ ∂̄g(p) · g_i'(s)/(g_i(s) − p)` of one piece is integrable on
`Ioc (t i) (t (i + 1)) × ℂ`. -/
theorem integrable_kernel {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) (hsupp : HasCompactSupport g)
    {i : ℕ} (hi : i < P.n) :
    Integrable (fun q : ℝ × ℂ => dbar g q.2 * ((P.g i q.1 - q.2)⁻¹ * deriv (P.g i) q.1))
      ((volume.restrict (Ioc (P.t i) (P.t (i + 1)))).prod volume) := by
  obtain ⟨hdc, hds⟩ := dbar_continuous_hasCompactSupport hg hsupp
  obtain ⟨R₀', hR₀'⟩ := hds.isCompact.isBounded.subset_closedBall 0
  set R₀ := max R₀' 0 with hR₀def
  have hR₀ : tsupport (dbar g) ⊆ Metric.closedBall 0 R₀ :=
    hR₀'.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hzero : ∀ p, R₀ < ‖p‖ → dbar g p = 0 := fun p hp =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hR₀ h
      rw [mem_closedBall_zero_iff] at this
      linarith
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R₀).exists_bound_of_continuousOn hdc.continuousOn
  set M' := max M 0 with hM'def
  have hMg : ∀ p, ‖dbar g p‖ ≤ M' := by
    intro p
    by_cases hp : ‖p‖ ≤ R₀
    · exact (hM p (mem_closedBall_zero_iff.mpr hp)).trans (le_max_left _ _)
    · rw [hzero p (not_le.mp hp), norm_zero]
      exact le_max_right _ _
  have hgi := P.contDiff i hi
  have hderiv : Continuous (deriv (P.g i)) := hgi.continuous_deriv le_rfl
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (P.t i) (P.t (i + 1))) hderiv.continuousOn
  set L' := max L 0 with hL'def
  have hL' : ∀ s ∈ Icc (P.t i) (P.t (i + 1)), ‖deriv (P.g i) s‖ ≤ L' := fun s hs =>
    (hL s hs).trans (le_max_left _ _)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (P.t i) (P.t (i + 1))) hgi.continuous.continuousOn
  set ρ := R₀ + max B 0 + 1 with hρdef
  set C := ∫ q in Metric.ball (0 : ℂ) ρ, ‖q‖⁻¹ with hCdef
  -- pointwise domination
  have hbound : ∀ s ∈ Icc (P.t i) (P.t (i + 1)), ∀ p : ℂ,
      ‖dbar g p * ((P.g i s - p)⁻¹ * deriv (P.g i) s)‖ ≤
        M' * L' * (Metric.ball (P.g i s) ρ).indicator (fun p => ‖p - P.g i s‖⁻¹) p := by
    intro s hs p
    by_cases hp : p ∈ Metric.ball (P.g i s) ρ
    · rw [indicator_of_mem hp, norm_mul, norm_mul, norm_inv, norm_sub_rev]
      have h3 : 0 ≤ ‖p - P.g i s‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
      calc ‖dbar g p‖ * (‖p - P.g i s‖⁻¹ * ‖deriv (P.g i) s‖)
          ≤ M' * (‖p - P.g i s‖⁻¹ * L') :=
            mul_le_mul (hMg p) (mul_le_mul_of_nonneg_left (hL' s hs) h3)
              (mul_nonneg h3 (norm_nonneg _)) (le_max_right M 0)
        _ = M' * L' * ‖p - P.g i s‖⁻¹ := by ring
    · rw [indicator_of_notMem hp, mul_zero]
      have h1 : ‖p - P.g i s‖ ≤ ‖p‖ + ‖P.g i s‖ := norm_sub_le _ _
      have h2 := hB s hs
      have h4 : max B 0 ≥ B := le_max_left _ _
      rw [Metric.mem_ball, dist_eq_norm, not_lt] at hp
      have : dbar g p = 0 := hzero p (by linarith)
      simp [this]
  -- the dominating function is integrable, with integral `M' * L' * C`
  have hD : ∀ w : ℂ, Integrable
      (fun p => M' * L' * (Metric.ball w ρ).indicator (fun p => ‖p - w‖⁻¹) p) := fun w =>
    ((integrableOn_inv_norm_sub w ρ).integrable_indicator
      Metric.isOpen_ball.measurableSet).const_mul (M' * L')
  have hDint : ∀ w : ℂ,
      ∫ p, M' * L' * (Metric.ball w ρ).indicator (fun p => ‖p - w‖⁻¹) p = M' * L' * C := by
    intro w
    rw [integral_const_mul, integral_indicator Metric.isOpen_ball.measurableSet,
      integral_ball_inv_norm_sub]
  -- measurability
  have hmeas : AEStronglyMeasurable
      (fun q : ℝ × ℂ => dbar g q.2 * ((P.g i q.1 - q.2)⁻¹ * deriv (P.g i) q.1))
      ((volume.restrict (Ioc (P.t i) (P.t (i + 1)))).prod volume) :=
    ((hdc.measurable.comp measurable_snd).mul
      ((((hgi.continuous.comp continuous_fst).sub continuous_snd).measurable.inv).mul
        (hderiv.measurable.comp measurable_fst))).aestronglyMeasurable
  refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs' : s ∈ Icc (P.t i) (P.t (i + 1)) := Ioc_subset_Icc_self hs
    refine (hD (P.g i s)).mono' ?_ (ae_of_all _ (hbound s hs'))
    exact (hdc.measurable.mul
      (((measurable_const.sub measurable_id).inv).mul_const _)).aestronglyMeasurable
  · refine Integrable.of_bound hmeas.norm.integral_prod_right' (M' * L' * C) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs' : s ∈ Icc (P.t i) (P.t (i + 1)) := Ioc_subset_Icc_self hs
    rw [Real.norm_of_nonneg (integral_nonneg fun p => norm_nonneg _), ← hDint (P.g i s)]
    exact integral_mono_of_nonneg (ae_of_all _ fun p => norm_nonneg _) (hD (P.g i s))
      (ae_of_all _ (hbound s hs'))

/-- Each piece's contribution `p ↦ ∂̄g(p) ∫ gᵢ'(s)/(gᵢ(s) − p) ds` is integrable. -/
theorem integrable_dbar_mul_pieceIntegral {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hsupp : HasCompactSupport g) {i : ℕ} (hi : i < P.n) :
    Integrable (fun p => dbar g p *
      ∫ s in P.t i..P.t (i + 1), (P.g i s - p)⁻¹ * deriv (P.g i) s) := by
  have hle : P.t i ≤ P.t (i + 1) := (P.lt i hi).le
  refine ((P.integrable_kernel hg hsupp hi).integral_prod_right).congr
    (ae_of_all _ fun p => ?_)
  simp only
  rw [integral_const_mul, intervalIntegral.integral_of_le hle]

/-- `p ↦ ∂̄g(p) W(p)` is integrable for `g` `C¹` with compact support. -/
theorem integrable_dbar_mul_windingNumber {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hsupp : HasCompactSupport g) :
    Integrable (fun p => dbar g p * (P.windingNumber p : ℂ)) := by
  have hae : ∀ᵐ p : ℂ, p ∉ P.curve := measure_eq_zero_iff_ae_notMem.mp P.volume_curve
  have h1 : Integrable (fun p => dbar g p * P.contourIntegral (fun z => (z - p)⁻¹)) :=
    (integrable_finsetSum _ fun i hi =>
      P.integrable_dbar_mul_pieceIntegral hg hsupp (Finset.mem_range.mp hi)).congr
      (ae_of_all _ fun p => by simp only [contourIntegral, Finset.mul_sum])
  have h2 : Integrable (fun p => dbar g p * (2 * π * I * (P.windingNumber p : ℂ))) :=
    h1.congr (hae.mono fun p hp => by simp only; rw [P.contourIntegral_inv_eq hp])
  refine (h2.const_mul (2 * π * I)⁻¹).congr (ae_of_all _ fun p => ?_)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only
  field_simp

/-- **Green's theorem for the winding number** (complex form): for a closed piecewise-`C¹`
curve and a `C¹` function `g` with compact support,
`∮ g dz = 2i ∫ ∂̄g(p) · W(p) dA(p)`. -/
theorem contourIntegral_eq_integral_dbar {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hsupp : HasCompactSupport g) :
    P.contourIntegral g = 2 * I * ∫ p, dbar g p * (P.windingNumber p : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpiece : ∀ i < P.n, ∫ s in P.t i..P.t (i + 1), g (P.g i s) * deriv (P.g i) s =
      (1 / π : ℂ) * ∫ p, dbar g p *
        ∫ s in P.t i..P.t (i + 1), (P.g i s - p)⁻¹ * deriv (P.g i) s := by
    intro i hi
    have hK := P.integrable_kernel hg hsupp hi
    have hle : P.t i ≤ P.t (i + 1) := (P.lt i hi).le
    have hpt : ∀ s, g (P.g i s) * deriv (P.g i) s =
        (1 / π : ℂ) * ∫ p, dbar g p * ((P.g i s - p)⁻¹ * deriv (P.g i) s) := by
      intro s
      have hcp := cauchyPompeiu hg hsupp (P.g i s)
      have : ∫ p, dbar g p * ((P.g i s - p)⁻¹ * deriv (P.g i) s) =
          ∫ p, (-(deriv (P.g i) s)) * (dbar g p / (p - P.g i s)) := by
        refine integral_congr_ae (ae_of_all _ fun p => ?_)
        simp only
        rw [← neg_sub, inv_neg]; ring
      rw [this, integral_const_mul, hcp]
      field_simp
    calc ∫ s in P.t i..P.t (i + 1), g (P.g i s) * deriv (P.g i) s
        = ∫ s in P.t i..P.t (i + 1),
            (1 / π : ℂ) * ∫ p, dbar g p * ((P.g i s - p)⁻¹ * deriv (P.g i) s) := by
          rw [show (fun s => g (P.g i s) * deriv (P.g i) s) = fun s =>
            (1 / π : ℂ) * ∫ p, dbar g p * ((P.g i s - p)⁻¹ * deriv (P.g i) s) from funext hpt]
      _ = (1 / π : ℂ) * ∫ s in Ioc (P.t i) (P.t (i + 1)),
            ∫ p, dbar g p * ((P.g i s - p)⁻¹ * deriv (P.g i) s) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hle]
      _ = (1 / π : ℂ) * ∫ p, ∫ s in Ioc (P.t i) (P.t (i + 1)),
            dbar g p * ((P.g i s - p)⁻¹ * deriv (P.g i) s) := by
          rw [integral_integral_swap
            (f := fun s p => dbar g p * ((P.g i s - p)⁻¹ * deriv (P.g i) s)) hK]
      _ = _ := by
          congr 1
          refine integral_congr_ae (ae_of_all _ fun p => ?_)
          simp only
          rw [integral_const_mul, intervalIntegral.integral_of_le hle]
  have hae : ∀ᵐ p : ℂ, p ∉ P.curve := measure_eq_zero_iff_ae_notMem.mp P.volume_curve
  calc P.contourIntegral g
      = ∑ i ∈ Finset.range P.n, (1 / π : ℂ) * ∫ p, dbar g p *
          ∫ s in P.t i..P.t (i + 1), (P.g i s - p)⁻¹ * deriv (P.g i) s :=
        Finset.sum_congr rfl fun i hi => hpiece i (Finset.mem_range.mp hi)
    _ = (1 / π : ℂ) * ∫ p, dbar g p * P.contourIntegral (fun z => (z - p)⁻¹) := by
        rw [← Finset.mul_sum, ← integral_finsetSum _ fun i hi =>
          P.integrable_dbar_mul_pieceIntegral hg hsupp (Finset.mem_range.mp hi)]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun p => ?_)
        simp only [contourIntegral, Finset.mul_sum]
    _ = (1 / π : ℂ) * ∫ p, dbar g p * (2 * π * I * (P.windingNumber p : ℂ)) := by
        congr 1
        refine integral_congr_ae (hae.mono fun p hp => ?_)
        simp only
        rw [P.contourIntegral_inv_eq hp]
    _ = 2 * I * ∫ p, dbar g p * (P.windingNumber p : ℂ) := by
        rw [← integral_const_mul, ← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun p => ?_)
        field_simp

/-- Cutting off a `C¹` function by a bump function equal to `1` on a ball containing the curve
and the support of the winding number changes neither `∮ g dz` nor `∂̄g · W`. -/
theorem exists_cutoff {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) :
    ∃ h : ℂ → ℂ, ContDiff ℝ 1 h ∧ HasCompactSupport h ∧
      P.contourIntegral h = P.contourIntegral g ∧
      ∀ p, dbar h p * (P.windingNumber p : ℂ) = dbar g p * (P.windingNumber p : ℂ) := by
  obtain ⟨R₁, hR₁⟩ := P.exists_forall_windingNumber_eq_zero
  obtain ⟨R₂, hR₂⟩ := P.isCompact_curve.isBounded.subset_closedBall 0
  set R := max (max R₁ R₂) 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR1 : R₁ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hR2 : R₂ ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  let φ : ContDiffBump (0 : ℂ) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  refine ⟨fun z => (φ z : ℂ) * g z, (ofRealCLM.contDiff.comp φ.contDiff).mul hg,
    (φ.hasCompactSupport.comp_left ofReal_zero).mul_right, ?_, ?_⟩
  · unfold contourIntegral
    refine Finset.sum_congr rfl fun i hi => intervalIntegral.integral_congr fun s hs => ?_
    have hi' := Finset.mem_range.mp hi
    rw [uIcc_of_le (P.lt i hi').le] at hs
    have hmem : P.g i s ∈ Metric.closedBall (0 : ℂ) φ.rIn := by
      have := hR₂ (P.mem_curve_of_mem_piece hi' hs)
      rw [mem_closedBall_zero_iff] at this ⊢
      show ‖P.g i s‖ ≤ R + 1
      linarith
    simp only [φ.one_of_mem_closedBall hmem, ofReal_one, one_mul]
  · intro p
    by_cases hp : ‖p‖ ≤ R
    · have hball : p ∈ Metric.ball (0 : ℂ) φ.rIn := by
        rw [mem_ball_zero_iff]
        show ‖p‖ < R + 1
        linarith
      have heq : (fun z => (φ z : ℂ) * g z) =ᶠ[𝓝 p] g :=
        (φ.eventuallyEq_one_of_mem_ball hball).mono fun z hz => by
          simp only [hz, Pi.one_apply, ofReal_one, one_mul]
      simp only [dbar, heq.fderiv_eq]
    · rw [hR₁ p (by linarith [not_le.mp hp])]
      simp

/-- **Green's theorem for the winding number** (complex form, no support hypothesis). -/
theorem contourIntegral_eq_integral_dbar' {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) :
    P.contourIntegral g = 2 * I * ∫ p, dbar g p * (P.windingNumber p : ℂ) := by
  obtain ⟨h, hh, hhs, hci, hd⟩ := P.exists_cutoff hg
  rw [← hci, P.contourIntegral_eq_integral_dbar hh hhs]
  congr 1
  exact integral_congr_ae (ae_of_all _ hd)

/-- `p ↦ ∂̄g(p) W(p)` is integrable for any `C¹` function `g`. -/
theorem integrable_dbar_mul_windingNumber' {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) :
    Integrable (fun p => dbar g p * (P.windingNumber p : ℂ)) := by
  obtain ⟨h, hh, hhs, -, hd⟩ := P.exists_cutoff hg
  exact (P.integrable_dbar_mul_windingNumber hh hhs).congr (ae_of_all _ hd)

/-! ### Real form -/

/-- The real derivative of `u − i v` in the direction `w`. -/
theorem fderiv_ofReal_sub_I_mul {u v : ℂ → ℝ} (hu : Differentiable ℝ u)
    (hv : Differentiable ℝ v) (p w : ℂ) :
    fderiv ℝ (fun z => (u z : ℂ) - I * (v z : ℂ)) p w =
      (fderiv ℝ u p w : ℂ) - I * (fderiv ℝ v p w : ℂ) := by
  have h1 : HasFDerivAt (fun z => (u z : ℂ)) (ofRealCLM.comp (fderiv ℝ u p)) p :=
    ofRealCLM.hasFDerivAt.comp p (hu p).hasFDerivAt
  have h2 : HasFDerivAt (fun z => I * (v z : ℂ)) ((I • ofRealCLM).comp (fderiv ℝ v p)) p :=
    (I • ofRealCLM).hasFDerivAt.comp p (hv p).hasFDerivAt
  have h : HasFDerivAt (fun z => (u z : ℂ) - I * (v z : ℂ))
      (ofRealCLM.comp (fderiv ℝ u p) - (I • ofRealCLM).comp (fderiv ℝ v p)) p := h1.sub h2
  rw [h.fderiv]
  simp

/-- The real part of `2i ∂̄(u − i v) W` is `(∂ₓv − ∂_y u) W`. -/
theorem re_two_I_mul_dbar {u v : ℂ → ℝ} (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (p : ℂ) (W : ℤ) :
    (2 * I * (dbar (fun z => (u z : ℂ) - I * (v z : ℂ)) p * (W : ℂ))).re =
      (fderiv ℝ v p 1 - fderiv ℝ u p I) * (W : ℝ) := by
  rw [dbar, fderiv_ofReal_sub_I_mul hu hv, fderiv_ofReal_sub_I_mul hu hv]
  simp
  ring

/-- On the open piece `(tᵢ, tᵢ₊₁)` the path agrees with `gᵢ`, as do the derivatives of its
real and imaginary parts. -/
theorem eq_and_deriv_re_im_eq {i : ℕ} (hi : i < P.n) {x : ℝ}
    (hx : x ∈ Ioo (P.t i) (P.t (i + 1))) :
    c x = P.g i x ∧ deriv (fun s => (c s).re) x = (deriv (P.g i) x).re ∧
      deriv (fun s => (c s).im) x = (deriv (P.g i) x).im := by
  have hd : Differentiable ℝ (P.g i) := (P.contDiff i hi).differentiable one_ne_zero
  have hcg : c =ᶠ[𝓝 x] P.g i :=
    eventuallyEq_of_mem (Icc_mem_nhds hx.1 hx.2) (P.eqOn i hi)
  refine ⟨hcg.eq_of_nhds, ?_, ?_⟩
  · have hcg' : (fun s => (c s).re) =ᶠ[𝓝 x] fun s => (P.g i s).re :=
      hcg.mono fun s hs => by simp only [hs]
    rw [hcg'.deriv_eq]
    have := (reCLM.hasFDerivAt.comp_hasDerivAt x (hd x).hasDerivAt).deriv
    simpa [Function.comp_def] using this
  · have hcg' : (fun s => (c s).im) =ᶠ[𝓝 x] fun s => (P.g i s).im :=
      hcg.mono fun s hs => by simp only [hs]
    rw [hcg'.deriv_eq]
    have := (imCLM.hasFDerivAt.comp_hasDerivAt x (hd x).hasDerivAt).deriv
    simpa [Function.comp_def] using this

/-- Each piece of the real line integral equals the real part of the complex piece. -/
theorem lineIntegralRe_piece {u v : ℂ → ℝ} {i : ℕ} (hi : i < P.n) :
    ∫ t in P.t i..P.t (i + 1), (u (c t) * deriv (fun s => (c s).re) t +
        v (c t) * deriv (fun s => (c s).im) t) =
      ∫ t in P.t i..P.t (i + 1), (u (P.g i t) * (deriv (P.g i) t).re +
        v (P.g i t) * (deriv (P.g i) t).im) := by
  have hle : P.t i ≤ P.t (i + 1) := (P.lt i hi).le
  rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  obtain ⟨h0, hre, him⟩ := P.eq_and_deriv_re_im_eq hi hx
  simp only [hre, him, h0]

/-- The real-form integrand of each piece is continuous. -/
theorem continuous_piece_integrand {u v : ℂ → ℝ} (hu : Continuous u) (hv : Continuous v)
    {i : ℕ} (hi : i < P.n) :
    Continuous fun t => u (P.g i t) * (deriv (P.g i) t).re +
      v (P.g i t) * (deriv (P.g i) t).im := by
  have hgi := P.contDiff i hi
  have hd := hgi.continuous_deriv le_rfl
  exact ((hu.comp hgi.continuous).mul (continuous_re.comp hd)).add
    ((hv.comp hgi.continuous).mul (continuous_im.comp hd))

/-- The real line integral is the real part of the complex contour integral of `u − i v`. -/
theorem lineIntegralRe_eq_re_contourIntegral {u v : ℂ → ℝ} (hu : Continuous u)
    (hv : Continuous v) :
    lineIntegralRe u v c a b =
      (P.contourIntegral fun z => (u z : ℂ) - I * (v z : ℂ)).re := by
  have hint : ∀ k < P.n, IntervalIntegrable
      (fun t => u (c t) * deriv (fun s => (c s).re) t + v (c t) * deriv (fun s => (c s).im) t)
      volume (P.t k) (P.t (k + 1)) := by
    intro k hk
    have hle : P.t k ≤ P.t (k + 1) := (P.lt k hk).le
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle, IntegrableOn,
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    refine ((P.continuous_piece_integrand hu hv hk).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self).congr_fun (fun x hx => ?_) measurableSet_Ioo
    obtain ⟨h0, hre, him⟩ := P.eq_and_deriv_re_im_eq hk hx
    simp only [hre, him, h0]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [P.first, P.last] at hsum
  rw [lineIntegralRe, contourIntegral, ← hsum, ← reCLM_apply, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have hgi := P.contDiff i hi'
  have hii : IntervalIntegrable
      (fun s => ((u (P.g i s) : ℂ) - I * (v (P.g i s) : ℂ)) * deriv (P.g i) s) volume
      (P.t i) (P.t (i + 1)) :=
    (((continuous_ofReal.comp (hu.comp hgi.continuous)).sub (continuous_const.mul
      (continuous_ofReal.comp (hv.comp hgi.continuous)))).mul
      (hgi.continuous_deriv le_rfl)).intervalIntegrable _ _
  rw [P.lineIntegralRe_piece hi', ← reCLM.intervalIntegral_comp_comm hii]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp [Complex.mul_re]

/-- **Green's theorem for the winding number** (real form): for a closed piecewise-`C¹` curve
`c` and `C¹` functions `u`, `v`,
`∮_c u dx + v dy = ∫ (∂v/∂x − ∂u/∂y)(p) · W(p) dA(p)`. -/
theorem lineIntegralRe_eq_integral {u v : ℂ → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    lineIntegralRe u v c a b =
      ∫ p, (fderiv ℝ v p 1 - fderiv ℝ u p I) * (P.windingNumber p : ℝ) := by
  have hud := hu.differentiable one_ne_zero
  have hvd := hv.differentiable one_ne_zero
  have hg : ContDiff ℝ 1 fun z => (u z : ℂ) - I * (v z : ℂ) :=
    (ofRealCLM.contDiff.comp hu).sub (contDiff_const.mul (ofRealCLM.contDiff.comp hv))
  have hint := (P.integrable_dbar_mul_windingNumber' hg).const_mul (2 * I)
  have hre := reCLM.integral_comp_comm hint
  simp only [reCLM_apply] at hre
  rw [P.lineIntegralRe_eq_re_contourIntegral hu.continuous hv.continuous,
    P.contourIntegral_eq_integral_dbar' hg, ← integral_const_mul, ← hre]
  exact integral_congr_ae (ae_of_all _ fun p => re_two_I_mul_dbar hud hvd p _)

/-! ### Green's theorem for a positively oriented closed curve -/

/-- **Green's theorem** for a positively oriented closed piecewise-`C¹` curve `c` (winding number
`1` on its interior, the union of the bounded components of the complement):
`∮_c u dx + v dy = ∬_{interior} (∂v/∂x − ∂u/∂y) dA`.  Together with
`IsJordanCurve.jordanInterior_eq` the interior of a simple closed curve is its unique bounded
complementary component. -/
theorem lineIntegralRe_eq_setIntegral_jordanInterior (hpos : P.IsPositivelyOriented)
    {u v : ℂ → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    lineIntegralRe u v c a b =
      ∫ p in jordanInterior c a b, (fderiv ℝ v p 1 - fderiv ℝ u p I) := by
  rw [P.lineIntegralRe_eq_integral hu hv,
    ← integral_indicator (isOpen_jordanInterior P.continuousOn).measurableSet]
  have hae : ∀ᵐ p : ℂ, p ∉ P.curve := measure_eq_zero_iff_ae_notMem.mp P.volume_curve
  refine integral_congr_ae (hae.mono fun p hp => ?_)
  simp only
  by_cases hpi : p ∈ jordanInterior c a b
  · rw [indicator_of_mem hpi, hpos p hpi]
    simp
  · rw [indicator_of_notMem hpi,
      P.windingNumber_eq_zero_of_mem_jordanExterior ⟨hp, fun hb => hpi ⟨hp, hb⟩⟩]
    simp

/-- **Green's theorem** for a closed piecewise-`C¹` curve whose winding number is a constant `w`
on its interior: `∮_c u dx + v dy = w ∬_{interior} (∂v/∂x − ∂u/∂y) dA`. -/
theorem lineIntegralRe_eq_mul_setIntegral_jordanInterior {w : ℤ}
    (hw : ∀ p ∈ jordanInterior c a b, P.windingNumber p = w)
    {u v : ℂ → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    lineIntegralRe u v c a b =
      (w : ℝ) * ∫ p in jordanInterior c a b, (fderiv ℝ v p 1 - fderiv ℝ u p I) := by
  rw [P.lineIntegralRe_eq_integral hu hv, ← integral_const_mul,
    ← integral_indicator (isOpen_jordanInterior P.continuousOn).measurableSet]
  have hae : ∀ᵐ p : ℂ, p ∉ P.curve := measure_eq_zero_iff_ae_notMem.mp P.volume_curve
  refine integral_congr_ae (hae.mono fun p hp => ?_)
  simp only
  by_cases hpi : p ∈ jordanInterior c a b
  · rw [indicator_of_mem hpi, hw p hpi]
    ring
  · rw [indicator_of_notMem hpi,
      P.windingNumber_eq_zero_of_mem_jordanExterior ⟨hp, fun hb => hpi ⟨hp, hb⟩⟩]
    simp

end ClosedPiecewiseC1

end Azurite.JordanCurve
