/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section7LG
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# DLMF §2.7(iii): Liouville–Green (WKBJ) Approximation — Example, 2.7.31–2.7.33

The equation 2.7.31, `w″ = (x + ln x) w`, treated with `f = x + ln x` (`exF`), `g = 0` on
`x > 1` (`f` is not positive on all of `(0, ∞)`).

* `dlmf_2_7_31_remark`: the choice `f = x`, `g = ln x` is not admissible, because
  `∫^∞ g f^{−1/2}` diverges (`𝒱_{x,∞}(F) = ∞`).
* 2.7.32 (`exR`, `dlmf_2_7_32`): `f^{1/2} = x^{1/2} + ½ x^{−1/2} ln x + O(x^{−3/2} (ln x)²)`,
  with the explicit bound `|exR x| ≤ (ln x)²/(8 x^{3/2})`.
* `exXi`: the antiderivative `ξ = ∫ f^{1/2}` normalized by
  `ξ(x) = ⅔ x^{3/2} + x^{1/2} ln x − 2x^{1/2} + o(1)`; `exSetup` (the hypotheses of the
  Liouville–Green theorem on `(1, ∞)`), `exControl_bound` (`|F′(x)| ≤ (3/2) x^{−5/2}`).
* 2.7.33 (`dlmf_2_7_33`): there is a solution `w₂ ∼ x^{−1/4−√x} exp(2x^{1/2} − ⅔ x^{3/2})` as
  `x → +∞` (from 2.7.22, 2.7.27).
-/

open Filter Topology Set MeasureTheory Asymptotics

namespace Azurite.DLMF

/-- `f(x) = x + ln x`. -/
noncomputable def exF (x : ℝ) : ℝ := x + Real.log x

/-- The remainder in 2.7.32: `f^{1/2} − x^{1/2} − ½ x^{−1/2} ln x`. -/
noncomputable def exR (t : ℝ) : ℝ :=
  Real.sqrt (t + Real.log t) - Real.sqrt t - Real.log t / (2 * Real.sqrt t)

theorem exF_pos {x : ℝ} (hx : 1 ≤ x) : 0 < exF x := by
  have := Real.log_nonneg hx
  rw [exF]; linarith

theorem exR_eq {t : ℝ} (ht : 1 ≤ t) :
    exR t = -(Real.sqrt (t + Real.log t) - Real.sqrt t) ^ 2 / (2 * Real.sqrt t) := by
  have hlog := Real.log_nonneg ht
  have hr : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by linarith)
  have hp2 : Real.sqrt (t + Real.log t) ^ 2 = t + Real.log t := Real.sq_sqrt (by linarith)
  have hr2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt (by linarith)
  rw [exR]
  field_simp
  linear_combination hp2 - hr2

/-- **DLMF 2.7.32**, explicitly: `|exR t| ≤ (ln t)²/(8 t^{3/2})` for `t ≥ 1`. -/
theorem abs_exR_le {t : ℝ} (ht : 1 ≤ t) :
    |exR t| ≤ Real.log t ^ 2 / (8 * t * Real.sqrt t) := by
  have hlog := Real.log_nonneg ht
  have ht0 : 0 < t := by linarith
  have hr : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  set p := Real.sqrt (t + Real.log t) with hp
  set r := Real.sqrt t with hr_def
  have hp2 : p ^ 2 = t + Real.log t := Real.sq_sqrt (by linarith)
  have hr2 : r ^ 2 = t := Real.sq_sqrt ht0.le
  have hpr : r ≤ p := Real.sqrt_le_sqrt (by linarith)
  -- `(p − r)(p + r) = ln t` and `p + r ≥ 2r`
  have hprod : (p - r) * (p + r) = Real.log t := by linear_combination hp2 - hr2
  have hle : p - r ≤ Real.log t / (2 * r) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  rw [exR_eq ht, abs_div, abs_neg, abs_of_nonneg (sq_nonneg _), abs_of_pos (by positivity)]
  have hsq : (p - r) ^ 2 ≤ (Real.log t / (2 * r)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hle 2
  calc (p - r) ^ 2 / (2 * r) ≤ (Real.log t / (2 * r)) ^ 2 / (2 * r) := by gcongr
    _ = Real.log t ^ 2 / (8 * t * r) := by
        rw [← hr2]
        field_simp
        ring

theorem exR_cont : ContinuousOn exR (Ioi 0) := by
  have hlog : ContinuousOn Real.log (Ioi 0) :=
    Real.continuousOn_log.mono fun x hx => (ne_of_gt (show (0 : ℝ) < x from hx))
  refine ((Real.continuous_sqrt.comp_continuousOn (continuousOn_id.add hlog)).sub
    Real.continuous_sqrt.continuousOn).sub (hlog.div (continuousOn_const.mul
      Real.continuous_sqrt.continuousOn) fun x hx => ?_)
  have : (0 : ℝ) < x := hx
  exact (mul_pos two_pos (Real.sqrt_pos.mpr this)).ne'

/-- `|exR t| ≤ 8 t^{−5/4}` for `t ≥ 1` (via `ln t ≤ 8 t^{1/8}`). -/
theorem abs_exR_le_rpow {t : ℝ} (ht : 1 ≤ t) : |exR t| ≤ 8 * t ^ (-(5 / 4 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have hlog := Real.log_nonneg ht
  have hl : Real.log t ≤ 8 * t ^ (1 / 8 : ℝ) := by
    have := Real.log_le_rpow_div ht0.le (by norm_num : (0 : ℝ) < 1 / 8)
    linarith [show t ^ (1 / 8 : ℝ) / (1 / 8) = 8 * t ^ (1 / 8 : ℝ) by ring]
  have hl2 : Real.log t ^ 2 ≤ 64 * t ^ (1 / 4 : ℝ) := by
    have h1 : Real.log t ^ 2 ≤ (8 * t ^ (1 / 8 : ℝ)) ^ 2 := pow_le_pow_left₀ hlog hl 2
    have h2 : (t ^ (1 / 8 : ℝ)) ^ 2 = t ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
    nlinarith [h2]
  have hpow : t ^ (-(5 / 4 : ℝ)) * (t * Real.sqrt t) = t ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, show t * t ^ (1 / 2 : ℝ) = t ^ (1 + 1 / 2 : ℝ) by
      rw [Real.rpow_add ht0, Real.rpow_one], ← Real.rpow_add ht0]
    norm_num
  have hr : 0 < t * Real.sqrt t := mul_pos ht0 (Real.sqrt_pos.mpr ht0)
  refine (abs_exR_le ht).trans ?_
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hpow]

theorem integrableOn_exR : IntegrableOn exR (Ioi 1) := by
  have hm : AEStronglyMeasurable exR (volume.restrict (Ioi (1 : ℝ))) :=
    (exR_cont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
  have hi : IntegrableOn (fun t : ℝ => 8 * t ^ (-(5 / 4 : ℝ))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(5 / 4 : ℝ)) < -1) one_pos).const_mul 8
  refine Integrable.mono' hi hm ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_eq_abs]
  exact abs_exR_le_rpow (le_of_lt ht)

/-- **DLMF 2.7.32**: `f^{1/2} = x^{1/2} + ½ x^{−1/2} ln x + O(x^{−3/2} (ln x)²)` as `x → ∞`. -/
theorem dlmf_2_7_32 :
    (fun x => Real.sqrt (exF x) - (x ^ (1 / 2 : ℝ) + 1 / 2 * x ^ (-(1 / 2 : ℝ)) * Real.log x))
      =O[atTop] fun x => x ^ (-(3 / 2 : ℝ)) * Real.log x ^ 2 := by
  refine IsBigO.of_bound (1 / 8) ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : 0 < x := by linarith
  have hs : x ^ (1 / 2 : ℝ) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
  have hs' : x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
    rw [Real.rpow_neg hx0.le, hs]
  have h32 : x ^ (-(3 / 2 : ℝ)) = (x * Real.sqrt x)⁻¹ := by
    rw [Real.rpow_neg hx0.le, Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hx0, Real.rpow_one]
  have he : Real.sqrt (exF x) - (x ^ (1 / 2 : ℝ) + 1 / 2 * x ^ (-(1 / 2 : ℝ)) * Real.log x) =
      exR x := by
    rw [hs, hs', exR, exF]
    field_simp
    ring
  rw [he, Real.norm_eq_abs, Real.norm_eq_abs, h32, abs_mul,
    abs_of_nonneg (sq_nonneg (Real.log x)),
    abs_of_pos (inv_pos.mpr (mul_pos hx0 (Real.sqrt_pos.mpr hx0)))]
  refine (abs_exR_le hx).trans (le_of_eq ?_)
  field_simp

/-! ### The antiderivative `ξ` -/

/-- `⅔ x^{3/2} + x^{1/2} ln x − 2 x^{1/2}`. -/
noncomputable def exMain (x : ℝ) : ℝ :=
  2 / 3 * (x * Real.sqrt x) + Real.sqrt x * Real.log x - 2 * Real.sqrt x

/-- `ξ = ∫ f^{1/2} = exMain − ∫_x^∞ exR`. -/
noncomputable def exXi (x : ℝ) : ℝ := exMain x - ∫ t in Ioi x, exR t

theorem integral_Ioi_exR_eq {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Ioi x, exR t = (∫ t in Ioi 1, exR t) - ∫ t in (1 : ℝ)..x, exR t := by
  rw [intervalIntegral.integral_of_le hx, eq_sub_iff_add_eq,
    ← setIntegral_union (disjoint_left.mpr fun t (h1 : t ∈ Ioi x) h2 => not_le.mpr h1 h2.2)
      measurableSet_Ioc
      (integrableOn_exR.mono_set (Ioi_subset_Ioi hx))
      (integrableOn_exR.mono_set Ioc_subset_Ioi_self), union_comm, Ioc_union_Ioi_eq_Ioi hx]

theorem exXi_hasDerivAt {x : ℝ} (hx : 1 < x) : HasDerivAt exXi (Real.sqrt (exF x)) x := by
  have hx0 : 0 < x := by linarith
  have hr : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt hx0.ne'
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0.ne'
  have hmain : HasDerivAt exMain (Real.sqrt x + Real.log x / (2 * Real.sqrt x)) x := by
    have := ((((hasDerivAt_id x).mul hsq).const_mul (2 / 3)).add (hsq.mul hlog)).sub
      (hsq.const_mul 2)
    refine this.congr_deriv ?_
    have hr2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
    simp only [id]
    field_simp
    linear_combination (6 - 2 * x) * hr2
  -- `d/dx ∫_x^∞ exR = −exR x`
  have hint : HasDerivAt (fun y => ∫ t in Ioi y, exR t) (-exR x) x := by
    have hFTC := intervalIntegral.integral_hasDerivAt_right
      (ContinuousOn.intervalIntegrable_of_Icc hx.le
        (exR_cont.mono fun t ht => show (0 : ℝ) < t from lt_of_lt_of_le one_pos ht.1))
      ((exR_cont.mono fun t (ht : 1 < t) => show (0 : ℝ) < t from lt_trans one_pos ht
        ).stronglyMeasurableAtFilter isOpen_Ioi x hx)
      (exR_cont.continuousAt (Ioi_mem_nhds hx0))
    refine (hFTC.const_sub (∫ t in Ioi 1, exR t)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy using integral_Ioi_exR_eq hy.le
  refine (hmain.sub hint).congr_deriv ?_
  rw [exR, exF]
  ring

theorem exXi_sub_exMain_tendsto : Tendsto (fun x => exXi x - exMain x) atTop (𝓝 0) := by
  have h := intervalIntegral_tendsto_integral_Ioi (μ := volume) 1 integrableOn_exR tendsto_id
  have : Tendsto (fun x => -((∫ t in Ioi 1, exR t) - ∫ t in (1 : ℝ)..x, exR t)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := ∫ t in Ioi 1, exR t)).sub h |>.neg
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [exXi, integral_Ioi_exR_eq hx]
  simp

/-! ### The Liouville–Green hypotheses on `(1, ∞)` -/

/-- The hypotheses of the Liouville–Green theorem for `f = x + ln x`, `g = 0` on `(1, ∞)`. -/
theorem exSetup : LGSetup (Ioi 1) exF (fun _ => 0) exXi where
  isOpen := isOpen_Ioi
  ordConnected := ordConnected_Ioi
  nonempty := nonempty_Ioi
  f_pos _ hx := exF_pos (le_of_lt hx)
  f_contDiff := contDiffOn_id.add (Real.contDiffOn_log.mono fun x (hx : 1 < x) =>
    (ne_of_gt (lt_trans one_pos hx)))
  g_cont := continuousOn_const
  ξ_deriv _ hx := exXi_hasDerivAt hx

theorem exF_hasDerivAt {x : ℝ} (hx : 0 < x) : HasDerivAt exF (1 + x⁻¹) x :=
  (hasDerivAt_id x).add (Real.hasDerivAt_log hx.ne')

/-- `F′(x) = f^{−1/4} (f^{−1/4})″` for `f = x + ln x`, `g = 0`, and `0 ≤ F′(x) ≤ (3/2) x^{−5/2}`. -/
theorem exControl_bound {x : ℝ} (hx : 1 < x) :
    |lgControl exF (fun _ => 0) x| ≤ 3 / 2 * x ^ (-(5 / 2 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  -- the first two derivatives of `φ = f^{−1/4}` near `x`
  set φ1 : ℝ → ℝ := fun y => (1 + y⁻¹) * (-(1 / 4 : ℝ)) * exF y ^ (-(1 / 4 : ℝ) - 1) with hφ1
  have hφ : ∀ y, 1 < y → HasDerivAt (lgPhi exF) (φ1 y) y := fun y hy =>
    (exF_hasDerivAt (by linarith)).rpow_const (Or.inl (exF_pos hy.le).ne')
  have hev : deriv (lgPhi exF) =ᶠ[𝓝 x] φ1 :=
    Filter.eventually_of_mem (Ioi_mem_nhds hx) fun y hy => (hφ y hy).deriv
  have hφ2 := ((((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_inv hx0.ne')).mul_const
    (-(1 / 4 : ℝ))).mul ((exF_hasDerivAt hx0).rpow_const (p := -(1 / 4 : ℝ) - 1)
      (Or.inl (exF_pos hx.le).ne')))
  have hdd : deriv (deriv (lgPhi exF)) x = _ := hev.deriv_eq.trans hφ2.deriv
  set F := exF x with hF
  have hFpos : 0 < F := exF_pos hx.le
  have hFx : x ≤ F := by have := Real.log_nonneg hx.le; rw [hF, exF]; linarith
  have hA : F ^ (-(1 / 4 : ℝ)) * F ^ (-(1 / 4 : ℝ) - 1) = F ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hFpos]; norm_num
  have hB : F ^ (-(1 / 4 : ℝ)) * F ^ (-(1 / 4 : ℝ) - 1 - 1) = F ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.rpow_add hFpos]; norm_num
  have hval : lgControl exF (fun _ => 0) x = 1 / 4 * (x ^ 2)⁻¹ * F ^ (-(3 / 2 : ℝ)) +
      5 / 16 * (1 + x⁻¹) ^ 2 * F ^ (-(5 / 2 : ℝ)) := by
    rw [lgControl, hdd, ← hA, ← hB]
    simp only [lgPhi, zero_div, sub_zero, Pi.add_apply]
    rw [← hF]
    ring
  have hA0 : 0 ≤ F ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hFpos.le _
  have hB0 : 0 ≤ F ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hFpos.le _
  have hA1 : F ^ (-(3 / 2 : ℝ)) ≤ x ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hx0 hFx (by norm_num)
  have hB1 : F ^ (-(5 / 2 : ℝ)) ≤ x ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hx0 hFx (by norm_num)
  have h7 : (x ^ 2)⁻¹ * x ^ (-(3 / 2 : ℝ)) ≤ x ^ (-(5 / 2 : ℝ)) := by
    rw [show (x ^ 2)⁻¹ = x ^ (-(2 : ℝ)) by rw [Real.rpow_neg hx0.le]; norm_cast,
      ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
  have hu : (1 + x⁻¹) ^ 2 ≤ 4 := by
    have : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx.le
    have : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
    nlinarith
  have hx2 : 0 ≤ (x ^ 2)⁻¹ := by positivity
  have hnonneg : 0 ≤ lgControl exF (fun _ => 0) x := by rw [hval]; positivity
  rw [abs_of_nonneg hnonneg, hval]
  have h1 : (x ^ 2)⁻¹ * F ^ (-(3 / 2 : ℝ)) ≤ x ^ (-(5 / 2 : ℝ)) :=
    (mul_le_mul_of_nonneg_left hA1 hx2).trans h7
  have h2 : (1 + x⁻¹) ^ 2 * F ^ (-(5 / 2 : ℝ)) ≤ 4 * x ^ (-(5 / 2 : ℝ)) :=
    mul_le_mul hu hB1 hB0 (by norm_num)
  nlinarith

theorem exControl_integrableOn (x : ℝ) :
    IntegrableOn (lgControl exF (fun _ => 0)) (Ioi 1 ∩ Ici x) := by
  have hm : AEStronglyMeasurable (lgControl exF (fun _ => 0)) (volume.restrict (Ioi 1 ∩ Ici x)) :=
    (exSetup.control_cont.mono inter_subset_left).aestronglyMeasurable
      (measurableSet_Ioi.inter measurableSet_Ici)
  have hi : IntegrableOn (fun t : ℝ => 3 / 2 * t ^ (-(5 / 2 : ℝ))) (Ioi 1 ∩ Ici x) :=
    IntegrableOn.mono_set ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-(5 / 2 : ℝ)) < -1)
      one_pos).const_mul (3 / 2)) inter_subset_left
  refine Integrable.mono' hi hm ?_
  refine (ae_restrict_iff' (measurableSet_Ioi.inter measurableSet_Ici)).mpr
    (Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_eq_abs]
  exact exControl_bound ht.1

theorem atTop_le_ioUpperEnd_Ioi (a : ℝ) : atTop ≤ ioUpperEnd (Ioi a) := by
  intro s hs
  have hs' : ∀ᶠ x in ioUpperEnd (Ioi a), x ∈ s := hs
  rw [eventually_ioUpperEnd nonempty_Ioi] at hs'
  obtain ⟨b, hb, h⟩ := hs'
  exact mem_atTop_sets.mpr ⟨b, fun x hx => h x (lt_of_lt_of_le hb hx) hx⟩

/-- **DLMF 2.7.33**: `w″ = (x + ln x) w` has a solution
`w₂(x) ∼ x^{−1/4−√x} exp(2 x^{1/2} − ⅔ x^{3/2})` as `x → +∞` (2.7.22 and 2.7.27 with
`f = x + ln x`, `g = 0` on `(1, ∞)` and `∫ f^{1/2}` normalized as in `exXi`). -/
theorem dlmf_2_7_33 :
    ∃ w₂ : ℝ → ℝ, IsLGSolution (Ioi 1) (fun x => x + Real.log x) (fun _ => 0) w₂ ∧
      AsympEqDLMF atTop w₂ fun x =>
        x ^ (-(1 / 4 : ℝ) - Real.sqrt x) *
          Real.exp (2 * x ^ (1 / 2 : ℝ) - 2 / 3 * x ^ (3 / 2 : ℝ)) := by
  obtain ⟨ε, hsol, hε⟩ := exSetup.dlmf_2_7_22 fun x _ => exControl_integrableOn x
  have hasy := exSetup.dlmf_2_7_27 (fun x _ => exControl_integrableOn x)
    (fun x hx => (hε x hx).2.1)
  refine ⟨_, hsol, ?_⟩
  have h1 := hasy.mono_left (atTop_le_ioUpperEnd_Ioi 1)
  -- `f^{−1/4} e^{−ξ} / target = (f/x)^{−1/4} e^{−(ξ − exMain)} → 1`
  have hlogx : Tendsto (fun x => exF x / x) atTop (𝓝 1) := by
    have := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have h := this.const_add 1
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [exF, id]
    field_simp
  have hpow : Tendsto (fun x => (exF x / x) ^ (-(1 / 4 : ℝ))) atTop (𝓝 1) := by
    have := (Real.continuousAt_rpow_const 1 (-(1 / 4 : ℝ)) (Or.inl one_ne_zero)).tendsto.comp
      hlogx
    rw [Real.one_rpow] at this
    exact this
  have hexp : Tendsto (fun x => Real.exp (-(exXi x - exMain x))) atTop (𝓝 1) := by
    have h0 : Tendsto (fun x => -(exXi x - exMain x)) atTop (𝓝 0) := by
      simpa using exXi_sub_exMain_tendsto.neg
    have := (Real.continuous_exp.tendsto 0).comp h0
    rw [Real.exp_zero] at this
    exact this
  have h2 := hpow.mul hexp
  rw [one_mul] at h2
  have h3 := h1.mul h2
  rw [one_mul] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hx0 : 0 < x := by linarith
  have hF : 0 < exF x := exF_pos hx.le
  have hs : x ^ (1 / 2 : ℝ) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
  have h32 : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx0,
      Real.rpow_one]
  have hsplit : x ^ (-(1 / 4 : ℝ) - Real.sqrt x) =
      x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.sqrt x * Real.log x)) := by
    rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_def_of_pos hx0 (-Real.sqrt x)]
    ring_nf
  have htarget : x ^ (-(1 / 4 : ℝ) - Real.sqrt x) *
      Real.exp (2 * x ^ (1 / 2 : ℝ) - 2 / 3 * x ^ (3 / 2 : ℝ)) =
      x ^ (-(1 / 4 : ℝ)) * Real.exp (-exMain x) := by
    rw [hsplit, hs, h32, mul_assoc, ← Real.exp_add, exMain]
    ring_nf
  have hdiv : (exF x / x) ^ (-(1 / 4 : ℝ)) = exF x ^ (-(1 / 4 : ℝ)) / x ^ (-(1 / 4 : ℝ)) :=
    Real.div_rpow hF.le hx0.le _
  have hxp : 0 < x ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hFp : 0 < exF x ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hF _
  rw [htarget, hdiv, show -(exXi x - exMain x) = -exXi x - -exMain x by ring, Real.exp_sub]
  simp only [lgPhi]
  have he1 := Real.exp_pos (-exXi x)
  have he2 := Real.exp_pos (-exMain x)
  field_simp

/-! ### Why not `f = x`, `g = ln x` -/

/-- **DLMF §2.7(iii), Example**: "We cannot take `f = x` and `g = ln x` because `∫ g f^{−1/2} dx`
would diverge as `x → +∞`": the error-control variation `𝒱_{x,∞}(F)` is infinite. -/
theorem dlmf_2_7_31_remark {x : ℝ} (hx : 1 < x) :
    ¬ IntegrableOn (lgControl (fun t => t) Real.log) (Ioi 1 ∩ Ici x) := by
  intro hint
  -- `F′(t) = (5/16) t^{−5/2} − ln t / √t` for `t > 0`
  have hφ : ∀ t, 0 < t → deriv (deriv (lgPhi fun t : ℝ => t)) t =
      -(1 / 4 : ℝ) * (-(1 / 4 : ℝ) - 1) * t ^ (-(1 / 4 : ℝ) - 1 - 1) := by
    intro t ht
    have h1 : ∀ y, 0 < y → HasDerivAt (lgPhi fun t : ℝ => t)
        (-(1 / 4 : ℝ) * y ^ (-(1 / 4 : ℝ) - 1)) y :=
      fun y hy => Real.hasDerivAt_rpow_const (Or.inl hy.ne')
    have hev : deriv (lgPhi fun t : ℝ => t) =ᶠ[𝓝 t]
        fun y => -(1 / 4 : ℝ) * y ^ (-(1 / 4 : ℝ) - 1) :=
      Filter.eventually_of_mem (Ioi_mem_nhds ht) fun y hy => (h1 y hy).deriv
    rw [hev.deriv_eq]
    exact ((Real.hasDerivAt_rpow_const (p := -(1 / 4 : ℝ) - 1) (Or.inl ht.ne')).const_mul
      (-(1 / 4 : ℝ))).deriv.trans (by ring)
  have hval : ∀ t ∈ Ioi (1 : ℝ) ∩ Ici x, Real.log t / Real.sqrt t =
      5 / 16 * t ^ (-(5 / 2 : ℝ)) - lgControl (fun t => t) Real.log t := by
    intro t ht
    have ht0 : 0 < t := lt_trans one_pos ht.1
    rw [lgControl, hφ t ht0]
    simp only [lgPhi]
    have : t ^ (-(1 / 4 : ℝ)) * t ^ (-(1 / 4 : ℝ) - 1 - 1) = t ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_add ht0]; norm_num
    linear_combination (-(1 / 4 : ℝ) * (-(1 / 4 : ℝ) - 1)) * this
  have hi1 : IntegrableOn (fun t : ℝ => 5 / 16 * t ^ (-(5 / 2 : ℝ))) (Ioi 1 ∩ Ici x) :=
    IntegrableOn.mono_set ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-(5 / 2 : ℝ)) < -1)
      one_pos).const_mul (5 / 16)) inter_subset_left
  have hlog : IntegrableOn (fun t => Real.log t / Real.sqrt t) (Ioi 1 ∩ Ici x) :=
    (hi1.sub hint).congr_fun (fun t ht => (hval t ht).symm)
      (measurableSet_Ioi.inter measurableSet_Ici)
  -- on `t ≥ max x e`, `t^{−1/2} ≤ ln t / √t`
  set c := max x (Real.exp 1) with hc
  have hc1 : 1 < c := lt_of_lt_of_le hx (le_max_left _ _)
  have hsub : Ioi c ⊆ Ioi 1 ∩ Ici x := fun t ht =>
    ⟨lt_trans hc1 ht, show x ≤ t from (le_max_left x (Real.exp 1)).trans
      (le_of_lt (by rw [← hc]; exact ht))⟩
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Ioi c) := by
    have hm : AEStronglyMeasurable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (volume.restrict (Ioi c)) :=
      (continuousOn_id.rpow_const fun t (ht : c < t) =>
        Or.inl (ne_of_gt (lt_trans (lt_trans one_pos hc1) ht))).aestronglyMeasurable
          measurableSet_Ioi
    refine Integrable.mono' (hlog.mono_set hsub) hm ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := lt_trans (lt_trans one_pos hc1) ht
    have hlog1 : 1 ≤ Real.log t :=
      (Real.le_log_iff_exp_le ht0).mpr ((le_max_right x (Real.exp 1)).trans
        (le_of_lt (by rw [← hc]; exact ht)))
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0.le _), Real.rpow_neg ht0.le,
      ← Real.sqrt_eq_rpow, inv_eq_one_div]
    exact div_le_div_of_nonneg_right hlog1 hs.le
  have := (integrableOn_Ioi_rpow_iff (lt_trans one_pos hc1)).mp hrpow
  norm_num at this

end Azurite.DLMF
