/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14TableSinImproper
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# DLMF Table 1.14.3, row 13: `𝓕_s[ln|(t + a)/(t − a)|]`

`dlmf_table_1_14_3_r13`, as an improper integral. Integration by parts against
`(cos(ax) − cos(xt))/x`, which vanishes at the logarithmic singularity `t = a`
(`integral_eq_of_hasDerivAt_off_countable_of_le`), reduces the row to
`∫_0^∞ (cos(ax) − cos(xt))/(t² − a²) dt = (π/2) sin(ax)/a` (`integral_cos_kernel`). That integral
is the limit `b = ε + ia → ia` of `∫_0^∞ (cos(ax) − cos(xt))/(t² + b²) dt
= (π/2)(cos(ax) − e^{−bx})/b`, by dominated convergence with `|t² + b²| ≥ (t + a)|t − a|`.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real

namespace Azurite.DLMF

/-! ### The kernel `(cos(ax) − cos(xt))/(t² − a²)` -/

theorem abs_cos_sub_cos_mul_le (a x t : ℝ) (hx : 0 < x) :
    |Real.cos (a * x) - Real.cos (x * t)| ≤ x * |t - a| := by
  have := Real.abs_cos_sub_cos_le (a * x) (x * t)
  rwa [show a * x - x * t = x * (a - t) by ring, abs_mul, abs_of_pos hx, abs_sub_comm a t] at this

/-- Domination: `|cos(ax) − cos(xt)|/D ≤ M/(1 + t²)` whenever `D ≥ (t + a)|t − a|`, `t ≥ 0`. -/
theorem cos_kernel_bound {a x t D : ℝ} (ha : 0 < a) (hx : 0 < x) (ht : 0 ≤ t)
    (hD : (t + a) * |t - a| ≤ D) :
    |Real.cos (a * x) - Real.cos (x * t)| / D ≤
      (x / a * (1 + (2 * a + 1) ^ 2) + 6) / (1 + t ^ 2) := by
  set N := |Real.cos (a * x) - Real.cos (x * t)|
  set C := 1 + (2 * a + 1) ^ 2
  have hN1 : N ≤ x * |t - a| := abs_cos_sub_cos_mul_le a x t hx
  have hN2 : N ≤ 2 := by
    have := abs_sub (Real.cos (a * x)) (Real.cos (x * t))
    have := Real.abs_cos_le_one (a * x); have := Real.abs_cos_le_one (x * t); linarith
  have hC : 0 < C := by positivity
  have hM : 0 < x / a * C + 6 := by positivity
  rcases eq_or_ne t a with rfl | hta
  · have : N = 0 := by simp [N, mul_comm]
    rw [this, zero_div]; positivity
  have hta' : 0 < |t - a| := abs_pos.mpr (sub_ne_zero.mpr hta)
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  rw [div_le_div_iff₀ hDpos (by positivity)]
  rcases le_or_gt t (2 * a + 1) with h | h
  · have h1 : 1 + t ^ 2 ≤ C := by simp only [C]; nlinarith
    have hta1 : 1 ≤ (t + a) / a := by rw [le_div_iff₀ ha]; linarith
    calc N * (1 + t ^ 2) ≤ x * |t - a| * C :=
          mul_le_mul hN1 h1 (by positivity) (by positivity)
      _ = x * |t - a| * C * 1 := by ring
      _ ≤ x * |t - a| * C * ((t + a) / a) :=
          mul_le_mul_of_nonneg_left hta1 (by positivity)
      _ = x / a * C * ((t + a) * |t - a|) := by field_simp
      _ ≤ (x / a * C + 6) * D :=
          mul_le_mul (by linarith) hD (by positivity) (by positivity)
  · have hD' : 3 * t ^ 2 / 4 ≤ D := by
      rw [abs_of_pos (by linarith : 0 < t - a)] at hD; nlinarith
    calc N * (1 + t ^ 2) ≤ 2 * (1 + t ^ 2) :=
          mul_le_mul_of_nonneg_right hN2 (by positivity)
      _ ≤ 6 * (3 * t ^ 2 / 4) := by nlinarith
      _ ≤ (x / a * C + 6) * D :=
          mul_le_mul (by have : 0 ≤ x / a * C := by positivity
                         linarith) hD' (by positivity) hM.le

theorem integrableOn_cos_kernel {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (Real.cos (a * x) - Real.cos (x * t)) / (t ^ 2 - a ^ 2))
      (Ioi 0) := by
  refine ((integrable_inv_one_add_sq.const_mul (x / a * (1 + (2 * a + 1) ^ 2) + 6)
    ).integrableOn).mono' ((by fun_prop : Measurable fun t : ℝ =>
      (Real.cos (a * x) - Real.cos (x * t)) / (t ^ 2 - a ^ 2)).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
  rw [Real.norm_eq_abs, abs_div, ← div_eq_mul_inv]
  refine cos_kernel_bound ha hx (le_of_lt ht) (le_of_eq ?_)
  rw [show t ^ 2 - a ^ 2 = (t + a) * (t - a) by ring, abs_mul,
    abs_of_pos (by linarith [show (0 : ℝ) < t from ht] : 0 < t + a)]

/-- `∫_0^∞ dt/(w² + t²) = (π/2)/w` (`ℜw > 0`), from Table 1.14.2 row 2 by continuity at `x = 0`. -/
theorem integral_Ioi_one_div_sq_add_sq {w : ℂ} (hw : 0 < w.re) :
    ∫ t in Ioi (0 : ℝ), 1 / (w ^ 2 + (t : ℂ) ^ 2) = (π / 2 : ℂ) / w := by
  have hg : IntegrableOn (fun t : ℝ => 1 / (w ^ 2 + (t : ℂ) ^ 2)) (Ioi 0) := by
    simpa only [one_div] using (integrable_inv_sq_add_sq hw).integrableOn
  have hc := ((continuous_dlmfFourierCos hg).tendsto 0).mono_left
    (nhdsWithin_le_nhds (s := Ioi 0))
  have hcont : Continuous fun y : ℝ => ((√(π / 2) : ℝ) : ℂ) * (cexp (-(w * y)) / w) := by
    fun_prop
  have h2 : Tendsto (fun y => dlmfFourierCos (fun t => 1 / (w ^ 2 + (t : ℂ) ^ 2)) y) (𝓝[>] 0)
      (𝓝 (((√(π / 2) : ℝ) : ℂ) * (cexp (-(w * ((0 : ℝ) : ℂ))) / w))) :=
    ((hcont.tendsto 0).mono_left nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall fun y hy => (dlmf_table_1_14_2_r2 hw hy).symm)
  have h := tendsto_nhds_unique hc h2
  unfold dlmfFourierCos at h
  simp only [zero_mul, Real.cos_zero, ofReal_one, mul_one, ofReal_zero, mul_zero, neg_zero,
    Complex.exp_zero] at h
  calc ∫ t in Ioi (0 : ℝ), 1 / (w ^ 2 + (t : ℂ) ^ 2)
      = (((√(π / 2) : ℝ) : ℂ) * ((√(2 / π) : ℝ) : ℂ)) *
          ∫ t in Ioi (0 : ℝ), 1 / (w ^ 2 + (t : ℂ) ^ 2) := by
        rw [sqrt_pi_div_two_mul, one_mul]
    _ = ((√(π / 2) : ℝ) : ℂ) * (((√(2 / π) : ℝ) : ℂ) *
          ∫ t in Ioi (0 : ℝ), 1 / (w ^ 2 + (t : ℂ) ^ 2)) := by ring
    _ = ((√(π / 2) : ℝ) : ℂ) * (((√(π / 2) : ℝ) : ℂ) * (1 / w)) := by rw [h]
    _ = (π / 2 : ℂ) / w := by
        rw [← mul_assoc, ← ofReal_mul, Real.mul_self_sqrt (by positivity)]
        push_cast; ring

theorem norm_sq_add_eps_ge {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (ε : ℝ) :
    (t + a) * |t - a| ≤ ‖(t : ℂ) ^ 2 + ((ε : ℂ) + a * I) ^ 2‖ := by
  have e : (t : ℂ) ^ 2 + ((ε : ℂ) + a * I) ^ 2 =
      (((t + a : ℝ) : ℂ) - ε * I) * (((t - a : ℝ) : ℂ) + ε * I) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [e, norm_mul]
  have h1 : |t + a| ≤ ‖(((t + a : ℝ) : ℂ) - ε * I)‖ := by
    have := Complex.abs_re_le_norm (((t + a : ℝ) : ℂ) - ε * I); simpa using this
  have h2 : |t - a| ≤ ‖(((t - a : ℝ) : ℂ) + ε * I)‖ := by
    have := Complex.abs_re_le_norm (((t - a : ℝ) : ℂ) + ε * I); simpa using this
  rw [abs_of_pos (by linarith)] at h1
  exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)

theorem integral_cos_kernel_complex {a x ε : ℝ} (hx : 0 < x) (hε : 0 < ε) :
    ∫ t in Ioi (0 : ℝ), ((Real.cos (a * x) - Real.cos (x * t) : ℝ) : ℂ) /
        ((t : ℂ) ^ 2 + ((ε : ℂ) + a * I) ^ 2) =
      (π / 2 : ℂ) * (((Real.cos (a * x) : ℝ) : ℂ) - cexp (-(((ε : ℂ) + a * I) * x))) /
        ((ε : ℂ) + a * I) := by
  set b : ℂ := (ε : ℂ) + a * I
  have hb : 0 < b.re := by simp [b, hε]
  have hb0 : b ≠ 0 := fun h => by rw [h] at hb; simp at hb
  have hg : IntegrableOn (fun t : ℝ => 1 / (b ^ 2 + (t : ℂ) ^ 2)) (Ioi 0) := by
    simpa only [one_div] using (integrable_inv_sq_add_sq hb).integrableOn
  have e : ∀ t : ℝ, ((Real.cos (a * x) - Real.cos (x * t) : ℝ) : ℂ) / ((t : ℂ) ^ 2 + b ^ 2) =
      ((Real.cos (a * x) : ℝ) : ℂ) * (1 / (b ^ 2 + (t : ℂ) ^ 2)) -
        1 / (b ^ 2 + (t : ℂ) ^ 2) * ((Real.cos (x * t) : ℝ) : ℂ) := fun t => by
    rw [add_comm ((t : ℂ) ^ 2)]; push_cast; ring
  simp_rw [e]
  rw [integral_sub (hg.const_mul _) (integrableOn_mul_cos hg x), integral_const_mul,
    integral_Ioi_one_div_sq_add_sq hb, integral_inv_sq_add_sq_cos hb hx]
  field_simp

/-- `∫_0^∞ (cos(ax) − cos(xt))/(t² − a²) dt = (π/2) sin(ax)/a` (`a, x > 0`), as the limit
`b = ε + ia → ia` of the closed form for `ℜb > 0`. -/
theorem integral_cos_kernel {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), (Real.cos (a * x) - Real.cos (x * t)) / (t ^ 2 - a ^ 2) =
      π / 2 * (Real.sin (a * x) / a) := by
  set M := x / a * (1 + (2 * a + 1) ^ 2) + 6
  set Fε : ℝ → ℝ → ℂ := fun ε t => ((Real.cos (a * x) - Real.cos (x * t) : ℝ) : ℂ) /
    ((t : ℂ) ^ 2 + ((ε : ℂ) + a * I) ^ 2)
  have hlim : Tendsto (fun ε => ∫ t in Ioi (0 : ℝ), Fε ε t) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (0 : ℝ),
        (((Real.cos (a * x) - Real.cos (x * t)) / (t ^ 2 - a ^ 2) : ℝ) : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => M * (1 + t ^ 2)⁻¹)
      ?_ ?_ (integrable_inv_one_add_sq.const_mul M).integrableOn ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hb : 0 < ((ε : ℂ) + a * I).re := by simpa using hε
      refine (Continuous.div (by fun_prop) (by fun_prop) fun t => ?_).aestronglyMeasurable
      rw [add_comm]; exact sq_add_sq_ne_zero hb t
    · refine Eventually.of_forall fun ε => (ae_restrict_iff' measurableSet_Ioi).mpr
        (ae_of_all _ fun t ht => ?_)
      simp only [Fε]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, ← div_eq_mul_inv]
      exact cos_kernel_bound ha hx (le_of_lt ht) (norm_sq_add_eps_ge ha (le_of_lt ht) ε)
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
      rcases eq_or_ne t a with rfl | hta
      · have h0 : Real.cos (t * x) - Real.cos (x * t) = 0 := by rw [mul_comm]; ring
        simp only [Fε, h0, ofReal_zero, zero_div]
        exact tendsto_const_nhds
      have hne : (t : ℂ) ^ 2 + (((0 : ℝ) : ℂ) + a * I) ^ 2 ≠ 0 := by
        have : (t : ℂ) ^ 2 + (((0 : ℝ) : ℂ) + a * I) ^ 2 = ((t ^ 2 - a ^ 2 : ℝ) : ℂ) := by
          push_cast; ring_nf; rw [I_sq]; ring
        rw [this, ofReal_ne_zero]
        intro h
        have : (t - a) * (t + a) = 0 := by linarith
        rcases mul_eq_zero.mp this with h1 | h1
        · exact hta (by linarith)
        · linarith [show (0 : ℝ) < t from ht]
      have hc : ContinuousAt (fun ε : ℝ => Fε ε t) 0 :=
        ContinuousAt.div (by fun_prop) (by fun_prop) hne
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      convert this using 2
      simp only [Fε]
      have e : (t : ℂ) ^ 2 + (((0 : ℝ) : ℂ) + a * I) ^ 2 = ((t ^ 2 - a ^ 2 : ℝ) : ℂ) := by
        push_cast; ring_nf; rw [I_sq]; ring
      rw [e]; push_cast; ring
  have hval : Tendsto (fun ε : ℝ => (π / 2 : ℂ) * (((Real.cos (a * x) : ℝ) : ℂ) -
      cexp (-(((ε : ℂ) + a * I) * x))) / ((ε : ℂ) + a * I)) (𝓝[>] 0)
      (𝓝 ((π / 2 : ℂ) * (((Real.cos (a * x) : ℝ) : ℂ) -
        cexp (-((((0 : ℝ) : ℂ) + a * I) * x))) / (((0 : ℝ) : ℂ) + a * I))) := by
    have hne : ((0 : ℝ) : ℂ) + a * I ≠ 0 := by
      simp [ha.ne']
    exact (ContinuousAt.div (f := fun ε : ℝ => (π / 2 : ℂ) * (((Real.cos (a * x) : ℝ) : ℂ) -
      cexp (-(((ε : ℂ) + a * I) * x)))) (g := fun ε : ℝ => (ε : ℂ) + a * I) (by fun_prop)
      (by fun_prop) hne).tendsto.mono_left nhdsWithin_le_nhds
  have hval' := hval.congr' (eventually_nhdsWithin_of_forall fun ε hε =>
    (integral_cos_kernel_complex hx hε).symm)
  have huniq := tendsto_nhds_unique hlim hval'
  rw [integral_complex_ofReal] at huniq
  apply ofReal_injective
  rw [huniq]
  have hexp : cexp (-((((0 : ℝ) : ℂ) + a * I) * x)) =
      ((Real.cos (a * x) : ℝ) : ℂ) - ((Real.sin (a * x) : ℝ) : ℂ) * I := by
    rw [show -((((0 : ℝ) : ℂ) + a * I) * x) = ((-(a * x) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  rw [hexp]
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  push_cast
  field_simp
  ring

/-! ### Integration by parts against `ln|(t + a)/(t − a)|` -/

theorem hasDerivAt_log_abs_div {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (hta : t ≠ a) :
    HasDerivAt (fun t : ℝ => Real.log |(t + a) / (t - a)|) (-(2 * a) / (t ^ 2 - a ^ 2)) t := by
  have hp : t + a ≠ 0 := by linarith
  have hm : t - a ≠ 0 := sub_ne_zero.mpr hta
  have e : (fun t : ℝ => Real.log |(t + a) / (t - a)|) = fun t => Real.log ((t + a) / (t - a)) :=
    funext fun _ => Real.log_abs _
  rw [e]
  have h1 := ((hasDerivAt_id' t).add_const a).div ((hasDerivAt_id' t).sub_const a) hm
  have h2 := h1.log (div_ne_zero hp hm)
  simp only [Pi.div_apply] at h2
  refine h2.congr_deriv ?_
  have hq : t ^ 2 - a ^ 2 ≠ 0 := by
    rw [show t ^ 2 - a ^ 2 = (t + a) * (t - a) by ring]; exact mul_ne_zero hp hm
  field_simp
  ring

theorem log_abs_div_eq {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (hta : t ≠ a) :
    Real.log |(t + a) / (t - a)| = Real.log (t + a) - Real.log (t - a) := by
  rw [Real.log_abs, Real.log_div (by linarith) (sub_ne_zero.mpr hta)]

theorem intervalIntegrable_log_abs_div {a : ℝ} (ha : 0 < a) {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun t : ℝ => Real.log |(t + a) / (t - a)|) volume 0 R := by
  have h1 : IntervalIntegrable (fun t : ℝ => Real.log (t + a)) volume 0 R := by
    have := (intervalIntegral.intervalIntegrable_log' (a := 0 - -a) (b := R - -a)).comp_sub_right
      (-a)
    simpa [sub_neg_eq_add] using this
  have h2 : IntervalIntegrable (fun t : ℝ => Real.log (t - a)) volume 0 R := by
    have := (intervalIntegral.intervalIntegrable_log' (a := 0 - a) (b := R - a)).comp_sub_right a
    simpa using this
  refine (h1.sub h2).congr_ae ?_
  rw [uIoc_of_le hR]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (Measure.ae_ne volume a)] with t ht hta
  exact (log_abs_div_eq ha ht.1.le hta).symm

theorem continuousOn_cos_sub_mul_log {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (R : ℝ) :
    ContinuousOn (fun t : ℝ => (Real.cos (a * x) - Real.cos (x * t)) / x *
      Real.log |(t + a) / (t - a)|) (Icc 0 R) := by
  intro t ht
  rcases eq_or_ne t a with rfl | hta
  · show Tendsto _ (𝓝[Icc 0 R] t) (𝓝 ((Real.cos (t * x) - Real.cos (x * t)) / x *
      Real.log |(t + t) / (t - t)|))
    rw [show Real.cos (t * x) - Real.cos (x * t) = 0 by rw [mul_comm]; ring, zero_div, zero_mul]
    set g : ℝ → ℝ := fun s => |s - t| * |Real.log (s + t)| + |(s - t) * Real.log (s - t)|
    have hg : ContinuousAt g t := by
      have h1 : ContinuousAt (fun s : ℝ => Real.log (s + t)) t :=
        (Real.continuousAt_log (by linarith)).comp (by fun_prop)
      have h2 : ContinuousAt (fun s : ℝ => (s - t) * Real.log (s - t)) t :=
        (Real.continuous_mul_log.comp (by fun_prop : Continuous fun s : ℝ => s - t)).continuousAt
      exact ((continuous_abs.continuousAt.comp (by fun_prop)).mul
        (continuous_abs.continuousAt.comp h1)).add (continuous_abs.continuousAt.comp h2)
    have hg0 : g t = 0 := by simp [g]
    have hgt := (hg.tendsto.mono_left (nhdsWithin_le_nhds (s := Icc 0 R)))
    rw [hg0] at hgt
    refine squeeze_zero_norm' ?_ hgt
    filter_upwards [self_mem_nhdsWithin] with s hs
    rcases eq_or_ne s t with rfl | hst
    · simp [g]
    rw [Real.norm_eq_abs, abs_mul, log_abs_div_eq ha hs.1 hst]
    have hS : |(Real.cos (t * x) - Real.cos (x * s)) / x| ≤ |s - t| := by
      rw [abs_div, abs_of_pos hx, div_le_iff₀ hx]
      linarith [abs_cos_sub_cos_mul_le t x s hx]
    calc |(Real.cos (t * x) - Real.cos (x * s)) / x| * |Real.log (s + t) - Real.log (s - t)|
        ≤ |s - t| * (|Real.log (s + t)| + |Real.log (s - t)|) :=
          mul_le_mul hS (abs_sub _ _) (abs_nonneg _) (abs_nonneg _)
      _ = g s := by simp only [g, abs_mul]; ring
  · refine ContinuousAt.continuousWithinAt ?_
    have hne : (t + a) / (t - a) ≠ 0 :=
      div_ne_zero (by linarith [ht.1]) (sub_ne_zero.mpr hta)
    have hd : ContinuousAt (fun t : ℝ => (t + a) / (t - a)) t :=
      (continuousAt_id.add continuousAt_const).div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.mpr hta)
    have hL : ContinuousAt (fun t : ℝ => Real.log |(t + a) / (t - a)|) t :=
      hd.abs.log (abs_ne_zero.mpr hne)
    exact (by fun_prop : Continuous fun t : ℝ => (Real.cos (a * x) - Real.cos (x * t)) / x)
      |>.continuousAt.mul hL

/-- `∫_0^R ln|(t + a)/(t − a)| sin(xt) dt =
(cos(ax) − cos(xR))/x · ln|(R + a)/(R − a)| + (2a/x) ∫_0^R (cos(ax) − cos(xt))/(t² − a²) dt`. -/
theorem integral_log_abs_div_mul_sin {a x : ℝ} (ha : 0 < a) (hx : 0 < x) {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in (0 : ℝ)..R, Real.log |(t + a) / (t - a)| * Real.sin (x * t) =
      (Real.cos (a * x) - Real.cos (x * R)) / x * Real.log |(R + a) / (R - a)| +
        2 * a / x * ∫ t in (0 : ℝ)..R, (Real.cos (a * x) - Real.cos (x * t)) / (t ^ 2 - a ^ 2) := by
  have hQ : IntervalIntegrable
      (fun t : ℝ => (Real.cos (a * x) - Real.cos (x * t)) / (t ^ 2 - a ^ 2)) volume 0 R :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
      ((integrableOn_cos_kernel ha hx).mono_set Ioc_subset_Ioi_self)
  have hLs : IntervalIntegrable
      (fun t : ℝ => Real.log |(t + a) / (t - a)| * Real.sin (x * t)) volume 0 R := by
    have := (intervalIntegrable_log_abs_div ha hR).continuousOn_mul
      (g := fun t => Real.sin (x * t)) (by fun_prop)
    simpa only [mul_comm] using this
  have hF := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t : ℝ => (Real.cos (a * x) - Real.cos (x * t)) / x * Real.log |(t + a) / (t - a)|)
    (fun t => Real.log |(t + a) / (t - a)| * Real.sin (x * t) -
      2 * a / x * ((Real.cos (a * x) - Real.cos (x * t)) / (t ^ 2 - a ^ 2)))
    hR (countable_singleton a) (continuousOn_cos_sub_mul_log ha hx R) (fun t ht => ?_)
    (hLs.sub (hQ.const_mul _))
  · rw [intervalIntegral.integral_sub hLs (hQ.const_mul _), intervalIntegral.integral_const_mul]
      at hF
    have h0 : (Real.cos (a * x) - Real.cos (x * 0)) / x * Real.log |(0 + a) / (0 - a)| = 0 := by
      rw [zero_add, zero_sub, div_neg, div_self ha.ne', abs_neg, abs_one, Real.log_one, mul_zero]
    rw [h0, sub_zero] at hF
    linarith
  · have htp : 0 < t := ht.1.1
    have hta : t ≠ a := ht.2
    have hS : HasDerivAt (fun t : ℝ => (Real.cos (a * x) - Real.cos (x * t)) / x)
        (Real.sin (x * t)) t := by
      have := ((hasDerivAt_const t (Real.cos (a * x))).sub
        ((hasDerivAt_id' t).const_mul x).cos).div_const x
      refine this.congr_deriv ?_
      field_simp
      ring
    have hq : t ^ 2 - a ^ 2 ≠ 0 := by
      rw [show t ^ 2 - a ^ 2 = (t + a) * (t - a) by ring]
      exact mul_ne_zero (by linarith) (sub_ne_zero.mpr hta)
    refine (hS.mul (hasDerivAt_log_abs_div ha htp.le hta)).congr_deriv ?_
    field_simp
    ring

/-! ### Row 13 -/

theorem tendsto_log_abs_div_atTop {a : ℝ} :
    Tendsto (fun R : ℝ => Real.log |(R + a) / (R - a)|) atTop (𝓝 0) := by
  have h1 : Tendsto (fun R : ℝ => 2 * a / (R - a)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ (-a) tendsto_id)
  have h2 : Tendsto (fun R : ℝ => (R + a) / (R - a)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add h1
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop a] with R hR
    have : R - a ≠ 0 := sub_ne_zero.mpr hR.ne'
    field_simp
    ring
  have h3 := ((Real.continuousAt_log one_ne_zero).tendsto.comp h2)
  rw [Real.log_one] at h3
  refine h3.congr fun R => ?_
  simp only [Function.comp, Real.log_abs]

/-- **Table 1.14.3, row 13**: `𝓕_s[ln|(t + a)/(t − a)|](x) = √(2π) sin(ax)/x` (`a > 0`, `x > 0`),
as an improper integral. -/
theorem dlmf_table_1_14_3_r13 {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    Tendsto (fun R => ((√(2 / π) : ℝ) : ℂ) *
        ∫ t in (0 : ℝ)..R, ((Real.log |(t + a) / (t - a)| : ℝ) : ℂ) *
          ((Real.sin (x * t) : ℝ) : ℂ)) atTop
      (𝓝 (((√(2 * π) : ℝ) : ℂ) * ((Real.sin (a * x) / x : ℝ) : ℂ))) := by
  have hS : Tendsto (fun R : ℝ => (Real.cos (a * x) - Real.cos (x * R)) / x *
      Real.log |(R + a) / (R - a)|) atTop (𝓝 0) := by
    have hz := (tendsto_log_abs_div_atTop (a := a)).norm.const_mul (2 / x)
    rw [norm_zero, mul_zero] at hz
    refine squeeze_zero_norm (fun R => ?_) hz
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos hx]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [div_le_div_iff_of_pos_right hx]
    have := abs_sub (Real.cos (a * x)) (Real.cos (x * R))
    have := Real.abs_cos_le_one (a * x); have := Real.abs_cos_le_one (x * R); linarith
  have hQ := (intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_cos_kernel ha hx)
    tendsto_id).const_mul (2 * a / x)
  rw [integral_cos_kernel ha hx] at hQ
  have hlim := hS.add hQ
  have hreal : Tendsto (fun R => ∫ t in (0 : ℝ)..R,
      Real.log |(t + a) / (t - a)| * Real.sin (x * t)) atTop
      (𝓝 (π * (Real.sin (a * x) / x))) := by
    rw [show π * (Real.sin (a * x) / x) = 0 + 2 * a / x * (π / 2 * (Real.sin (a * x) / a)) by
      field_simp; ring]
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with R hR
    rw [integral_log_abs_div_mul_sin ha hx hR]
    rfl
  have h := tendsto_sqrt_two_div_pi_ofReal hreal
  simp_rw [← ofReal_mul]
  convert h using 2
  push_cast
  rw [← sqrt_two_div_pi_mul_pi]
  ring

end Azurite.DLMF
