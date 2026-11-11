/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section9
import Mathlib.Analysis.MellinTransform

/-!
# DLMF §5.9(i): integral representations valid over other regions

Formalizations of <https://dlmf.nist.gov/5.9>, equations 5.9.4 and 5.9.5.

* 5.9.4, `Γ(z) = ∫₁^∞ t^{z−1} e^{−t} dt + ∑_{k≥0} (−1)ᵏ/((z + k) k!)`, `z ≠ 0, −1, …`
  (`dlmf_5_9_4`): for `ℜz > 0` split Euler's integral at `1` and integrate the exponential series
  termwise on `(0, 1]` (`hasSum_integral_exp_tail`); the integral over `(1, ∞)` is entire (a
  Mellin transform, `differentiable_upperGammaOne`) and the series is analytic off the poles
  (`differentiableAt_gammaSeries`), so the identity theorem extends the formula.
* 5.9.5, `Γ(z) = ∫₀^∞ t^{z−1} (e^{−t} − ∑_{k=0}^{n} (−t)ᵏ/k!) dt`, `−n − 1 < ℜz < −n`
  (`dlmf_5_9_5`): on `(0, 1]` the integrand is the tail of the exponential series (termwise
  again), on `(1, ∞)` the subtracted powers integrate to `−1/(z + k)`; the sum is 5.9.4.
-/

open Complex Filter Topology Set MeasureTheory Asymptotics
open scoped Real Nat

namespace Azurite.DLMF

theorem hasSum_cexp (x : ℂ) : HasSum (fun n : ℕ => x ^ n / (n ! : ℂ)) (cexp x) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-! ### The integral over `(1, ∞)` -/

/-- `∫₁^∞ t^{z−1} e^{−t} dt`. -/
noncomputable def upperGammaOne (z : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (z - 1) * cexp (-t)

theorem upperGammaOne_eq_mellin (z : ℂ) :
    upperGammaOne z = mellin ((Ioi (1 : ℝ)).indicator fun t : ℝ => cexp (-(t : ℂ))) z := by
  unfold mellin upperGammaOne
  have e : ∀ t : ℝ, (t : ℂ) ^ (z - 1) • (Ioi (1 : ℝ)).indicator (fun t : ℝ => cexp (-(t : ℂ))) t =
      (Ioi (1 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ (z - 1) * cexp (-(t : ℂ))) t := fun t => by
    by_cases ht : t ∈ Ioi (1 : ℝ) <;> simp [ht]
  simp_rw [e]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one]

theorem differentiable_upperGammaOne : Differentiable ℂ upperGammaOne := by
  intro s
  rw [show upperGammaOne = fun z => mellin ((Ioi (1 : ℝ)).indicator
    fun t : ℝ => cexp (-(t : ℂ))) z from funext upperGammaOne_eq_mellin]
  refine mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) (b := s.re - 1) one_pos ?_ ?_ ?_
    (by linarith)
  · exact ((by fun_prop : Continuous fun t : ℝ => cexp (-(t : ℂ))).locallyIntegrable.indicator
      measurableSet_Ioi).locallyIntegrableOn _
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 1] with t ht
    rw [indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht), Complex.norm_exp, one_mul]
    simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  · refine IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with t ht
    rw [indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from fun h => by
      simp only [mem_Ioi] at h; linarith [ht.2])]
    simp

/-! ### The series -/

/-- The terms `(−1)ᵏ/((z + k) k!)` of 5.9.4. -/
noncomputable def gammaSeriesTerm (k : ℕ) (z : ℂ) : ℂ := (-1) ^ k / ((z + k) * (k ! : ℂ))

theorem summable_inv_factorial : Summable (fun k : ℕ => 1 / (k ! : ℝ)) := by
  simpa using Real.summable_pow_div_factorial 1

theorem differentiableAt_gammaSeries {z₀ : ℂ} (hz₀ : z₀ ∉ gammaPoles) :
    DifferentiableAt ℂ (fun z => ∑' k, gammaSeriesTerm k z) z₀ := by
  obtain ⟨r, hr, c, hc, hb⟩ := exists_norm_add_nat_ge hz₀
  have hne : ∀ w ∈ Metric.ball z₀ r, ∀ k : ℕ, w + k ≠ 0 := fun w hw k h => by
    have := hb w hw k
    rw [h, norm_zero] at this
    have : 0 < c * ((k : ℝ) + 1) := by positivity
    linarith
  have hd : DifferentiableOn ℂ (fun z => ∑' k, gammaSeriesTerm k z) (Metric.ball z₀ r) := by
    refine differentiableOn_tsum_of_summable_norm (summable_inv_factorial.mul_left (1 / c))
      (fun k w hw => ?_) Metric.isOpen_ball (fun k w hw => ?_)
    · have := hne w hw k
      have hf : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      show DifferentiableWithinAt ℂ (fun z => (-1) ^ k / ((z + k) * (k ! : ℂ))) _ _
      exact ((differentiableAt_const _).div ((differentiableAt_id.add_const (k : ℂ)).mul_const _)
        (mul_ne_zero this hf)).differentiableWithinAt
    · have h1 := hb w hw k
      have hk : (0 : ℝ) < c * ((k : ℝ) + 1) := by positivity
      have hf : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
      rw [gammaSeriesTerm, norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_mul,
        Complex.norm_natCast]
      rw [div_le_iff₀ (mul_pos (by linarith) hf)]
      calc (1 : ℝ) = 1 / c * (1 / k !) * (c * k !) := by field_simp
        _ ≤ 1 / c * (1 / k !) * (‖w + k‖ * k !) := by
          gcongr
          nlinarith
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))

/-! ### Termwise integration on `(0, 1]` -/

theorem integral_Ioc_cpow (w : ℂ) (hw : 0 < w.re) :
    ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) = 1 / w := by
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl (by simp; linarith))]
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  simp [hw0]

theorem integrableOn_Ioc_cpow_sub_one (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1)) (Ioc 0 1) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith))

theorem integral_Ioc_rpow (s : ℝ) (hs : 0 < s) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ (s - 1) = 1 / s := by
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith))]
  simp [Real.zero_rpow hs.ne']

/-- Termwise integration of the tail of the exponential series against `t^{z−1}` on `(0, 1]`:
`∫₀¹ t^{z−1} (e^{−t} − ∑_{j<m} (−t)ʲ/j!) dt = ∑_{k≥0} (−1)^{k+m}/((z + k + m)(k + m)!)`,
`ℜz + m > 0`. -/
theorem hasSum_integral_exp_tail (m : ℕ) {z : ℂ} (hz : 0 < z.re + m) :
    HasSum (fun k : ℕ => gammaSeriesTerm (k + m) z)
      (∫ t in Ioc (0 : ℝ) 1,
        (t : ℂ) ^ (z - 1) * (cexp (-t) - ∑ j ∈ Finset.range m, (-(t : ℂ)) ^ j / (j ! : ℂ))) := by
  set F : ℕ → ℝ → ℂ := fun k t => (t : ℂ) ^ (z - 1) * ((-(t : ℂ)) ^ (k + m) / ((k + m) ! : ℂ))
    with hF
  have hpt : ∀ t : ℝ, HasSum (fun k => F k t)
      ((t : ℂ) ^ (z - 1) * (cexp (-t) - ∑ j ∈ Finset.range m, (-(t : ℂ)) ^ j / (j ! : ℂ))) :=
    fun t => ((hasSum_nat_add_iff' m).mpr (hasSum_cexp (-(t : ℂ)))).mul_left _
  have hFeq : ∀ k : ℕ, ∀ t ∈ Ioc (0 : ℝ) 1, F k t =
      (-1) ^ (k + m) / ((k + m) ! : ℂ) * (t : ℂ) ^ ((z + (k + m : ℕ)) - 1) := fun k t ht => by
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht.1)
    simp only [hF]
    rw [show z + ((k + m : ℕ) : ℂ) - 1 = (z - 1) + ((k + m : ℕ) : ℂ) by ring, cpow_add _ _ ht0,
      cpow_natCast, neg_pow]
    ring
  have hre : ∀ k : ℕ, 0 < (z + (k + m : ℕ)).re := fun k => by
    simp only [add_re, natCast_re]; push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hint : ∀ k : ℕ, Integrable (F k) (volume.restrict (Ioc 0 1)) := fun k =>
    ((integrableOn_Ioc_cpow_sub_one _ (hre k)).const_mul ((-1) ^ (k + m) / ((k + m) ! : ℂ))).congr
      ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => (hFeq k t ht).symm))
  have hval : ∀ k : ℕ, ∫ t in Ioc (0 : ℝ) 1, F k t = gammaSeriesTerm (k + m) z := fun k => by
    rw [setIntegral_congr_fun measurableSet_Ioc (hFeq k), integral_const_mul,
      integral_Ioc_cpow _ (hre k), gammaSeriesTerm]
    push_cast
    field_simp
  have hnorm : ∀ k : ℕ, ∫ t in Ioc (0 : ℝ) 1, ‖F k t‖ =
      1 / ((k + m) ! : ℝ) * (1 / (z.re + (k + m : ℕ))) := fun k => by
    have : ∀ t ∈ Ioc (0 : ℝ) 1, ‖F k t‖ = 1 / ((k + m) ! : ℝ) * t ^ ((z.re + (k + m : ℕ)) - 1) :=
      fun t ht => by
        rw [hFeq k t ht, norm_mul, norm_cpow_eq_rpow_re_of_pos ht.1, norm_div, norm_pow, norm_neg,
          norm_one, one_pow, Complex.norm_natCast]
        simp
    rw [setIntegral_congr_fun measurableSet_Ioc this, integral_const_mul,
      integral_Ioc_rpow _ (by have := hre k; simpa using this)]
  have hsum : Summable fun k : ℕ => ∫ t in Ioc (0 : ℝ) 1, ‖F k t‖ := by
    simp_rw [hnorm]
    refine (summable_inv_factorial.mul_left (1 / (z.re + m))).of_nonneg_of_le
      (fun k => ?_) (fun k => ?_)
    · have := hre k; simp only [add_re, natCast_re] at this; positivity
    · have h1 : (k ! : ℝ) ≤ (k + m) ! := by exact_mod_cast Nat.factorial_le (by omega)
      have h2 : z.re + m ≤ z.re + (k + m : ℕ) := by
        push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have h3 : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
      rw [mul_comm]
      gcongr
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  simp_rw [hval] at h
  convert h using 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  exact ((hpt t).tsum_eq).symm

/-! ### 5.9.4 -/

theorem integral_Ioc_add_upperGammaOne {z : ℂ} (hz : 0 < z.re) :
    Gamma z = (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (z - 1) * cexp (-t)) + upperGammaOne z := by
  rw [Gamma_eq_integral hz, GammaIntegral, ← Ioc_union_Ioi_eq_Ioi zero_le_one]
  have hi := GammaIntegral_convergent hz
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one] at hi
  rw [setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hi.mono_set subset_union_left) (hi.mono_set subset_union_right), upperGammaOne]
  congr 1 <;> refine setIntegral_congr_fun (by measurability) fun t _ => ?_ <;> push_cast <;> ring

/-- **DLMF 5.9.4**: `Γ(z) = ∫₁^∞ t^{z−1} e^{−t} dt + ∑_{k≥0} (−1)ᵏ/((z + k) k!)`,
`z ≠ 0, −1, −2, …`. -/
theorem dlmf_5_9_4 {z : ℂ} (hz : z ∉ gammaPoles) :
    Gamma z = (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (z - 1) * cexp (-t)) +
      ∑' k : ℕ, (-1) ^ k / ((z + k) * (k ! : ℂ)) := by
  have hU : IsOpen gammaPolesᶜ := isClosed_gammaPoles.isOpen_compl
  have hR : AnalyticOnNhd ℂ (fun z => upperGammaOne z + ∑' k, gammaSeriesTerm k z)
      gammaPolesᶜ :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      ((differentiable_upperGammaOne w).add (differentiableAt_gammaSeries hw))
        |>.differentiableWithinAt) hU
  have heq := eqOn_of_eq_on_pos_reals dlmf_5_2_i_analytic hR isPreconnected_compl_gammaPoles hU
    (not_mem_gammaPoles_of_re_pos (by simp)) (fun x hx _ => by
      have hx' : 0 < (x : ℂ).re := by simpa using hx
      have h := hasSum_integral_exp_tail 0 (z := x) (by simpa using hx)
      simp only [add_zero, Finset.range_zero, Finset.sum_empty, sub_zero] at h
      rw [integral_Ioc_add_upperGammaOne hx', h.tsum_eq.symm, add_comm])
  exact heq hz

/-! ### 5.9.5 -/

theorem norm_cexp_neg_sub_sum_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (m : ℕ) :
    ‖cexp (-t) - ∑ j ∈ Finset.range m, (-(t : ℂ)) ^ j / (j ! : ℂ)‖ ≤ 2 * t ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, Complex.norm_exp]
    have : (-(t : ℂ)).re = -t := by simp
    rw [this]
    have := Real.exp_le_one_iff.mpr (by linarith : -t ≤ 0)
    linarith
  · have hx : ‖-(t : ℂ)‖ ≤ 1 := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1
    have h := Complex.exp_bound hx hm
    have hn : ‖-(t : ℂ)‖ = t := by rw [norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht0]
    rw [hn] at h
    refine h.trans ?_
    have hf : (1 : ℝ) ≤ m ! := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : ((m.succ : ℕ) : ℝ) * ((m ! : ℝ) * m)⁻¹ ≤ 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      push_cast
      nlinarith
    have ht : 0 ≤ t ^ m := pow_nonneg ht0 m
    nlinarith

/-- **DLMF 5.9.5**: `Γ(z) = ∫₀^∞ t^{z−1} (e^{−t} − ∑_{k=0}^{n} (−t)ᵏ/k!) dt`,
`−n − 1 < ℜz < −n`. -/
theorem dlmf_5_9_5 (n : ℕ) {z : ℂ} (h1 : -(n : ℝ) - 1 < z.re) (h2 : z.re < -n) :
    Gamma z = ∫ t in Ioi (0 : ℝ),
      (t : ℂ) ^ (z - 1) * (cexp (-t) - ∑ k ∈ Finset.range (n + 1), (-(t : ℂ)) ^ k / (k ! : ℂ)) := by
  set P : ℝ → ℂ := fun t => ∑ k ∈ Finset.range (n + 1), (-(t : ℂ)) ^ k / (k ! : ℂ) with hP
  have hpole : z ∉ gammaPoles := by
    rw [not_mem_gammaPoles]
    intro m hm
    have := congrArg re hm
    simp only [neg_re, natCast_re] at this
    rcases le_or_gt m n with h | h
    · have : (m : ℝ) ≤ n := by exact_mod_cast h
      linarith
    · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
      linarith
  have hzm : 0 < z.re + ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  -- integrability on `(0, 1]`
  have hint1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * (cexp (-t) - P t)) (Ioc 0 1) := by
    refine Integrable.mono' (((integrableOn_Ioc_cpow_sub_one (z + ((n + 1 : ℕ) : ℂ))
      (by simpa using hzm)
      ).norm).const_mul 2) ?_ ((ae_restrict_iff' measurableSet_Ioc).mpr
        (ae_of_all _ fun t ht => ?_))
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioc
      refine ContinuousAt.continuousWithinAt ?_
      have : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht.1
      have hc : ContinuousAt (fun t : ℝ => (t : ℂ)) t := continuous_ofReal.continuousAt
      exact (hc.cpow continuousAt_const this).mul (by simp only [hP]; fun_prop)
    · have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht.1)
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht.1, norm_cpow_eq_rpow_re_of_pos ht.1]
      have hb := norm_cexp_neg_sub_sum_le ht.1.le ht.2 (n + 1)
      have e : t ^ (z.re - 1) * t ^ (n + 1) = t ^ ((z + ((n + 1 : ℕ) : ℂ) - 1).re) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add ht.1]
        congr 1
        simp only [sub_re, add_re, natCast_re, one_re]
        ring
      calc t ^ (z.re - 1) * ‖cexp (-t) - P t‖ ≤ t ^ (z.re - 1) * (2 * t ^ (n + 1)) :=
            mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht.1.le _)
        _ = 2 * t ^ ((z + ((n + 1 : ℕ) : ℂ) - 1).re) := by rw [← e]; ring
  -- the pieces on `(1, ∞)`
  have hpow : ∀ k ∈ Finset.range (n + 1),
      IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z + k - 1)) (Ioi 1) ∧
        ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (z + k - 1) = -1 / (z + k) := fun k hk => by
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hr : (z + k - 1).re < -1 := by simp; linarith
    refine ⟨integrableOn_Ioi_cpow_of_lt hr one_pos, ?_⟩
    rw [integral_Ioi_cpow_of_lt hr one_pos]
    simp
  have hupper : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * cexp (-t)) (Ioi 1) := by
    refine Integrable.mono' (exp_neg_integrableOn_Ioi 1 one_pos) ?_
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
      refine ContinuousAt.continuousWithinAt ?_
      have : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr (lt_trans one_pos ht)
      have hc : ContinuousAt (fun t : ℝ => (t : ℂ)) t := continuous_ofReal.continuousAt
      exact (hc.cpow continuousAt_const this).mul (by fun_prop)
    · have ht' : (1 : ℝ) < t := ht
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (lt_trans one_pos ht'), Complex.norm_exp]
      simp only [neg_re, ofReal_re]
      rw [show -1 * t = -t by ring]
      have : t ^ ((z - 1).re) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos ht'.le (by simp; linarith)
      have := Real.exp_pos (-t)
      nlinarith
  -- the integrand on `(1, ∞)`
  have hG1 : ∀ t ∈ Ioi (1 : ℝ), (t : ℂ) ^ (z - 1) * (cexp (-t) - P t) =
      (t : ℂ) ^ (z - 1) * cexp (-t) - ∑ k ∈ Finset.range (n + 1),
        ((-1) ^ k / (k ! : ℂ)) * (t : ℂ) ^ (z + k - 1) := fun t ht => by
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt (lt_trans one_pos ht))
    rw [mul_sub, hP, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show z + (k : ℂ) - 1 = (z - 1) + k by ring, cpow_add _ _ ht0, cpow_natCast, neg_pow]
    ring
  have hsumint : IntegrableOn (fun t : ℝ => ∑ k ∈ Finset.range (n + 1),
      ((-1) ^ k / (k ! : ℂ)) * (t : ℂ) ^ (z + k - 1)) (Ioi 1) :=
    integrable_finsetSum _ fun k hk => (hpow k hk).1.const_mul _
  have hint2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * (cexp (-t) - P t)) (Ioi 1) :=
    (hupper.sub hsumint).congr_fun (fun t ht => (hG1 t ht).symm) measurableSet_Ioi
  have hI2 : ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (z - 1) * (cexp (-t) - P t) =
      upperGammaOne z + ∑ k ∈ Finset.range (n + 1), gammaSeriesTerm k z := by
    rw [setIntegral_congr_fun measurableSet_Ioi hG1, integral_sub hupper hsumint,
      integral_finsetSum _ fun k hk => (hpow k hk).1.const_mul _, upperGammaOne, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [integral_const_mul, (hpow k hk).2, gammaSeriesTerm]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have htail := hasSum_integral_exp_tail (n + 1) hzm
  have hsplit : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (z - 1) * (cexp (-t) - P t) =
      (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (z - 1) * (cexp (-t) - P t)) +
        ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (z - 1) * (cexp (-t) - P t) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint1 hint2]
  rw [hsplit, hI2, ← htail.tsum_eq, dlmf_5_9_4 hpole]
  have hs : Summable fun k => gammaSeriesTerm k z :=
    (summable_nat_add_iff (n + 1)).mp htail.summable
  rw [show (∑' k : ℕ, (-1) ^ k / ((z + k) * (k ! : ℂ))) = ∑' k, gammaSeriesTerm k z from rfl,
    show (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (z - 1) * cexp (-t)) = upperGammaOne z from rfl,
    ← hs.sum_add_tsum_nat_add (n + 1)]
  ring

end Azurite.DLMF
