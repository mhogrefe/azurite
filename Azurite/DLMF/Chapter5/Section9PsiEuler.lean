/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section9Psi
import Azurite.DLMF.Chapter1.Section14Mellin
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# DLMF §5.9(ii): Euler's constant and the derivatives of `Γ`

Formalizations of <https://dlmf.nist.gov/5.9>, equations 5.9.19, 5.9.18 (first three forms),
5.9.16 (second equality) and 5.9.14.

* 5.9.19 (`dlmf_5_9_19`): `Γ⁽ⁿ⁾(z) = ∫₀^∞ (ln t)ⁿ e^{−t} t^{z−1} dt` for `ℜz > 0`, by iterating
  Mathlib's derivative of a Mellin transform (`mellin_hasDerivAt_of_isBigO_rpow`), with
  `|ln t| ≤ t^{−ε}/ε` near `0` and `ln t ≤ t` near `∞`.
* 5.9.18: the first form is Mathlib's `Real.eulerMascheroniConstant_eq_neg_integral_log`
  (`γ = −Γ′(1)`); the third splits it at `1` and integrates by parts on both pieces (against
  `1 − e^{−t}` on `(0, 1]`, `−e^{−t}` on `(1, ∞)`); the second adds
  `∫₀¹ dt/(1 + t) = ∫₁^∞ dt/(t(1 + t)) = ln 2` to the third.
* 5.9.16 (second equality): `t = e^{−u}` in the first.
* 5.9.14: `t = eᵘ − 1` turns `∫₀^∞ (1/(1 + t) − (1 + t)^{−z}) dt/t` into the first integral of
  5.9.16, and the second form of 5.9.18 is the rest.
-/

open Complex Filter Topology Set MeasureTheory Asymptotics
open scoped Real

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-! ### 5.9.19 -/

/-- `(ln t)ⁿ e^{−t}`. -/
noncomputable def logPowExp (n : ℕ) (t : ℝ) : ℂ := ((Real.log t ^ n * Real.exp (-t) : ℝ) : ℂ)

theorem abs_log_le_rpow_neg {t ε : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hε : 0 < ε) :
    |Real.log t| ≤ t ^ (-ε) / ε := by
  have hl : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1
  have h := Real.log_le_rpow_div (inv_nonneg.mpr ht0.le) hε
  rw [Real.log_inv, Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le] at h
  rw [abs_of_nonpos hl]
  exact h

theorem logPowExp_isBigO_nhdsGT (n : ℕ) {b : ℝ} (hb : 0 < b) :
    logPowExp n =O[𝓝[>] 0] (· ^ (-b)) := by
  set ε := b / (n + 1) with hεdef
  have hε : 0 < ε := by positivity
  refine IsBigO.of_bound (1 / ε ^ n) ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  rw [logPowExp, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht0 _), abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : |Real.log t| ^ n ≤ (t ^ (-ε) / ε) ^ n :=
    pow_le_pow_left₀ (abs_nonneg _) (abs_log_le_rpow_neg ht0 ht1.le hε) n
  have h3 : (t ^ (-ε)) ^ n ≤ t ^ (-b) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    refine Real.rpow_le_rpow_of_exponent_ge ht0 ht1.le ?_
    rw [hεdef]
    have : (n : ℝ) / (n + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    calc -b ≤ -(b * (n / (n + 1))) := by nlinarith
      _ = -(b / (n + 1)) * n := by ring
  calc |Real.log t| ^ n * Real.exp (-t) ≤ (t ^ (-ε) / ε) ^ n * 1 :=
        mul_le_mul h2 h1 (Real.exp_pos _).le (by positivity)
    _ = 1 / ε ^ n * (t ^ (-ε)) ^ n := by rw [div_pow]; ring
    _ ≤ 1 / ε ^ n * t ^ (-b) := by gcongr

theorem logPowExp_isBigO_atTop (n : ℕ) (a : ℝ) : logPowExp n =O[atTop] (· ^ (-a)) := by
  have he := (isLittleO_exp_neg_mul_rpow_atTop one_pos (-(a + n))).isBigO
  have hl : (fun t : ℝ => Real.log t ^ n) =O[atTop] fun t : ℝ => t ^ (n : ℝ) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    have ht0 : 0 < t := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, Real.rpow_natCast,
      abs_of_pos (pow_pos ht0 n), one_mul, abs_of_nonneg (Real.log_nonneg ht)]
    exact pow_le_pow_left₀ (Real.log_nonneg ht) ((Real.log_le_sub_one_of_pos ht0).trans
      (by linarith)) n
  have hp := hl.mul he
  have h1 : logPowExp n =O[atTop] fun x => Real.log x ^ n * Real.exp (-1 * x) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
    rw [logPowExp, Complex.norm_real, one_mul, neg_one_mul]
  have h2 : (fun x : ℝ => x ^ (n : ℝ) * x ^ (-(a + n))) =ᶠ[atTop] fun x => x ^ (-a) := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [← Real.rpow_add ht]
    ring_nf
  exact h1.trans (hp.trans_eventuallyEq h2)

theorem continuousOn_logPowExp (n : ℕ) : ContinuousOn (logPowExp n) (Ioi 0) := fun t ht => by
  have ht' : t ≠ 0 := (show (0 : ℝ) < t from ht).ne'
  unfold logPowExp
  exact (continuous_ofReal.continuousAt.comp (((Real.continuousAt_log ht').pow n).mul
    (Real.continuous_exp.comp continuous_neg).continuousAt)).continuousWithinAt

theorem iteratedDeriv_Gamma_eq_mellin (n : ℕ) :
    ∀ z : ℂ, 0 < z.re → iteratedDeriv n Gamma z = mellin (logPowExp n) z := by
  induction n with
  | zero =>
    intro z hz
    rw [iteratedDeriv_zero, Gamma_eq_integral hz, GammaIntegral_eq_mellin]
    congr 1
    funext t
    simp [logPowExp]
  | succ n ih =>
    intro z hz
    have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
    have heq : iteratedDeriv n Gamma =ᶠ[𝓝 z] mellin (logPowExp n) :=
      eventually_of_mem (hU.mem_nhds hz) fun w hw => ih w hw
    have hd := (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ) (a := z.re + 1) (b := z.re / 2)
      ((continuousOn_logPowExp n).locallyIntegrableOn measurableSet_Ioi)
      (logPowExp_isBigO_atTop n _) (by linarith)
      (logPowExp_isBigO_nhdsGT n (by linarith)) (by linarith)).2
    rw [iteratedDeriv_succ, heq.deriv_eq, hd.deriv]
    congr 1
    funext t
    simp only [logPowExp, real_smul]
    push_cast
    ring

theorem mellinConvergent_logPowExp (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    MellinConvergent (logPowExp n) z :=
  mellinConvergent_of_isBigO_rpow (a := z.re + 1) (b := z.re / 2)
    ((continuousOn_logPowExp n).locallyIntegrableOn measurableSet_Ioi)
    (logPowExp_isBigO_atTop n _) (by linarith) (logPowExp_isBigO_nhdsGT n (by linarith))
    (by linarith)

/-- **DLMF 5.9.19**: for `n ≥ 0` and `ℜz > 0`, `Γ⁽ⁿ⁾(z) = ∫₀^∞ (ln t)ⁿ e^{−t} t^{z−1} dt`. -/
theorem dlmf_5_9_19 (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    iteratedDeriv n Gamma z =
      ∫ t in Ioi (0 : ℝ), (Real.log t : ℂ) ^ n * Real.exp (-t) * (t : ℂ) ^ (z - 1) := by
  rw [iteratedDeriv_Gamma_eq_mellin n z hz, mellin]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [logPowExp, smul_eq_mul]
  push_cast
  ring

/-- The integrand of 5.9.19 is integrable on `(0, ∞)`. -/
theorem integrableOn_dlmf_5_9_19 (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (Real.log t : ℂ) ^ n * Real.exp (-t) * (t : ℂ) ^ (z - 1))
      (Ioi 0) := by
  refine (mellinConvergent_logPowExp n hz).congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [logPowExp, smul_eq_mul]
  push_cast
  ring

/-! ### 5.9.18 -/

/-- **DLMF 5.9.18** (first form): `γ = −∫₀^∞ e^{−t} ln t dt`. -/
theorem dlmf_5_9_18_1 : γ = -∫ t in Ioi (0 : ℝ), Real.exp (-t) * Real.log t := by
  rw [Real.eulerMascheroniConstant_eq_neg_integral_log]
  simp_rw [mul_comm (Real.exp _)]

theorem integrableOn_exp_neg_mul_log :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * Real.log t) (Ioi 0) := by
  have h := integrableOn_dlmf_5_9_19 1 (z := 1) (by simp)
  rw [IntegrableOn.iff_ofReal (𝕜 := ℂ)]
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [pow_one, sub_self, cpow_zero, mul_one]
  rw [mul_comm]
  exact (RCLike.ofReal_mul _ _).symm

theorem abs_one_sub_exp_neg_le {t : ℝ} (ht : 0 ≤ t) : |1 - Real.exp (-t)| ≤ t := by
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 := Real.add_one_le_exp (-t)
  rw [abs_of_nonneg (by linarith)]
  linarith

theorem integrableOn_one_sub_exp_neg_div :
    IntegrableOn (fun t : ℝ => (1 - Real.exp (-t)) / t) (Ioc 0 1) := by
  refine Integrable.mono' (g := fun _ => (1 : ℝ))
    (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioc))
    ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_))
  · have ht' : t ≠ 0 := ht.1.ne'
    exact (((continuous_const.sub (Real.continuous_exp.comp continuous_neg)).continuousAt).div
      continuousAt_id ht').continuousWithinAt
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos ht.1, div_le_one ht.1]
    exact abs_one_sub_exp_neg_le ht.1.le

theorem integrableOn_exp_neg_div_Ioi_one :
    IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioi 1) := by
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 1) := by
    simpa using exp_neg_integrableOn_Ioi 1 one_pos
  refine hexp.mono' ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
  · exact ContinuousOn.aestronglyMeasurable (fun t ht => (((Real.continuous_exp.comp
      continuous_neg).continuousAt).div continuousAt_id
      (by have : (1 : ℝ) < t := ht; exact ne_of_gt (by simp only [id]; linarith))
      ).continuousWithinAt) measurableSet_Ioi
  · have ht' : (1 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos (by linarith),
      div_le_iff₀ (by linarith)]
    nlinarith [Real.exp_pos (-t)]

/-- `∫₁^∞ e^{−t} ln t dt = ∫₁^∞ e^{−t}/t dt` (by parts). -/
theorem integral_exp_neg_mul_log_Ioi_one :
    ∫ t in Ioi (1 : ℝ), Real.exp (-t) * Real.log t = ∫ t in Ioi (1 : ℝ), Real.exp (-t) / t := by
  have h := integral_Ioi_mul_deriv_eq_deriv_mul (a := 1) (a' := 0) (b' := 0)
    (u := Real.log) (u' := fun t => t⁻¹) (v := fun t => -Real.exp (-t))
    (v' := fun t => Real.exp (-t))
    (fun t ht => Real.hasDerivAt_log (by have : (1 : ℝ) < t := ht; linarith))
    (fun t _ => by
      have := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).neg
      exact this.congr_deriv (by simp))
    ((integrableOn_exp_neg_mul_log.mono_set (Ioi_subset_Ioi zero_le_one)).congr_fun
      (fun t _ => by simp [mul_comm]) measurableSet_Ioi)
    (integrableOn_exp_neg_div_Ioi_one.neg.congr_fun (fun t _ => by
      simp only [Pi.mul_apply, Pi.neg_apply]; ring) measurableSet_Ioi)
    (by
      have : Tendsto (fun t : ℝ => Real.log t * -Real.exp (-t)) (𝓝[>] 1)
          (𝓝 (Real.log 1 * -Real.exp (-1))) :=
        ((Real.continuousAt_log one_ne_zero).mul
          (Real.continuous_exp.comp continuous_neg).continuousAt.neg).tendsto.mono_left
          nhdsWithin_le_nhds
      rw [Real.log_one, zero_mul] at this
      exact this)
    (by
      have h1 : Tendsto (fun t : ℝ => t * Real.exp (-t)) atTop (𝓝 0) := by
        simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
      refine squeeze_zero_norm' ?_ h1
      filter_upwards [eventually_ge_atTop 1] with t ht
      have ht0 : 0 < t := by linarith
      simp only [Pi.mul_apply, norm_mul, norm_neg, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_of_nonneg (Real.log_nonneg ht)]
      gcongr
      linarith [Real.log_le_sub_one_of_pos ht0])
  simp only [sub_zero, zero_sub] at h
  rw [show (fun t : ℝ => Real.exp (-t) * Real.log t) = fun t => Real.log t * Real.exp (-t) from
    funext fun t => mul_comm _ _, h, ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  ring

/-- `∫₀¹ e^{−t} ln t dt = −∫₀¹ (1 − e^{−t})/t dt` (by parts). -/
theorem integral_exp_neg_mul_log_Ioc :
    ∫ t in Ioc (0 : ℝ) 1, Real.exp (-t) * Real.log t =
      -∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t := by
  have hint1 : IntervalIntegrable (fun t : ℝ => Real.exp (-t) * Real.log t) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (integrableOn_exp_neg_mul_log.mono_set Ioc_subset_Ioi_self)
  have hint2 : IntervalIntegrable (fun t : ℝ => (1 - Real.exp (-t)) / t) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      integrableOn_one_sub_exp_neg_div
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := 0) (b := 1)
    (f := fun t => (1 - Real.exp (-t)) * Real.log t)
    (f' := fun t => Real.exp (-t) * Real.log t + (1 - Real.exp (-t)) / t) (fa := 0) (fb := 0)
    zero_lt_one
    (fun t ht => by
      have h1 : HasDerivAt (fun t => 1 - Real.exp (-t)) (Real.exp (-t)) t := by
        simpa using ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).const_sub 1
      convert h1.mul (Real.hasDerivAt_log ht.1.ne') using 1
      field_simp)
    (hint1.add hint2)
    (by
      have h0 : Tendsto (fun t : ℝ => t * Real.log t) (𝓝[>] 0) (𝓝 0) := by
        simpa using Real.continuous_mul_log.continuousAt (x := 0) |>.tendsto.mono_left
          nhdsWithin_le_nhds
      refine squeeze_zero_norm' (a := fun t => ‖t * Real.log t‖) ?_ (by simpa using h0.norm)
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0 : ℝ) < t := ht
      rw [norm_mul, norm_mul, Real.norm_eq_abs (1 - _), Real.norm_of_nonneg ht'.le]
      exact mul_le_mul_of_nonneg_right (abs_one_sub_exp_neg_le ht'.le) (norm_nonneg _))
    (by
      have : Tendsto (fun t : ℝ => (1 - Real.exp (-t)) * Real.log t) (𝓝[<] 1)
          (𝓝 ((1 - Real.exp (-1)) * Real.log 1)) :=
        ((continuous_const.sub (Real.continuous_exp.comp continuous_neg)).continuousAt.mul
          (Real.continuousAt_log one_ne_zero)).tendsto.mono_left nhdsWithin_le_nhds
      simpa using this)
  rw [intervalIntegral.integral_add hint1 hint2, sub_zero] at h
  rw [← intervalIntegral.integral_of_le zero_le_one]
  linarith

/-- **DLMF 5.9.18** (third form): `γ = ∫₀¹ (1 − e^{−t}) dt/t − ∫₁^∞ e^{−t} dt/t`. -/
theorem dlmf_5_9_18_3 :
    γ = (∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t) - ∫ t in Ioi (1 : ℝ), Real.exp (-t) / t := by
  rw [dlmf_5_9_18_1, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (integrableOn_exp_neg_mul_log.mono_set Ioc_subset_Ioi_self)
      (integrableOn_exp_neg_mul_log.mono_set (Ioi_subset_Ioi zero_le_one)),
    integral_exp_neg_mul_log_Ioc, integral_exp_neg_mul_log_Ioi_one]
  ring

theorem integral_one_div_mul_one_add_Ioi_one :
    IntegrableOn (fun t : ℝ => 1 / (t * (1 + t))) (Ioi 1) ∧
      ∫ t in Ioi (1 : ℝ), 1 / (t * (1 + t)) = Real.log 2 := by
  set g : ℝ → ℝ := fun t => Real.log t - Real.log (1 + t) with hg
  have hd : ∀ t ∈ Ici (1 : ℝ), HasDerivAt g (1 / (t * (1 + t))) t := fun t ht => by
    have ht' : (1 : ℝ) ≤ t := ht
    have h1 := Real.hasDerivAt_log (show t ≠ 0 by linarith)
    have h2 := ((hasDerivAt_id t).const_add 1).log (show 1 + id t ≠ 0 by simp; linarith)
    have ht0 : t ≠ 0 := by linarith
    have ht1 : 1 + t ≠ 0 := by linarith
    exact (h1.sub h2).congr_deriv (by simp only [id]; field_simp; ring)
  have hlim : Tendsto g atTop (𝓝 0) := by
    have e : ∀ t : ℝ, 0 < t → g t = -Real.log (1 + t⁻¹) := fun t ht => by
      rw [hg]
      simp only
      rw [show 1 + t⁻¹ = (1 + t) / t by field_simp; ring,
        Real.log_div (by linarith) ht.ne']
      ring
    have h1 : Tendsto (fun t : ℝ => 1 + t⁻¹) atTop (𝓝 1) := by
      simpa using tendsto_inv_atTop_zero.const_add (1 : ℝ)
    have h2 : Tendsto (fun t : ℝ => -Real.log (1 + t⁻¹)) atTop (𝓝 0) := by
      simpa using ((Real.continuousAt_log one_ne_zero).tendsto.comp h1).neg
    exact h2.congr' (eventually_of_mem (Ioi_mem_atTop 0) fun t ht => (e t ht).symm)
  have hpos : ∀ t ∈ Ioi (1 : ℝ), 0 ≤ 1 / (t * (1 + t)) := fun t ht => by
    have : (1 : ℝ) < t := ht
    positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_Ioi_deriv_of_nonneg' hd hpos hlim)
    hlim, hg]
  norm_num

theorem integral_one_div_one_add_Ioc :
    ∫ t in (0 : ℝ)..1, 1 / (1 + t) = Real.log 2 := by
  have := integral_one_div_of_pos (a := 1) (b := 2) one_pos two_pos
  rw [show (2 : ℝ) / 1 = 2 by norm_num] at this
  rw [← this, intervalIntegral.integral_comp_add_left (fun t => 1 / t) 1]
  norm_num

/-- **DLMF 5.9.18** (second form): `γ = ∫₀^∞ (1/(1 + t) − e^{−t}) dt/t`. -/
theorem dlmf_5_9_18_2 :
    γ = ∫ t in Ioi (0 : ℝ), (1 / (1 + t) - Real.exp (-t)) / t := by
  obtain ⟨hi1, hv1⟩ := integral_one_div_mul_one_add_Ioi_one
  have hiA : IntegrableOn (fun t : ℝ => 1 / (1 + t)) (Ioc 0 1) :=
    (ContinuousOn.integrableOn_Icc (continuousOn_const.div (continuousOn_const.add continuousOn_id)
      fun t ht => by have : (0 : ℝ) ≤ t := ht.1; simp; linarith)).mono_set Ioc_subset_Icc_self
  have e1 : ∀ t ∈ Ioc (0 : ℝ) 1, (1 / (1 + t) - Real.exp (-t)) / t =
      (1 - Real.exp (-t)) / t - 1 / (1 + t) := fun t ht => by
    have := ht.1
    field_simp
    ring
  have e2 : ∀ t ∈ Ioi (1 : ℝ), (1 / (1 + t) - Real.exp (-t)) / t =
      1 / (t * (1 + t)) - Real.exp (-t) / t := fun t ht => by
    have : (1 : ℝ) < t := ht
    field_simp
  have hpc : IntegrableOn (fun t : ℝ => (1 / (1 + t) - Real.exp (-t)) / t) (Ioc 0 1) :=
    (integrableOn_one_sub_exp_neg_div.sub hiA).congr_fun (fun t ht => (e1 t ht).symm)
      measurableSet_Ioc
  have hpi : IntegrableOn (fun t : ℝ => (1 / (1 + t) - Real.exp (-t)) / t) (Ioi 1) :=
    (hi1.sub integrableOn_exp_neg_div_Ioi_one).congr_fun (fun t ht => (e2 t ht).symm)
      measurableSet_Ioi
  have i1 : ∫ t in Ioc (0 : ℝ) 1, (1 - Real.exp (-t)) / t =
      ∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t :=
    (intervalIntegral.integral_of_le zero_le_one).symm
  have i2 : ∫ t in Ioc (0 : ℝ) 1, 1 / (1 + t) = Real.log 2 := by
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_one_div_one_add_Ioc]
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi hpc hpi, setIntegral_congr_fun measurableSet_Ioc e1,
    setIntegral_congr_fun measurableSet_Ioi e2, integral_sub integrableOn_one_sub_exp_neg_div hiA,
    integral_sub hi1 integrableOn_exp_neg_div_Ioi_one, hv1, i1, i2, dlmf_5_9_18_3]
  ring

/-- The integrand of the second form of 5.9.18 is integrable on `(0, ∞)`. -/
theorem integrableOn_dlmf_5_9_18_2 :
    IntegrableOn (fun t : ℝ => (1 / (1 + t) - Real.exp (-t)) / t) (Ioi 0) := by
  obtain ⟨hi1, -⟩ := integral_one_div_mul_one_add_Ioi_one
  have hiA : IntegrableOn (fun t : ℝ => 1 / (1 + t)) (Ioc 0 1) :=
    (ContinuousOn.integrableOn_Icc (continuousOn_const.div (continuousOn_const.add continuousOn_id)
      fun t ht => by have : (0 : ℝ) ≤ t := ht.1; simp; linarith)).mono_set Ioc_subset_Icc_self
  have hpc : IntegrableOn (fun t : ℝ => (1 / (1 + t) - Real.exp (-t)) / t) (Ioc 0 1) :=
    (integrableOn_one_sub_exp_neg_div.sub hiA).congr_fun (fun t ht => by
      have := ht.1
      simp only [Pi.sub_apply]
      field_simp
      ring) measurableSet_Ioc
  have hpi : IntegrableOn (fun t : ℝ => (1 / (1 + t) - Real.exp (-t)) / t) (Ioi 1) :=
    (hi1.sub integrableOn_exp_neg_div_Ioi_one).congr_fun (fun t ht => by
      have : (1 : ℝ) < t := ht
      simp only [Pi.sub_apply]
      field_simp) measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact hpc.union hpi

/-! ### 5.9.16 (second equality) -/

theorem hasDerivAt_rexp_neg (u : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-u)) u :=
  ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).congr_deriv (by ring)

theorem image_exp_neg_Ioi : (fun u : ℝ => Real.exp (-u)) '' Ioi 0 = Ioo 0 1 := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : (0 : ℝ) < u := hu
    exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩
  · rintro ⟨h0, h1⟩
    exact ⟨-Real.log t, by simpa using Real.log_neg h0 h1, by simp [Real.exp_log h0]⟩

theorem psiExpSubst {z : ℂ} {u : ℝ} (hu : 0 < u) :
    |-Real.exp (-u)| • ((1 - ((Real.exp (-u) : ℝ) : ℂ) ^ (z - 1)) /
      (1 - ((Real.exp (-u) : ℝ) : ℂ))) = (cexp (-u) - cexp (-(z * u))) / (1 - cexp (-u)) := by
  have he : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hne : (1 : ℂ) - cexp (-u) ≠ 0 := by
    rw [← ofReal_neg, ← ofReal_exp]
    exact_mod_cast (sub_pos.mpr he).ne'
  rw [abs_neg, abs_of_pos (Real.exp_pos _), ofReal_exp_cpow, real_smul, ofReal_exp, ofReal_neg]
  have hm : cexp (-(u : ℂ)) * cexp (-(u : ℂ) * (z - 1)) = cexp (-(z * u)) := by
    rw [← Complex.exp_add]
    ring_nf
  rw [mul_div_assoc', mul_sub, mul_one, hm]

/-- **DLMF 5.9.16** (second equality): for `ℜz > 0`,
`ψ(z) + γ = ∫₀¹ (1 − t^{z−1})/(1 − t) dt`. -/
theorem dlmf_5_9_16_2 {z : ℂ} (hz : 0 < z.re) :
    digamma z + γ = ∫ t in (0 : ℝ)..1, (1 - (t : ℂ) ^ (z - 1)) / (1 - t) := by
  rw [dlmf_5_9_16 hz, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← image_exp_neg_Ioi, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun u _ => (hasDerivAt_rexp_neg u).hasDerivWithinAt)
      (fun a _ b _ h => by simpa using h)]
  exact setIntegral_congr_fun measurableSet_Ioi fun u hu => (psiExpSubst hu).symm

/-- The integrand of the second equality of 5.9.16 is integrable on `(0, 1)`. -/
theorem integrableOn_dlmf_5_9_16_2 {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (1 - (t : ℂ) ^ (z - 1)) / (1 - t)) (Ioo 0 1) := by
  rw [← image_exp_neg_Ioi, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (fun u _ => (hasDerivAt_rexp_neg u).hasDerivWithinAt)
      (fun a _ b _ h => by simpa using h)]
  exact (integrableOn_dlmf_5_9_16 hz).congr_fun (fun u hu => (psiExpSubst hu).symm)
    measurableSet_Ioi

/-! ### 5.9.14 -/

theorem image_exp_sub_one_Ioi : (fun u : ℝ => Real.exp u - 1) '' Ioi 0 = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : (0 : ℝ) < u := hu
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr hu')
  · intro ht
    have ht' : (0 : ℝ) < t := ht
    refine ⟨Real.log (1 + t), Real.log_pos (by linarith), ?_⟩
    simp only
    rw [Real.exp_log (by linarith)]
    ring

theorem psiShiftSubst {z : ℂ} {u : ℝ} (hu : 0 < u) :
    |Real.exp u| • ((1 / (1 + ((Real.exp u - 1 : ℝ) : ℂ)) -
      1 / (1 + ((Real.exp u - 1 : ℝ) : ℂ)) ^ z) / ((Real.exp u - 1 : ℝ) : ℂ)) =
      (cexp (-u) - cexp (-(z * u))) / (1 - cexp (-u)) := by
  have h1 : (1 : ℂ) + ((Real.exp u - 1 : ℝ) : ℂ) = ((Real.exp u : ℝ) : ℂ) := by push_cast; ring
  have he : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu
  have hE0 : cexp u ≠ 0 := Complex.exp_ne_zero _
  have hE1 : cexp u - 1 ≠ 0 := by
    rw [← ofReal_exp]
    exact_mod_cast (sub_pos.mpr he).ne'
  have hZ : cexp (u * z) ≠ 0 := Complex.exp_ne_zero _
  rw [h1, ofReal_exp_cpow, abs_of_pos (Real.exp_pos _), real_smul, ofReal_exp, Complex.exp_neg,
    show -(z * u) = -(u * z) by ring, Complex.exp_neg]
  push_cast
  have hE1' : 1 - (cexp u)⁻¹ ≠ 0 := by
    rw [show 1 - (cexp u)⁻¹ = (cexp u - 1) / cexp u by field_simp]
    exact div_ne_zero hE1 hE0
  field_simp

/-- **DLMF 5.9.14**: for `ℜz > 0`, `ψ(z) = ∫₀^∞ (e^{−t} − 1/(1 + t)^z) dt/t`. -/
theorem dlmf_5_9_14 {z : ℂ} (hz : 0 < z.re) :
    digamma z = ∫ t in Ioi (0 : ℝ), (cexp (-t) - 1 / (1 + (t : ℂ)) ^ z) / t := by
  set B : ℝ → ℂ := fun t => (1 / (1 + (t : ℂ)) - 1 / (1 + (t : ℂ)) ^ z) / t with hB
  have hder : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun u : ℝ => Real.exp u - 1) (Real.exp u)
      (Ioi 0) u := fun u _ => ((Real.hasDerivAt_exp u).sub_const 1).hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => Real.exp u - 1) (Ioi 0) := fun a _ b _ h => by
    simpa using h
  have hBi : IntegrableOn B (Ioi 0) := by
    rw [← image_exp_sub_one_Ioi, integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi hder hinj]
    exact (integrableOn_dlmf_5_9_16 hz).congr_fun (fun u hu => (psiShiftSubst hu).symm)
      measurableSet_Ioi
  have hBv : ∫ t in Ioi (0 : ℝ), B t = digamma z + γ := by
    rw [← image_exp_sub_one_Ioi, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder
      hinj, dlmf_5_9_16 hz]
    exact setIntegral_congr_fun measurableSet_Ioi fun u hu => psiShiftSubst hu
  have hAi : IntegrableOn (fun t : ℝ => (((1 / (1 + t) - Real.exp (-t)) / t : ℝ) : ℂ)) (Ioi 0) :=
    integrableOn_dlmf_5_9_18_2.ofReal
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (cexp (-t) - 1 / (1 + (t : ℂ)) ^ z) / t =
      -(((1 / (1 + t) - Real.exp (-t)) / t : ℝ) : ℂ) + B t := fun t ht => by
    have ht' : (0 : ℝ) < t := ht
    have h1 : (1 : ℂ) + t ≠ 0 := by exact_mod_cast (show (1 : ℝ) + t ≠ 0 by linarith)
    simp only [hB]
    push_cast
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hsum := integral_add (μ := volume.restrict (Ioi 0)) hAi.neg hBi
  simp only [Pi.neg_apply] at hsum
  rw [hsum, integral_neg, hBv, integral_complex_ofReal, ← dlmf_5_9_18_2]
  ring

end Azurite.DLMF
