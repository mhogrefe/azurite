/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section9Regions

/-!
# DLMF §5.9(i): trigonometric integrals

Formalizations of <https://dlmf.nist.gov/5.9>, equations 5.9.6–5.9.9. The integrals converge
conditionally at `∞`, so they are stated as limits of `∫₀^R` as `R → ∞`.

* An Abelian theorem (`tendsto_laplace_of_tendsto_integral`): if `∫₀^R g → L`, then
  `∫₀^∞ e^{−εt} g(t) dt → L` as `ε → 0+` (integration by parts against the bounded primitive,
  the substitution `t = u/ε` and dominated convergence).
* Convergence of `∫₁^R t^w e^{±it} dt` for `ℜw < 0` (`exists_tendsto_integral_cpow_mul_cexp`,
  one integration by parts).
* 5.9.6, `Γ(z) cos(½πz) = ∫₀^∞ t^{z−1} cos t dt`, `0 < ℜz < 1` (`dlmf_5_9_6`): the Abel means
  are `½Γ(z)((ε − i)^{−z} + (ε + i)^{−z})` by the complex Laplace transform of §5.9 (5.9.1).
* 5.9.7, `Γ(z) sin(½πz) = ∫₀^∞ t^{z−1} sin t dt`, `−1 < ℜz < 1` (`dlmf_5_9_7`, `z ≠ 0`; at
  `z = 0` the right side is Dirichlet's `π/2`, the limit of the left side): for `ℜz ≤ 0` the Abel
  means are continued analytically in `z` as Mellin transforms.
* 5.9.8–5.9.9, `Γ(1 + 1/n) cos(π/(2n)) = ∫₀^∞ cos(tⁿ) dt` and the sine analogue, `n ≥ 2`
  (`dlmf_5_9_8`, `dlmf_5_9_9`), by `u = tⁿ`.
-/

open Complex Filter Topology Set MeasureTheory Asymptotics
open scoped Real Nat

namespace Azurite.DLMF

/-! ### An Abelian theorem -/

theorem intervalIntegrable_of_continuousOn_Ioi {g : ℝ → ℂ} (hg : ContinuousOn g (Ioi 0))
    (hg0 : IntegrableOn g (Ioc 0 1)) {R : ℝ} (hR : 0 ≤ R) : IntervalIntegrable g volume 0 R := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR]
  refine (hg0.union ((hg.mono fun t ht => ?_).integrableOn_compact (isCompact_Icc (a := 1)
    (b := max 1 R)))).mono_set fun t ht => ?_
  · exact lt_of_lt_of_le one_pos ht.1
  · rcases le_or_gt t 1 with h | h
    · exact Or.inl ⟨ht.1, h⟩
    · exact Or.inr ⟨h.le, le_max_of_le_right ht.2⟩

/-- **Abelian theorem** for Laplace transforms: if `∫₀^R g → L` then
`∫₀^∞ e^{−εt} g(t) dt → L` as `ε → 0+`. -/
theorem tendsto_laplace_of_tendsto_integral {g : ℝ → ℂ} {L : ℂ} (hg : ContinuousOn g (Ioi 0))
    (hg0 : IntegrableOn g (Ioc 0 1))
    (hint : ∀ ε : ℝ, 0 < ε → IntegrableOn (fun t : ℝ => cexp (-(ε * t)) * g t) (Ioi 0))
    (hG : Tendsto (fun R => ∫ t in (0 : ℝ)..R, g t) atTop (𝓝 L)) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), cexp (-(ε * t)) * g t) (𝓝[>] 0) (𝓝 L) := by
  set G : ℝ → ℂ := fun R => ∫ t in (0 : ℝ)..R, g t with hGdef
  have hII : ∀ R, 0 ≤ R → IntervalIntegrable g volume 0 R := fun R hR =>
    intervalIntegrable_of_continuousOn_Ioi hg hg0 hR
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt G (g t) t := fun t ht =>
    intervalIntegral.integral_hasDerivAt_right (hII t (le_of_lt ht))
      (hg.stronglyMeasurableAtFilter isOpen_Ioi t ht) (hg.continuousAt (isOpen_Ioi.mem_nhds ht))
  have hcontI : ∀ T, 0 ≤ T → ContinuousOn G (Icc 0 T) := fun T hT => by
    have := intervalIntegral.continuousOn_primitive_interval' (hII T hT)
      (left_mem_uIcc (a := (0 : ℝ)) (b := T))
    rwa [uIcc_of_le hT] at this
  -- `G` is bounded on `[0, ∞)`
  obtain ⟨M, hM⟩ : ∃ M, ∀ t, 0 ≤ t → ‖G t‖ ≤ M := by
    obtain ⟨T, hT⟩ := eventually_atTop.mp (hG.norm.eventually (gt_mem_nhds (lt_add_one ‖L‖)))
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := max T 0)).exists_bound_of_continuousOn
      (hcontI _ (le_max_right _ _))
    refine ⟨max C (‖L‖ + 1), fun t ht => ?_⟩
    rcases le_or_gt t (max T 0) with h | h
    · exact (hC t ⟨ht, h⟩).trans (le_max_left _ _)
    · exact (hT t (le_of_lt (lt_of_le_of_lt (le_max_left _ _) h))).le.trans (le_max_right _ _)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 le_rfl)
  -- integration by parts: `∫ e^{−εt} g = ε ∫ e^{−εt} G`
  have hparts : ∀ ε : ℝ, 0 < ε → ∫ t in Ioi (0 : ℝ), cexp (-(ε * t)) * g t =
      ε * ∫ t in Ioi (0 : ℝ), cexp (-(ε * t)) * G t := fun ε hε => by
    have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => cexp (-(ε * t)))
        (-(ε : ℂ) * cexp (-(ε * t))) t := fun t _ => by
      have h1 : HasDerivAt (fun t : ℝ => -((ε : ℂ) * t)) (-(ε : ℂ)) t := by
        have := ((hasDerivAt_id (t : ℂ)).const_mul (ε : ℂ)).neg.comp_ofReal
        simpa using this
      simpa [mul_comm] using h1.cexp
    have hu'v : IntegrableOn (fun t : ℝ => -(ε : ℂ) * cexp (-(ε * t)) * G t) (Ioi 0) := by
      refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hε).const_mul (ε * M)) ?_
        ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
      · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
        exact ((by fun_prop : Continuous fun t : ℝ => -(ε : ℂ) * cexp (-(ε * t))).continuousAt.mul
          (hderiv t ht).continuousAt).continuousWithinAt
      · rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε,
          Complex.norm_exp]
        have : (-((ε : ℂ) * t)).re = -ε * t := by simp
        rw [this]
        nlinarith [mul_le_mul_of_nonneg_left (hM t (le_of_lt ht))
          (mul_nonneg hε.le (Real.exp_pos (-ε * t)).le)]
    have h0 : Tendsto (fun t : ℝ => cexp (-(ε * t)) * G t) (𝓝[>] 0) (𝓝 0) := by
      have hc : ContinuousWithinAt (fun t : ℝ => cexp (-(ε * t)) * G t) (Icc 0 1) 0 :=
        ((by fun_prop : Continuous fun t : ℝ => cexp (-(ε * t))).continuousWithinAt).mul
          (hcontI 1 zero_le_one 0 ⟨le_rfl, zero_le_one⟩)
      have := hc.tendsto.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
      rw [nhdsWithin_Ioo_eq_nhdsGT one_pos] at this
      simpa [hGdef] using this
    have hinf : Tendsto (fun t : ℝ => cexp (-(ε * t)) * G t) atTop (𝓝 0) := by
      have hb : Tendsto (fun t : ℝ => M * Real.exp (-ε * t)) atTop (𝓝 0) := by
        have := (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hε)).inv_tendsto_atTop
        simpa [Function.comp_def, Real.exp_neg, neg_mul] using this.const_mul M
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [eventually_ge_atTop 0] with t ht
      rw [norm_mul, Complex.norm_exp]
      have : (-((ε : ℂ) * t)).re = -ε * t := by simp
      rw [this, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM t ht) (Real.exp_pos _).le
    have := integral_Ioi_mul_deriv_eq_deriv_mul hu hderiv (hint ε hε) hu'v h0 hinf
    rw [this]
    simp only [sub_zero, zero_sub, neg_mul, integral_neg, neg_neg]
    rw [← integral_const_mul]
    congr 1
    funext t
    ring
  -- substitution `t = u/ε`
  have hsubst : ∀ ε : ℝ, 0 < ε → ε * ∫ t in Ioi (0 : ℝ), cexp (-(ε * t)) * G t =
      ∫ u in Ioi (0 : ℝ), cexp (-(u : ℂ)) * G (ε⁻¹ * u) := fun ε hε => by
    have := integral_comp_mul_left_Ioi (fun t : ℝ => cexp (-(ε * t)) * G t) 0 (inv_pos.mpr hε)
    simp only [mul_zero, inv_inv] at this
    rw [show (∫ u in Ioi (0 : ℝ), cexp (-(u : ℂ)) * G (ε⁻¹ * u)) =
      ∫ x in Ioi (0 : ℝ), cexp (-((ε : ℂ) * ((ε⁻¹ * x : ℝ) : ℂ))) * G (ε⁻¹ * x) from by
        refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
        push_cast
        rw [← mul_assoc, mul_inv_cancel₀ (ofReal_ne_zero.mpr hε.ne'), one_mul], this,
      Complex.real_smul]
  -- dominated convergence
  have hdct : Tendsto (fun ε : ℝ => ∫ u in Ioi (0 : ℝ), cexp (-(u : ℂ)) * G (ε⁻¹ * u))
      (𝓝[>] 0) (𝓝 (∫ u in Ioi (0 : ℝ), cexp (-(u : ℂ)) * L)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun u => M * Real.exp (-u)) ?_ ?_
      ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioi
      have hpos : 0 < ε⁻¹ * u := mul_pos (inv_pos.mpr hε) hu
      exact ((by fun_prop : Continuous fun u : ℝ => cexp (-(u : ℂ))).continuousAt.mul
        ((hderiv _ hpos).continuousAt.comp (continuousAt_const.mul continuousAt_id)))
        |>.continuousWithinAt
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => ?_)
      rw [norm_mul, Complex.norm_exp, mul_comm]
      simp only [neg_re, ofReal_re]
      exact mul_le_mul_of_nonneg_right
        (hM _ (mul_nonneg (inv_pos.mpr hε).le (le_of_lt hu))) (Real.exp_pos _).le
    · exact ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul M).congr
        (ae_of_all _ fun u => by simp)
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => ?_)
      refine Tendsto.const_mul _ (hG.comp ?_)
      exact (tendsto_inv_nhdsGT_zero.atTop_mul_const hu)
  have hone : ∫ u in Ioi (0 : ℝ), cexp (-(u : ℂ)) * L = L := by
    rw [integral_mul_const]
    have : ∫ u in Ioi (0 : ℝ), cexp (-(u : ℂ)) = 1 := by
      have h2 : (∫ u in Ioi (0 : ℝ), ((Real.exp (-u) : ℝ) : ℂ)) = 1 := by
        rw [integral_complex_ofReal, integral_exp_neg_Ioi_zero]; simp
      rw [← h2]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      push_cast; rfl
    rw [this, one_mul]
  rw [hone] at hdct
  refine hdct.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [hparts ε hε, hsubst ε hε]

/-! ### Convergence of `∫₁^R t^w e^{ict} dt` -/

theorem hasDerivAt_ofReal_cpow' (w : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ w) (w * (t : ℂ) ^ (w - 1)) t := by
  have h := ((hasDerivAt_id (t : ℂ)).cpow_const (c := w)
    (ofReal_mem_slitPlane.mpr ht)).comp_ofReal
  simpa using h

theorem norm_cexp_mul_I (c t : ℝ) : ‖cexp (c * I * t)‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- `∫₁^R t^w e^{ict} dt` converges as `R → ∞` when `ℜw < 0`, `c ≠ 0`. -/
theorem exists_tendsto_integral_cpow_mul_cexp {w : ℂ} (hw : w.re < 0) {c : ℝ} (hc : c ≠ 0) :
    ∃ L, Tendsto (fun R => ∫ t in (1 : ℝ)..R, (t : ℂ) ^ w * cexp (c * I * t)) atTop (𝓝 L) := by
  have hcI : (c : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hc) I_ne_zero
  set v : ℝ → ℂ := fun t => cexp (c * I * t) / (c * I) with hv
  have hvd : ∀ t : ℝ, HasDerivAt v (cexp (c * I * t)) t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => (c : ℂ) * I * t) ((c : ℂ) * I) t := by
      simpa using ((hasDerivAt_id (t : ℂ)).const_mul ((c : ℂ) * I)).comp_ofReal
    have := h1.cexp.div_const ((c : ℂ) * I)
    convert this using 1
    rw [mul_div_assoc, div_self hcI, mul_one]
  have hint : IntegrableOn (fun t : ℝ => w * (t : ℂ) ^ (w - 1) * v t) (Ioi 1) := by
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (a := w.re - 1) (by linarith)
      one_pos).const_mul (‖w‖ / |c|)) ?_
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
      exact (((hasDerivAt_ofReal_cpow' (w - 1) (lt_trans one_pos ht)).continuousAt.const_mul w).mul
        (hvd t).continuousAt).continuousWithinAt
    · have ht' : (0 : ℝ) < t := lt_trans one_pos ht
      rw [hv, norm_mul, norm_mul, norm_div, norm_cexp_mul_I, norm_cpow_eq_rpow_re_of_pos ht',
        norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs]
      simp only [sub_re, one_re, mul_one]
      rw [div_mul_eq_mul_div, mul_one_div]
  refine ⟨0 - (1 : ℂ) ^ w * v 1 - ∫ t in Ioi (1 : ℝ), w * (t : ℂ) ^ (w - 1) * v t, ?_⟩
  have hb : Tendsto (fun R : ℝ => (R : ℂ) ^ w * v R) atTop (𝓝 0) := by
    have hR0 : Tendsto (fun R : ℝ => R ^ w.re * (1 / |c|)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := -w.re) (by linarith)).mul_const (1 / |c|)
      simpa using this
    refine squeeze_zero_norm' ?_ hR0
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hR, hv, norm_div, norm_cexp_mul_I, norm_mul, norm_I,
      Complex.norm_real, Real.norm_eq_abs, mul_one]
  have hlim := (hb.sub_const ((1 : ℂ) ^ w * v 1)).sub
    (intervalIntegral_tendsto_integral_Ioi 1 hint tendsto_id)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with R hR
  have hsub : ∀ x ∈ uIcc (1 : ℝ) R, 0 < x := fun x hx => by
    rw [uIcc_of_le hR] at hx; exact lt_of_lt_of_le one_pos hx.1
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x hx => hasDerivAt_ofReal_cpow' w
    (hsub x hx)) (fun x _ => hvd x) ?_ ?_]
  · simp only [id, ofReal_one]
  · refine ContinuousOn.intervalIntegrable fun x hx => ?_
    exact ((hasDerivAt_ofReal_cpow' (w - 1) (hsub x hx)).continuousAt.const_mul w)
      |>.continuousWithinAt
  · exact (by fun_prop : Continuous fun t : ℝ => cexp (c * I * t)).intervalIntegrable _ _

/-! ### The Abel means -/

/-- `∫₀^∞ e^{−εt} t^{z−1} e^{ict} dt = Γ(z)(ε − ic)^{−z}` (`ℜz > 0`, `ε > 0`). -/
theorem integral_laplace_cpow_mul_cexp {z : ℂ} (hz : 0 < z.re) {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    ∫ t in Ioi (0 : ℝ), cexp (-(ε * t)) * ((t : ℂ) ^ (z - 1) * cexp (c * I * t)) =
      Gamma z * ((ε : ℂ) - c * I) ^ (-z) := by
  rw [← integral_cpow_mul_cexp_neg hz (by simpa using hε)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [show -(((ε : ℂ) - c * I) * t) = -(ε * t) + c * I * t by ring, Complex.exp_add]
  ring

theorem integrableOn_laplace_cpow_mul_cexp {z : ℂ} (hz : 0 < z.re) {ε : ℝ} (hε : 0 < ε)
    (c : ℝ) :
    IntegrableOn (fun t : ℝ => cexp (-(ε * t)) * ((t : ℂ) ^ (z - 1) * cexp (c * I * t)))
      (Ioi 0) := by
  refine (integrableOn_cpow_sub_one_mul_cexp_neg hz (z := (ε : ℂ) - c * I)
    (by simpa using hε)).congr_fun
    (fun t _ => ?_) measurableSet_Ioi
  dsimp only
  rw [show -(((ε : ℂ) - c * I) * t) = -(ε * t) + c * I * t by ring, Complex.exp_add]
  ring

theorem tendsto_cpow_neg_sub_I (z : ℂ) (c : ℝ) (hc : c ≠ 0) :
    Tendsto (fun ε : ℝ => ((ε : ℂ) - c * I) ^ (-z)) (𝓝[>] 0) (𝓝 ((-(c * I)) ^ (-z))) := by
  have hmem : -((c : ℂ) * I) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right; simpa using hc
  have h1 : Tendsto (fun ε : ℝ => (ε : ℂ) - c * I) (𝓝[>] 0) (𝓝 (-(c * I))) := by
    have hc : Continuous (fun ε : ℝ => (ε : ℂ) - c * I) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact (continuousAt_cpow_const hmem).tendsto.comp h1

theorem neg_I_cpow_neg (z : ℂ) : (-I) ^ (-z) = cexp (π / 2 * z * I) := by
  rw [cpow_def_of_ne_zero (neg_ne_zero.mpr I_ne_zero), log_neg_I]; ring_nf

theorem I_cpow_neg (z : ℂ) : I ^ (-z) = cexp (-(π / 2 * z * I)) := by
  rw [cpow_def_of_ne_zero I_ne_zero, log_I]; ring_nf

/-! ### Assembling the trigonometric integrals -/

theorem exists_tendsto_integral_zero {g : ℝ → ℂ} (hg : ContinuousOn g (Ioi 0))
    (hg0 : IntegrableOn g (Ioc 0 1))
    (h1 : ∃ L, Tendsto (fun R => ∫ t in (1 : ℝ)..R, g t) atTop (𝓝 L)) :
    ∃ L, Tendsto (fun R => ∫ t in (0 : ℝ)..R, g t) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := h1
  refine ⟨(∫ t in (0 : ℝ)..1, g t) + L, (hL.const_add _).congr' ?_⟩
  filter_upwards [eventually_ge_atTop 1] with R hR
  refine intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_of_continuousOn_Ioi hg hg0 zero_le_one) ?_
  refine ContinuousOn.intervalIntegrable (hg.mono fun x hx => ?_)
  rw [uIcc_of_le hR] at hx
  exact lt_of_lt_of_le one_pos hx.1

theorem tendsto_of_abel {g : ℝ → ℂ} {V : ℂ} (hg : ContinuousOn g (Ioi 0))
    (hg0 : IntegrableOn g (Ioc 0 1))
    (hint : ∀ ε : ℝ, 0 < ε → IntegrableOn (fun t : ℝ => cexp (-(ε * t)) * g t) (Ioi 0))
    (hconv : ∃ L, Tendsto (fun R => ∫ t in (0 : ℝ)..R, g t) atTop (𝓝 L))
    (hab : Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), cexp (-(ε * t)) * g t) (𝓝[>] 0) (𝓝 V)) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, g t) atTop (𝓝 V) := by
  obtain ⟨L, hL⟩ := hconv
  rwa [tendsto_nhds_unique (tendsto_laplace_of_tendsto_integral hg hg0 hint hL) hab] at hL

/-- `t^w (a e^{it} + b e^{−it})` has a convergent integral over `(1, ∞)` when `ℜw < 0`. -/
theorem exists_tendsto_integral_cpow_mul_trig {w : ℂ} (hw : w.re < 0) (a b : ℂ) :
    ∃ L, Tendsto (fun R => ∫ t in (1 : ℝ)..R, (t : ℂ) ^ w *
      (a * cexp (((1 : ℝ) : ℂ) * I * t) + b * cexp (((-1 : ℝ) : ℂ) * I * t))) atTop (𝓝 L) := by
  obtain ⟨L₁, h₁⟩ := exists_tendsto_integral_cpow_mul_cexp hw one_ne_zero
  obtain ⟨L₂, h₂⟩ := exists_tendsto_integral_cpow_mul_cexp hw (neg_ne_zero.mpr one_ne_zero)
  refine ⟨a * L₁ + b * L₂, ((h₁.const_mul a).add (h₂.const_mul b)).congr' ?_⟩
  filter_upwards [eventually_ge_atTop 1] with R hR
  have hc : ∀ c : ℝ, IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ w * cexp (c * I * t)) volume 1 R :=
    fun c => by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    rw [uIcc_of_le hR] at hx
    exact ((hasDerivAt_ofReal_cpow' w (lt_of_lt_of_le one_pos hx.1)).continuousAt.mul
      (by fun_prop : Continuous fun t : ℝ => cexp (c * I * t)).continuousAt).continuousWithinAt
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((hc 1).const_mul a) ((hc (-1)).const_mul b)]
  congr 1
  funext t
  ring

theorem ofReal_cos_eq_cexp (t : ℝ) : ((Real.cos t : ℝ) : ℂ) =
    1 / 2 * cexp (((1 : ℝ) : ℂ) * I * t) + 1 / 2 * cexp (((-1 : ℝ) : ℂ) * I * t) := by
  rw [ofReal_cos, ← mul_right_inj' (two_ne_zero : (2 : ℂ) ≠ 0), two_cos]
  push_cast
  ring_nf

theorem ofReal_sin_eq_cexp (t : ℝ) : ((Real.sin t : ℝ) : ℂ) =
    1 / (2 * I) * cexp (((1 : ℝ) : ℂ) * I * t) + -1 / (2 * I) * cexp (((-1 : ℝ) : ℂ) * I * t) := by
  rw [ofReal_sin, ← mul_right_inj' (two_ne_zero : (2 : ℂ) ≠ 0), two_sin]
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem continuousOn_cpow_mul (z : ℂ) {h : ℝ → ℂ} (hh : Continuous h) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * h t) (Ioi 0) := fun _ ht =>
  ((hasDerivAt_ofReal_cpow' (z - 1) ht).continuousAt.mul hh.continuousAt).continuousWithinAt

/-- **DLMF 5.9.6**: `Γ(z) cos(½πz) = ∫₀^∞ t^{z−1} cos t dt` (`0 < ℜz < 1`; limit of `∫₀^R`). -/
theorem dlmf_5_9_6 {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, (t : ℂ) ^ (z - 1) * Real.cos t) atTop
      (𝓝 (Gamma z * Complex.cos (π * z / 2))) := by
  have hg := continuousOn_cpow_mul z (h := fun t : ℝ => ((Real.cos t : ℝ) : ℂ)) (by fun_prop)
  have hg0 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * Real.cos t) (Ioc 0 1) := by
    refine Integrable.mono' (integrableOn_Ioc_cpow_sub_one z h0).norm
      (hg.mono Ioc_subset_Ioi_self |>.aestronglyMeasurable measurableSet_Ioc)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one t)
  have hsplit : ∀ ε : ℝ, ∀ t : ℝ, cexp (-(ε * t)) * ((t : ℂ) ^ (z - 1) * Real.cos t) =
      1 / 2 * (cexp (-(ε * t)) * ((t : ℂ) ^ (z - 1) * cexp (((1 : ℝ) : ℂ) * I * t))) +
        1 / 2 * (cexp (-(ε * t)) * ((t : ℂ) ^ (z - 1) * cexp (((-1 : ℝ) : ℂ) * I * t))) :=
    fun ε t => by rw [ofReal_cos_eq_cexp]; ring
  have hint : ∀ ε : ℝ, 0 < ε → IntegrableOn
      (fun t : ℝ => cexp (-(ε * t)) * ((t : ℂ) ^ (z - 1) * Real.cos t)) (Ioi 0) := fun ε hε => by
    simp_rw [hsplit ε]
    exact ((integrableOn_laplace_cpow_mul_cexp h0 hε 1).const_mul _).add
      ((integrableOn_laplace_cpow_mul_cexp h0 hε (-1)).const_mul _)
  have hconv := exists_tendsto_integral_zero hg hg0 (by
    obtain ⟨L, hL⟩ := exists_tendsto_integral_cpow_mul_trig (w := z - 1) (by simp; linarith)
      (1 / 2) (1 / 2)
    exact ⟨L, hL.congr fun R => by simp_rw [ofReal_cos_eq_cexp]⟩)
  refine tendsto_of_abel hg hg0 hint hconv ?_
  have hval : ∀ ε : ℝ, 0 < ε →
      ∫ t in Ioi (0 : ℝ), cexp (-(ε * t)) * ((t : ℂ) ^ (z - 1) * Real.cos t) =
        1 / 2 * (Gamma z * ((ε : ℂ) - ((1 : ℝ) : ℂ) * I) ^ (-z)) +
          1 / 2 * (Gamma z * ((ε : ℂ) - ((-1 : ℝ) : ℂ) * I) ^ (-z)) := fun ε hε => by
    simp_rw [hsplit ε]
    rw [integral_add ((integrableOn_laplace_cpow_mul_cexp h0 hε 1).const_mul _)
      ((integrableOn_laplace_cpow_mul_cexp h0 hε (-1)).const_mul _), integral_const_mul,
      integral_const_mul, integral_laplace_cpow_mul_cexp h0 hε,
      integral_laplace_cpow_mul_cexp h0 hε]
  have hlim := ((tendsto_cpow_neg_sub_I z 1 one_ne_zero).const_mul (Gamma z)
    |>.const_mul (1 / 2)).add
    ((tendsto_cpow_neg_sub_I z (-1) (neg_ne_zero.mpr one_ne_zero)).const_mul (Gamma z)
      |>.const_mul (1 / 2))
  have hV : 1 / 2 * (Gamma z * (-(((1 : ℝ) : ℂ) * I)) ^ (-z)) +
      1 / 2 * (Gamma z * (-(((-1 : ℝ) : ℂ) * I)) ^ (-z)) = Gamma z * Complex.cos (π * z / 2) := by
    push_cast
    rw [one_mul, neg_one_mul, neg_neg, neg_I_cpow_neg, I_cpow_neg, ← mul_right_inj'
      (two_ne_zero : (2 : ℂ) ≠ 0)]
    rw [show 2 * (Gamma z * Complex.cos (π * z / 2)) = Gamma z * (2 * Complex.cos (π * z / 2)) by
      ring, two_cos]
    ring_nf
  rw [← hV]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [hval ε hε]

/-- The Abel means of the sine integral, `∫₀^∞ e^{−εt} t^{z−1} sin t dt`. -/
noncomputable def sinAbel (ε : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), cexp (-(ε * t)) * ((t : ℂ) ^ (z - 1) * Real.sin t)

theorem norm_sinAbel_integrand_le {ε : ℝ} (z : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖cexp (-(ε * t)) * ((t : ℂ) ^ (z - 1) * Real.sin t)‖ ≤ t ^ z.re * Real.exp (-(ε * t)) := by
  rw [norm_mul, norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
    Real.norm_eq_abs]
  have h1 : |Real.sin t| ≤ t := by
    have := Real.abs_sin_le_abs (x := t); rwa [abs_of_pos ht] at this
  have h2 : t ^ (z - 1).re * t = t ^ z.re := by
    rw [sub_re, one_re, Real.rpow_sub ht, Real.rpow_one]; field_simp
  have : (-((ε : ℂ) * t)).re = -(ε * t) := by simp
  rw [this]
  calc Real.exp (-(ε * t)) * (t ^ (z - 1).re * |Real.sin t|)
      ≤ Real.exp (-(ε * t)) * (t ^ (z - 1).re * t) := by gcongr
    _ = _ := by rw [h2]; ring

theorem integrableOn_sinAbel {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : -1 < z.re) :
    IntegrableOn (fun t : ℝ => cexp (-(ε * t)) * ((t : ℂ) ^ (z - 1) * Real.sin t)) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_rpow_mul_exp_neg_mul hz hε) ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht =>
      norm_sinAbel_integrand_le z ht))
  refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
  exact ((by fun_prop : Continuous fun t : ℝ => cexp (-(ε * t))).continuousAt.mul
    ((hasDerivAt_ofReal_cpow' (z - 1) ht).continuousAt.mul
      (by fun_prop : Continuous fun t : ℝ => ((Real.sin t : ℝ) : ℂ)).continuousAt))
    |>.continuousWithinAt

theorem sinAbel_eq_mellin (ε : ℝ) (z : ℂ) :
    sinAbel ε z = mellin (fun t : ℝ => cexp (-(ε * t)) * Real.sin t) z := by
  unfold sinAbel mellin
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [smul_eq_mul]
  ring

theorem differentiableAt_sinAbel {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : -1 < z.re) :
    DifferentiableAt ℂ (sinAbel ε) z := by
  rw [show sinAbel ε = mellin (fun t : ℝ => cexp (-(ε * t)) * Real.sin t) from
    funext (sinAbel_eq_mellin ε)]
  refine mellin_differentiableAt_of_isBigO_rpow_exp (a := ε) (b := -1) hε ?_ ?_ ?_ hz
  · exact (by fun_prop : Continuous fun t : ℝ => cexp (-(ε * t)) * Real.sin t)
      |>.locallyIntegrable.locallyIntegrableOn _
  · refine IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, one_mul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have : (-((ε : ℂ) * t)).re = -ε * t := by simp
    rw [this]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sin_le_one t)
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, one_mul, neg_neg,
      Real.rpow_one, Real.norm_eq_abs, abs_of_pos ht']
    have : (-((ε : ℂ) * t)).re = -(ε * t) := by simp
    rw [this]
    have h1 : |Real.sin t| ≤ t := by
      have := Real.abs_sin_le_abs (x := t); rwa [abs_of_pos ht'] at this
    have h2 : Real.exp (-(ε * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    nlinarith [abs_nonneg (Real.sin t), Real.exp_pos (-(ε * t))]

/-- The Abel means of the sine integral in closed form: for `ℜz > −1`,
`z ∫₀^∞ e^{−εt} t^{z−1} sin t dt = Γ(z + 1) ((ε − i)^{−z} − (ε + i)^{−z})/(2i)`. -/
theorem mul_sinAbel_eq {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : -1 < z.re) :
    z * sinAbel ε z = Gamma (z + 1) *
      ((((ε : ℂ) - ((1 : ℝ) : ℂ) * I) ^ (-z) - ((ε : ℂ) - ((-1 : ℝ) : ℂ) * I) ^ (-z)) /
        (2 * I)) := by
  set U : Set ℂ := {w | -1 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hne : ∀ c : ℝ, (ε : ℂ) - (c : ℂ) * I ≠ 0 := fun c h => by
    have := congrArg re h; simp at this; linarith
  have hF : AnalyticOnNhd ℂ (fun w => w * sinAbel ε w) U :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      (differentiableAt_id.mul (differentiableAt_sinAbel hε hw)).differentiableWithinAt) hUo
  have hG : AnalyticOnNhd ℂ (fun w => Gamma (w + 1) *
      ((((ε : ℂ) - ((1 : ℝ) : ℂ) * I) ^ (-w) - ((ε : ℂ) - ((-1 : ℝ) : ℂ) * I) ^ (-w)) / (2 * I)))
      U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    have hw' : ∀ m : ℕ, w + 1 ≠ -m := fun m h => by
      have := congrArg re h
      simp only [add_re, one_re, neg_re, natCast_re] at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      simp only [mem_ofPred_eq, hU] at hw
      linarith
    refine (((differentiableAt_Gamma _ hw').comp w (differentiableAt_id.add_const 1)).mul
      ((((differentiableAt_id.neg.const_cpow (Or.inl (hne 1))).sub
        (differentiableAt_id.neg.const_cpow (Or.inl (hne (-1))))).div_const _)))
      |>.differentiableWithinAt
  refine eqOn_of_eq_on_pos_reals hF hG (convex_halfSpace_re_gt (-1)).isPreconnected hUo
    (by simp [hU]) (fun x hx _ => ?_) (show z ∈ U from hz)
  have hx' : 0 < (x : ℂ).re := by simpa using hx
  have hsplit : ∀ t : ℝ, cexp (-(ε * t)) * ((t : ℂ) ^ ((x : ℂ) - 1) * Real.sin t) =
      1 / (2 * I) * (cexp (-(ε * t)) * ((t : ℂ) ^ ((x : ℂ) - 1) * cexp (((1 : ℝ) : ℂ) * I * t))) +
        -1 / (2 * I) * (cexp (-(ε * t)) * ((t : ℂ) ^ ((x : ℂ) - 1) *
          cexp (((-1 : ℝ) : ℂ) * I * t))) := fun t => by rw [ofReal_sin_eq_cexp]; ring
  rw [sinAbel]
  simp_rw [hsplit]
  rw [integral_add ((integrableOn_laplace_cpow_mul_cexp hx' hε 1).const_mul _)
    ((integrableOn_laplace_cpow_mul_cexp hx' hε (-1)).const_mul _), integral_const_mul,
    integral_const_mul, integral_laplace_cpow_mul_cexp hx' hε,
    integral_laplace_cpow_mul_cexp hx' hε,
    Gamma_add_one _ (ofReal_ne_zero.mpr hx.ne')]
  ring

/-- **DLMF 5.9.7**: `Γ(z) sin(½πz) = ∫₀^∞ t^{z−1} sin t dt` (`−1 < ℜz < 1`, `z ≠ 0`; limit of
`∫₀^R`). At `z = 0` the integral is Dirichlet's `π/2`, the limit of the left side. -/
theorem dlmf_5_9_7 {z : ℂ} (h0 : -1 < z.re) (h1 : z.re < 1) (hz : z ≠ 0) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, (t : ℂ) ^ (z - 1) * Real.sin t) atTop
      (𝓝 (Gamma z * Complex.sin (π * z / 2))) := by
  have hg := continuousOn_cpow_mul z (h := fun t : ℝ => ((Real.sin t : ℝ) : ℂ)) (by fun_prop)
  have hg0 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * Real.sin t) (Ioc 0 1) := by
    refine Integrable.mono' (integrableOn_Ioc_cpow_sub_one (z + 1) (by simp; linarith)).norm
      (hg.mono Ioc_subset_Ioi_self |>.aestronglyMeasurable measurableSet_Ioc)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_))
    have h := norm_sinAbel_integrand_le (ε := 0) z ht.1
    simp only [ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul,
      Real.exp_zero, mul_one] at h
    rw [norm_cpow_eq_rpow_re_of_pos ht.1]
    simpa using h
  have hint : ∀ ε : ℝ, 0 < ε → IntegrableOn
      (fun t : ℝ => cexp (-(ε * t)) * ((t : ℂ) ^ (z - 1) * Real.sin t)) (Ioi 0) :=
    fun ε hε => integrableOn_sinAbel hε h0
  have hconv := exists_tendsto_integral_zero hg hg0 (by
    obtain ⟨L, hL⟩ := exists_tendsto_integral_cpow_mul_trig (w := z - 1) (by simp; linarith)
      (1 / (2 * I)) (-1 / (2 * I))
    exact ⟨L, hL.congr fun R => by simp_rw [ofReal_sin_eq_cexp]⟩)
  refine tendsto_of_abel hg hg0 hint hconv ?_
  have hval : ∀ ε : ℝ, 0 < ε → sinAbel ε z = Gamma z *
      ((((ε : ℂ) - ((1 : ℝ) : ℂ) * I) ^ (-z) - ((ε : ℂ) - ((-1 : ℝ) : ℂ) * I) ^ (-z)) / (2 * I)) :=
    fun ε hε => by
    have h := mul_sinAbel_eq hε h0
    rw [Gamma_add_one _ hz, mul_assoc] at h
    exact mul_left_cancel₀ hz h
  have hlim := ((tendsto_cpow_neg_sub_I z 1 one_ne_zero).sub
    (tendsto_cpow_neg_sub_I z (-1) (neg_ne_zero.mpr one_ne_zero))).div_const (2 * I)
    |>.const_mul (Gamma z)
  have hV : Gamma z * (((-(((1 : ℝ) : ℂ) * I)) ^ (-z) - (-(((-1 : ℝ) : ℂ) * I)) ^ (-z)) / (2 * I)) =
      Gamma z * Complex.sin (π * z / 2) := by
    congr 1
    push_cast
    rw [one_mul, neg_one_mul, neg_neg, neg_I_cpow_neg, I_cpow_neg,
      ← mul_right_inj' (two_ne_zero : (2 : ℂ) ≠ 0), two_sin]
    field_simp
    ring_nf
    rw [I_sq]
    ring_nf
  rw [← hV]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [← hval ε hε, sinAbel]

/-! ### 5.9.8–5.9.9 -/

/-- The substitution `u = tⁿ`: `∫₀^R h(tⁿ) dt = (1/n) ∫₀^{Rⁿ} u^{1/n − 1} h(u) du`. -/
theorem integral_comp_pow_eq {n : ℕ} (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : Continuous h) {R : ℝ}
    (hR : 0 ≤ R) :
    (((∫ t in (0 : ℝ)..R, h (t ^ n)) : ℝ) : ℂ) =
      1 / (n : ℂ) * ∫ u in (0 : ℝ)..R ^ n, (u : ℂ) ^ (((1 / n : ℝ) : ℂ) - 1) * h u := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set g : ℝ → ℝ := fun u => u ^ (1 / (n : ℝ) - 1) * h u / n with hg
  set f : ℝ → ℝ := fun t => t ^ n with hf
  set f' : ℝ → ℝ := fun t => n * t ^ (n - 1) with hf'
  have hRn : 0 ≤ R ^ n := pow_nonneg hR n
  have hgI : IntegrableOn g (Icc 0 (R ^ n)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    have hi := (intervalIntegral.intervalIntegrable_rpow' (r := 1 / (n : ℝ) - 1)
      (by have : 0 < 1 / (n : ℝ) := by positivity
          linarith) (a := 0) (b := R ^ n))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hRn] at hi
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R ^ n)).exists_bound_of_continuousOn
      hh.continuousOn
    refine Integrable.mono' (hi.norm.const_mul (C / n)) ?_
      ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun u hu => ?_))
    · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioc
      exact (((Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hu.1))).mul
        hh.continuousAt).div_const _).continuousWithinAt
    · have hC' := hC u (Ioc_subset_Icc_self hu)
      rw [hg, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hn0, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hu.1 _)]
      rw [Real.norm_eq_abs] at hC'
      have hp := Real.rpow_pos_of_pos hu.1 (1 / (n : ℝ) - 1)
      rw [div_le_iff₀ hn0]
      calc u ^ (1 / (n : ℝ) - 1) * |h u| ≤ u ^ (1 / (n : ℝ) - 1) * C := by gcongr
        _ = C / n * u ^ (1 / (n : ℝ) - 1) * n := by field_simp
  have hpt : ∀ t : ℝ, 0 < t → (g ∘ f) t * f' t = h (t ^ n) := fun t ht => by
    show (t ^ n) ^ (1 / (n : ℝ) - 1) * h (t ^ n) / n * (n * t ^ (n - 1)) = h (t ^ n)
    have : (t ^ n) ^ (1 / (n : ℝ) - 1) * t ^ (n - 1) = 1 := by
      rw [← Real.rpow_natCast t n, ← Real.rpow_mul ht.le, ← Real.rpow_natCast t (n - 1),
        ← Real.rpow_add ht, Nat.cast_sub hn]
      have : (n : ℝ) * (1 / n - 1) + ((n : ℝ) - (1 : ℕ)) = 0 := by field_simp; push_cast; ring
      rw [this, Real.rpow_zero]
    calc (t ^ n) ^ (1 / (n : ℝ) - 1) * h (t ^ n) / n * (n * t ^ (n - 1))
        = h (t ^ n) * ((t ^ n) ^ (1 / (n : ℝ) - 1) * t ^ (n - 1)) * ((n : ℝ) / n) := by ring
      _ = _ := by rw [this, div_self hn0.ne', mul_one, mul_one]
  have hsub := intervalIntegral.integral_comp_mul_deriv''' (a := 0) (b := R) (f := f) (f' := f')
    (g := g) (hf := (continuous_pow n).continuousOn)
    (hff' := fun x _ => (hasDerivAt_pow n x).hasDerivWithinAt)
    (hg_cont := by
      refine ContinuousOn.mono (s := Ioi 0) (fun u hu => ?_) ?_
      · exact (((Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hu))).mul
          hh.continuousAt).div_const _).continuousWithinAt
      · rintro _ ⟨t, ht, rfl⟩
        simp only [min_eq_left hR, max_eq_right hR] at ht
        exact pow_pos ht.1 n)
    (hg1 := hgI.mono_set (by
      rintro _ ⟨t, ht, rfl⟩
      rw [uIcc_of_le hR] at ht
      exact ⟨pow_nonneg ht.1 n, pow_le_pow_left₀ ht.1 ht.2 n⟩))
    (hg2 := by
      rw [uIcc_of_le hR, integrableOn_Icc_iff_integrableOn_Ioc]
      refine ((hh.comp (continuous_pow n)).continuousOn.integrableOn_compact
        (isCompact_Icc (a := 0) (b := R))).mono_set Ioc_subset_Icc_self |>.congr_fun
        (fun t ht => (hpt t ht.1).symm) measurableSet_Ioc)
  have hL : ∫ t in (0 : ℝ)..R, h (t ^ n) = ∫ t in (0 : ℝ)..R, (g ∘ f) t * f' t := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
    rw [uIoc_of_le hR] at ht
    exact (hpt t ht.1).symm
  rw [hL, hsub]
  simp only [hf, zero_pow (by omega : n ≠ 0)]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hRn] at hu
  simp only [hg]
  push_cast
  rw [Complex.ofReal_cpow hu.1]
  push_cast
  field_simp

theorem tendsto_comp_pow_of_tendsto {n : ℕ} (hn : 2 ≤ n) {h : ℝ → ℝ} (hh : Continuous h) {V : ℂ}
    (hT : Tendsto (fun R => ∫ u in (0 : ℝ)..R, (u : ℂ) ^ (((1 / n : ℝ) : ℂ) - 1) * h u) atTop
      (𝓝 V)) :
    Tendsto (fun R : ℝ => (((∫ t in (0 : ℝ)..R, h (t ^ n)) : ℝ) : ℂ)) atTop (𝓝 (1 / n * V)) := by
  have h1 : Tendsto (fun R : ℝ => R ^ n) atTop atTop := tendsto_pow_atTop (by omega)
  refine ((hT.comp h1).const_mul (1 / (n : ℂ))).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  rw [integral_comp_pow_eq (by omega) hh hR]
  rfl

theorem tendsto_real_of_tendsto_ofReal {F : ℝ → ℝ} {L : ℝ}
    (h : Tendsto (fun R => ((F R : ℝ) : ℂ)) atTop (𝓝 (L : ℂ))) : Tendsto F atTop (𝓝 L) := by
  have := (continuous_re.tendsto _).comp h
  simpa [Function.comp_def] using this

theorem one_div_mul_Gamma_eq {n : ℕ} (hn : 1 ≤ n) :
    1 / (n : ℂ) * Gamma (((1 / n : ℝ)) : ℂ) = ((Real.Gamma (1 + 1 / n) : ℝ) : ℂ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [add_comm, Real.Gamma_add_one (one_div_pos.mpr hn0).ne', ofReal_mul,
    ← Complex.Gamma_ofReal]
  push_cast
  ring

/-- **DLMF 5.9.8**: `Γ(1 + 1/n) cos(π/(2n)) = ∫₀^∞ cos(tⁿ) dt`, `n = 2, 3, …` (limit of `∫₀^R`). -/
theorem dlmf_5_9_8 {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, Real.cos (t ^ n)) atTop
      (𝓝 (Real.Gamma (1 + 1 / n) * Real.cos (π / (2 * n)))) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hz0 : 0 < (((1 / n : ℝ)) : ℂ).re := by simp; positivity
  have hz1 : (((1 / n : ℝ)) : ℂ).re < 1 := by
    simp only [ofReal_re]
    rw [div_lt_one hn0]
    exact_mod_cast (by omega : 1 < n)
  have h := tendsto_comp_pow_of_tendsto hn Real.continuous_cos (dlmf_5_9_6 hz0 hz1)
  refine tendsto_real_of_tendsto_ofReal ?_
  convert h using 2
  rw [← mul_assoc, one_div_mul_Gamma_eq (by omega)]
  push_cast
  ring_nf

/-- **DLMF 5.9.9**: `Γ(1 + 1/n) sin(π/(2n)) = ∫₀^∞ sin(tⁿ) dt`, `n = 2, 3, …` (limit of `∫₀^R`). -/
theorem dlmf_5_9_9 {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, Real.sin (t ^ n)) atTop
      (𝓝 (Real.Gamma (1 + 1 / n) * Real.sin (π / (2 * n)))) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hz0 : -1 < (((1 / n : ℝ)) : ℂ).re := by
    have := one_div_pos.mpr hn0
    simp only [ofReal_re]
    linarith
  have hz1 : (((1 / n : ℝ)) : ℂ).re < 1 := by
    simp only [ofReal_re]
    rw [div_lt_one hn0]
    exact_mod_cast (by omega : 1 < n)
  have hz : (((1 / n : ℝ)) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (one_div_pos.mpr hn0).ne'
  have h := tendsto_comp_pow_of_tendsto hn Real.continuous_sin (dlmf_5_9_7 hz0 hz1 hz)
  refine tendsto_real_of_tendsto_ofReal ?_
  convert h using 2
  rw [← mul_assoc, one_div_mul_Gamma_eq (by omega)]
  push_cast
  ring_nf

end Azurite.DLMF
