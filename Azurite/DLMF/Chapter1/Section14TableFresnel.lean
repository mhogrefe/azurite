/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14TableFourier
import Azurite.DLMF.Chapter1.Section14StieltjesAbel
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# DLMF Table 1.14.1: Fourier transforms of `sin(at²)` and `cos(at²)`

These are not Lebesgue integrable; the transform is `lim_{R→∞} (2π)^{−1/2} ∫_{−R}^{R}`.

* `fresnelPhase a y t = e^{i(at² + yt)}`; `norm_integral_fresnelPhase_le` (Abel's bound with
  `1/(2at + y)`), `fresnel_cauchy`, `tendsto_fresnelLim` (`∫_0^∞` converges).
* Abelian theorem `tendsto_fresnel_gauss` (`∫_0^∞ e^{−εt²} e^{i(at² + yt)} dt` → the improper
  integral as `ε → 0+`); `integral_gauss_fresnel` (Mathlib's `fourierIntegral_gaussian` with
  `b = ε − ia`), `fresnelLim_add_neg`, `tendsto_integral_fresnelPhase`
  (`∫_{−R}^{R} e^{i(at² + yt)} dt → fresnelG a y = √(π/a) e^{i(π/4 − y²/(4a))}`, `fresnelG_eq`).
* **`dlmf_table_1_14_1_r9`** (`sin(at²)`), **`dlmf_table_1_14_1_r10`** (`cos(at²)`).
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real

namespace Azurite.DLMF

/-- The phase `e^{i(at² + yt)}`. -/
noncomputable def fresnelPhase (a y t : ℝ) : ℂ := cexp (I * ((a * t ^ 2 + y * t : ℝ) : ℂ))

theorem norm_fresnelPhase (a y t : ℝ) : ‖fresnelPhase a y t‖ = 1 := by
  rw [fresnelPhase, mul_comm, Complex.norm_exp_ofReal_mul_I]

theorem continuous_fresnelPhase (a y : ℝ) : Continuous (fresnelPhase a y) := by
  unfold fresnelPhase; fun_prop

theorem hasDerivAt_fresnelPhase (a y t : ℝ) :
    HasDerivAt (fresnelPhase a y) (fresnelPhase a y t * (I * ((2 * a * t + y : ℝ) : ℂ))) t := by
  have h : HasDerivAt (fun t : ℝ => a * t ^ 2 + y * t) (2 * a * t + y) t := by
    have := ((hasDerivAt_pow 2 t).const_mul a).add ((hasDerivAt_id t).const_mul y)
    convert this using 1
    · funext u; simp
    · simp; ring
  exact ((h.ofReal_comp).const_mul I).cexp

/-- **The tail of the Fresnel integral** (Abel's bound with `h = 1/(2at + y)`):
`‖∫_R^{R'} e^{i(at² + yt)} dt‖ ≤ 2/(aR + 1)` for `R ≥ (|y| + 1)/a`. -/
theorem norm_integral_fresnelPhase_le {a y : ℝ} (ha : 0 < a) {R R' : ℝ}
    (hR : (|y| + 1) / a ≤ R) (hRR' : R ≤ R') :
    ‖∫ t in R..R', fresnelPhase a y t‖ ≤ 2 / (a * R + 1) := by
  have haR : |y| + 1 ≤ a * R := by rwa [div_le_iff₀ ha, mul_comm] at hR
  have hpos : ∀ t, R ≤ t → a * t + 1 ≤ 2 * a * t + y := fun t ht => by
    have := neg_abs_le y; nlinarith
  have hpos' : ∀ t, R ≤ t → 0 < 2 * a * t + y := fun t ht => by
    have h1 := hpos t ht
    have h2 : 0 < a * t + 1 := by nlinarith [abs_nonneg y]
    linarith
  set g : ℝ → ℂ := fun t => fresnelPhase a y t * ((2 * a * t + y : ℝ) : ℂ)
  set h : ℝ → ℂ := fun t => ((1 / (2 * a * t + y) : ℝ) : ℂ)
  set h' : ℝ → ℂ := fun t => ((-(2 * a) / (2 * a * t + y) ^ 2 : ℝ) : ℂ)
  have e : ∫ t in R..R', fresnelPhase a y t = ∫ t in R..R', g t * h t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hRR'] at ht
    have hne : ((2 * a * t + y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos' t ht.1).ne'
    simp only [g, h]; push_cast at hne ⊢; field_simp
  have hgI : IntervalIntegrable g volume R R' :=
    ((continuous_fresnelPhase a y).mul (by fun_prop)).intervalIntegrable _ _
  have hprim : ∀ u ∈ Icc R R', ‖∫ t in R..u, g t‖ ≤ 2 := by
    intro u hu
    have hd : ∀ t ∈ uIcc R u, HasDerivAt (fun t => fresnelPhase a y t / I) (g t) t := fun t _ => by
      convert (hasDerivAt_fresnelPhase a y t).div_const I using 1
      simp only [g]; field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (((continuous_fresnelPhase a y).mul (by fun_prop)).intervalIntegrable _ _), ← sub_div,
      norm_div, norm_I, div_one]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_fresnelPhase, norm_fresnelPhase]; norm_num
  have hh : ∀ t ∈ Icc R R', HasDerivAt h (h' t) t := fun t ht => by
    have hne := (hpos' t ht.1).ne'
    have := (((hasDerivAt_id t).const_mul (2 * a)).add_const y).inv hne
    convert this.ofReal_comp using 1
    · funext u; simp [h]
    · simp only [h', id]; push_cast; ring
  have hh' : ContinuousOn h' (Icc R R') := by
    refine (continuous_ofReal.comp_continuousOn ?_)
    exact continuousOn_const.div (by fun_prop) fun t ht => pow_ne_zero _ (hpos' t ht.1).ne'
  have hab := norm_integral_mul_le_abel hRR' hgI hh hh' hprim
  -- `∫ |h'| = h(R) − h(R')`
  have hint : ∫ u in R..R', ‖h' u‖ = 1 / (2 * a * R + y) - 1 / (2 * a * R' + y) := by
    have hd : ∀ t ∈ uIcc R R', HasDerivAt (fun t : ℝ => -(1 / (2 * a * t + y)))
        (2 * a / (2 * a * t + y) ^ 2) t := fun t ht => by
      rw [uIcc_of_le hRR'] at ht
      have hne := (hpos' t ht.1).ne'
      have := ((((hasDerivAt_id t).const_mul (2 * a)).add_const y).inv hne).neg
      convert this using 1
      · funext u; simp
      · simp only [id]; ring
    rw [intervalIntegral.integral_congr (g := fun t => 2 * a / (2 * a * t + y) ^ 2) fun t ht => by
        rw [uIcc_of_le hRR'] at ht
        simp only [h', Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_pow,
          abs_of_pos (by positivity : (0 : ℝ) < 2 * a), sq_abs],
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (ContinuousOn.intervalIntegrable (by
          rw [uIcc_of_le hRR']
          exact continuousOn_const.div (by fun_prop) fun t ht =>
            pow_ne_zero _ (hpos' t ht.1).ne'))]
    ring
  rw [e]
  refine hab.trans ?_
  simp only [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr
    (hpos' R' hRR')), hint]
  have h1 : 1 / (2 * a * R + y) ≤ 1 / (a * R + 1) :=
    one_div_le_one_div_of_le (by nlinarith [abs_nonneg y]) (hpos R le_rfl)
  have : 2 / (a * R + 1) = 2 * (1 / (a * R + 1)) := by ring
  linarith

/-- The improper half-line integral `∫_0^∞ e^{i(at² + yt)} dt`. -/
noncomputable def fresnelLim (a y : ℝ) : ℂ :=
  limUnder atTop fun R => ∫ t in (0 : ℝ)..R, fresnelPhase a y t

theorem fresnel_cauchy {a : ℝ} (ha : 0 < a) (y : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ T, 0 ≤ T ∧ ∀ R R', T ≤ R → R ≤ R' → ‖∫ t in R..R', fresnelPhase a y t‖ ≤ η := by
  refine ⟨max ((|y| + 1) / a) (2 / (a * η)), by positivity, fun R R' hR hRR' => ?_⟩
  refine (norm_integral_fresnelPhase_le ha ((le_max_left _ _).trans hR) hRR').trans ?_
  have hR2 : 2 / (a * η) ≤ R := (le_max_right _ _).trans hR
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR2
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ (by positivity)] at hR2
  nlinarith

theorem tendsto_fresnelLim {a : ℝ} (ha : 0 < a) (y : ℝ) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, fresnelPhase a y t) atTop (𝓝 (fresnelLim a y)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_integral_of_cauchy
    (fun R _ => (continuous_fresnelPhase a y).intervalIntegrable 0 R) fun η hη =>
      fresnel_cauchy ha y hη
  exact tendsto_nhds_limUnder ⟨L, hL⟩

theorem integrableOn_gauss_fresnel {ε : ℝ} (hε : 0 < ε) (a y : ℝ) (s : Set ℝ) :
    IntegrableOn (fun t : ℝ => (Real.exp (-(ε * t ^ 2)) : ℂ) * fresnelPhase a y t) s := by
  refine Integrable.integrableOn (Integrable.mono' (integrable_exp_neg_mul_sq hε)
    ((by fun_prop : Continuous fun t : ℝ => (Real.exp (-(ε * t ^ 2)) : ℂ)).mul
      (continuous_fresnelPhase a y)).aestronglyMeasurable (ae_of_all _ fun t => ?_))
  rw [norm_mul, norm_fresnelPhase, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul]

/-- **Abel's theorem for the Fresnel integral**: `∫_0^∞ e^{−εt²} e^{i(at² + yt)} dt` tends to the
improper integral as `ε → 0+`. -/
theorem tendsto_fresnel_gauss {a : ℝ} (ha : 0 < a) (y : ℝ) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), (Real.exp (-(ε * t ^ 2)) : ℂ) * fresnelPhase a y t)
      (𝓝[>] 0) (𝓝 (fresnelLim a y)) := by
  rw [Metric.tendsto_nhds]
  intro η' hη'
  set η := η' / 4
  have hη : 0 < η := by positivity
  obtain ⟨T, hT0, hT⟩ := fresnel_cauchy ha y hη
  have hlin : Tendsto (fun ε : ℝ => ε * T ^ 3) (𝓝[>] 0) (𝓝 0) := by
    have : Continuous fun ε : ℝ => ε * T ^ 3 := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlin.eventually (gt_mem_nhds hη)] with ε hε hεT
  have hε0 : 0 < ε := hε
  set k : ℝ → ℂ := fun t => (Real.exp (-(ε * t ^ 2)) : ℂ)
  have hkc : Continuous k := by fun_prop
  set φ := fresnelPhase a y
  have hφc : Continuous φ := continuous_fresnelPhase a y
  have hbound : ∀ R, T ≤ R → ‖(∫ t in (0 : ℝ)..R, k t * φ t) - ∫ t in (0 : ℝ)..R, φ t‖ ≤
      ε * T ^ 3 + η + η := by
    intro R hTR
    have hI : ∀ u v : ℝ, IntervalIntegrable (fun t => k t * φ t) volume u v := fun u v =>
      (hkc.mul hφc).intervalIntegrable u v
    have hI' : ∀ u v : ℝ, IntervalIntegrable φ volume u v := fun u v => hφc.intervalIntegrable u v
    have e : (∫ t in (0 : ℝ)..R, k t * φ t) - ∫ t in (0 : ℝ)..R, φ t =
        (∫ t in (0 : ℝ)..T, (k t - 1) * φ t) + (∫ t in T..R, k t * φ t) - ∫ t in T..R, φ t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hI 0 T) (hI T R),
        ← intervalIntegral.integral_add_adjacent_intervals (hI' 0 T) (hI' T R)]
      have : ∫ t in (0 : ℝ)..T, (k t - 1) * φ t =
          (∫ t in (0 : ℝ)..T, k t * φ t) - ∫ t in (0 : ℝ)..T, φ t := by
        simp_rw [sub_mul, one_mul]; exact intervalIntegral.integral_sub (hI 0 T) (hI' 0 T)
      rw [this]; ring
    rw [e]
    have h1 : ‖∫ t in (0 : ℝ)..T, (k t - 1) * φ t‖ ≤ ε * T ^ 3 := by
      calc _ ≤ ∫ t in (0 : ℝ)..T, ε * T ^ 2 := by
            refine intervalIntegral.norm_integral_le_of_norm_le hT0 (ae_of_all _ fun t ht => ?_)
              intervalIntegrable_const
            rw [norm_mul, norm_fresnelPhase, mul_one]
            simp only [k]
            rw [← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonpos (by linarith [Real.exp_le_one_iff.mpr (by nlinarith [ht.1] :
                -(ε * t ^ 2) ≤ 0)])]
            have := Real.add_one_le_exp (-(ε * t ^ 2))
            have : t ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ ht.1.le ht.2 2
            nlinarith
        _ = ε * T ^ 3 := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    have h2 : ‖∫ t in T..R, k t * φ t‖ ≤ η := by
      have hk : ∀ t ∈ Icc T R, HasDerivAt k ((-(2 * ε * t) * Real.exp (-(ε * t ^ 2)) : ℝ)) t :=
        fun t _ => by
          have := (((hasDerivAt_pow 2 t).const_mul ε).neg.exp).ofReal_comp
          convert this using 1
          first | (simp; done) | (simp; ring)
      have hab := norm_integral_mul_le_abel hTR (hI' T R) (h := k) hk
        ((continuous_ofReal.comp (by fun_prop)).continuousOn) fun u hu => hT T u le_rfl hu.1
      rw [show (fun t => φ t * k t) = fun t => k t * φ t from funext fun t => mul_comm _ _] at hab
      refine hab.trans ?_
      have hint : ∫ u in T..R, ‖(((-(2 * ε * u) * Real.exp (-(ε * u ^ 2))) : ℝ) : ℂ)‖ =
          Real.exp (-(ε * T ^ 2)) - Real.exp (-(ε * R ^ 2)) := by
        have hd : ∀ t ∈ uIcc T R, HasDerivAt (fun t : ℝ => -Real.exp (-(ε * t ^ 2)))
            (2 * ε * t * Real.exp (-(ε * t ^ 2))) t := fun t _ => by
          have := (((hasDerivAt_pow 2 t).const_mul ε).neg.exp).neg
          convert this using 1
          first | (simp; done) | (simp; ring)
        rw [intervalIntegral.integral_congr (g := fun t => 2 * ε * t * Real.exp (-(ε * t ^ 2)))
            fun t ht => by
              rw [uIcc_of_le hTR] at ht
              simp only [Complex.norm_real, Real.norm_eq_abs]
              rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by nlinarith [ht.1])
                (Real.exp_pos _).le)]
              ring,
          intervalIntegral.integral_eq_sub_of_hasDerivAt hd
            (Continuous.intervalIntegrable (by fun_prop) _ _)]
        ring
      rw [hint]
      simp only [k, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      have : Real.exp (-(ε * T ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      nlinarith
    have h3 : ‖∫ t in T..R, φ t‖ ≤ η := hT T R le_rfl hTR
    calc _ ≤ ‖(∫ t in (0 : ℝ)..T, (k t - 1) * φ t) + ∫ t in T..R, k t * φ t‖ +
          ‖∫ t in T..R, φ t‖ := norm_sub_le _ _
      _ ≤ _ := by
          have := norm_add_le (∫ t in (0 : ℝ)..T, (k t - 1) * φ t) (∫ t in T..R, k t * φ t)
          linarith
  have hlim1 : Tendsto (fun R => ∫ t in (0 : ℝ)..R, k t * φ t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), k t * φ t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_gauss_fresnel hε0 a y _) tendsto_id
  have := le_of_tendsto ((hlim1.sub (tendsto_fresnelLim ha y)).norm)
    ((eventually_ge_atTop T).mono hbound)
  rw [dist_eq_norm]
  have h4 : η' = 4 * η := by simp only [η]; ring
  simp only [k, φ] at this
  linarith

theorem fresnelPhase_neg (a y t : ℝ) : fresnelPhase a y (-t) = fresnelPhase a (-y) t := by
  unfold fresnelPhase; congr 3; ring

/-- The Gaussian-damped integrals: `∫_ℝ e^{−εt²} e^{i(at² + yt)} dt = (π/b)^{1/2} e^{−y²/(4b)}` with
`b = ε − ia`, split at `0`. -/
theorem integral_gauss_fresnel {ε : ℝ} (hε : 0 < ε) (a y : ℝ) :
    (∫ t in Ioi (0 : ℝ), (Real.exp (-(ε * t ^ 2)) : ℂ) * fresnelPhase a y t) +
      ∫ t in Ioi (0 : ℝ), (Real.exp (-(ε * t ^ 2)) : ℂ) * fresnelPhase a (-y) t =
    ((π : ℂ) / (ε - I * a)) ^ (1 / 2 : ℂ) * cexp (-(y : ℂ) ^ 2 / (4 * (ε - I * a))) := by
  have hb : 0 < ((ε : ℂ) - I * a).re := by simpa using hε
  have h := fourierIntegral_gaussian hb (y : ℂ)
  have e : (fun x : ℝ => cexp (I * (y : ℂ) * x) * cexp (-((ε : ℂ) - I * a) * (x : ℂ) ^ 2)) =
      fun t : ℝ => (Real.exp (-(ε * t ^ 2)) : ℂ) * fresnelPhase a y t := by
    funext t
    rw [fresnelPhase, ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    push_cast; ring_nf
  rw [e] at h
  rw [← h, integral_eq_Ioi_add_neg (integrableOn_gauss_fresnel hε a y _)
    ((integrableOn_gauss_fresnel hε a (-y) _).congr_fun (fun t _ => by
      simp only [fresnelPhase_neg, neg_sq]) measurableSet_Ioi)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [fresnelPhase_neg, neg_sq]

/-- `G(y) = (π/(−ia))^{1/2} e^{−y²/(4(−ia))}`, the value of `∫_ℝ e^{i(at² + yt)} dt`. -/
noncomputable def fresnelG (a y : ℝ) : ℂ :=
  ((π : ℂ) / (-(I * a))) ^ (1 / 2 : ℂ) * cexp (-(y : ℂ) ^ 2 / (4 * (-(I * a))))

theorem fresnelLim_add_neg {a : ℝ} (ha : 0 < a) (y : ℝ) :
    fresnelLim a y + fresnelLim a (-y) = fresnelG a y := by
  have h1 := (tendsto_fresnel_gauss ha y).add (tendsto_fresnel_gauss ha (-y))
  have hb0 : (-(I * (a : ℂ))) ≠ 0 := by
    simp only [neg_ne_zero]; exact mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr ha.ne')
  have hslit : (π : ℂ) / (-(I * a)) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right
    rw [show (π : ℂ) / (-(I * a)) = I * ((π / a : ℝ) : ℂ) by
      push_cast; field_simp; ring_nf; rw [I_sq]; ring]
    simp; exact ha.ne'
  have hcont : ContinuousAt
      (fun b : ℂ => ((π : ℂ) / b) ^ (1 / 2 : ℂ) * cexp (-(y : ℂ) ^ 2 / (4 * b)))
      (-(I * a)) := by
    refine ContinuousAt.mul ?_ ?_
    · exact (continuousAt_cpow_const hslit).comp (continuousAt_const.div continuousAt_id hb0)
    · exact (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
        (mul_ne_zero (by norm_num) hb0)).cexp
  have hb : Tendsto (fun ε : ℝ => ((ε : ℂ) - I * a)) (𝓝[>] 0) (𝓝 (-(I * a))) := by
    have : Continuous fun ε : ℝ => ((ε : ℂ) - I * a) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 := hcont.tendsto.comp hb
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_gauss_fresnel hε a y).symm

/-- `∫_{−R}^{R} e^{i(at² + yt)} dt → G(y)`. -/
theorem tendsto_integral_fresnelPhase {a : ℝ} (ha : 0 < a) (y : ℝ) :
    Tendsto (fun R => ∫ t in -R..R, fresnelPhase a y t) atTop (𝓝 (fresnelG a y)) := by
  rw [← fresnelLim_add_neg ha y]
  refine ((tendsto_fresnelLim ha y).add (tendsto_fresnelLim ha (-y))).congr fun R => ?_
  have hI : ∀ u v, IntervalIntegrable (fresnelPhase a y) volume u v := fun u v =>
    (continuous_fresnelPhase a y).intervalIntegrable u v
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI (-R) 0) (hI 0 R), add_comm]
  congr 1
  have := intervalIntegral.integral_comp_neg (a := 0) (b := R) (fresnelPhase a y)
  simp only [neg_zero] at this
  rw [← this]
  simp only [fresnelPhase_neg]

/-- `G(y) = √(π/a) e^{i(π/4 − y²/(4a))}`. -/
theorem fresnelG_eq {a : ℝ} (ha : 0 < a) (y : ℝ) :
    fresnelG a y = ((√(π / a) : ℝ) : ℂ) * cexp (I * ((π / 4 - y ^ 2 / (4 * a) : ℝ) : ℂ)) := by
  set r := π / a
  have hr : 0 < r := div_pos Real.pi_pos ha
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have h1 : (π : ℂ) / (-(I * a)) = (r : ℂ) * I := by
    simp only [r]; push_cast; field_simp; ring_nf; rw [I_sq]
  have h2 : ((r : ℂ) * I) ^ (1 / 2 : ℂ) = ((√r : ℝ) : ℂ) * cexp (I * ((π / 4 : ℝ) : ℂ)) := by
    rw [cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hr.ne') I_ne_zero),
      log_ofReal_mul hr I_ne_zero, log_I, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr, ofReal_exp,
      ← Complex.exp_add]
    congr 1; push_cast; ring
  have h3 : -(y : ℂ) ^ 2 / (4 * (-(I * a))) = I * ((-(y ^ 2 / (4 * a)) : ℝ) : ℂ) := by
    push_cast; field_simp; ring_nf; rw [I_sq]; ring
  unfold fresnelG
  rw [h1, h2, h3, mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

theorem fresnelPhase_conj (a y t : ℝ) :
    starRingEnd ℂ (fresnelPhase a y t) = cexp (-(I * ((a * t ^ 2 + y * t : ℝ) : ℂ))) := by
  rw [fresnelPhase, ← Complex.exp_conj]; simp

theorem intervalIntegral_conj (f : ℝ → ℂ) (u v : ℝ) :
    ∫ t in u..v, starRingEnd ℂ (f t) = starRingEnd ℂ (∫ t in u..v, f t) := by
  simp only [intervalIntegral, integral_conj, map_sub]

/-- `G + Ḡ = 2√(π/a) cos(π/4 − y²/(4a))` and `G − Ḡ = 2i√(π/a) sin(π/4 − y²/(4a))`. -/
theorem fresnelG_add_conj {a : ℝ} (ha : 0 < a) (y : ℝ) :
    fresnelG a y + starRingEnd ℂ (fresnelG a y) =
      2 * ((√(π / a) * Real.cos (π / 4 - y ^ 2 / (4 * a)) : ℝ) : ℂ) ∧
    fresnelG a y - starRingEnd ℂ (fresnelG a y) =
      2 * I * ((√(π / a) * Real.sin (π / 4 - y ^ 2 / (4 * a)) : ℝ) : ℂ) := by
  rw [fresnelG_eq ha y]
  set θ := π / 4 - y ^ 2 / (4 * a)
  have e : cexp (I * (θ : ℂ)) = Real.cos θ + Real.sin θ * I := by
    rw [mul_comm, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  rw [e]
  simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
  constructor <;> push_cast <;> ring

/-- **Table 1.14.1, row 10**: `𝓕[cos(at²)](x) = (2a)^{−1/2} cos(x²/(4a) − π/4)` (`a > 0`), the
integral converging as `lim_{R→∞} ∫_{−R}^{R}` (it is not absolutely convergent). -/
theorem dlmf_table_1_14_1_r10 {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Tendsto (fun R => ((√(2 * π) : ℝ) : ℂ)⁻¹ *
        ∫ t in -R..R, (Real.cos (a * t ^ 2) : ℂ) * cexp (I * x * t)) atTop
      (𝓝 ((1 / √(2 * a) * Real.cos (x ^ 2 / (4 * a) - π / 4) : ℝ) : ℂ)) := by
  have hpt : ∀ t : ℝ, (Real.cos (a * t ^ 2) : ℂ) * cexp (I * x * t) =
      (fresnelPhase a x t + starRingEnd ℂ (fresnelPhase a (-x) t)) / 2 := fun t => by
    rw [fresnelPhase_conj, fresnelPhase, ofReal_cos, Complex.cos, div_mul_eq_mul_div, add_mul,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 2 <;> (congr 1; push_cast; ring)
  have hI : ∀ y : ℝ, ∀ u v, IntervalIntegrable (fresnelPhase a y) volume u v := fun y u v =>
    (continuous_fresnelPhase a y).intervalIntegrable u v
  have hR : ∀ R : ℝ, ∫ t in -R..R, (Real.cos (a * t ^ 2) : ℂ) * cexp (I * x * t) =
      ((∫ t in -R..R, fresnelPhase a x t) +
        starRingEnd ℂ (∫ t in -R..R, fresnelPhase a (-x) t)) / 2 := fun R => by
    simp_rw [hpt]
    have hc : IntervalIntegrable (fun t => starRingEnd ℂ (fresnelPhase a (-x) t)) volume (-R) R :=
      (continuous_conj.comp (continuous_fresnelPhase a (-x))).intervalIntegrable _ _
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hI x _ _) hc,
      intervalIntegral_conj]
  simp_rw [hR]
  have hlim := (((tendsto_integral_fresnelPhase ha x).add
    ((continuous_conj.tendsto _).comp (tendsto_integral_fresnelPhase ha (-x)))).div_const
      2).const_mul
    ((√(2 * π) : ℝ) : ℂ)⁻¹
  have hG : fresnelG a (-x) = fresnelG a x := by simp [fresnelG]
  rw [hG, (fresnelG_add_conj ha x).1] at hlim
  refine hlim.congr' (Eventually.of_forall fun R => rfl) |>.trans (le_of_eq ?_)
  congr 1
  rw [show x ^ 2 / (4 * a) - π / 4 = -(π / 4 - x ^ 2 / (4 * a)) by ring, Real.cos_neg]
  have h1 : (√(2 * π) : ℝ) ≠ 0 := by positivity
  have h2 : (√(2 * a) : ℝ) ≠ 0 := by positivity
  have e : √(π / a) = √(2 * π) / √(2 * a) := by
    rw [Real.sqrt_div' π ha.le, Real.sqrt_mul' 2 Real.pi_pos.le, Real.sqrt_mul' 2 ha.le]
    have : √2 ≠ 0 := by positivity
    field_simp
  rw [e]
  push_cast
  field_simp

/-- **Table 1.14.1, row 9**: `𝓕[sin(at²)](x) = −(2a)^{−1/2} sin(x²/(4a) − π/4)` (`a > 0`), the
integral converging as `lim_{R→∞} ∫_{−R}^{R}`. -/
theorem dlmf_table_1_14_1_r9 {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Tendsto (fun R => ((√(2 * π) : ℝ) : ℂ)⁻¹ *
        ∫ t in -R..R, (Real.sin (a * t ^ 2) : ℂ) * cexp (I * x * t)) atTop
      (𝓝 ((-(1 / √(2 * a)) * Real.sin (x ^ 2 / (4 * a) - π / 4) : ℝ) : ℂ)) := by
  have hpt : ∀ t : ℝ, (Real.sin (a * t ^ 2) : ℂ) * cexp (I * x * t) =
      (fresnelPhase a x t - starRingEnd ℂ (fresnelPhase a (-x) t)) / (2 * I) := fun t => by
    rw [fresnelPhase_conj, fresnelPhase, ofReal_sin, Complex.sin]
    have e1 : cexp (-((a * t ^ 2 : ℝ) : ℂ) * I) * cexp (I * x * t) =
        cexp (-(I * ((a * t ^ 2 + -x * t : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : cexp (((a * t ^ 2 : ℝ) : ℂ) * I) * cexp (I * x * t) =
        cexp (I * ((a * t ^ 2 + x * t : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [← e1, ← e2]
    field_simp
    ring_nf
    rw [I_sq]; ring
  have hI : ∀ y : ℝ, ∀ u v, IntervalIntegrable (fresnelPhase a y) volume u v := fun y u v =>
    (continuous_fresnelPhase a y).intervalIntegrable u v
  have hR : ∀ R : ℝ, ∫ t in -R..R, (Real.sin (a * t ^ 2) : ℂ) * cexp (I * x * t) =
      ((∫ t in -R..R, fresnelPhase a x t) -
        starRingEnd ℂ (∫ t in -R..R, fresnelPhase a (-x) t)) / (2 * I) := fun R => by
    simp_rw [hpt]
    have hc : IntervalIntegrable (fun t => starRingEnd ℂ (fresnelPhase a (-x) t)) volume (-R) R :=
      (continuous_conj.comp (continuous_fresnelPhase a (-x))).intervalIntegrable _ _
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (hI x _ _) hc,
      intervalIntegral_conj]
  simp_rw [hR]
  have hlim := (((tendsto_integral_fresnelPhase ha x).sub
    ((continuous_conj.tendsto _).comp (tendsto_integral_fresnelPhase ha (-x)))).div_const
      (2 * I)).const_mul ((√(2 * π) : ℝ) : ℂ)⁻¹
  have hG : fresnelG a (-x) = fresnelG a x := by simp [fresnelG]
  rw [hG, (fresnelG_add_conj ha x).2] at hlim
  refine hlim.congr' (Eventually.of_forall fun R => rfl) |>.trans (le_of_eq ?_)
  congr 1
  rw [show x ^ 2 / (4 * a) - π / 4 = -(π / 4 - x ^ 2 / (4 * a)) by ring, Real.sin_neg]
  have h1 : (√(2 * π) : ℝ) ≠ 0 := by positivity
  have h2 : (√(2 * a) : ℝ) ≠ 0 := by positivity
  have e : √(π / a) = √(2 * π) / √(2 * a) := by
    rw [Real.sqrt_div' π ha.le, Real.sqrt_mul' 2 Real.pi_pos.le, Real.sqrt_mul' 2 ha.le]
    have : √2 ≠ 0 := by positivity
    field_simp
  rw [e]
  push_cast
  field_simp

end Azurite.DLMF
