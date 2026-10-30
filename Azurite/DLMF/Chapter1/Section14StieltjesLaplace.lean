/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14Stieltjes
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# DLMF §1.14(vi): the Stieltjes transform as an iterated Laplace transform (1.14.50)

Under DLMF's hypotheses both Laplace integrals may converge only conditionally (the outer one at
`0+` as well as at `∞`), so `ℒ` is read as an improper integral (`laplaceImp`).

* Inner integrals: `exists_laplace_bound`, `laplace_cauchy` (uniform for `x ≥ ε`, Abel's bound with
  the multiplier `lapH = (1 + t) e^{−xt}`), `tendsto_laplaceImp`, `continuous_laplacePartial`.
* `stieltjesPhi` (`Φ(y) = ∫_0^∞ f(t) e^{−(s+t)y}/(s + t) dt`): `tendsto_stieltjesPhi`,
  `tendsto_stieltjesPhi_atTop` (`Φ(X) → 0`), `tendsto_stieltjesPhi_zero` (Abelian theorem:
  `Φ(ε) → 𝒮f(s)`).
* `integral_box` (Fubini on `[ε, X] × [0, R]`), `tendsto_integral_box` (dominated convergence),
  `integral_laplace_eq_phi` (`∫_ε^X e^{−sx} ℒf(x) dx = Φ(ε) − Φ(X)`).
* **`dlmf_1_14_50`**: for `ℜs > 0`, `ℒf(x)` converges for all `x > 0` and
  `∫_ε^X e^{−sx} ℒf(x) dx → 𝒮f(s)` as `ε → 0+`, `X → ∞`.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real Interval

namespace Azurite.DLMF

/-- The Laplace transform `ℒf(x) = ∫_0^∞ e^{−xt} f(t) dt` as an improper integral (DLMF 1.14.17
read as in §1.4(v)). -/
noncomputable def laplaceImp (f : ℝ → ℝ) (x : ℂ) : ℂ :=
  limUnder atTop fun R => ∫ t in (0 : ℝ)..R, cexp (-(x * t)) * (f t : ℂ)

/-- `(1 + t) e^{−εt} ≤ 1 + 1/ε` for `t ≥ 0`. -/
theorem one_add_mul_exp_le {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    (1 + t) * Real.exp (-(ε * t)) ≤ 1 + 1 / ε := by
  have h1 := Real.add_one_le_exp (ε * t)
  have h2 : (1 + t) ≤ (1 + 1 / ε) * (1 + ε * t) := by
    rw [show (1 + 1 / ε) * (1 + ε * t) = 1 + t + 1 / ε + ε * t by field_simp; ring]
    have : 0 ≤ ε * t := by positivity
    have : 0 < 1 / ε := by positivity
    linarith
  calc (1 + t) * Real.exp (-(ε * t)) ≤ (1 + 1 / ε) * (1 + ε * t) * Real.exp (-(ε * t)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (1 + 1 / ε) * ((1 + ε * t) * Real.exp (-(ε * t))) := by ring
    _ ≤ (1 + 1 / ε) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← le_div_iff₀ (Real.exp_pos _), one_div, ← Real.exp_neg, neg_neg]
        linarith
    _ = 1 + 1 / ε := mul_one _

/-- The multiplier `h_x(t) = (1 + t) e^{−xt}` turning `f/(1 + t)` into `e^{−xt} f`. -/
noncomputable def lapH (x t : ℝ) : ℝ := (1 + t) * Real.exp (-(x * t))

noncomputable def lapH' (x t : ℝ) : ℝ := Real.exp (-(x * t)) * (1 - x * (1 + t))

theorem hasDerivAt_lapH (x t : ℝ) : HasDerivAt (lapH x) (lapH' x t) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-(x * t))) (Real.exp (-(x * t)) * -x) t := by
    simpa using ((hasDerivAt_id t).const_mul x).neg.exp
  convert ((hasDerivAt_id t).const_add 1).mul h1 using 1
  · funext y; simp [lapH]
  · simp only [lapH', id]; ring

/-- `‖h_x(R')‖ + ∫_R^{R'} |h_x′| ≤ 2 + 4/ε` for `x ≥ ε > 0`, `0 ≤ R ≤ R'`. -/
theorem lapH_bound {ε x R R' : ℝ} (hε : 0 < ε) (hx : ε ≤ x) (hR : 0 ≤ R) (hRR' : R ≤ R') :
    |lapH x R'| + ∫ t in R..R', |lapH' x t| ≤ 2 + 4 / ε := by
  have hx0 : 0 < x := hε.trans_le hx
  have hmono : ∀ t, 0 ≤ t → Real.exp (-(x * t)) ≤ Real.exp (-(ε * t)) := fun t ht =>
    Real.exp_le_exp.mpr (by nlinarith)
  have p1 : |lapH x R'| ≤ 1 + 1 / ε := by
    rw [abs_of_nonneg (by unfold lapH; exact mul_nonneg (by linarith) (Real.exp_pos _).le)]
    exact (mul_le_mul_of_nonneg_left (hmono R' (hR.trans hRR')) (by linarith)).trans
      (one_add_mul_exp_le hε (hR.trans hRR'))
  -- `∫_R^{R'} e^{−xt}(1 + x(1 + t)) dt = [−e^{−xt}(t + 1 + 2/x)]_R^{R'}`
  have hF : ∀ t ∈ uIcc R R', HasDerivAt (fun t : ℝ => -(Real.exp (-(x * t)) * (t + 1 + 2 / x)))
      (Real.exp (-(x * t)) * (1 + x * (1 + t))) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-(x * t))) (Real.exp (-(x * t)) * -x) t := by
      simpa using ((hasDerivAt_id t).const_mul x).neg.exp
    convert (h1.mul (((hasDerivAt_id t).add_const 1).add_const (2 / x))).neg using 1
    · funext y; simp
    · simp only [id]; field_simp; ring
  have p2 : ∫ t in R..R', |lapH' x t| ≤ 1 + 1 / ε + 2 / ε := by
    calc ∫ t in R..R', |lapH' x t| ≤ ∫ t in R..R', Real.exp (-(x * t)) * (1 + x * (1 + t)) := by
          refine intervalIntegral.integral_mono_on hRR' ?_ ?_ fun t ht => ?_
          · exact (Continuous.intervalIntegrable (by unfold lapH'; fun_prop) _ _).abs
          · exact Continuous.intervalIntegrable (by fun_prop) _ _
          · unfold lapH'
            rw [abs_mul, abs_of_pos (Real.exp_pos _)]
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            have : 0 ≤ x * (1 + t) := by nlinarith [ht.1]
            rw [abs_le]; constructor <;> linarith
      _ = Real.exp (-(x * R)) * (R + 1 + 2 / x) - Real.exp (-(x * R')) * (R' + 1 + 2 / x) := by
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
            (Continuous.intervalIntegrable (by fun_prop) _ _)]
          ring
      _ ≤ Real.exp (-(x * R)) * (R + 1) + Real.exp (-(x * R)) * (2 / x) := by
          have : 0 ≤ Real.exp (-(x * R')) * (R' + 1 + 2 / x) := by
            have := Real.exp_pos (-(x * R')); have : 0 ≤ R' := hR.trans hRR'; positivity
          nlinarith
      _ ≤ 1 + 1 / ε + 2 / ε := by
          have e1 : Real.exp (-(x * R)) * (R + 1) ≤ 1 + 1 / ε := by
            rw [mul_comm, add_comm R]
            exact (mul_le_mul_of_nonneg_left (hmono R hR) (by linarith)).trans
              (one_add_mul_exp_le hε hR)
          have e2 : Real.exp (-(x * R)) * (2 / x) ≤ 2 / ε := by
            have h1 : Real.exp (-(x * R)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
            have h2 : 2 / x ≤ 2 / ε := div_le_div_of_nonneg_left (by norm_num) hε hx
            calc _ ≤ 1 * (2 / x) := mul_le_mul_of_nonneg_right h1 (by positivity)
              _ ≤ 2 / ε := by linarith
          linarith
  have : 1 + 1 / ε + (1 + 1 / ε + 2 / ε) = 2 + 4 / ε := by ring
  linarith

theorem cexp_neg_mul_ofReal (x t : ℝ) : cexp (-((x : ℂ) * t)) = (Real.exp (-(x * t)) : ℂ) := by
  push_cast; ring_nf

theorem laplace_integrand_eq (f : ℝ → ℝ) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    cexp (-((x : ℂ) * t)) * (f t : ℂ) = (f t : ℂ) / (1 + t) * (lapH x t : ℂ) := by
  have hne : (1 + (t : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < 1 + t := by linarith
    exact_mod_cast this.ne'
  rw [cexp_neg_mul_ofReal, lapH]
  push_cast
  field_simp

/-- Abel's bound with the multiplier `h_x`. -/
theorem norm_integral_lapH_le {g : ℝ → ℂ} {x ε R R' B : ℝ}
    (hg : IntervalIntegrable g volume R R') (hε : 0 < ε) (hx : ε ≤ x) (hR : 0 ≤ R)
    (hRR' : R ≤ R') (hB : ∀ u ∈ Icc R R', ‖∫ t in R..u, g t‖ ≤ B) :
    ‖∫ t in R..R', g t * (lapH x t : ℂ)‖ ≤ B * (2 + 4 / ε) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB R ⟨le_rfl, hRR'⟩)
  have h := norm_integral_mul_le_abel hRR' hg (h := fun t => (lapH x t : ℂ))
    (h' := fun t => (lapH' x t : ℂ)) (fun t _ => (hasDerivAt_lapH x t).ofReal_comp)
    ((continuous_ofReal.comp (by unfold lapH'; fun_prop)).continuousOn) hB
  simp only [Complex.norm_real, Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left (lapH_bound hε hx hR hRR') hB0)

theorem intervalIntegrable_laplace {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) (x : ℝ)
    {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun t => cexp (-((x : ℂ) * t)) * (f t : ℂ)) volume 0 R := by
  have := intervalIntegrable_mul_of_continuousOn hf hR (k := fun t => cexp (-((x : ℂ) * t)))
    (by fun_prop)
  simpa [mul_comm] using this

theorem one_mem_slitPlane : (1 : ℂ) ∈ slitPlane := by rw [mem_slitPlane_iff]; left; norm_num

section Inner

variable {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) {s₀ : ℂ} (hs₀ : s₀ ∈ slitPlane)
  (hconv : StieltjesConverges f s₀)

include hf hs₀ hconv

/-- The partial Laplace integrals are bounded uniformly for `x ≥ ε`. -/
theorem exists_laplace_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ∀ x : ℝ, ε ≤ x → ∀ R : ℝ, 0 ≤ R →
    ‖∫ t in (0 : ℝ)..R, cexp (-((x : ℂ) * t)) * (f t : ℂ)‖ ≤ B * (2 + 4 / ε) := by
  set g : ℝ → ℂ := fun t => (f t : ℂ) / (1 + t) with hg
  have hgI : ∀ R, 0 ≤ R → IntervalIntegrable g volume 0 R := fun R hR => by
    simpa [hg] using intervalIntegrable_div_pow hf one_mem_slitPlane 1 hR
  obtain ⟨B, hB⟩ := exists_bound_of_tendsto_integral hgI
    (tendsto_stieltjesPartial hf hs₀ hconv one_mem_slitPlane)
  refine ⟨B, (norm_nonneg _).trans (hB 0 le_rfl), fun ε hε x hx R hR => ?_⟩
  rw [intervalIntegral.integral_congr (g := fun t => g t * (lapH x t : ℂ)) fun t ht => by
    rw [uIcc_of_le hR] at ht; exact laplace_integrand_eq f x ht.1]
  exact norm_integral_lapH_le (hgI R hR) hε hx le_rfl hR fun u hu => hB u hu.1

/-- Cauchy's criterion for the Laplace integrals, uniformly for `x ≥ ε`. -/
theorem laplace_cauchy {η : ℝ} (hη : 0 < η) : ∃ T : ℝ, 0 ≤ T ∧ ∀ ε : ℝ, 0 < ε → ∀ x : ℝ,
    ε ≤ x → ∀ R R' : ℝ, T ≤ R → R ≤ R' →
      ‖∫ t in R..R', cexp (-((x : ℂ) * t)) * (f t : ℂ)‖ ≤ η * (2 + 4 / ε) := by
  set g : ℝ → ℂ := fun t => (f t : ℂ) / (1 + t) with hg
  have hgI : ∀ R, 0 ≤ R → IntervalIntegrable g volume 0 R := fun R hR => by
    simpa [hg] using intervalIntegrable_div_pow hf one_mem_slitPlane 1 hR
  obtain ⟨T, hT0, hT⟩ := cauchy_of_tendsto_integral hgI
    (tendsto_stieltjesPartial hf hs₀ hconv one_mem_slitPlane) hη
  refine ⟨T, hT0, fun ε hε x hx R R' hR hRR' => ?_⟩
  have hR0 : 0 ≤ R := hT0.trans hR
  rw [intervalIntegral.integral_congr (g := fun t => g t * (lapH x t : ℂ)) fun t ht => by
    rw [uIcc_of_le hRR'] at ht; exact laplace_integrand_eq f x (hR0.trans ht.1)]
  exact norm_integral_lapH_le ((hgI R hR0).symm.trans (hgI R' (hR0.trans hRR'))) hε hx hR0 hRR'
    fun u hu => hT R u hR (hR.trans hu.1)

/-- For `x > 0` the Laplace integral `ℒf(x)` converges. -/
theorem tendsto_laplaceImp {x : ℝ} (hx : 0 < x) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, cexp (-((x : ℂ) * t)) * (f t : ℂ)) atTop
      (𝓝 (laplaceImp f x)) := by
  have hI : ∀ R, 0 ≤ R → IntervalIntegrable (fun t => cexp (-((x : ℂ) * t)) * (f t : ℂ))
      volume 0 R := fun R hR => intervalIntegrable_laplace hf x hR
  obtain ⟨L, hL⟩ := exists_tendsto_integral_of_cauchy hI fun η hη => by
    obtain ⟨T, hT0, hT⟩ := laplace_cauchy hf hs₀ hconv (η := η / (2 + 4 / x)) (by positivity)
    refine ⟨T, hT0, fun R R' hR hRR' => ?_⟩
    have := hT x hx x le_rfl R R' hR hRR'
    rwa [div_mul_cancel₀ _ (by positivity)] at this
  exact tendsto_nhds_limUnder ⟨L, hL⟩

end Inner

/-- The partial Laplace integrals are continuous in `x`. -/
theorem continuous_laplacePartial {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) {R : ℝ}
    (hR : 0 ≤ R) :
    Continuous fun x : ℝ => ∫ t in (0 : ℝ)..R, cexp (-((x : ℂ) * t)) * (f t : ℂ) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  have hfI := intervalIntegrable_of_integrableOn hf hR
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun t => Real.exp ((|x₀| + 1) * R) * |f t|) ?_ ?_ (hfI.abs.const_mul _) ?_
  · refine Eventually.of_forall fun x => ?_
    rw [uIoc_of_le hR]
    exact (intervalIntegrable_laplace hf x hR).1.aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
    refine ae_of_all _ fun t ht => ?_
    rw [uIoc_of_le hR] at ht
    rw [norm_mul, cexp_neg_mul_ofReal, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
    rw [Metric.mem_ball, Real.dist_eq] at hx
    have h1 : |x| ≤ |x₀| + 1 := by
      have := abs_sub_abs_le_abs_sub x x₀; linarith
    have h2 : -(x * t) ≤ |x| * t := by
      have := neg_abs_le x; nlinarith [ht.1]
    nlinarith [ht.1, ht.2, abs_nonneg x]
  · exact ae_of_all _ fun t _ => by fun_prop

/-! ### `Φ(y) = ∫_0^∞ f(t) e^{−(s+t)y}/(s + t) dt` -/

theorem norm_cexp_neg_add_mul (s : ℂ) (t y : ℝ) :
    ‖cexp (-((s + t) * y))‖ = Real.exp (-((s.re + t) * y)) := by
  rw [Complex.norm_exp]; congr 1; simp

theorem hasDerivAt_cexp_neg_mul (s : ℂ) (y t : ℝ) :
    HasDerivAt (fun t : ℝ => cexp (-((s + t) * y))) (cexp (-((s + t) * y)) * -(y : ℂ)) t := by
  have h : HasDerivAt (fun t : ℝ => -((s + (t : ℂ)) * y)) (-(y : ℂ)) t := by
    have := (((hasDerivAt_id t).ofReal_comp.const_add s).mul_const (y : ℂ)).neg
    convert this using 1
    · funext u; simp
    · simp
  exact h.cexp

/-- Abel's bound with the multiplier `e^{−(s+t)y}`: total variation `≤ e^{−(Re s + R)y}`. -/
theorem norm_integral_cexp_le {g : ℝ → ℂ} {s : ℂ} {y R R' B : ℝ} (hy : 0 ≤ y) (hRR' : R ≤ R')
    (hg : IntervalIntegrable g volume R R')
    (hB : ∀ u ∈ Icc R R', ‖∫ t in R..u, g t‖ ≤ B) :
    ‖∫ t in R..R', g t * cexp (-((s + t) * y))‖ ≤ B * Real.exp (-((s.re + R) * y)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB R ⟨le_rfl, hRR'⟩)
  have h := norm_integral_mul_le_abel hRR' hg (h := fun t => cexp (-((s + t) * y)))
    (h' := fun t => cexp (-((s + t) * y)) * -(y : ℂ)) (fun t _ => hasDerivAt_cexp_neg_mul s y t)
    (by fun_prop) hB
  have hint : ∫ u in R..R', ‖cexp (-((s + u) * y)) * -(y : ℂ)‖ =
      Real.exp (-((s.re + R) * y)) - Real.exp (-((s.re + R') * y)) := by
    have hd : ∀ t ∈ uIcc R R', HasDerivAt (fun t : ℝ => -Real.exp (-((s.re + t) * y)))
        (Real.exp (-((s.re + t) * y)) * y) t := fun t _ => by
      have := (((hasDerivAt_id t).const_add s.re).mul_const y).neg.exp.neg
      convert this using 1
      · funext u; simp
      · simp
    rw [intervalIntegral.integral_congr (g := fun t => Real.exp (-((s.re + t) * y)) * y)
      fun t _ => by
        simp only
        rw [norm_mul, norm_cexp_neg_add_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hy],
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (Continuous.intervalIntegrable (by fun_prop) _ _)]
    ring
  rw [hint, norm_cexp_neg_add_mul] at h
  calc _ ≤ B * (Real.exp (-((s.re + R') * y)) +
        (Real.exp (-((s.re + R) * y)) - Real.exp (-((s.re + R') * y)))) := h
    _ = B * Real.exp (-((s.re + R) * y)) := by ring

theorem exp_neg_re_le (s : ℂ) {y R : ℝ} (hy : 0 ≤ y) (hR : 0 ≤ R) :
    Real.exp (-((s.re + R) * y)) ≤ Real.exp (-(s.re * y)) :=
  Real.exp_le_exp.mpr (by nlinarith)

/-- `Φ(y) = ∫_0^∞ f(t) e^{−(s+t)y}/(s + t) dt` (improper). -/
noncomputable def stieltjesPhi (f : ℝ → ℝ) (s : ℂ) (y : ℝ) : ℂ :=
  limUnder atTop fun R => ∫ t in (0 : ℝ)..R, (f t : ℂ) / (s + t) * cexp (-((s + t) * y))

section Phi

variable {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) {s₀ : ℂ} (hs₀ : s₀ ∈ slitPlane)
  (hconv : StieltjesConverges f s₀) {s : ℂ} (hs : 0 < s.re)

theorem mem_slitPlane_of_re_pos {s : ℂ} (hs : 0 < s.re) : s ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl hs)

include hf hs in
theorem intervalIntegrable_phi (y : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun t => (f t : ℂ) / (s + t) * cexp (-((s + t) * y))) volume 0 R := by
  have := intervalIntegrable_mul_of_continuousOn hf hR
    (k := fun t => ((s + t) ^ 1)⁻¹ * cexp (-((s + t) * y)))
    ((continuousOn_inv_add_pow (mem_slitPlane_of_re_pos hs) 1 R).mul (by fun_prop))
  refine this.congr fun t _ => ?_
  simp only [pow_one]; ring

include hf hs₀ hconv hs

/-- `Φ(y)` converges for `y ≥ 0`. -/
theorem tendsto_stieltjesPhi {y : ℝ} (hy : 0 ≤ y) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, (f t : ℂ) / (s + t) * cexp (-((s + t) * y))) atTop
      (𝓝 (stieltjesPhi f s y)) := by
  have hsS := mem_slitPlane_of_re_pos hs
  have hgI : ∀ R, 0 ≤ R → IntervalIntegrable (fun t => (f t : ℂ) / (s + t)) volume 0 R :=
    fun R hR => by simpa using intervalIntegrable_div_pow hf hsS 1 hR
  obtain ⟨L, hL⟩ := exists_tendsto_integral_of_cauchy
    (fun R hR => intervalIntegrable_phi hf hs y hR)
    fun η hη => by
      obtain ⟨T, hT0, hT⟩ := cauchy_of_tendsto_integral hgI
        (tendsto_stieltjesPartial hf hs₀ hconv hsS) hη
      refine ⟨T, hT0, fun R R' hR hRR' => ?_⟩
      have hR0 := hT0.trans hR
      refine (norm_integral_cexp_le hy hRR' ((hgI R hR0).symm.trans (hgI R' (hR0.trans hRR')))
        fun u hu => hT R u hR (hR.trans hu.1)).trans ?_
      have : Real.exp (-((s.re + R) * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      nlinarith
  exact tendsto_nhds_limUnder ⟨L, hL⟩

/-- `Φ(X) → 0` as `X → ∞`. -/
theorem tendsto_stieltjesPhi_atTop : Tendsto (stieltjesPhi f s) atTop (𝓝 0) := by
  have hsS := mem_slitPlane_of_re_pos hs
  have hgI : ∀ R, 0 ≤ R → IntervalIntegrable (fun t => (f t : ℂ) / (s + t)) volume 0 R :=
    fun R hR => by simpa using intervalIntegrable_div_pow hf hsS 1 hR
  obtain ⟨B, hB⟩ := exists_bound_of_tendsto_integral hgI (tendsto_stieltjesPartial hf hs₀ hconv hsS)
  have hbound : ∀ X, 0 ≤ X → ‖stieltjesPhi f s X‖ ≤ B * Real.exp (-(s.re * X)) := by
    intro X hX
    refine le_of_tendsto (tendsto_stieltjesPhi hf hs₀ hconv hs hX).norm ?_
    filter_upwards [eventually_ge_atTop 0] with R hR
    refine (norm_integral_cexp_le hX hR (hgI R hR) fun u hu => hB u hu.1).trans ?_
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 le_rfl)
    exact mul_le_mul_of_nonneg_left (by simp) hB0
  have hlim : Tendsto (fun X : ℝ => B * Real.exp (-(s.re * X))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hs)).const_mul B
    simpa [Function.comp_def] using this
  exact squeeze_zero_norm' ((eventually_ge_atTop 0).mono hbound) hlim

/-- **Abel's theorem**: `Φ(ε) → 𝒮f(s)` as `ε → 0+`. -/
theorem tendsto_stieltjesPhi_zero :
    Tendsto (stieltjesPhi f s) (𝓝[>] 0) (𝓝 (stieltjes f s)) := by
  have hsS := mem_slitPlane_of_re_pos hs
  set gs : ℝ → ℂ := fun t => (f t : ℂ) / (s + t) with hgs
  have hgI : ∀ R, 0 ≤ R → IntervalIntegrable gs volume 0 R :=
    fun R hR => by simpa using intervalIntegrable_div_pow hf hsS 1 hR
  have hS := tendsto_stieltjesPartial hf hs₀ hconv hsS
  rw [Metric.tendsto_nhds]
  intro η' hη'
  obtain ⟨T, hT0, hT⟩ := cauchy_of_tendsto_integral hgI hS (η := η' / 4) (by positivity)
  set G := ∫ t in (0 : ℝ)..T, ‖gs t‖
  set K := ‖s‖ + T
  have hK : 0 ≤ K := by positivity
  have hlin : Tendsto (fun ε : ℝ => K * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((continuous_const_mul K).tendsto 0).mono_left nhdsWithin_le_nhds
  have hlin2 : Tendsto (fun ε : ℝ => 2 * K * ε * G) (𝓝[>] 0) (𝓝 0) := by
    have : Continuous fun ε : ℝ => 2 * K * ε * G := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlin.eventually (ge_mem_nhds one_pos),
    hlin2.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η' / 4))] with ε hε hKε hG
  have hε0 : 0 < ε := hε
  -- the bound on every partial integral
  have hR : ∀ R, T ≤ R → ‖(∫ t in (0 : ℝ)..R, gs t * cexp (-((s + t) * ε))) -
      ∫ t in (0 : ℝ)..R, gs t‖ ≤ η' / 4 + η' / 4 + η' / 4 := by
    intro R hTR
    have hR0 := hT0.trans hTR
    have hgh : ∀ a b, 0 ≤ a → a ≤ b → IntervalIntegrable (fun t => gs t * cexp (-((s + t) * ε)))
        volume a b := fun a b ha hab =>
      (intervalIntegrable_phi hf hs ε ha).symm.trans (intervalIntegrable_phi hf hs ε (ha.trans hab))
    have e : (∫ t in (0 : ℝ)..R, gs t * cexp (-((s + t) * ε))) - ∫ t in (0 : ℝ)..R, gs t =
        (∫ t in (0 : ℝ)..T, gs t * (cexp (-((s + t) * ε)) - 1)) +
        (∫ t in T..R, gs t * cexp (-((s + t) * ε))) - ∫ t in T..R, gs t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hgh 0 T le_rfl hT0)
          (hgh T R hT0 hTR),
        ← intervalIntegral.integral_add_adjacent_intervals (hgI T hT0)
          ((hgI T hT0).symm.trans (hgI R hR0))]
      have : ∫ t in (0 : ℝ)..T, gs t * (cexp (-((s + t) * ε)) - 1) =
          (∫ t in (0 : ℝ)..T, gs t * cexp (-((s + t) * ε))) - ∫ t in (0 : ℝ)..T, gs t := by
        simp_rw [mul_sub, mul_one]
        exact intervalIntegral.integral_sub (hgh 0 T le_rfl hT0) (hgI T hT0)
      rw [this]; ring
    rw [e]
    have h1 : ‖∫ t in (0 : ℝ)..T, gs t * (cexp (-((s + t) * ε)) - 1)‖ ≤ η' / 4 := by
      calc _ ≤ ∫ t in (0 : ℝ)..T, ‖gs t‖ * (2 * K * ε) := by
            refine intervalIntegral.norm_integral_le_of_norm_le hT0 (ae_of_all _ fun t ht => ?_)
              ((hgI T hT0).norm.mul_const _)
            rw [norm_mul]
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            have hz : ‖-((s + t) * ε)‖ ≤ K * ε := by
              rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε0.le]
              refine mul_le_mul_of_nonneg_right ?_ hε0.le
              refine (norm_add_le _ _).trans ?_
              rw [Complex.norm_real, Real.norm_of_nonneg ht.1.le]; linarith [ht.2]
            calc _ ≤ 2 * ‖-((s + t) * ε)‖ := Complex.norm_exp_sub_one_le (hz.trans hKε)
              _ ≤ 2 * K * ε := by linarith
        _ = 2 * K * ε * G := by rw [intervalIntegral.integral_mul_const]; ring
        _ ≤ η' / 4 := hG.le
    have h2 : ‖∫ t in T..R, gs t * cexp (-((s + t) * ε))‖ ≤ η' / 4 := by
      refine (norm_integral_cexp_le hε0.le hTR ((hgI T hT0).symm.trans (hgI R hR0))
        fun u hu => hT T u le_rfl hu.1).trans ?_
      have : Real.exp (-((s.re + T) * ε)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      nlinarith
    have h3 : ‖∫ t in T..R, gs t‖ ≤ η' / 4 := hT T R le_rfl hTR
    have h4 := norm_add_le (∫ t in (0 : ℝ)..T, gs t * (cexp (-((s + t) * ε)) - 1))
      (∫ t in T..R, gs t * cexp (-((s + t) * ε)))
    calc _ ≤ ‖(∫ t in (0 : ℝ)..T, gs t * (cexp (-((s + t) * ε)) - 1)) +
          ∫ t in T..R, gs t * cexp (-((s + t) * ε))‖ + ‖∫ t in T..R, gs t‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hlim := ((tendsto_stieltjesPhi hf hs₀ hconv hs hε0.le).sub hS).norm
  rw [dist_eq_norm]
  have := le_of_tendsto hlim ((eventually_ge_atTop T).mono hR)
  linarith

end Phi

/-! ### Fubini on a box and passage to the limit -/

/-- **Fubini on `[ε, X] × [0, R]`**:
`∫_ε^X e^{−sx} ∫_0^R e^{−xt} f(t) dt dx = ∫_0^R f(t)/(s+t) (e^{−(s+t)ε} − e^{−(s+t)X}) dt`. -/
theorem integral_box {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) {s : ℂ} (hs : 0 < s.re)
    {ε X R : ℝ} (hε : 0 < ε) (hεX : ε ≤ X) (hR : 0 ≤ R) :
    ∫ x in ε..X, cexp (-(s * x)) * ∫ t in (0 : ℝ)..R, cexp (-((x : ℂ) * t)) * (f t : ℂ) =
      (∫ t in (0 : ℝ)..R, (f t : ℂ) / (s + t) * cexp (-((s + t) * ε))) -
        ∫ t in (0 : ℝ)..R, (f t : ℂ) / (s + t) * cexp (-((s + t) * X)) := by
  set F : ℝ → ℝ → ℂ := fun x t => cexp (-(s * x)) * (cexp (-((x : ℂ) * t)) * (f t : ℂ))
  have hfI : IntegrableOn (fun t => (f t : ℂ)) (Ioc 0 R) :=
    ((hf R).mono_set Ioc_subset_Icc_self).ofReal
  have hFint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc ε X)).prod (volume.restrict (Ioc 0 R))) := by
    have hbd : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * ‖(f p.2 : ℂ)‖)
        ((volume.restrict (Ioc ε X)).prod (volume.restrict (Ioc 0 R))) :=
      (integrable_const (1 : ℝ)).mul_prod hfI.norm
    refine hbd.mono' ?_ ?_
    · exact ((Continuous.aestronglyMeasurable (by fun_prop :
        Continuous fun p : ℝ × ℝ => cexp (-(s * p.1)) * cexp (-((p.1 : ℂ) * p.2)))).mul
          hfI.aestronglyMeasurable.comp_snd).congr (ae_of_all _ fun p => by
            simp only [F, Function.uncurry, Pi.mul_apply, mul_assoc])
    · rw [Measure.prod_restrict]
      refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) fun p hp => ?_
      obtain ⟨hx, ht⟩ := hp
      simp only [Function.uncurry, F, norm_mul, one_mul]
      have h1 : ‖cexp (-(s * p.1))‖ ≤ 1 := by
        rw [Complex.norm_exp]; simp; nlinarith [hx.1, hε]
      have h2 : ‖cexp (-((p.1 : ℂ) * p.2))‖ ≤ 1 := by
        rw [cexp_neg_mul_ofReal, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
          Real.exp_le_one_iff]
        nlinarith [hx.1, ht.1]
      calc _ ≤ 1 * (1 * ‖(f p.2 : ℂ)‖) := by gcongr
        _ = ‖(f p.2 : ℂ)‖ := by ring
  have hinner : ∀ t ∈ Ioc 0 R, ∫ x in Ioc ε X, F x t =
      (f t : ℂ) / (s + t) * cexp (-((s + t) * ε)) -
        (f t : ℂ) / (s + t) * cexp (-((s + t) * X)) := by
    intro t ht
    have hne : s + t ≠ 0 := add_ofReal_ne_zero (mem_slitPlane_iff.mpr (Or.inl hs)) ht.1.le
    rw [← intervalIntegral.integral_of_le hεX]
    have e : ∀ x : ℝ, F x t = (f t : ℂ) * cexp (-(s + t) * x) := fun x => by
      simp only [F]; rw [← mul_assoc, ← Complex.exp_add]; ring_nf
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex (neg_ne_zero.mpr hne)]
    field_simp
    ring_nf
  have hL : ∫ x in ε..X, cexp (-(s * x)) * ∫ t in (0 : ℝ)..R, cexp (-((x : ℂ) * t)) * (f t : ℂ) =
      ∫ x in Ioc ε X, ∫ t in Ioc 0 R, F x t := by
    rw [intervalIntegral.integral_of_le hεX]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    rw [intervalIntegral.integral_of_le hR, ← integral_const_mul]
  rw [hL, integral_integral_swap hFint, ← intervalIntegral.integral_sub
    (intervalIntegrable_phi hf hs ε hR) (intervalIntegrable_phi hf hs X hR),
    intervalIntegral.integral_of_le hR]
  exact setIntegral_congr_fun measurableSet_Ioc hinner

section Final

variable {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) {s₀ : ℂ} (hs₀ : s₀ ∈ slitPlane)
  (hconv : StieltjesConverges f s₀) {s : ℂ} (hs : 0 < s.re)

include hf hs₀ hconv hs

/-- Passage to the limit `R → ∞` on the box (dominated convergence). -/
theorem tendsto_integral_box {ε X : ℝ} (hε : 0 < ε) (hεX : ε ≤ X) :
    Tendsto (fun R => ∫ x in ε..X, cexp (-(s * x)) *
        ∫ t in (0 : ℝ)..R, cexp (-((x : ℂ) * t)) * (f t : ℂ)) atTop
      (𝓝 (∫ x in ε..X, cexp (-(s * x)) * laplaceImp f x)) := by
  obtain ⟨B, hB0, hB⟩ := exists_laplace_bound hf hs₀ hconv
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => B * (2 + 4 / ε)) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [eventually_ge_atTop 0] with R hR
    exact ((by fun_prop : Continuous fun x : ℝ => cexp (-(s * x))).mul
      (continuous_laplacePartial hf hR)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 0] with R hR
    refine ae_of_all _ fun x hx => ?_
    rw [uIoc_of_le hεX] at hx
    rw [norm_mul]
    have h1 : ‖cexp (-(s * x))‖ ≤ 1 := by
      rw [Complex.norm_exp]; simp; nlinarith [hx.1, hε]
    calc _ ≤ 1 * (B * (2 + 4 / ε)) :=
          mul_le_mul h1 (hB ε hε x hx.1.le R hR) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · refine ae_of_all _ fun x hx => ?_
    rw [uIoc_of_le hεX] at hx
    exact (tendsto_laplaceImp hf hs₀ hconv (hε.trans hx.1)).const_mul _

/-- On the box, `∫_ε^X e^{−sx} ℒf(x) dx = Φ(ε) − Φ(X)`. -/
theorem integral_laplace_eq_phi {ε X : ℝ} (hε : 0 < ε) (hεX : ε ≤ X) :
    ∫ x in ε..X, cexp (-(s * x)) * laplaceImp f x = stieltjesPhi f s ε - stieltjesPhi f s X := by
  refine tendsto_nhds_unique (tendsto_integral_box hf hs₀ hconv hs hε hεX) ?_
  refine ((tendsto_stieltjesPhi hf hs₀ hconv hs hε.le).sub
    (tendsto_stieltjesPhi hf hs₀ hconv hs (hε.le.trans hεX))).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  exact (integral_box hf hs hε hεX hR).symm

/-- **DLMF 1.14.50**: `𝒮f = ℒ(ℒf)`.  If `f` is integrable on every `[0, R]` (in particular if it is
piecewise continuous on `[0, ∞)`) and (1.14.47) converges, then for `ℜs > 0` the Laplace transform
`ℒf(x) = ∫_0^∞ e^{−xt} f(t) dt` converges for every `x > 0`, and
`ℒ(ℒf)(s) = ∫_0^∞ e^{−sx} ℒf(x) dx = 𝒮f(s)`, the outer integral converging as an improper
integral at both ends (`ε → 0+`, `X → ∞`). -/
theorem dlmf_1_14_50 :
    (∀ x : ℝ, 0 < x → Tendsto (fun R => ∫ t in (0 : ℝ)..R, cexp (-((x : ℂ) * t)) * (f t : ℂ))
      atTop (𝓝 (laplaceImp f x))) ∧
    Tendsto (fun p : ℝ × ℝ => ∫ x in p.1..p.2, cexp (-(s * x)) * laplaceImp f x)
      (𝓝[>] 0 ×ˢ atTop) (𝓝 (stieltjes f s)) := by
  refine ⟨fun x hx => tendsto_laplaceImp hf hs₀ hconv hx, ?_⟩
  have h := ((tendsto_stieltjesPhi_zero hf hs₀ hconv hs).comp tendsto_fst).sub
    ((tendsto_stieltjesPhi_atTop hf hs₀ hconv hs).comp tendsto_snd)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [prod_mem_prod (Ioo_mem_nhdsGT one_pos) (eventually_ge_atTop (1 : ℝ))] with p hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  exact (integral_laplace_eq_phi hf hs₀ hconv hs h1 (h2.le.trans h3)).symm

end Final

end Azurite.DLMF
