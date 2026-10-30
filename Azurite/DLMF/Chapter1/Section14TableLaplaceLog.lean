/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14TableLaplace

/-!
# DLMF Table 1.14.4: Laplace transforms of `g(t)/t` (rows 13–16)

* Row 13 (`laplace_exp_sub_exp_div`, `dlmf_table_1_14_4_r13`): `(e^{−bt} − e^{−at})/t =
  ∫_0^1 (a − b) e^{−(b + v(a − b))t} dv` and Fubini give `ln(s + a) − ln(s + b)`, which is the
  principal `ln((s + a)/(s + b))` (`log_sub_log_of_re_pos`).
* Rows 14–15 (`2(1 − cosh(at))/t`, `2(1 − cos(at))/t`): two instances of row 13, combined with
  `log_add_log_of_im_eq_neg` (`(s + a)/s + (s − a)/s = 2`). Row 15 is row 14 at `ia`; for real `a`
  its condition `ℜs > |ℑa|` is DLMF's `ℜs > 0`.
* **Discrepancy (row 14).** DLMF's condition `ℜ(s + a) > 0` is insufficient: for `a = 1`, `s = 1/2`
  the integrand is not integrable (`dlmf_table_1_14_4_r14_condition`). The row is proved for
  `ℜs > |ℜa|`.
* Row 16 (`sin(at)/t`, real `a`, `ℜs > 0`): `sin(at)/t = ∫_0^1 a cos(avt) dv`, Fubini with row 8,
  and `d/dv arctan(va/s)` (`hasDerivAt_arctan_mul`) give the principal `arctan(a/s)`.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real

namespace Azurite.DLMF

/-! ### Logarithms -/

theorem log_eq_of_exp_eq {z u : ℂ} (h : cexp u = z) (h1 : -π < u.im) (h2 : u.im ≤ π) :
    Complex.log z = u := by
  rw [← h, log_exp h1 h2]

/-- `ln w₁ − ln w₂ = ln(w₁/w₂)` for `ℜw₁, ℜw₂ > 0`. -/
theorem log_sub_log_of_re_pos {w₁ w₂ : ℂ} (h1 : 0 < w₁.re) (h2 : 0 < w₂.re) :
    Complex.log w₁ - Complex.log w₂ = Complex.log (w₁ / w₂) := by
  have hw1 : w₁ ≠ 0 := fun h => by rw [h] at h1; simp at h1
  have hw2 : w₂ ≠ 0 := fun h => by rw [h] at h2; simp at h2
  have a1 := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl h1))
  have a2 := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl h2))
  refine (log_eq_of_exp_eq ?_ ?_ ?_).symm
  · rw [Complex.exp_sub, exp_log hw1, exp_log hw2]
  · rw [sub_im, log_im, log_im]; linarith
  · rw [sub_im, log_im, log_im]; linarith

theorem div_mem_slitPlane {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) : x / y ∈ slitPlane := by
  have hy0 : y ≠ 0 := fun h => by rw [h] at hy; simp at hy
  rw [mem_slitPlane_iff]
  by_contra hc
  push Not at hc
  have e : x = ((x / y).re : ℂ) * y := by
    rw [show ((x / y).re : ℂ) = x / y from Complex.ext (by simp) (by simp [hc.2])]
    field_simp
  have := congrArg Complex.re e
  rw [re_ofReal_mul] at this
  nlinarith [hc.1]

/-- `ln z₁ + ln z₂ = ln(z₁ z₂)` for `z₁, z₂` off the negative axis with `ℑz₁ = −ℑz₂`. -/
theorem log_add_log_of_im_eq_neg {z₁ z₂ : ℂ} (h1 : z₁ ∈ slitPlane) (h2 : z₂ ∈ slitPlane)
    (him : z₁.im = -z₂.im) : Complex.log z₁ + Complex.log z₂ = Complex.log (z₁ * z₂) := by
  have hz1 := slitPlane_ne_zero h1
  have hz2 := slitPlane_ne_zero h2
  have p1 : arg z₁ < π := arg_lt_pi_iff.mpr (by
    rw [mem_slitPlane_iff] at h1; rcases h1 with h | h; exacts [Or.inl h.le, Or.inr h])
  have p2 : arg z₂ < π := arg_lt_pi_iff.mpr (by
    rw [mem_slitPlane_iff] at h2; rcases h2 with h | h; exacts [Or.inl h.le, Or.inr h])
  have q1 := neg_pi_lt_arg z₁
  have q2 := neg_pi_lt_arg z₂
  have hs : -π < arg z₁ + arg z₂ ∧ arg z₁ + arg z₂ < π := by
    rcases lt_trichotomy z₁.im 0 with h | h | h
    · have := arg_neg_iff.mpr h
      have := arg_nonneg_iff.mpr (by linarith : 0 ≤ z₂.im)
      constructor <;> linarith
    · have hz2i : z₂.im = 0 := by linarith
      have e1 : arg z₁ = 0 := by
        rw [arg_eq_zero_iff]; rw [mem_slitPlane_iff] at h1
        exact ⟨by rcases h1 with h1 | h1 <;> [linarith; exact absurd h h1], h⟩
      have e2 : arg z₂ = 0 := by
        rw [arg_eq_zero_iff]; rw [mem_slitPlane_iff] at h2
        exact ⟨by rcases h2 with h2 | h2 <;> [linarith; exact absurd hz2i h2], hz2i⟩
      rw [e1, e2]; constructor <;> linarith [Real.pi_pos]
    · have := arg_nonneg_iff.mpr h.le
      have := arg_neg_iff.mpr (by linarith : z₂.im < 0)
      constructor <;> linarith
  refine (log_eq_of_exp_eq ?_ ?_ ?_).symm
  · rw [Complex.exp_add, exp_log hz1, exp_log hz2]
  · rw [add_im, log_im, log_im]; exact hs.1
  · rw [add_im, log_im, log_im]; exact hs.2.le

/-! ### Row 13: `(e^{−bt} − e^{−at})/t` -/

theorem re_path_ge {s a b : ℂ} {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    min (s + a).re (s + b).re ≤ (s + b + v * (a - b)).re := by
  have e : (s + b + v * (a - b)).re = (1 - v) * (s + b).re + v * (s + a).re := by
    simp only [add_re, mul_re, ofReal_re, ofReal_im, sub_re, zero_mul, sub_zero]; ring
  rw [e]
  have h1 := min_le_left (s + a).re (s + b).re
  have h2 := min_le_right (s + a).re (s + b).re
  nlinarith [hv.1, hv.2]

/-- Row 13 with integrability: `∫_0^∞ e^{−st}(e^{−bt} − e^{−at})/t dt = ln(s + a) − ln(s + b)`. -/
theorem laplace_exp_sub_exp_div {s a b : ℂ} (ha : 0 < (s + a).re) (hb : 0 < (s + b).re) :
    IntegrableOn (fun t : ℝ => cexp (-(s * t)) * ((cexp (-(b * t)) - cexp (-(a * t))) / t))
        (Ioi 0) ∧
      laplace (fun t => (cexp (-(b * t)) - cexp (-(a * t))) / t) s =
        Complex.log (s + a) - Complex.log (s + b) := by
  set m := min (s + a).re (s + b).re
  have hm : 0 < m := lt_min ha hb
  set μ := volume.restrict (Ioc (0 : ℝ) 1)
  set ν := volume.restrict (Ioi (0 : ℝ))
  set G : ℝ → ℝ → ℂ := fun v t => (a - b) * cexp (-((s + b + v * (a - b)) * t))
  have hGc : Continuous (Function.uncurry G) := by
    simp only [G, Function.uncurry_def]; fun_prop
  have hfin : IsFiniteMeasure μ := by simp only [μ]; infer_instance
  have hGi : Integrable (Function.uncurry G) (μ.prod ν) := by
    have hb' : Integrable (fun t : ℝ => Real.exp (-m * t)) ν := exp_neg_integrableOn_Ioi 0 hm
    refine ((integrable_const ‖a - b‖).mul_prod hb').mono' hGc.aestronglyMeasurable ?_
    rw [Measure.prod_restrict]
    refine (ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioi)).mpr
      (ae_of_all _ fun z hz => ?_)
    simp only [Function.uncurry, G, norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have hr := re_path_ge (s := s) (a := a) (b := b) ⟨hz.1.1.le, hz.1.2⟩
    have ht : 0 < z.2 := hz.2
    have : (-((s + b + (z.1 : ℂ) * (a - b)) * (z.2 : ℂ))).re =
        -((s + b + (z.1 : ℂ) * (a - b)).re * z.2) := by simp
    rw [this, neg_mul]
    exact neg_le_neg (mul_le_mul_of_nonneg_right hr ht.le)
  have hinner : ∀ t ∈ Ioi (0 : ℝ), ∫ v, G v t ∂μ =
      cexp (-(s * t)) * ((cexp (-(b * t)) - cexp (-(a * t))) / t) := fun t ht => by
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    simp only [μ, G]
    rw [← intervalIntegral.integral_of_le zero_le_one]
    rcases eq_or_ne a b with rfl | hab
    · simp
    have hc : -((a - b) * t) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (sub_ne_zero.mpr hab) ht0)
    have e : ∀ v : ℝ, (a - b) * cexp (-((s + b + v * (a - b)) * t)) =
        (a - b) * cexp (-((s + b) * t)) * cexp (-((a - b) * t) * v) := fun v => by
      rw [mul_assoc, ← Complex.exp_add]; ring_nf
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
    simp only [ofReal_one, mul_one, ofReal_zero, mul_zero, Complex.exp_zero]
    have e2 : cexp (-((s + b) * t)) * cexp (-((a - b) * t)) =
        cexp (-(s * t)) * cexp (-(a * t)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
    have e3 : cexp (-((s + b) * t)) = cexp (-(s * t)) * cexp (-(b * t)) := by
      rw [← Complex.exp_add]; ring_nf
    field_simp
    rw [mul_sub, e2, e3]
    ring
  have houter : ∀ v ∈ Ioc (0 : ℝ) 1, ∫ t, G v t ∂ν = (a - b) / (s + b + v * (a - b)) :=
    fun v hv => by
      have hr : 0 < (s + b + v * (a - b)).re := hm.trans_le (re_path_ge ⟨hv.1.le, hv.2⟩)
      simp only [ν, G]
      rw [integral_const_mul, integral_Ioi_cexp_neg hr]
      ring
  refine ⟨?_, ?_⟩
  · have hI : IntegrableOn (fun t => ∫ v, G v t ∂μ) (Ioi 0) := hGi.integral_prod_right
    exact hI.congr_fun hinner measurableSet_Ioi
  unfold laplace
  rw [← setIntegral_congr_fun measurableSet_Ioi hinner, ← integral_integral_swap hGi,
    setIntegral_congr_fun measurableSet_Ioc houter, ← intervalIntegral.integral_of_le zero_le_one]
  have hderiv : ∀ v ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun v : ℝ => Complex.log (s + b + v * (a - b)))
      ((a - b) / (s + b + v * (a - b))) v := fun v hv => by
    rw [uIcc_of_le zero_le_one] at hv
    have hr : 0 < (s + b + v * (a - b)).re := hm.trans_le (re_path_ge hv)
    have h1 : HasDerivAt (fun v : ℝ => s + b + v * (a - b)) (a - b) v := by
      have := ((hasDerivAt_id v).ofReal_comp.mul_const (a - b)).const_add (s + b)
      simpa using this
    have := h1.clog_real (Or.inl hr)
    simpa using this
  have hcont : ContinuousOn (fun v : ℝ => (a - b) / (s + b + v * (a - b))) (uIcc 0 1) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun v hv => ?_
    rw [uIcc_of_le zero_le_one] at hv
    have hr : 0 < (s + b + v * (a - b)).re := hm.trans_le (re_path_ge hv)
    intro h; rw [h] at hr; simp at hr
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [ofReal_one, one_mul, ofReal_zero, zero_mul, add_zero]
  ring_nf

/-- **Table 1.14.4, row 13**: `ℒ[(e^{−bt} − e^{−at})/t](s) = ln((s + a)/(s + b))` (`ℜs > −ℜa`,
`ℜs > −ℜb`; principal logarithm). -/
theorem dlmf_table_1_14_4_r13 {s a b : ℂ} (ha : 0 < (s + a).re) (hb : 0 < (s + b).re) :
    laplace (fun t => (cexp (-(b * t)) - cexp (-(a * t))) / t) s =
      Complex.log ((s + a) / (s + b)) := by
  rw [(laplace_exp_sub_exp_div ha hb).2, log_sub_log_of_re_pos ha hb]

/-! ### Rows 14–15: `2(1 − cosh(at))/t`, `2(1 − cos(at))/t` -/

/-- **Table 1.14.4, row 14**: `ℒ[2(1 − cosh(at))/t](s) = ln(1 − a²/s²)` for `ℜs > |ℜa|`. DLMF prints
the condition `ℜ(s + a) > 0`, which does not make the integral converge
(`dlmf_table_1_14_4_r14_condition`). -/
theorem dlmf_table_1_14_4_r14 {s a : ℂ} (h : |a.re| < s.re) :
    laplace (fun t => 2 * (1 - Complex.cosh (a * t)) / t) s =
      Complex.log (1 - a ^ 2 / s ^ 2) := by
  have hs : 0 < s.re := lt_of_le_of_lt (abs_nonneg _) h
  have hs0 : s ≠ 0 := fun e => by rw [e] at hs; simp at hs
  have h1 := re_add_pos_of_abs_re h
  have h2 : 0 < (s + -a).re := by rw [← sub_eq_add_neg]; exact re_sub_pos_of_abs_re h
  have h0 : 0 < (s + 0).re := by simpa using hs
  have A := laplace_exp_sub_exp_div (b := 0) h1 h0
  have B := laplace_exp_sub_exp_div (b := 0) h2 h0
  have e : ∀ t : ℝ, cexp (-(s * t)) * (2 * (1 - Complex.cosh (a * t)) / t) =
      cexp (-(s * t)) * ((cexp (-(0 * t)) - cexp (-(a * t))) / t) +
        cexp (-(s * t)) * ((cexp (-(0 * t)) - cexp (-(-a * t))) / t) := fun t => by
    rw [Complex.cosh]; simp only [zero_mul, neg_zero, Complex.exp_zero, neg_mul, neg_neg]
    ring
  unfold laplace
  simp_rw [e]
  rw [integral_add A.1 B.1]
  unfold laplace at A B
  rw [A.2, B.2, add_zero, log_sub_log_of_re_pos h1 hs, log_sub_log_of_re_pos h2 hs,
    log_add_log_of_im_eq_neg (div_mem_slitPlane h1 hs) (div_mem_slitPlane h2 hs)]
  · congr 1
    field_simp
    ring
  · have : (s + a) / s + (s + -a) / s = 2 := by field_simp; ring
    have := congrArg Complex.im this
    simp only [add_im] at this
    norm_num at this
    linarith

/-- DLMF's printed condition for row 14 is insufficient: for `a = 1`, `s = 1/2` one has
`ℜ(s + a) > 0`, but `e^{−st} · 2(1 − cosh(at))/t` is not integrable on `(0, ∞)`. -/
theorem dlmf_table_1_14_4_r14_condition :
    0 < ((1 / 2 : ℂ) + 1).re ∧ ¬ IntegrableOn
      (fun t : ℝ => cexp (-((1 / 2 : ℂ) * t)) * (2 * (1 - Complex.cosh (1 * t)) / t)) (Ioi 0) := by
  refine ⟨by norm_num, fun hint => ?_⟩
  have hge : ∀ t : ℝ, 10 ≤ t →
      1 ≤ ‖cexp (-((1 / 2 : ℂ) * t)) * (2 * (1 - Complex.cosh (1 * t)) / t)‖ := fun t ht => by
    have htp : 0 < t := by linarith
    have e : cexp (-((1 / 2 : ℂ) * t)) * (2 * (1 - Complex.cosh (1 * t)) / t) =
        ((Real.exp (-(t / 2)) * (2 * (1 - Real.cosh t) / t) : ℝ) : ℂ) := by
      push_cast; ring_nf
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    refine le_trans ?_ (neg_le_abs _)
    rw [show -(Real.exp (-(t / 2)) * (2 * (1 - Real.cosh t) / t)) =
      Real.exp (-(t / 2)) * (2 * (Real.cosh t - 1)) / t by ring, Real.cosh_eq]
    have hq := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ t / 2)
    have h1 : Real.exp (-(t / 2)) * Real.exp t = Real.exp (t / 2) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-(t / 2)) * Real.exp (-t) ≥ 0 := by positivity
    have h3 : Real.exp (-(t / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [one_le_div₀ htp]
    nlinarith
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi 10) := by
    refine (hint.mono_set (Ioi_subset_Ioi (by norm_num))).norm.mono' (by fun_prop)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
    rw [norm_one]; exact hge t (le_of_lt ht)
  rw [integrableOn_const_iff] at hc
  rcases hc with hc | hc
  · simp at hc
  · simp at hc

/-- **Table 1.14.4, row 15**: `ℒ[2(1 − cos(at))/t](s) = ln(1 + a²/s²)` for `ℜs > |ℑa|` (for real
`a`, DLMF's `ℜs > 0`). -/
theorem dlmf_table_1_14_4_r15 {s a : ℂ} (h : |a.im| < s.re) :
    laplace (fun t => 2 * (1 - Complex.cos (a * t)) / t) s = Complex.log (1 + a ^ 2 / s ^ 2) := by
  have h' : |(a * I).re| < s.re := by simpa using h
  have e : (fun t : ℝ => 2 * (1 - Complex.cos (a * t)) / t) =
      fun t : ℝ => 2 * (1 - Complex.cosh (a * I * t)) / t := by
    funext t; rw [show a * I * (t : ℂ) = a * t * I by ring, Complex.cosh_mul_I]
  rw [e, dlmf_table_1_14_4_r14 h']
  congr 1
  ring_nf
  rw [I_sq]
  ring

/-! ### Row 16: `sin(at)/t` -/

theorem hasDerivAt_arctan_mul {c : ℂ} (hc : c.re ≠ 0) (v : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.arctan (v * c)) (c / (1 + (v * c) ^ 2)) v := by
  have hre : ((v : ℂ) * c * I).re = -(v * c.im) := by simp
  have him : ((v : ℂ) * c * I).im = v * c.re := by simp
  have h1 : 1 - (v : ℂ) * c * I ≠ 0 := fun h => by
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp only [sub_re, one_re, hre, zero_re, sub_im, one_im, him, zero_im] at hr hi
    have hv : v = 0 := by
      rcases mul_eq_zero.mp (by linarith : v * c.re = 0) with h | h
      · exact h
      · exact absurd h hc
    rw [hv] at hr; simp at hr
  have h2 : 1 + (v : ℂ) * c * I ≠ 0 := fun h => by
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp only [add_re, one_re, hre, zero_re, add_im, one_im, him, zero_im] at hr hi
    have hv : v = 0 := by
      rcases mul_eq_zero.mp (by linarith : v * c.re = 0) with h | h
      · exact h
      · exact absurd h hc
    rw [hv] at hr; simp at hr
  have hu : HasDerivAt (fun v : ℝ => (v : ℂ) * c * I) (c * I) v := by
    have := ((hasDerivAt_id v).ofReal_comp.mul_const c).mul_const I
    simp only [id] at this
    exact this.congr_deriv (by push_cast; ring)
  have hq := ((hasDerivAt_const v (1 : ℂ)).add hu).div ((hasDerivAt_const v (1 : ℂ)).sub hu) h1
  have hslit : (1 + (v : ℂ) * c * I) / (1 - (v : ℂ) * c * I) ∈ slitPlane := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · refine Or.inr ?_
      set u := (v : ℂ) * c * I
      have hN : 0 < normSq (1 - u) := normSq_pos.mpr h1
      rw [div_im]
      simp only [add_im, sub_im, add_re, sub_re, one_im, one_re]
      have : (0 + u.im) * (1 - u.re) / normSq (1 - u) - (1 + u.re) * (0 - u.im) / normSq (1 - u)
          = 2 * u.im / normSq (1 - u) := by ring
      rw [this, him]
      exact div_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero hv hc)) hN.ne'
  have hl := (hq.clog_real hslit).const_mul (-I / 2)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, zero_add, zero_sub] at hl
  unfold Complex.arctan
  refine hl.congr_deriv ?_
  have h3 : 1 + ((v : ℂ) * c) ^ 2 ≠ 0 := by
    have : 1 + ((v : ℂ) * c) ^ 2 = (1 - (v : ℂ) * c * I) * (1 + (v : ℂ) * c * I) := by
      ring_nf; rw [I_sq]; ring
    rw [this]; exact mul_ne_zero h1 h2
  field_simp
  ring_nf
  rw [I_sq]
  ring_nf

/-- **Table 1.14.4, row 16**: `ℒ[sin(at)/t](s) = arctan(a/s)` (`a` real, `ℜs > 0`; principal
`arctan`). -/
theorem dlmf_table_1_14_4_r16 {s : ℂ} (hs : 0 < s.re) (a : ℝ) :
    laplace (fun t => Complex.sin (a * t) / t) s = Complex.arctan (a / s) := by
  have hs0 : s ≠ 0 := fun e => by rw [e] at hs; simp at hs
  rcases eq_or_ne a 0 with rfl | ha
  · simp [laplace, Complex.arctan]
  set c : ℂ := (a : ℂ) / s
  have hc : c.re ≠ 0 := by
    simp only [c, div_re, ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
    exact div_ne_zero (mul_ne_zero ha hs.ne') (normSq_pos.mpr hs0).ne'
  set μ := volume.restrict (Ioc (0 : ℝ) 1)
  set ν := volume.restrict (Ioi (0 : ℝ))
  set G : ℝ → ℝ → ℂ := fun v t => cexp (-(s * t)) * ((a * Real.cos (a * v * t) : ℝ) : ℂ)
  have hGc : Continuous (Function.uncurry G) := by
    simp only [G, Function.uncurry_def]; fun_prop
  have hfin : IsFiniteMeasure μ := by simp only [μ]; infer_instance
  have hGi : Integrable (Function.uncurry G) (μ.prod ν) := by
    have hb' : Integrable (fun t : ℝ => Real.exp (-s.re * t)) ν := exp_neg_integrableOn_Ioi 0 hs
    refine ((integrable_const |a|).mul_prod hb').mono' hGc.aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    simp only [Function.uncurry, G, norm_mul, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs]
    have : (-(s * (z.2 : ℂ))).re = -s.re * z.2 := by simp
    rw [this, mul_comm]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _)
      (Real.abs_cos_le_one _)) (Real.exp_pos _).le
  have hinner : ∀ t ∈ Ioi (0 : ℝ), ∫ v, G v t ∂μ =
      cexp (-(s * t)) * (Complex.sin (a * t) / t) := fun t ht => by
    have ht0 : t ≠ 0 := ne_of_gt ht
    simp only [μ, G]
    rw [integral_const_mul, integral_complex_ofReal, ← intervalIntegral.integral_of_le zero_le_one]
    have hp : ∀ v : ℝ, a * Real.cos (a * v * t) = a * (fun v => Real.cos v) ((a * t) * v) :=
      fun v => by simp only; ring_nf
    simp_rw [hp]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _
      (mul_ne_zero ha ht0), integral_cos, mul_zero, mul_one, Real.sin_zero, sub_zero,
      smul_eq_mul]
    congr 1
    rw [show (a : ℂ) * (t : ℂ) = ((a * t : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin]
    have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0
    push_cast
    field_simp
  have houter : ∀ v ∈ Ioc (0 : ℝ) 1, ∫ t, G v t ∂ν = a * (s / (s ^ 2 + (a * v : ℂ) ^ 2)) :=
    fun v _ => by
      have h8 := dlmf_table_1_14_4_r8 (s := s) (a := ((a * v : ℝ) : ℂ)) (by simpa using hs)
      unfold laplace at h8
      simp only [ν, G]
      push_cast at h8 ⊢
      rw [← h8, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      ring
  unfold laplace
  rw [← setIntegral_congr_fun measurableSet_Ioi hinner, ← integral_integral_swap hGi,
    setIntegral_congr_fun measurableSet_Ioc houter, ← intervalIntegral.integral_of_le zero_le_one]
  have hden : ∀ v : ℝ, s ^ 2 + (a * v : ℂ) ^ 2 ≠ 0 := fun v =>
    sq_add_sq_ne_zero_of_im (a := ((a * v : ℝ) : ℂ)) (by simpa using hs) |> fun h => by
      push_cast at h; exact h
  have hderiv : ∀ v ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun v : ℝ => Complex.arctan (v * c))
      (a * (s / (s ^ 2 + (a * v : ℂ) ^ 2))) v := fun v _ => by
    refine (hasDerivAt_arctan_mul hc v).congr_deriv ?_
    have := hden v
    have h3 : 1 + ((v : ℂ) * c) ^ 2 ≠ 0 := by
      simp only [c]
      intro h; apply this
      have : s ^ 2 + (a * v : ℂ) ^ 2 = s ^ 2 * (1 + ((v : ℂ) * (a / s)) ^ 2) := by
        field_simp
      rw [this, h, mul_zero]
    simp only [c]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_const.mul (continuous_const.div (by fun_prop) hden)).intervalIntegrable _ _)]
  simp [c, Complex.arctan]

end Azurite.DLMF
