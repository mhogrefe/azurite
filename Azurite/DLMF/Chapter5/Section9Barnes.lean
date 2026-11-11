/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section9
import Azurite.DLMF.Chapter1.Section14TableCos
import Azurite.DLMF.Chapter1.Section14TableMellinLog
import Azurite.DLMF.Chapter1.Section14HilbertDense
import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# DLMF §5.9(i): equation 5.9.11

Formalization of <https://dlmf.nist.gov/5.9>, equation 5.9.11,
`Ln Γ(z + 1) = −γz − (2πi)⁻¹ ∫_{−c−i∞}^{−c+i∞} π z^{−s} ζ(−s)/(s sin(πs)) ds`,
`|ph z| ≤ π − δ`, `1 < c < 2`. Mathlib has no complex `ln Γ`; the formula is stated exponentiated
(`dlmf_5_9_11`), for every `z` in the slit plane `|ph z| < π`; the contour integral is written
with `s = −c + iy`, `ds = i dy`.

* `𝓜[ln(1 + ax) − ax](s) = π a^{−s}/(s sin(πs))` for `|ph a| < π`, `−2 < ℜs < −1`
  (`mellin_barnesF`): integration by parts against Table 1.14.5, row 4 (`1/(1 + ax)`).
* Mellin inversion at `x = 1` (Mathlib's `mellinInv_mellin_eq`; the transform decays like
  `e^{−(π − |ph a|)|y|}` on vertical lines, `norm_sin_pi_mul_ge`) gives the Mellin–Barnes integral
  `ln(1 + a) − a = (2π)⁻¹ ∫ π a^{−s}/(s sin(πs)) dy` (`log_one_add_sub_eq_integral`).
* With `a = z/n` and `∑ₙ n^{s} = ζ(−s)` (dominated, since `ℜs < −1`) the sum over `n` is the
  integral in 5.9.11 (`hasSum_log_one_add_sub`), and Weierstrass's product 5.8.2 gives
  `Γ(1 + z) = exp(−γz − ∑ₙ (ln(1 + z/n) − z/n))`.
-/

open Complex Filter Topology Set MeasureTheory Asymptotics
open scoped Real

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-- `ln(1 + ax) − ax`. -/
noncomputable def barnesF (a : ℂ) (x : ℝ) : ℂ := Complex.log (1 + a * x) - a * x

theorem hasDerivAt_barnesF {a : ℂ} (ha : a ∈ slitPlane) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (barnesF a) (a / (1 + a * x) - a) x := by
  have h2 : HasDerivAt (fun x : ℝ => a * (x : ℂ)) a x := by
    simpa using ((hasDerivAt_id (x : ℂ)).const_mul a).comp_ofReal
  exact (hasDerivAt_log_one_add_mul ha hx).sub h2

theorem norm_deriv_barnesF_le {a : ℂ} {c : ℝ} (hc : 0 < c)
    (hcb : ∀ x : ℝ, 0 ≤ x → c * (1 + x) ≤ ‖1 + a * x‖) {t : ℝ} (ht : 0 ≤ t) :
    ‖a / (1 + a * t) - a‖ ≤ ‖a‖ ^ 2 / c * (t / (1 + t)) := by
  have h1 := hcb t ht
  have hpos : 0 < ‖1 + a * t‖ := lt_of_lt_of_le (by positivity) h1
  have hne : 1 + a * t ≠ 0 := norm_pos_iff.mp hpos
  have e : a / (1 + a * t) - a = -(a ^ 2 * t) / (1 + a * t) := by field_simp; ring
  rw [e, norm_div, norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht, div_le_iff₀ hpos]
  calc ‖a‖ ^ 2 * t = ‖a‖ ^ 2 / c * (t / (1 + t)) * (c * (1 + t)) := by
        field_simp
    _ ≤ ‖a‖ ^ 2 / c * (t / (1 + t)) * ‖1 + a * t‖ := by gcongr

theorem barnesF_zero (a : ℂ) : barnesF a 0 = 0 := by simp [barnesF]

/-- `|ln(1 + ax) − ax| ≤ K x²` and `≤ K x`, `K = |a|²/c`. -/
theorem norm_barnesF_le {a : ℂ} (ha : a ∈ slitPlane) {c : ℝ} (hc : 0 < c)
    (hcb : ∀ x : ℝ, 0 ≤ x → c * (1 + x) ≤ ‖1 + a * x‖) {x : ℝ} (hx : 0 ≤ x) :
    ‖barnesF a x‖ ≤ ‖a‖ ^ 2 / c * x ^ 2 ∧ ‖barnesF a x‖ ≤ ‖a‖ ^ 2 / c * x := by
  set K := ‖a‖ ^ 2 / c with hK
  have hK0 : 0 ≤ K := by positivity
  have hne : ∀ t : ℝ, 0 ≤ t → 1 + a * t ≠ 0 := fun t ht e => by
    have := hcb t ht; rw [e, norm_zero] at this; nlinarith
  have hd : ∀ t ∈ uIcc (0 : ℝ) x, HasDerivAt (barnesF a) (a / (1 + a * t) - a) t := fun t ht => by
    rw [uIcc_of_le hx] at ht; exact hasDerivAt_barnesF ha ht.1
  have hcont : ContinuousOn (fun t : ℝ => a / (1 + a * t) - a) (uIcc 0 x) := by
    refine (ContinuousOn.div continuousOn_const (by fun_prop) fun t ht => hne t ?_).sub
      continuousOn_const
    rw [uIcc_of_le hx] at ht; exact ht.1
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable
  rw [barnesF_zero, sub_zero] at hI
  rw [← hI]
  constructor
  · refine (intervalIntegral.norm_integral_le_of_norm_le hx (g := fun t => K * t)
      (ae_of_all _ fun t ht => ?_)
      ((by fun_prop : Continuous fun t : ℝ => K * t).intervalIntegrable 0 x)).trans ?_
    · refine (norm_deriv_barnesF_le hc hcb ht.1.le).trans ?_
      have : t / (1 + t) ≤ t := div_le_self ht.1.le (by linarith [ht.1])
      exact mul_le_mul_of_nonneg_left this hK0
    · rw [intervalIntegral.integral_const_mul, integral_id]
      nlinarith [sq_nonneg x]
  · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x) (C := K)
      (f := fun t : ℝ => a / (1 + a * t) - a) (fun t ht => by
        rw [uIoc_of_le hx] at ht
        refine (norm_deriv_barnesF_le hc hcb ht.1.le).trans ?_
        have : t / (1 + t) ≤ 1 := by rw [div_le_one (by linarith [ht.1])]; linarith
        exact mul_le_of_le_one_right hK0 this)
    rwa [sub_zero, abs_of_nonneg hx] at this

theorem continuousOn_barnesF {a : ℂ} (ha : a ∈ slitPlane) : ContinuousOn (barnesF a) (Ici 0) :=
  fun _ hx => (hasDerivAt_barnesF ha hx).continuousAt.continuousWithinAt

theorem mellinConvergent_barnesF {a : ℂ} (ha : a ∈ slitPlane) {s : ℂ} (h1 : -2 < s.re)
    (h2 : s.re < -1) : MellinConvergent (barnesF a) s := by
  obtain ⟨c, hc, hcb⟩ := exists_norm_one_add_mul_ge ha
  set K := ‖a‖ ^ 2 / c with hK
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (s - 1) • barnesF a t)
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    exact (((continuous_ofReal.continuousAt).cpow continuousAt_const
      (ofReal_mem_slitPlane.mpr hx)).smul
      (hasDerivAt_barnesF ha (le_of_lt hx)).continuousAt).continuousWithinAt
  unfold MellinConvergent
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := s.re + 1)
        (by linarith))
    refine (h.const_mul K).mono' (hmeas.mono_set Ioc_subset_Ioi_self)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun x hx => ?_))
    have hx0 : (0 : ℝ) < x := hx.1
    rw [smul_eq_mul, norm_cpow_mul_le hx0, sub_re, one_re]
    calc x ^ (s.re - 1) * ‖barnesF a x‖ ≤ x ^ (s.re - 1) * (K * x ^ 2) :=
          mul_le_mul_of_nonneg_left (norm_barnesF_le ha hc hcb hx0.le).1
            (Real.rpow_pos_of_pos hx0 _).le
      _ = K * x ^ (s.re + 1) := by
          rw [show s.re + 1 = (s.re - 1) + 2 by ring, Real.rpow_add hx0, Real.rpow_two]; ring
  · refine ((integrableOn_Ioi_rpow_of_lt (a := s.re) h2 one_pos).const_mul K).mono'
      (hmeas.mono_set (Ioi_subset_Ioi zero_le_one))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_))
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    rw [smul_eq_mul, norm_cpow_mul_le hx0, sub_re, one_re]
    calc x ^ (s.re - 1) * ‖barnesF a x‖ ≤ x ^ (s.re - 1) * (K * x) :=
          mul_le_mul_of_nonneg_left (norm_barnesF_le ha hc hcb hx0.le).2
            (Real.rpow_pos_of_pos hx0 _).le
      _ = K * x ^ s.re := by
          rw [show s.re = (s.re - 1) + 1 by ring, Real.rpow_add hx0, Real.rpow_one]; ring_nf

/-- `𝓜[ln(1 + ax) − ax](s) = π a^{−s}/(s sin(πs))` (`|ph a| < π`, `−2 < ℜs < −1`). -/
theorem mellin_barnesF {a : ℂ} (ha : a ∈ slitPlane) {s : ℂ} (h1 : -2 < s.re) (h2 : s.re < -1) :
    mellin (barnesF a) s = π * a ^ (-s) / (s * Complex.sin (π * s)) := by
  have hs : s ≠ 0 := fun h => by rw [h] at h2; simp at h2; linarith
  have ha0 := slitPlane_ne_zero ha
  obtain ⟨c, hc, hcb⟩ := exists_norm_one_add_mul_ge ha
  set K := ‖a‖ ^ 2 / c with hK
  have hK0 : 0 ≤ K := by positivity
  have hne : ∀ t : ℝ, 0 ≤ t → 1 + a * t ≠ 0 := fun t ht e => by
    have := hcb t ht; rw [e, norm_zero] at this; nlinarith
  have hu := fun x (hx : x ∈ Ioi (0 : ℝ)) => hasDerivAt_barnesF ha (le_of_lt hx)
  have h2' : IntegrableOn (fun x : ℝ => (x : ℂ) ^ s * (a / (1 + a * x) - a)) (Ioi 0) := by
    refine ((integrableOn_rpow_div_one_add_pow (α := s.re + 1) (k := 1) (by linarith)
      (by push_cast; linarith)).const_mul K).mono' ?_
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_))
    · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
      have hx' := hne x (le_of_lt hx)
      have hc : ContinuousAt (fun x : ℝ => a / (1 + a * (x : ℂ)) - a) x := by
        fun_prop (disch := exact hx')
      exact (((continuous_ofReal.continuousAt).cpow continuousAt_const
        (ofReal_mem_slitPlane.mpr hx)).mul hc).continuousWithinAt
    · have hx0 : (0 : ℝ) < x := hx
      rw [norm_cpow_mul_le hx0, pow_one]
      calc x ^ s.re * ‖a / (1 + a * x) - a‖ ≤ x ^ s.re * (K * (x / (1 + x))) :=
            mul_le_mul_of_nonneg_left (norm_deriv_barnesF_le hc hcb hx0.le)
              (Real.rpow_pos_of_pos hx0 _).le
        _ = K * (x ^ (s.re + 1) / (1 + x)) := by
            rw [Real.rpow_add_one hx0.ne']; ring
  have h0 : Tendsto (fun x : ℝ => (x : ℂ) ^ s * barnesF a x) (𝓝[>] 0) (𝓝 0) := by
    have hz := (tendsto_rpow_add_one_nhdsGT (σ := s.re + 1) (by linarith)).const_mul K
    rw [mul_zero] at hz
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [norm_cpow_mul_le hx0]
    calc x ^ s.re * ‖barnesF a x‖ ≤ x ^ s.re * (K * x ^ 2) :=
          mul_le_mul_of_nonneg_left (norm_barnesF_le ha hc hcb hx0.le).1
            (Real.rpow_pos_of_pos hx0 _).le
      _ = K * x ^ (s.re + 1 + 1) := by
          rw [show s.re + 1 + 1 = s.re + 2 by ring, Real.rpow_add hx0, Real.rpow_two]; ring
  have hinf : Tendsto (fun x : ℝ => (x : ℂ) ^ s * barnesF a x) atTop (𝓝 0) := by
    have hz := (tendsto_rpow_neg_atTop (y := -(s.re + 1)) (by linarith)).const_mul K
    rw [mul_zero] at hz
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [norm_cpow_mul_le hx, neg_neg]
    calc x ^ s.re * ‖barnesF a x‖ ≤ x ^ s.re * (K * x) :=
          mul_le_mul_of_nonneg_left (norm_barnesF_le ha hc hcb hx.le).2
            (Real.rpow_pos_of_pos hx _).le
      _ = K * x ^ (s.re + 1) := by rw [Real.rpow_add_one hx.ne']; ring
  have hM : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ s * (a / (1 + a * x) - a) =
      -a ^ 2 * mellin (fun x : ℝ => 1 / (1 + a * x)) (s + 2) := by
    rw [mellin, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
    have := hne x (le_of_lt hx)
    rw [smul_eq_mul, show s + 2 - 1 = s + 1 by ring, cpow_add _ _ hx0, cpow_one]
    field_simp
    ring
  rw [mellin_by_parts hs hu (mellinConvergent_barnesF ha h1 h2) h2' h0 hinf, hM,
    mellin_one_div_one_add_mul ha (by simp; linarith) (by simp; linarith),
    show -(s + 2) = -s + -2 by ring, cpow_add _ _ ha0,
    show (π : ℂ) * (s + 2) = π * s + 2 * π by ring, Complex.sin_add_two_pi,
    show (-2 : ℂ) = ((-2 : ℤ) : ℂ) by norm_num, cpow_intCast]
  have hsin : Complex.sin (π * s) ≠ 0 := sin_pi_mul_ne_zero_of (m := -2) (by simpa using h1)
    (by push_cast; linarith)
  field_simp

/-! ### Mellin inversion on a vertical line -/

/-- `|sin(π(σ + iy))| ≥ min(|sin πσ|, 1)/4 · e^{π|y|}`. -/
theorem norm_sin_pi_mul_ge {σ : ℝ} (y : ℝ) :
    min |Real.sin (π * σ)| 1 / 4 * Real.exp (π * |y|) ≤
      ‖Complex.sin (π * ((σ : ℂ) + y * I))‖ := by
  set A := |Real.sin (π * σ)| with hA
  have hsq : ‖Complex.sin (π * ((σ : ℂ) + y * I))‖ ^ 2 =
      Real.sin (π * σ) ^ 2 + Real.sinh (π * y) ^ 2 := by
    rw [show (π : ℂ) * ((σ : ℂ) + y * I) = ((π * σ : ℝ) : ℂ) + ((π * y : ℝ) : ℂ) * I by
      push_cast; ring, Complex.sin_add_mul_I, ← ofReal_sin, ← ofReal_cos, ← ofReal_cosh,
      ← ofReal_sinh, ← ofReal_mul, ← ofReal_mul, Complex.sq_norm, normSq_add_mul_I]
    have := Real.cosh_sq (π * y)
    have := Real.sin_sq_add_cos_sq (π * σ)
    nlinarith
  have hn := norm_nonneg (Complex.sin (π * ((σ : ℂ) + y * I)))
  have hA_le : A ≤ ‖Complex.sin (π * ((σ : ℂ) + y * I))‖ := by
    rw [hA, ← Real.sqrt_sq (abs_nonneg _), sq_abs, ← Real.sqrt_sq hn, hsq]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (Real.sinh (π * y))])
  have hS_le : Real.sinh (π * |y|) ≤ ‖Complex.sin (π * ((σ : ℂ) + y * I))‖ := by
    have h1 : Real.sinh (π * |y|) = |Real.sinh (π * y)| := by
      rw [Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos]
    rw [h1, ← Real.sqrt_sq (abs_nonneg _), sq_abs, ← Real.sqrt_sq hn, hsq]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (Real.sin (π * σ))])
  have hm1 : min A 1 ≤ A := min_le_left _ _
  have hm2 : min A 1 ≤ 1 := min_le_right _ _
  have hm0 : 0 ≤ min A 1 := le_min (abs_nonneg _) zero_le_one
  rcases le_or_gt (Real.exp (π * |y|)) 4 with h | h
  · calc min A 1 / 4 * Real.exp (π * |y|) ≤ min A 1 / 4 * 4 := by gcongr
      _ ≤ A := by linarith
      _ ≤ _ := hA_le
  · have hsinh : Real.exp (π * |y|) / 4 ≤ Real.sinh (π * |y|) := by
      rw [Real.sinh_eq]
      have : Real.exp (-(π * |y|)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by have := Real.pi_pos; nlinarith [abs_nonneg y])
      linarith
    calc min A 1 / 4 * Real.exp (π * |y|) ≤ 1 / 4 * Real.exp (π * |y|) := by gcongr
      _ = Real.exp (π * |y|) / 4 := by ring
      _ ≤ _ := hsinh.trans hS_le

/-- The Mellin–Barnes kernel `π a^{−s}/(s sin(πs))` on the line `ℜs = σ`. -/
noncomputable def barnesKernel (a : ℂ) (σ y : ℝ) : ℂ :=
  π * a ^ (-((σ : ℂ) + y * I)) / (((σ : ℂ) + y * I) * Complex.sin (π * ((σ : ℂ) + y * I)))

theorem norm_barnesKernel_le {a : ℂ} (ha : a ∈ slitPlane) {σ : ℝ} (h1 : -2 < σ) (h2 : σ < -1)
    (y : ℝ) : ‖barnesKernel a σ y‖ ≤ π * ‖a‖ ^ (-σ) / (min |Real.sin (π * σ)| 1 / 4) *
      Real.exp (-((π - |arg a|) * |y|)) := by
  have ha0 := slitPlane_ne_zero ha
  have hsinσ : Real.sin (π * σ) ≠ 0 := by
    have := sin_pi_mul_ne_zero_of (s := (σ : ℂ)) (m := -2) (by simp; linarith)
      (by simp; linarith)
    rwa [← ofReal_mul, ← ofReal_sin, ofReal_ne_zero] at this
  set m := min |Real.sin (π * σ)| 1 / 4 with hm
  have hm0 : 0 < m := by rw [hm]; have := abs_pos.mpr hsinσ; positivity
  have hS := norm_sin_pi_mul_ge (σ := σ) y
  have hs1 : 1 ≤ ‖(σ : ℂ) + y * I‖ := by
    have := Complex.abs_re_le_norm ((σ : ℂ) + y * I)
    simp at this
    rw [abs_of_neg (by linarith)] at this
    linarith
  have hpow : ‖a ^ (-((σ : ℂ) + y * I))‖ ≤ ‖a‖ ^ (-σ) * Real.exp (|arg a| * |y|) := by
    have hre : (-((σ : ℂ) + y * I)).re = -σ := by simp
    have him : (-((σ : ℂ) + y * I)).im = -y := by simp
    rw [norm_cpow_of_ne_zero ha0, hre, him]
    rw [div_eq_mul_inv, ← Real.exp_neg]
    gcongr
    rw [neg_mul_eq_mul_neg, neg_neg]
    calc arg a * y ≤ |arg a * y| := le_abs_self _
      _ = |arg a| * |y| := abs_mul _ _
  have hden : m * Real.exp (π * |y|) ≤
      ‖((σ : ℂ) + y * I) * Complex.sin (π * ((σ : ℂ) + y * I))‖ := by
    rw [norm_mul]
    calc m * Real.exp (π * |y|) = 1 * (m * Real.exp (π * |y|)) := (one_mul _).symm
      _ ≤ _ := mul_le_mul hs1 hS (by positivity) (norm_nonneg _)
  rw [barnesKernel, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, div_le_iff₀ (lt_of_lt_of_le (by positivity) hden)]
  have he : Real.exp (-((π - |arg a|) * |y|)) * Real.exp (π * |y|) = Real.exp (|arg a| * |y|) := by
    rw [← Real.exp_add]; ring_nf
  calc π * ‖a ^ (-((σ : ℂ) + y * I))‖ ≤ π * (‖a‖ ^ (-σ) * Real.exp (|arg a| * |y|)) := by gcongr
    _ = π * ‖a‖ ^ (-σ) / m * Real.exp (-((π - |arg a|) * |y|)) * (m * Real.exp (π * |y|)) := by
        rw [← he]; field_simp
    _ ≤ _ := by gcongr

theorem integrable_barnesKernel {a : ℂ} (ha : a ∈ slitPlane) {σ : ℝ} (h1 : -2 < σ)
    (h2 : σ < -1) : Integrable (barnesKernel a σ) := by
  have ha0 := slitPlane_ne_zero ha
  have harg : |arg a| < π := abs_lt.mpr ⟨by linarith [neg_pi_lt_arg a],
    lt_of_le_of_ne (arg_le_pi a) (slitPlane_arg_ne_pi ha)⟩
  refine ((integrable_exp_neg_abs (b := π - |arg a|) (by linarith)).const_mul
    (π * ‖a‖ ^ (-σ) / (min |Real.sin (π * σ)| 1 / 4))).mono' ?_
    (ae_of_all _ fun y => norm_barnesKernel_le ha h1 h2 y)
  refine Continuous.aestronglyMeasurable ?_
  have hsin : ∀ y : ℝ, ((σ : ℂ) + y * I) * Complex.sin (π * ((σ : ℂ) + y * I)) ≠ 0 := fun y => by
    refine mul_ne_zero (fun h => ?_) (sin_pi_mul_ne_zero_of (m := -2) (by simp; linarith)
      (by simp; linarith))
    have := congrArg re h; simp at this; linarith
  unfold barnesKernel
  exact (continuous_const.mul (Continuous.const_cpow (f := fun y : ℝ => -((σ : ℂ) + y * I))
    (by fun_prop) (Or.inl ha0))).div (by fun_prop) hsin

/-- The Mellin–Barnes integral: `ln(1 + a) − a = (2π)⁻¹ ∫ π a^{−s}/(s sin(πs)) dy`,
`s = σ + iy`, `−2 < σ < −1`, `|ph a| < π`. -/
theorem log_one_add_sub_eq_integral {a : ℂ} (ha : a ∈ slitPlane) {σ : ℝ} (h1 : -2 < σ)
    (h2 : σ < -1) :
    Complex.log (1 + a) - a = 1 / (2 * π) * ∫ y : ℝ, barnesKernel a σ y := by
  have hmel : ∀ y : ℝ, mellin (barnesF a) ((σ : ℂ) + y * I) = barnesKernel a σ y := fun y => by
    rw [mellin_barnesF ha (by simpa using h1) (by simpa using h2), barnesKernel]
  have hV : VerticalIntegrable (mellin (barnesF a)) σ := by
    unfold VerticalIntegrable
    simp_rw [hmel]
    exact integrable_barnesKernel ha h1 h2
  have hinv := mellinInv_mellin_eq σ (barnesF a) one_pos
    (mellinConvergent_barnesF ha (by simpa using h1) (by simpa using h2)) hV
    (hasDerivAt_barnesF ha zero_le_one).continuousAt
  rw [mellinInv] at hinv
  simp_rw [hmel, ofReal_one, one_cpow, one_smul] at hinv
  rw [barnesF] at hinv
  simp only [ofReal_one, mul_one] at hinv
  rw [← hinv, real_smul]
  push_cast
  ring

/-! ### Summing over `n` -/

theorem ofReal_mul_mem_slitPlane {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ slitPlane) :
    (r : ℂ) * z ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  rcases hz with h | h
  · left; rw [re_ofReal_mul]; positivity
  · right; rw [im_ofReal_mul]; exact mul_ne_zero hr.ne' h

theorem one_div_cpow_neg {m : ℝ} (hm : 0 < m) (s : ℂ) :
    ((1 / m : ℝ) : ℂ) ^ (-s) = (m : ℂ) ^ s := by
  have h1 : ((1 / m : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have h2 : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm.ne'
  rw [cpow_def_of_ne_zero h1, cpow_def_of_ne_zero h2, ← ofReal_log (by positivity),
    ← ofReal_log hm.le, one_div, Real.log_inv]
  push_cast
  ring_nf

theorem barnesKernel_div {z : ℂ} (hz : z ∈ slitPlane) (σ y : ℝ) (n : ℕ) :
    barnesKernel (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * z) σ y =
      (((n + 1 : ℕ) : ℂ)) ^ ((σ : ℂ) + y * I) * barnesKernel z σ y := by
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold barnesKernel
  rw [ofReal_mul_cpow_complex (by positivity) (slitPlane_ne_zero hz), one_div_cpow_neg hm]
  push_cast
  ring

/-- `∑_{n≥1} (ln(1 + z/n) − z/n) = (2π)⁻¹ ∫ π z^{−s} ζ(−s)/(s sin(πs)) dy`, `s = σ + iy`. -/
theorem hasSum_log_one_add_sub {z : ℂ} (hz : z ∈ slitPlane) {σ : ℝ} (h1 : -2 < σ)
    (h2 : σ < -1) :
    HasSum (fun n : ℕ => Complex.log (1 + z / ((n : ℂ) + 1)) - z / ((n : ℂ) + 1))
      (1 / (2 * π) * ∫ y : ℝ, barnesKernel z σ y * riemannZeta (-((σ : ℂ) + y * I))) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  set F : ℕ → ℝ → ℂ := fun n y => barnesKernel (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * z) σ y with hF
  have hmem : ∀ n : ℕ, (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * z) ∈ slitPlane := fun n =>
    ofReal_mul_mem_slitPlane (by positivity) hz
  have hint : ∀ n, Integrable (F n) := fun n => integrable_barnesKernel (hmem n) h1 h2
  have hnormF : ∀ n, ∫ y, ‖F n y‖ = ((n : ℝ) + 1) ^ σ * ∫ y, ‖barnesKernel z σ y‖ := fun n => by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hF]
    rw [barnesKernel_div hz, norm_mul, norm_natCast_cpow_of_pos (by omega)]
    simp
  have hsum : Summable fun n => ∫ y, ‖F n y‖ := by
    simp_rw [hnormF]
    refine Summable.mul_right _ ?_
    have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr h2)
    simpa using this
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hval : ∀ n : ℕ, ∫ y, F n y =
      2 * π * (Complex.log (1 + z / ((n : ℂ) + 1)) - z / ((n : ℂ) + 1)) := fun n => by
    have := log_one_add_sub_eq_integral (hmem n) h1 h2
    have e : (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * z) = z / ((n : ℂ) + 1) := by push_cast; ring
    calc ∫ y, F n y = 2 * π * (Complex.log (1 + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * z) -
          ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * z) := by rw [this]; field_simp; rfl
      _ = _ := by rw [e]
  simp_rw [hval] at h
  have hpt : ∀ y : ℝ, HasSum (fun n => F n y)
      (barnesKernel z σ y * riemannZeta (-((σ : ℂ) + y * I))) := fun y => by
    set s : ℂ := (σ : ℂ) + y * I with hs
    have hre : 1 < (-s).re := by simp [hs]; linarith
    have hz0 : riemannZeta (-s) = ∑' n : ℕ, 1 / (n : ℂ) ^ (-s) := zeta_eq_tsum_one_div_nat_cpow hre
    have hS := (Complex.summable_one_div_nat_cpow.mpr hre).hasSum
    rw [← hz0] at hS
    have hS' := (hasSum_nat_add_iff' 1).mpr hS
    have h0 : (1 : ℂ) / (((0 : ℕ) : ℂ)) ^ (-s) = 0 := by
      rw [Nat.cast_zero, zero_cpow (neg_ne_zero.mpr fun h => by
        rw [h] at hre; simp at hre; linarith)]
      simp
    simp only [Finset.sum_range_one, h0, sub_zero] at hS'
    have := hS'.mul_right (barnesKernel z σ y)
    convert this using 1
    · funext n
      simp only [hF]
      rw [barnesKernel_div hz, one_div, cpow_neg, inv_inv]
    · ring
  have hint' : ∫ y, ∑' n, F n y = ∫ y, barnesKernel z σ y * riemannZeta (-((σ : ℂ) + y * I)) :=
    integral_congr_ae (ae_of_all _ fun y => (hpt y).tsum_eq)
  rw [hint'] at h
  have := h.mul_left (1 / (2 * (π : ℂ)))
  convert this using 1
  funext n
  field_simp

/-! ### `Γ(1 + z)` through Weierstrass's product -/

theorem Gamma_add_one_eq_exp {z : ℂ} (hz : z ∈ slitPlane) {S : ℂ}
    (hS : HasSum (fun n : ℕ => Complex.log (1 + z / ((n : ℂ) + 1)) - z / ((n : ℂ) + 1)) S) :
    Gamma (z + 1) = cexp (-(γ * z) - S) := by
  have hz0 := slitPlane_ne_zero hz
  obtain ⟨-, hW⟩ := dlmf_5_8_2 z
  have hP := hS.cexp
  have hfac : ∀ n : ℕ, (cexp ∘ fun n : ℕ => Complex.log (1 + z / ((n : ℂ) + 1)) -
      z / ((n : ℂ) + 1)) n = (1 + z / ((n : ℂ) + 1)) * cexp (-(z / ((n : ℂ) + 1))) := fun n => by
    have hmem : 1 + z / ((n : ℂ) + 1) ≠ 0 := by
      have := one_add_mul_mem_slitPlane (x := 1 / ((n : ℝ) + 1)) hz (by positivity)
      refine slitPlane_ne_zero ?_
      convert this using 2
      push_cast; ring
    rw [Function.comp_apply, Complex.exp_sub, Complex.exp_log hmem, Complex.exp_neg, div_eq_mul_inv]
  have hP' : HasProd (fun n : ℕ => (1 + z / ((n : ℂ) + 1)) * cexp (-(z / ((n : ℂ) + 1))))
      (cexp S) := by
    convert hP using 1
    funext n
    exact (hfac n).symm
  rw [hP'.tprod_eq] at hW
  have hG : Gamma z ≠ 0 := by
    intro h
    rw [h, div_zero] at hW
    have : z * cexp (γ * z) * cexp S ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero hz0 (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)
    exact this hW.symm
  rw [Gamma_add_one z hz0]
  have hA : cexp (γ * z) * cexp S ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  have hGz : Gamma z = (z * (cexp (γ * z) * cexp S))⁻¹ := by
    rw [← mul_assoc, ← hW, one_div, inv_inv]
  have e : z * Gamma z = (cexp (γ * z) * cexp S)⁻¹ := by
    rw [hGz]; field_simp
  rw [e, ← Complex.exp_add, ← Complex.exp_neg]
  congr 1
  ring

/-- **DLMF 5.9.11**: for `|ph z| < π` and `1 < c < 2`,
`Γ(z + 1) = exp(−γz − (2πi)⁻¹ ∫_{−c−i∞}^{−c+i∞} π z^{−s} ζ(−s)/(s sin(πs)) ds)`, the contour
integral written with `s = −c + iy`, `ds = i dy`. -/
theorem dlmf_5_9_11 {z : ℂ} (hz : z ∈ slitPlane) {c : ℝ} (hc1 : 1 < c) (hc2 : c < 2) :
    Gamma (z + 1) = cexp (-(γ * z) - 1 / (2 * π * I) * (I * ∫ y : ℝ,
      π * z ^ (-(-(c : ℂ) + y * I)) * riemannZeta (-(-(c : ℂ) + y * I)) /
        ((-(c : ℂ) + y * I) * Complex.sin (π * (-(c : ℂ) + y * I))))) := by
  have h := hasSum_log_one_add_sub hz (σ := -c) (by linarith) (by linarith)
  rw [Gamma_add_one_eq_exp hz h]
  congr 1
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have e : ∫ y : ℝ, barnesKernel z (-c) y * riemannZeta (-(((-c : ℝ) : ℂ) + y * I)) =
      ∫ y : ℝ, π * z ^ (-(-(c : ℂ) + y * I)) * riemannZeta (-(-(c : ℂ) + y * I)) /
        ((-(c : ℂ) + y * I) * Complex.sin (π * (-(c : ℂ) + y * I))) := by
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [barnesKernel]
    push_cast
    ring
  rw [e, ← mul_assoc, show (1 : ℂ) / (2 * π * I) * I = 1 / (2 * π) by field_simp]

end Azurite.DLMF
