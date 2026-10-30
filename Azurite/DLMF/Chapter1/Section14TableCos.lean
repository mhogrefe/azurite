/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14CosSin
import Azurite.DLMF.Chapter1.Section14TableFresnel
import Azurite.DLMF.Chapter1.Section14TableHyperbolic
import Azurite.DLMF.Chapter1.Section14LaplaceInversion

/-!
# DLMF Table 1.14.2: Fourier cosine transforms

Rows of <https://dlmf.nist.gov/1.14.T2> for `𝓕_c f(x) = √(2/π) ∫_0^∞ f(t) cos(xt) dt`
(`dlmfFourierCos`). Logarithm rows 9–10: `Section14TableCosLog.lean`.

* Inversion: `dlmfFourierCos_dlmfFourierCos` (`C¹`, integrable `f` with integrable transform;
  from `dlmf_1_14_11`). Rows 2–4 come from rows 5 and `t e^{−at}` by inversion.
* Linearity: `dlmfFourierCos_const_mul`, `dlmfFourierCos_add`.
* Rows: `dlmf_table_1_14_2_r1` (box), `_r2` (`1/(a² + t²)`), `_r3` (`1/(a² + t²)²`), `_r4`
  (`4a³/(4a⁴ + t⁴)`), `_r5` (`e^{−at}`), `_r6` (`e^{−at²}`, principal square root),
  `_r7`/`_r8` (`sin(at²)`, `cos(at²)`: improper limits of `∫_0^R`, from Table 1.14.1 rows 9–10
  via `integral_even_mul_exp`).
* **Erratum (row 4).** DLMF states `ℜa > 0`, but `4a⁴ + t⁴` vanishes at `t = √2` for
  `a = e^{iπ/4}`; the row needs `|ph a| < π/4`, stated as `|ℑa| < ℜa`.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real

namespace Azurite.DLMF

/-! ### Tools -/

theorem boundedVariationOn_of_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) {a b : ℝ} (hab : a ≤ b) :
    BoundedVariationOn f (Icc a b) := by
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_Icc a b) isCompact_Icc
  have := hK.locallyBoundedVariationOn a b ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  rwa [inter_self] at this

/-- **Inversion of the cosine transform** at a point of continuity `u > 0` (from `dlmf_1_14_11`),
when the transform is integrable. -/
theorem dlmfFourierCos_dlmfFourierCos {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0))
    (hc : ContDiff ℝ 1 f) (hF : IntegrableOn (dlmfFourierCos f) (Ioi 0)) {u : ℝ} (hu : 0 < u) :
    dlmfFourierCos (dlmfFourierCos f) u = f u := by
  have hδ : 0 < u / 2 := by positivity
  have h := dlmf_1_14_11 (u := u) hf hδ (by linarith)
    (boundedVariationOn_of_contDiff hc (by linarith))
    (hc.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hc.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  rw [add_self_div_two] at h
  have hint : IntegrableOn (fun x => dlmfFourierCos f x * ((Real.cos (u * x) : ℝ) : ℂ)) (Ioi 0) :=
    Integrable.mono' hF.norm (hF.aestronglyMeasurable.mul
      (by fun_prop : Continuous fun x : ℝ => ((Real.cos (u * x) : ℝ) : ℂ)).aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _))
  have h2 := (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id).const_mul
    ((√(2 / π) : ℝ) : ℂ)
  exact tendsto_nhds_unique h2 h

theorem ofReal_cos_eq (x t : ℝ) :
    ((Real.cos (x * t) : ℝ) : ℂ) = (cexp (I * x * t) + cexp (-(I * x * t))) / 2 := by
  rw [ofReal_cos, Complex.cos]; push_cast; ring_nf

theorem cexp_mul_cos_eq (b : ℂ) (x t : ℝ) :
    cexp (-(b * t)) * ((Real.cos (x * t) : ℝ) : ℂ) =
      (cexp (-((b - I * x) * t)) + cexp (-((b + I * x) * t))) / 2 := by
  rw [ofReal_cos_eq, mul_div_assoc', mul_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 2 <;> congr 1 <;> ring

theorem re_sub_I_mul (b : ℂ) (x : ℝ) : (b - I * x).re = b.re := by simp
theorem re_add_I_mul (b : ℂ) (x : ℝ) : (b + I * x).re = b.re := by simp

theorem mul_sub_add_I (b : ℂ) (x : ℝ) : (b - I * x) * (b + I * x) = b ^ 2 + (x : ℂ) ^ 2 := by
  ring_nf; rw [I_sq]; ring

theorem sq_add_sq_ne_zero {b : ℂ} (hb : 0 < b.re) (x : ℝ) : b ^ 2 + (x : ℂ) ^ 2 ≠ 0 := by
  rw [← mul_sub_add_I]
  refine mul_ne_zero (fun h => ?_) (fun h => ?_)
  · have := congrArg Complex.re h; simp at this; linarith
  · have := congrArg Complex.re h; simp at this; linarith

/-- **Table 1.14.2, row 5**: `𝓕_c[e^{−at}](x) = √(2/π) a/(a² + x²)` (`ℜa > 0`). -/
theorem dlmf_table_1_14_2_r5 {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    dlmfFourierCos (fun t => cexp (-(a * t))) x =
      ((√(2 / π) : ℝ) : ℂ) * (a / (a ^ 2 + (x : ℂ) ^ 2)) := by
  have h1 : 0 < (a - I * x).re := by rw [re_sub_I_mul]; exact ha
  have h2 : 0 < (a + I * x).re := by rw [re_add_I_mul]; exact ha
  unfold dlmfFourierCos
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => cexp_mul_cos_eq a x t), integral_div,
    integral_add (integrableOn_Ioi_cexp_neg h1) (integrableOn_Ioi_cexp_neg h2),
    integral_Ioi_cexp_neg h1, integral_Ioi_cexp_neg h2]
  have hne1 : a - I * x ≠ 0 := fun h => by rw [h] at h1; simp at h1
  have hne2 : a + I * x ≠ 0 := fun h => by rw [h] at h2; simp at h2
  congr 1
  rw [div_add_div _ _ hne1 hne2, mul_sub_add_I]
  field_simp [sq_add_sq_ne_zero ha x]
  ring

/-- `𝓕_c[t e^{−at}](x) = √(2/π)(a² − x²)/(a² + x²)²` (`ℜa > 0`). -/
theorem dlmfFourierCos_mul_cexp {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    dlmfFourierCos (fun t => (t : ℂ) * cexp (-(a * t))) x =
      ((√(2 / π) : ℝ) : ℂ) * ((a ^ 2 - (x : ℂ) ^ 2) / (a ^ 2 + (x : ℂ) ^ 2) ^ 2) := by
  have h1 : 0 < (a - I * x).re := by rw [re_sub_I_mul]; exact ha
  have h2 : 0 < (a + I * x).re := by rw [re_add_I_mul]; exact ha
  unfold dlmfFourierCos
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ =>
      ((t : ℂ) * cexp (-((a - I * x) * t)) + (t : ℂ) * cexp (-((a + I * x) * t))) / 2)
      (fun t _ => by simp only; rw [mul_assoc, cexp_mul_cos_eq]; ring),
    integral_div, integral_add (integrableOn_Ioi_mul_cexp_neg h1)
      (integrableOn_Ioi_mul_cexp_neg h2),
    integral_Ioi_mul_cexp_neg h1, integral_Ioi_mul_cexp_neg h2]
  have hne1 : a - I * x ≠ 0 := fun h => by rw [h] at h1; simp at h1
  have hne2 : a + I * x ≠ 0 := fun h => by rw [h] at h2; simp at h2
  have hs := sq_add_sq_ne_zero ha x
  congr 1
  rw [← mul_sub_add_I] at hs ⊢
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- **Table 1.14.2, row 1**: `f(t) = 1` for `0 < t < a`, `0` for `t > a` (`a > 0`):
`𝓕_c f(x) = √(2/π) sin(ax)/x` (`x > 0`). -/
theorem dlmf_table_1_14_2_r1 {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < x) :
    dlmfFourierCos (fun t => if t < a then 1 else 0) x =
      ((√(2 / π) * (Real.sin (a * x) / x) : ℝ) : ℂ) := by
  unfold dlmfFourierCos
  have e : ∀ t : ℝ, (if t < a then (1 : ℂ) else 0) * ((Real.cos (x * t) : ℝ) : ℂ) =
      (Iio a).indicator (fun t => ((Real.cos (x * t) : ℝ) : ℂ)) t := fun t => by
    simp only [indicator, mem_Iio]; split_ifs <;> simp
  simp_rw [e]
  rw [setIntegral_indicator measurableSet_Iio, show Ioi (0 : ℝ) ∩ Iio a = Ioo 0 a by
      ext t; simp, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha.le,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_comp_mul_left _ hx.ne',
    integral_cos, mul_zero, Real.sin_zero, sub_zero, smul_eq_mul]
  push_cast
  field_simp

theorem ofReal_mul_cpow_complex {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ((r : ℂ) * z) ^ w = (r : ℂ) ^ w * z ^ w := by
  rw [cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hr.ne') hz),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), cpow_def_of_ne_zero hz,
    log_ofReal_mul hr hz, ← Complex.exp_add, ofReal_log hr.le]
  congr 1; ring

/-- **Table 1.14.2, row 6**: `𝓕_c[e^{−at²}](x) = (2a)^{−1/2} e^{−x²/(4a)}` (`ℜa > 0`, principal
powers). -/
theorem dlmf_table_1_14_2_r6 {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    dlmfFourierCos (fun t => cexp (-(a * (t : ℂ) ^ 2))) x =
      1 / (2 * a) ^ (1 / 2 : ℂ) * cexp (-(x : ℂ) ^ 2 / (4 * a)) := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hint : IntegrableOn (fun t : ℝ => cexp (-(a * (t : ℂ) ^ 2))) (Ioi 0) := by
    have := integrable_cexp_neg_mul_sq ha
    exact this.integrableOn.congr_fun (fun t _ => by ring_nf) measurableSet_Ioi
  rw [← dlmfFourier_evenExt hint]
  have he : evenExt (fun t : ℝ => cexp (-(a * (t : ℂ) ^ 2))) =
      fun t : ℝ => cexp (-(a * (t : ℂ) ^ 2)) := by
    funext t; simp only [evenExt]; congr 3; rw [← ofReal_pow, sq_abs, ofReal_pow]
  rw [he, dlmfFourier]
  have h := fourierIntegral_gaussian ha (x : ℂ)
  rw [show (fun t : ℝ => cexp (-(a * (t : ℂ) ^ 2)) * cexp (I * x * t)) =
      fun t : ℝ => cexp (I * x * t) * cexp (-a * (t : ℂ) ^ 2) by funext t; ring_nf, h]
  have harg : a.arg ≠ π := by
    intro h'; have := (abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha)); rw [h', abs_of_pos Real.pi_pos]
      at this; linarith [Real.pi_pos]
  rw [div_eq_mul_inv (π : ℂ) a, ofReal_mul_cpow_complex Real.pi_pos (inv_ne_zero ha0),
    inv_cpow _ _ harg, show (2 : ℂ) * a = ((2 : ℝ) : ℂ) * a by norm_num,
    ofReal_mul_cpow_complex two_pos ha0, cpow_half_ofReal Real.pi_pos.le,
    cpow_half_ofReal (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul' 2 Real.pi_pos.le]
  have h1 : ((√2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : √2 ≠ 0)
  have h2 : ((√π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h3 : a ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; tauto
  push_cast
  field_simp

/-- Even functions: `(2π)^{−1/2} ∫_{−R}^{R} g(t) e^{ixt} dt = √(2/π) ∫_0^R g(t) cos(xt) dt`. -/
theorem integral_even_mul_exp {g : ℝ → ℝ} (hg : Continuous g) (heven : ∀ t, g (-t) = g t)
    (x R : ℝ) :
    ((√(2 * π) : ℝ) : ℂ)⁻¹ * ∫ t in -R..R, (g t : ℂ) * cexp (I * x * t) =
      ((√(2 / π) : ℝ) : ℂ) * ∫ t in (0 : ℝ)..R, (g t : ℂ) * ((Real.cos (x * t) : ℝ) : ℂ) := by
  rw [intervalIntegral_eq_halves (g := fun t : ℝ => (g t : ℂ) * cexp (I * x * t)) (by fun_prop) R]
  have e : ∀ t : ℝ, (g t : ℂ) * cexp (I * x * t) + (g (-t) : ℂ) * cexp (I * x * ((-t : ℝ) : ℂ)) =
      2 * ((g t : ℂ) * ((Real.cos (x * t) : ℝ) : ℂ)) := fun t => by
    rw [heven, ofReal_cos_eq]; push_cast; ring_nf
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, ← sqrt_two_div_pi]
  ring

/-- **Table 1.14.2, row 7**: `𝓕_c[sin(at²)](x) = −(2a)^{−1/2} sin(x²/(4a) − π/4)` (`a > 0`), as the
limit of `√(2/π) ∫_0^R` (the integral is not absolutely convergent). -/
theorem dlmf_table_1_14_2_r7 {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Tendsto (fun R => ((√(2 / π) : ℝ) : ℂ) *
        ∫ t in (0 : ℝ)..R, (Real.sin (a * t ^ 2) : ℂ) * ((Real.cos (x * t) : ℝ) : ℂ)) atTop
      (𝓝 ((-(1 / √(2 * a)) * Real.sin (x ^ 2 / (4 * a) - π / 4) : ℝ) : ℂ)) := by
  refine (dlmf_table_1_14_1_r9 ha x).congr fun R => ?_
  exact integral_even_mul_exp (g := fun t => Real.sin (a * t ^ 2)) (by fun_prop)
    (fun t => by simp) x R

/-- **Table 1.14.2, row 8**: `𝓕_c[cos(at²)](x) = (2a)^{−1/2} cos(x²/(4a) − π/4)` (`a > 0`). -/
theorem dlmf_table_1_14_2_r8 {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Tendsto (fun R => ((√(2 / π) : ℝ) : ℂ) *
        ∫ t in (0 : ℝ)..R, (Real.cos (a * t ^ 2) : ℂ) * ((Real.cos (x * t) : ℝ) : ℂ)) atTop
      (𝓝 ((1 / √(2 * a) * Real.cos (x ^ 2 / (4 * a) - π / 4) : ℝ) : ℂ)) := by
  refine (dlmf_table_1_14_1_r10 ha x).congr fun R => ?_
  exact integral_even_mul_exp (g := fun t => Real.cos (a * t ^ 2)) (by fun_prop)
    (fun t => by simp) x R

/-! ### Rows 2–4 by inversion -/

theorem dlmfFourierCos_const_mul (c : ℂ) (g : ℝ → ℂ) (x : ℝ) :
    dlmfFourierCos (fun t => c * g t) x = c * dlmfFourierCos g x := by
  unfold dlmfFourierCos
  simp_rw [mul_assoc]
  rw [integral_const_mul]; ring

theorem integrableOn_mul_cos {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0)) (x : ℝ) :
    IntegrableOn (fun t => g t * ((Real.cos (x * t) : ℝ) : ℂ)) (Ioi 0) :=
  Integrable.mono' hg.norm (hg.aestronglyMeasurable.mul
    (by fun_prop : Continuous fun t : ℝ => ((Real.cos (x * t) : ℝ) : ℂ)).aestronglyMeasurable)
    (ae_of_all _ fun t => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _))

theorem dlmfFourierCos_add {g h : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0))
    (hh : IntegrableOn h (Ioi 0)) (x : ℝ) :
    dlmfFourierCos (fun t => g t + h t) x = dlmfFourierCos g x + dlmfFourierCos h x := by
  unfold dlmfFourierCos
  simp_rw [add_mul]
  rw [integral_add (integrableOn_mul_cos hg x) (integrableOn_mul_cos hh x)]; ring

/-- `|x² + w²| ≥ ℜw (x² + |w|²)/|w|` for `ℜw > 0`. -/
theorem norm_sq_add_sq_ge {w : ℂ} (hw : 0 < w.re) (x : ℝ) :
    w.re * (x ^ 2 + ‖w‖ ^ 2) / ‖w‖ ≤ ‖w ^ 2 + (x : ℂ) ^ 2‖ := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have e : w ^ 2 + (x : ℂ) ^ 2 = w * ((x : ℂ) ^ 2 / w + w) := by field_simp; ring
  have hre : ((x : ℂ) ^ 2 / w + w).re = w.re * (x ^ 2 + ‖w‖ ^ 2) / ‖w‖ ^ 2 := by
    rw [add_re, div_re]
    simp only [← ofReal_pow, ofReal_re, ofReal_im, zero_mul, Complex.normSq_eq_norm_sq]
    field_simp
    ring
  rw [e, norm_mul]
  have := Complex.re_le_norm ((x : ℂ) ^ 2 / w + w)
  rw [hre] at this
  calc w.re * (x ^ 2 + ‖w‖ ^ 2) / ‖w‖ = ‖w‖ * (w.re * (x ^ 2 + ‖w‖ ^ 2) / ‖w‖ ^ 2) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left this hn.le

theorem integrable_inv_sq_add_sq {w : ℂ} (hw : 0 < w.re) :
    Integrable fun x : ℝ => (w ^ 2 + (x : ℂ) ^ 2)⁻¹ := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hb : Integrable fun x : ℝ => ‖w‖ / w.re * ((1 + (x / ‖w‖) ^ 2)⁻¹ / ‖w‖ ^ 2) :=
    ((integrable_inv_one_add_sq.comp_div hn.ne').div_const _).const_mul _
  refine hb.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  have h := norm_sq_add_sq_ge hw x
  have hpos : 0 < w.re * (x ^ 2 + ‖w‖ ^ 2) / ‖w‖ := by positivity
  rw [norm_inv]
  calc ‖w ^ 2 + (x : ℂ) ^ 2‖⁻¹ ≤ (w.re * (x ^ 2 + ‖w‖ ^ 2) / ‖w‖)⁻¹ := inv_anti₀ hpos h
    _ = _ := by field_simp; ring

theorem contDiff_ofReal_complex : ContDiff ℝ ⊤ fun t : ℝ => (t : ℂ) := ofRealCLM.contDiff

theorem contDiff_cexp_neg (a : ℂ) : ContDiff ℝ 1 fun t : ℝ => cexp (-(a * t)) :=
  ((contDiff_const.mul (contDiff_ofReal_complex.of_le le_top)).neg).cexp

/-- **Table 1.14.2, row 2**: `𝓕_c[1/(a² + t²)](x) = √(π/2) e^{−ax}/a` (`ℜa > 0`, `x > 0`). -/
theorem dlmf_table_1_14_2_r2 {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    dlmfFourierCos (fun t => 1 / (a ^ 2 + (t : ℂ) ^ 2)) x =
      ((√(π / 2) : ℝ) : ℂ) * (cexp (-(a * x)) / a) := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hF : dlmfFourierCos (fun t => cexp (-(a * t))) =
      fun x : ℝ => ((√(2 / π) : ℝ) : ℂ) * a * (1 / (a ^ 2 + (x : ℂ) ^ 2)) := by
    funext y; rw [dlmf_table_1_14_2_r5 ha y]; ring
  have hFi : IntegrableOn (dlmfFourierCos fun t => cexp (-(a * t))) (Ioi 0) := by
    rw [hF]
    exact ((integrable_inv_sq_add_sq ha).const_mul
      (((√(2 / π) : ℝ) : ℂ) * a)).integrableOn.congr_fun
      (fun t _ => by simp only [one_div]) measurableSet_Ioi
  have h := dlmfFourierCos_dlmfFourierCos (integrableOn_Ioi_cexp_neg ha) (contDiff_cexp_neg a)
    hFi hx
  rw [hF, dlmfFourierCos_const_mul] at h
  have hc : ((√(2 / π) : ℝ) : ℂ) * a ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by positivity : √(2 / π) ≠ 0)) ha0
  rw [← h]
  have hsq : ((√(π / 2) : ℝ) : ℂ) * ((√(2 / π) : ℝ) : ℂ) = 1 := by
    rw [← ofReal_mul, ← Real.sqrt_mul (by positivity),
      show π / 2 * (2 / π) = 1 by field_simp, Real.sqrt_one, ofReal_one]
  have e : ((√(π / 2) : ℝ) : ℂ) * (((√(2 / π) : ℝ) : ℂ) * a *
      dlmfFourierCos (fun x => 1 / (a ^ 2 + (x : ℂ) ^ 2)) x / a) =
      (((√(π / 2) : ℝ) : ℂ) * ((√(2 / π) : ℝ) : ℂ)) *
        dlmfFourierCos (fun x => 1 / (a ^ 2 + (x : ℂ) ^ 2)) x := by
    field_simp
  rw [e, hsq, one_mul]

theorem sqrt_pi_div_two_mul : ((√(π / 2) : ℝ) : ℂ) * ((√(2 / π) : ℝ) : ℂ) = 1 := by
  rw [← ofReal_mul, ← Real.sqrt_mul (by positivity),
    show π / 2 * (2 / π) = 1 by field_simp, Real.sqrt_one, ofReal_one]

theorem norm_inv_sq_add_sq_le {w : ℂ} (hw : 0 < w.re) (x : ℝ) :
    ‖(w ^ 2 + (x : ℂ) ^ 2)⁻¹‖ ≤ 1 / (w.re * ‖w‖) := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have h := norm_sq_add_sq_ge hw x
  have h2 : w.re * ‖w‖ ≤ w.re * (x ^ 2 + ‖w‖ ^ 2) / ‖w‖ := by
    rw [le_div_iff₀ hn]; nlinarith [sq_nonneg x]
  rw [norm_inv, one_div]
  exact inv_anti₀ (by positivity) (h2.trans h)

theorem integrable_inv_sq_add_sq_sq {w : ℂ} (hw : 0 < w.re) :
    Integrable fun x : ℝ => ((w ^ 2 + (x : ℂ) ^ 2) ^ 2)⁻¹ := by
  refine ((integrable_inv_sq_add_sq hw).norm.const_mul (1 / (w.re * ‖w‖))).mono' (by fun_prop)
    (ae_of_all _ fun x => ?_)
  rw [← inv_pow, norm_pow, sq]
  exact mul_le_mul_of_nonneg_right (norm_inv_sq_add_sq_le hw x) (norm_nonneg _)

/-- **Table 1.14.2, row 3**: `𝓕_c[1/(a² + t²)²](x) = √(π/2) (1 + ax) e^{−ax}/(2a³)` (`ℜa > 0`,
`x > 0`). -/
theorem dlmf_table_1_14_2_r3 {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    dlmfFourierCos (fun t => 1 / (a ^ 2 + (t : ℂ) ^ 2) ^ 2) x =
      ((√(π / 2) : ℝ) : ℂ) * ((1 + a * x) * cexp (-(a * x)) / (2 * a ^ 3)) := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  set g : ℝ → ℂ := fun t => cexp (-(a * t)) + a * ((t : ℂ) * cexp (-(a * t)))
  have hgi : IntegrableOn g (Ioi 0) :=
    (integrableOn_Ioi_cexp_neg ha).add ((integrableOn_Ioi_mul_cexp_neg ha).const_mul a)
  have hgc : ContDiff ℝ 1 g :=
    (contDiff_cexp_neg a).add (contDiff_const.mul
      ((contDiff_ofReal_complex.of_le le_top).mul (contDiff_cexp_neg a)))
  have hF : dlmfFourierCos g =
      fun x : ℝ => ((√(2 / π) : ℝ) : ℂ) * (2 * a ^ 3) * (1 / (a ^ 2 + (x : ℂ) ^ 2) ^ 2) := by
    funext y
    rw [dlmfFourierCos_add (integrableOn_Ioi_cexp_neg ha)
      ((integrableOn_Ioi_mul_cexp_neg ha).const_mul a), dlmfFourierCos_const_mul,
      dlmf_table_1_14_2_r5 ha y, dlmfFourierCos_mul_cexp ha y]
    have hs := sq_add_sq_ne_zero ha y
    field_simp
    ring
  have hFi : IntegrableOn (dlmfFourierCos g) (Ioi 0) := by
    rw [hF]
    exact ((integrable_inv_sq_add_sq_sq ha).const_mul (((√(2 / π) : ℝ) : ℂ) * (2 * a ^ 3))
      ).integrableOn.congr_fun (fun t _ => by simp only [one_div]) measurableSet_Ioi
  have h := dlmfFourierCos_dlmfFourierCos hgi hgc hFi hx
  rw [hF, dlmfFourierCos_const_mul] at h
  rw [show (1 + a * x) * cexp (-(a * x)) = g x by simp only [g]; ring, ← h]
  have e : ((√(π / 2) : ℝ) : ℂ) * (((√(2 / π) : ℝ) : ℂ) * (2 * a ^ 3) *
      dlmfFourierCos (fun x => 1 / (a ^ 2 + (x : ℂ) ^ 2) ^ 2) x / (2 * a ^ 3)) =
      (((√(π / 2) : ℝ) : ℂ) * ((√(2 / π) : ℝ) : ℂ)) *
        dlmfFourierCos (fun x => 1 / (a ^ 2 + (x : ℂ) ^ 2) ^ 2) x := by
    field_simp
  rw [e, sqrt_pi_div_two_mul, one_mul]

/-- **Table 1.14.2, row 4**: `𝓕_c[4a³/(4a⁴ + t⁴)](x) = √π e^{−ax} sin(ax + π/4)` (`x > 0`), for
`|ℑa| < ℜa`, i.e. `|ph a| < π/4`.  (DLMF states `ℜa > 0`; but for `ph a = ±π/4` the denominator
`4a⁴ + t⁴` vanishes at a real `t`, e.g. `a = e^{iπ/4}`, `t = √2`, and the integral diverges; the
formula holds exactly when both `a(1 ± i)` have positive real part.) -/
theorem dlmf_table_1_14_2_r4 {a : ℂ} (ha : |a.im| < a.re) {x : ℝ} (hx : 0 < x) :
    dlmfFourierCos (fun t => 4 * a ^ 3 / (4 * a ^ 4 + (t : ℂ) ^ 4)) x =
      ((√π : ℝ) : ℂ) * cexp (-(a * x)) * Complex.sin (a * x + π / 4) := by
  set b₁ := a * (1 - I)
  set b₂ := a * (1 + I)
  have hb1 : 0 < b₁.re := by simp only [b₁]; simp; linarith [neg_abs_le a.im]
  have hb2 : 0 < b₂.re := by simp only [b₂]; simp; linarith [le_abs_self a.im]
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  set g : ℝ → ℂ := fun t => (1 - I) / 2 * cexp (-(b₁ * t)) + (1 + I) / 2 * cexp (-(b₂ * t))
  have hgi : IntegrableOn g (Ioi 0) :=
    ((integrableOn_Ioi_cexp_neg hb1).const_mul _).add ((integrableOn_Ioi_cexp_neg hb2).const_mul _)
  have hgc : ContDiff ℝ 1 g :=
    (contDiff_const.mul (contDiff_cexp_neg b₁)).add (contDiff_const.mul (contDiff_cexp_neg b₂))
  have hden : ∀ y : ℝ, 4 * a ^ 4 + (y : ℂ) ^ 4 = (b₁ ^ 2 + (y : ℂ) ^ 2) * (b₂ ^ 2 + (y : ℂ) ^ 2) :=
    fun y => by
      have hI4 : I ^ 4 = 1 := by
        rw [show I ^ 4 = (I ^ 2) ^ 2 by ring, I_sq]; norm_num
      simp only [b₁, b₂]; ring_nf; simp only [I_sq, hI4]; ring
  have hF : dlmfFourierCos g = fun x : ℝ => ((√(2 / π) : ℝ) : ℂ) *
      (4 * a ^ 3 / (4 * a ^ 4 + (x : ℂ) ^ 4)) := by
    funext y
    rw [dlmfFourierCos_add ((integrableOn_Ioi_cexp_neg hb1).const_mul _)
      ((integrableOn_Ioi_cexp_neg hb2).const_mul _), dlmfFourierCos_const_mul,
      dlmfFourierCos_const_mul, dlmf_table_1_14_2_r5 hb1 y, dlmf_table_1_14_2_r5 hb2 y, hden]
    have h1 := sq_add_sq_ne_zero hb1 y
    have h2 := sq_add_sq_ne_zero hb2 y
    field_simp
    simp only [b₁, b₂]
    have hI4 : I ^ 4 = 1 := by
      rw [show I ^ 4 = (I ^ 2) ^ 2 by ring, I_sq]; norm_num
    ring_nf
    simp only [I_sq, hI4]
    ring
  have hFi : IntegrableOn (dlmfFourierCos g) (Ioi 0) := by
    have e : dlmfFourierCos g = fun y : ℝ => (1 - I) / 2 * (((√(2 / π) : ℝ) : ℂ) * b₁ *
        (b₁ ^ 2 + (y : ℂ) ^ 2)⁻¹) + (1 + I) / 2 * (((√(2 / π) : ℝ) : ℂ) * b₂ *
        (b₂ ^ 2 + (y : ℂ) ^ 2)⁻¹) := by
      funext y
      rw [dlmfFourierCos_add ((integrableOn_Ioi_cexp_neg hb1).const_mul _)
        ((integrableOn_Ioi_cexp_neg hb2).const_mul _), dlmfFourierCos_const_mul,
        dlmfFourierCos_const_mul, dlmf_table_1_14_2_r5 hb1 y, dlmf_table_1_14_2_r5 hb2 y]
      ring
    rw [e]
    exact ((((integrable_inv_sq_add_sq hb1).const_mul _).const_mul _).add
      (((integrable_inv_sq_add_sq hb2).const_mul _).const_mul _)).integrableOn
  have h := dlmfFourierCos_dlmfFourierCos hgi hgc hFi hx
  rw [hF, dlmfFourierCos_const_mul] at h
  have hg : g x = cexp (-(a * x)) * (Complex.cos (a * x) + Complex.sin (a * x)) := by
    simp only [g, b₁, b₂, Complex.cos, Complex.sin]
    rw [show -(a * (1 - I) * x) = -(a * x) + a * x * I by ring,
      show -(a * (1 + I) * x) = -(a * x) + -(a * x) * I by ring, Complex.exp_add,
      Complex.exp_add]
    field_simp
    ring_nf
  have hsin : Complex.sin (a * x + π / 4) =
      ((√2 / 2 : ℝ) : ℂ) * (Complex.sin (a * x) + Complex.cos (a * x)) := by
    rw [Complex.sin_add, ← ofReal_ofNat 4, ← ofReal_div, ← ofReal_cos, ← ofReal_sin,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    ring
  have hcoef : ((√π : ℝ) : ℂ) * ((√2 / 2 : ℝ) : ℂ) = ((√(π / 2) : ℝ) : ℂ) := by
    rw [← ofReal_mul]; congr 1
    rw [Real.sqrt_div' π (by norm_num : (0 : ℝ) ≤ 2)]
    have : √2 ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  rw [hsin, show ((√π : ℝ) : ℂ) * cexp (-(a * x)) * (((√2 / 2 : ℝ) : ℂ) *
      (Complex.sin (a * x) + Complex.cos (a * x))) = ((√(π / 2) : ℝ) : ℂ) * g x by
    rw [hg, ← hcoef]; ring, ← h, ← mul_assoc, sqrt_pi_div_two_mul, one_mul]

end Azurite.DLMF
