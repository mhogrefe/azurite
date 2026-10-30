/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14TableCosLog
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# DLMF Table 1.14.3: Fourier sine transforms

Rows of <https://dlmf.nist.gov/1.14.T3> for `𝓕_s f(x) = √(2/π) ∫_0^∞ f(t) sin(xt) dt`
(`dlmfFourierSin`) that are Lebesgue integrals. Improper rows 1–4 and 11:
`Section14TableSinImproper.lean`; row 12: `Section14TableSinArctan.lean`; row 13:
`Section14TableSinLog.lean`.

* Tools: `cexp_mul_sin_eq`, `dlmfFourierSin_const_mul`, `integrableOn_mul_sin`;
  `dlmfFourierSin_deriv` (integration by parts, `𝓕_s(g′) = −x 𝓕_c(g)`); `dlmfFourierSin_div`
  (Fubini with `sin(xt)/t = ∫_0^x cos(st) ds`: `𝓕_s[g/t](x) = ∫_0^x 𝓕_c[g](s) ds`).
* Rows: `dlmf_table_1_14_3_r8` (`e^{−at}`), `_r9` (`t e^{−at}`), `_r5` (`t/(a² + t²)²`, from
  Table 1.14.2 row 2 by parts), `_r10` (`t e^{−at²}`, from Table 1.14.2 row 6 by parts), `_r6`
  (`1/(t(a² + t²))`), `_r7` (`e^{−at}/t`, principal `arctan`, via `hasDerivAt_complex_arctan_div`).
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real

namespace Azurite.DLMF

/-! ### Tools -/

theorem cexp_mul_sin_eq (b : ℂ) (x t : ℝ) :
    cexp (-(b * t)) * ((Real.sin (x * t) : ℝ) : ℂ) =
      (cexp (-((b - I * x) * t)) - cexp (-((b + I * x) * t))) / (2 * I) := by
  rw [ofReal_sin, Complex.sin]
  have e1 : cexp (-((b - I * x) * t)) = cexp (-(b * t)) * cexp (I * ((x * t : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  have e2 : cexp (-((b + I * x) * t)) = cexp (-(b * t)) * cexp (-(I * ((x * t : ℝ) : ℂ))) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  rw [e1, e2]
  field_simp
  ring_nf
  rw [I_sq]
  ring_nf

theorem dlmfFourierSin_const_mul (c : ℂ) (g : ℝ → ℂ) (x : ℝ) :
    dlmfFourierSin (fun t => c * g t) x = c * dlmfFourierSin g x := by
  unfold dlmfFourierSin
  simp_rw [mul_assoc]
  rw [integral_const_mul]; ring

theorem integrableOn_mul_sin {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0)) (x : ℝ) :
    IntegrableOn (fun t => g t * ((Real.sin (x * t) : ℝ) : ℂ)) (Ioi 0) :=
  Integrable.mono' hg.norm (hg.aestronglyMeasurable.mul
    (by fun_prop : Continuous fun t : ℝ => ((Real.sin (x * t) : ℝ) : ℂ)).aestronglyMeasurable)
    (ae_of_all _ fun t => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_sin_le_one _))

/-- Integration by parts: `𝓕_s(g′)(x) = −x 𝓕_c(g)(x)` for `g`, `g′` integrable on `(0, ∞)`. -/
theorem dlmfFourierSin_deriv {g g' : ℝ → ℂ} (hd : ∀ t, HasDerivAt g (g' t) t)
    (hg : IntegrableOn g (Ioi 0)) (hg' : IntegrableOn g' (Ioi 0)) (x : ℝ) :
    dlmfFourierSin g' x = -x * dlmfFourierCos g x := by
  have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => ((Real.sin (x * t) : ℝ) : ℂ))
      ((x : ℂ) * ((Real.cos (x * t) : ℝ) : ℂ)) t := fun t _ => by
    have := ((hasDerivAt_id t).const_mul x).sin.ofReal_comp
    simp only [id, mul_one] at this
    exact this.congr_deriv (by push_cast; ring)
  have h0 : Tendsto ((fun t : ℝ => ((Real.sin (x * t) : ℝ) : ℂ)) * g) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous ((fun t : ℝ => ((Real.sin (x * t) : ℝ) : ℂ)) * g) :=
      (by fun_prop : Continuous fun t : ℝ => ((Real.sin (x * t) : ℝ) : ℂ)).mul
        (continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt)
    have := hc.tendsto 0
    simp only [Pi.mul_apply, mul_zero, Real.sin_zero, ofReal_zero, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto ((fun t : ℝ => ((Real.sin (x * t) : ℝ) : ℂ)) * g) atTop (𝓝 0) := by
    have hg0 := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun t _ => hd t) hg' hg
    refine squeeze_zero_norm (fun t => ?_) (tendsto_norm_zero.comp hg0)
    simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, Function.comp_apply]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu (fun t _ => hd t)
    (by simpa [Pi.mul_def, mul_comm] using integrableOn_mul_sin hg' x)
    (by
      have : IntegrableOn (fun t => (x : ℂ) * (g t * ((Real.cos (x * t) : ℝ) : ℂ))) (Ioi 0) :=
        (integrableOn_mul_cos hg x).const_mul (x : ℂ)
      refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply]; ring)
    h0 hinf
  unfold dlmfFourierSin dlmfFourierCos
  have e1 : ∫ t in Ioi (0 : ℝ), g' t * ((Real.sin (x * t) : ℝ) : ℂ) =
      ∫ t in Ioi (0 : ℝ), ((Real.sin (x * t) : ℝ) : ℂ) * g' t := by
    simp_rw [mul_comm (g' _)]
  have e2 : ∫ t in Ioi (0 : ℝ), (x : ℂ) * ((Real.cos (x * t) : ℝ) : ℂ) * g t =
      (x : ℂ) * ∫ t in Ioi (0 : ℝ), g t * ((Real.cos (x * t) : ℝ) : ℂ) := by
    rw [← integral_const_mul]; simp_rw [mul_comm (g _), mul_assoc]
  rw [e1, h, e2]
  ring

/-! ### Exponential rows -/

/-- **Table 1.14.3, row 8**: `𝓕_s[e^{−at}](x) = √(2/π) x/(a² + x²)` (`ℜa > 0`). -/
theorem dlmf_table_1_14_3_r8 {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    dlmfFourierSin (fun t => cexp (-(a * t))) x =
      ((√(2 / π) : ℝ) : ℂ) * (x / (a ^ 2 + (x : ℂ) ^ 2)) := by
  have h1 : 0 < (a - I * x).re := by rw [re_sub_I_mul]; exact ha
  have h2 : 0 < (a + I * x).re := by rw [re_add_I_mul]; exact ha
  unfold dlmfFourierSin
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => cexp_mul_sin_eq a x t), integral_div,
    integral_sub (integrableOn_Ioi_cexp_neg h1) (integrableOn_Ioi_cexp_neg h2),
    integral_Ioi_cexp_neg h1, integral_Ioi_cexp_neg h2]
  have hne1 : a - I * x ≠ 0 := fun h => by rw [h] at h1; simp at h1
  have hne2 : a + I * x ≠ 0 := fun h => by rw [h] at h2; simp at h2
  congr 1
  rw [div_sub_div _ _ hne1 hne2, mul_sub_add_I]
  field_simp [sq_add_sq_ne_zero ha x]
  ring_nf

/-- **Table 1.14.3, row 9**: `𝓕_s[t e^{−at}](x) = √(2/π) 2ax/(a² + x²)²` (`ℜa > 0`). -/
theorem dlmf_table_1_14_3_r9 {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    dlmfFourierSin (fun t => (t : ℂ) * cexp (-(a * t))) x =
      ((√(2 / π) : ℝ) : ℂ) * (2 * a * x / (a ^ 2 + (x : ℂ) ^ 2) ^ 2) := by
  have h1 : 0 < (a - I * x).re := by rw [re_sub_I_mul]; exact ha
  have h2 : 0 < (a + I * x).re := by rw [re_add_I_mul]; exact ha
  unfold dlmfFourierSin
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ =>
      ((t : ℂ) * cexp (-((a - I * x) * t)) - (t : ℂ) * cexp (-((a + I * x) * t))) / (2 * I))
      (fun t _ => by simp only; rw [mul_assoc, cexp_mul_sin_eq]; ring),
    integral_div, integral_sub (integrableOn_Ioi_mul_cexp_neg h1)
      (integrableOn_Ioi_mul_cexp_neg h2),
    integral_Ioi_mul_cexp_neg h1, integral_Ioi_mul_cexp_neg h2]
  have hne1 : a - I * x ≠ 0 := fun h => by rw [h] at h1; simp at h1
  have hne2 : a + I * x ≠ 0 := fun h => by rw [h] at h2; simp at h2
  congr 1
  rw [← mul_sub_add_I]
  field_simp
  ring_nf

/-! ### Rows by integration by parts -/

theorem abs_mul_norm_inv_sq_add_sq_le {w : ℂ} (hw : 0 < w.re) (x : ℝ) :
    |x| * ‖(w ^ 2 + (x : ℂ) ^ 2)⁻¹‖ ≤ 1 / (2 * w.re) := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hpos : 0 < ‖w ^ 2 + (x : ℂ) ^ 2‖ := norm_pos_iff.mpr (sq_add_sq_ne_zero hw x)
  have h := norm_sq_add_sq_ge hw x
  have h2 : 2 * w.re * |x| ≤ w.re * (x ^ 2 + ‖w‖ ^ 2) / ‖w‖ := by
    rw [le_div_iff₀ hn]
    have : 2 * |x| * ‖w‖ ≤ x ^ 2 + ‖w‖ ^ 2 := by
      nlinarith [sq_nonneg (|x| - ‖w‖), sq_abs x]
    nlinarith
  rw [norm_inv, ← div_eq_mul_inv, div_le_iff₀ hpos]
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  linarith

theorem integrable_mul_inv_sq_add_sq_sq {w : ℂ} (hw : 0 < w.re) :
    Integrable fun x : ℝ => (x : ℂ) / (w ^ 2 + (x : ℂ) ^ 2) ^ 2 := by
  refine ((integrable_inv_sq_add_sq hw).norm.const_mul (1 / (2 * w.re))).mono' (by
    refine Continuous.aestronglyMeasurable ?_
    exact continuous_ofReal.div (by fun_prop) fun x => pow_ne_zero 2 (sq_add_sq_ne_zero hw x))
    (ae_of_all _ fun x => ?_)
  rw [div_eq_mul_inv, ← inv_pow, norm_mul, norm_pow, sq, Complex.norm_real, Real.norm_eq_abs,
    ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (abs_mul_norm_inv_sq_add_sq_le hw x) (norm_nonneg _)

theorem sqrt_pi_div_eight : ((√(π / 8) : ℝ) : ℂ) = ((√(π / 2) : ℝ) : ℂ) / 2 := by
  have : √(π / 8) = √(π / 2) / 2 := by
    rw [show π / 8 = π / 2 / 2 ^ 2 by ring, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (by norm_num)]
  rw [this]; push_cast; ring

/-- **Table 1.14.3, row 5**: `𝓕_s[t/(a² + t²)²](x) = √(π/8) (x/a) e^{−ax}` (`ℜa > 0`, `x > 0`). -/
theorem dlmf_table_1_14_3_r5 {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    dlmfFourierSin (fun t => (t : ℂ) / (a ^ 2 + (t : ℂ) ^ 2) ^ 2) x =
      ((√(π / 8) : ℝ) : ℂ) * (x / a * cexp (-(a * x))) := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => 1 / (a ^ 2 + (t : ℂ) ^ 2))
      (-2 * ((t : ℂ) / (a ^ 2 + (t : ℂ) ^ 2) ^ 2)) t := fun t => by
    have h1 := (((hasDerivAt_id t).ofReal_comp.pow 2).const_add (a ^ 2)).inv
      (sq_add_sq_ne_zero ha t)
    simp only [id, one_div, Pi.pow_apply] at h1 ⊢
    refine h1.congr_deriv ?_
    push_cast; field_simp
  have hg : IntegrableOn (fun t : ℝ => 1 / (a ^ 2 + (t : ℂ) ^ 2)) (Ioi 0) := by
    simpa only [one_div] using (integrable_inv_sq_add_sq ha).integrableOn
  have hg' : IntegrableOn (fun t : ℝ => -2 * ((t : ℂ) / (a ^ 2 + (t : ℂ) ^ 2) ^ 2)) (Ioi 0) :=
    ((integrable_mul_inv_sq_add_sq_sq ha).const_mul (-2)).integrableOn
  have h := dlmfFourierSin_deriv hd hg hg' x
  rw [dlmfFourierSin_const_mul, dlmf_table_1_14_2_r2 ha hx] at h
  have e : dlmfFourierSin (fun t => (t : ℂ) / (a ^ 2 + (t : ℂ) ^ 2) ^ 2) x =
      -(1 / 2) * (-2 * dlmfFourierSin (fun t => (t : ℂ) / (a ^ 2 + (t : ℂ) ^ 2) ^ 2) x) := by
    ring
  rw [e, h, sqrt_pi_div_eight]
  field_simp

/-- **Table 1.14.3, row 10**: `𝓕_s[t e^{−at²}](x) = (2a)^{−3/2} x e^{−x²/(4a)}` (`ℜa > 0`, i.e.
`|ph a| < π/2`; principal powers). -/
theorem dlmf_table_1_14_3_r10 {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    dlmfFourierSin (fun t => (t : ℂ) * cexp (-(a * (t : ℂ) ^ 2))) x =
      (2 * a) ^ (-(3 / 2) : ℂ) * x * cexp (-(x : ℂ) ^ 2 / (4 * a)) := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have h2a : (2 : ℂ) * a ≠ 0 := mul_ne_zero two_ne_zero ha0
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => cexp (-(a * (t : ℂ) ^ 2)))
      (-(2 * a) * ((t : ℂ) * cexp (-(a * (t : ℂ) ^ 2)))) t := fun t => by
    have h1 := (((hasDerivAt_id t).ofReal_comp.pow 2).const_mul a).neg.cexp
    simp only [id, Pi.pow_apply, Pi.neg_apply] at h1
    refine h1.congr_deriv ?_
    push_cast; ring
  have hg : IntegrableOn (fun t : ℝ => cexp (-(a * (t : ℂ) ^ 2))) (Ioi 0) := by
    have := integrable_cexp_neg_mul_sq ha
    exact this.integrableOn.congr_fun (fun t _ => by simp only [neg_mul]) measurableSet_Ioi
  have hg' : IntegrableOn
      (fun t : ℝ => -(2 * a) * ((t : ℂ) * cexp (-(a * (t : ℂ) ^ 2)))) (Ioi 0) := by
    have := (integrable_mul_cexp_neg_mul_sq ha).const_mul (-(2 * a))
    exact this.integrableOn.congr_fun (fun t _ => by simp only [neg_mul]) measurableSet_Ioi
  have h := dlmfFourierSin_deriv hd hg hg' x
  rw [dlmfFourierSin_const_mul, dlmf_table_1_14_2_r6 ha x] at h
  have e : dlmfFourierSin (fun t => (t : ℂ) * cexp (-(a * (t : ℂ) ^ 2))) x =
      (-(2 * a))⁻¹ * (-(2 * a) *
        dlmfFourierSin (fun t => (t : ℂ) * cexp (-(a * (t : ℂ) ^ 2))) x) := by
    rw [← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr h2a), one_mul]
  have hp : (2 * a) ^ (-(3 / 2) : ℂ) = (2 * a)⁻¹ * (1 / (2 * a) ^ (1 / 2 : ℂ)) := by
    rw [show (-(3 / 2) : ℂ) = -1 + -(1 / 2) by norm_num, cpow_add _ _ h2a, cpow_neg_one,
      cpow_neg]
    simp only [one_div]
  rw [e, h, hp]
  field_simp

/-! ### Rows by `sin(xt)/t = ∫_0^x cos(st) ds` -/

/-- `𝓕_s[g(t)/t](x) = ∫_0^x 𝓕_c[g](s) ds` for `g` integrable on `(0, ∞)` (Fubini). -/
theorem dlmfFourierSin_div {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0)) {x : ℝ} (hx : 0 ≤ x) :
    dlmfFourierSin (fun t => g t / t) x = ∫ s in (0 : ℝ)..x, dlmfFourierCos g s := by
  unfold dlmfFourierSin dlmfFourierCos
  rw [intervalIntegral.integral_of_le hx, integral_const_mul]
  congr 1
  set μ := volume.restrict (Ioc (0 : ℝ) x)
  set ν := volume.restrict (Ioi (0 : ℝ))
  set G : ℝ → ℝ → ℂ := fun s t => g t * ((Real.cos (s * t) : ℝ) : ℂ)
  have hGm : AEStronglyMeasurable (Function.uncurry G) (μ.prod ν) :=
    (hg.aestronglyMeasurable.comp_snd).mul
      ((by fun_prop : Continuous fun z : ℝ × ℝ => ((Real.cos (z.1 * z.2) : ℝ) : ℂ))
        |>.aestronglyMeasurable)
  have hfin : IsFiniteMeasure μ := by
    simp only [μ]; infer_instance
  have hGi : Integrable (Function.uncurry G) (μ.prod ν) := by
    refine ((integrable_const (1 : ℝ)).mul_prod hg.norm).mono' hGm (ae_of_all _ fun z => ?_)
    simp only [Function.uncurry, G, norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)
  rw [integral_integral_swap hGi]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [G]
  have ht0 : t ≠ 0 := (ne_of_lt ht).symm
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hx, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_comp_mul_right (fun s => Real.cos s) ht0, integral_cos, zero_mul,
    Real.sin_zero, sub_zero, smul_eq_mul, mul_comm x t]
  push_cast
  field_simp

/-- **Table 1.14.3, row 6**: `𝓕_s[1/(t(a² + t²))](x) = √(π/2) (1 − e^{−ax})/a²` (`ℜa > 0`,
`x > 0`). -/
theorem dlmf_table_1_14_3_r6 {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    dlmfFourierSin (fun t => 1 / ((t : ℂ) * (a ^ 2 + (t : ℂ) ^ 2))) x =
      ((√(π / 2) : ℝ) : ℂ) * ((1 - cexp (-(a * x))) / a ^ 2) := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hg : IntegrableOn (fun t : ℝ => 1 / (a ^ 2 + (t : ℂ) ^ 2)) (Ioi 0) := by
    simpa only [one_div] using (integrable_inv_sq_add_sq ha).integrableOn
  have e : (fun t : ℝ => 1 / ((t : ℂ) * (a ^ 2 + (t : ℂ) ^ 2))) =
      fun t : ℝ => 1 / (a ^ 2 + (t : ℂ) ^ 2) / t := by
    funext t; rw [div_div, mul_comm]
  rw [e, dlmfFourierSin_div hg hx.le, intervalIntegral.integral_of_le hx.le,
    setIntegral_congr_fun measurableSet_Ioc (g := fun s : ℝ =>
      ((√(π / 2) : ℝ) : ℂ) / a * cexp (-a * s))
      (fun s hs => by
        simp only
        rw [dlmf_table_1_14_2_r2 ha hs.1]; ring_nf),
    ← intervalIntegral.integral_of_le hx.le, intervalIntegral.integral_const_mul,
    integral_exp_mul_complex (neg_ne_zero.mpr ha0)]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring_nf

theorem hasDerivAt_complex_arctan_div {a : ℂ} (ha : 0 < a.re) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fun s : ℝ => Complex.arctan (s / a)) (a / (a ^ 2 + (s : ℂ) ^ 2)) s := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hne : ∀ c : ℂ, c.re = a.re → c ≠ 0 := fun c hc h => by
    rw [h, zero_re] at hc; linarith
  have h1 : 1 - (s : ℂ) / a * I ≠ 0 := fun h => by
    have : a * (1 - (s : ℂ) / a * I) = a - s * I := by field_simp
    exact hne (a - s * I) (by simp) (by rw [← this, h, mul_zero])
  have h2 : 1 + (s : ℂ) / a * I ≠ 0 := fun h => by
    have : a * (1 + (s : ℂ) / a * I) = a + s * I := by field_simp
    exact hne (a + s * I) (by simp) (by rw [← this, h, mul_zero])
  have hu : HasDerivAt (fun s : ℝ => (s : ℂ) / a * I) (1 / a * I) s := by
    have := ((hasDerivAt_id s).ofReal_comp.div_const a).mul_const I
    simp only [id] at this
    exact this.congr_deriv (by push_cast; ring)
  have hq := ((hasDerivAt_const s (1 : ℂ)).add hu).div ((hasDerivAt_const s (1 : ℂ)).sub hu) h1
  have hslit : (1 + (s : ℂ) / a * I) / (1 - (s : ℂ) / a * I) ∈ slitPlane := by
    rcases hs.eq_or_lt with rfl | hs
    · simp
    · refine Or.inr (ne_of_gt ?_)
      set v := (s : ℂ) / a * I
      have hv : 0 < v.im := by
        simp only [v, mul_I_im, div_re, ofReal_re, ofReal_im, zero_mul]
        have := normSq_pos.mpr ha0
        positivity
      have hN : 0 < normSq (1 - v) := normSq_pos.mpr h1
      rw [div_im]
      simp only [add_im, sub_im, add_re, sub_re, one_im, one_re]
      have : (0 + v.im) * (1 - v.re) / normSq (1 - v) - (1 + v.re) * (0 - v.im) / normSq (1 - v)
          = 2 * v.im / normSq (1 - v) := by ring
      rw [this]; positivity
  have hl := (hq.clog_real hslit).const_mul (-I / 2)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, zero_add, zero_sub] at hl
  unfold Complex.arctan
  refine hl.congr_deriv ?_
  have hs2 := sq_add_sq_ne_zero ha s
  field_simp
  ring_nf
  rw [I_sq]
  ring_nf
  field_simp
  ring

/-- **Table 1.14.3, row 7**: `𝓕_s[e^{−at}/t](x) = √(2/π) arctan(x/a)` (`ℜa > 0`, `x > 0`;
principal `arctan`). -/
theorem dlmf_table_1_14_3_r7 {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    dlmfFourierSin (fun t => cexp (-(a * t)) / t) x =
      ((√(2 / π) : ℝ) : ℂ) * Complex.arctan (x / a) := by
  rw [dlmfFourierSin_div (integrableOn_Ioi_cexp_neg ha) hx.le]
  simp_rw [dlmf_table_1_14_2_r5 ha]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => Complex.arctan (s / a)) (fun s hs => hasDerivAt_complex_arctan_div ha
      (by rw [uIcc_of_le hx.le] at hs; exact hs.1))
    ((continuous_const.div (by fun_prop) fun s => sq_add_sq_ne_zero ha s).intervalIntegrable
      _ _)]
  simp [Complex.arctan]

end Azurite.DLMF
