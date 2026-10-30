/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14TableCos
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# DLMF Table 1.14.2: Fourier cosine transforms of logarithms (rows 9–10)

* `log_one_add_eq_integral`: `ln(1 + a²/t²) = ∫_0^1 2sa²/(t² + (sa)²) ds` (`ℜa > 0`, `t > 0`).
* `integral_inv_sq_add_sq_cos`: `∫_0^∞ cos(xt)/(w² + t²) dt = (π/2) e^{−wx}/w` (row 2).
* `integral_log_one_add_cos`: Fubini over `(0, 1] × (0, ∞)` (with the bound
  `|w² + t²| ≥ ℜw (t² + |w|²)/|w|`) gives integrability and
  `∫_0^∞ ln(1 + a²/t²) cos(xt) dt = π(1 − e^{−ax})/x`.
* Rows: `dlmf_table_1_14_2_r9`; `dlmf_table_1_14_2_r10_sub` (`ln(a² + t²) − ln(b² + t²)`, all
  `ℜa, ℜb > 0`); `dlmf_table_1_14_2_r10` (DLMF's literal `ln((a² + t²)/(b² + t²))`).
* **Erratum (row 10).** With principal logarithms, `ln((a² + t²)/(b² + t²))` differs from
  `ln(a² + t²) − ln(b² + t²)` by `±2πi` on an interval of `t` when e.g. `a = ε + i`, `b = ε − i`
  (small `ε > 0`), so the literal row fails under DLMF's `ℜa, ℜb > 0`; it holds for
  `|ph a|, |ph b| < π/4`, where both arguments lie in `(−π/2, π/2)`.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real

namespace Azurite.DLMF

theorem sq_mem_slitPlane {w : ℂ} (hw : 0 < w.re) : w ^ 2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases him : w.im = 0
  · left; simp only [sq, mul_re, him, mul_zero, sub_zero]; positivity
  · right; simp only [sq, mul_im]
    intro h; apply him; nlinarith [mul_self_nonneg w.im, hw]

theorem one_add_div_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) {r : ℝ} (hr : 0 < r) :
    1 + z / r ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  rcases hz with h | h
  · left; simp [div_re]; positivity
  · right; simp [div_im]; exact ⟨h, hr.ne'⟩

/-- For `t > 0` and `0 ≤ s`, `1 + (sa)²/t²` lies in the cut plane (`ℜa > 0`). -/
theorem one_add_mem_slitPlane {a : ℂ} (ha : 0 < a.re) {t s : ℝ} (ht : 0 < t) (hsl : 0 ≤ s) :
    1 + ((s : ℂ) * a) ^ 2 / ((t ^ 2 : ℝ) : ℂ) ∈ slitPlane := by
  rcases hsl.eq_or_lt with rfl | hslp
  · simp
  · exact one_add_div_mem_slitPlane (sq_mem_slitPlane (by simpa using mul_pos hslp ha))
      (by positivity)

/-- `ln(1 + a²/t²) = ∫_0^1 2sa²/(t² + (sa)²) ds` for `t > 0`, `ℜa > 0`. -/
theorem log_one_add_eq_integral {a : ℂ} (ha : 0 < a.re) {t : ℝ} (ht : 0 < t) :
    Complex.log (1 + a ^ 2 / ((t ^ 2 : ℝ) : ℂ)) =
      ∫ s in (0 : ℝ)..1, 2 * s * a ^ 2 / ((t ^ 2 : ℝ) + ((s : ℂ) * a) ^ 2) := by
  have ht2 : ((t ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : t ^ 2 ≠ 0)
  have hne : ∀ s : ℝ, 0 ≤ s → ((t ^ 2 : ℝ) : ℂ) + ((s : ℂ) * a) ^ 2 ≠ 0 := fun s hsl h => by
    have hm := one_add_mem_slitPlane ha ht hsl
    have : 1 + ((s : ℂ) * a) ^ 2 / ((t ^ 2 : ℝ) : ℂ) = 0 := by
      rw [← mul_div_cancel_left₀ (1 + ((s : ℂ) * a) ^ 2 / ((t ^ 2 : ℝ) : ℂ)) ht2, mul_add,
        mul_div_cancel₀ _ ht2, mul_one, h, zero_div]
    rw [this] at hm; exact slitPlane_ne_zero hm rfl
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun s : ℝ => Complex.log (1 + ((s : ℂ) * a) ^ 2 / ((t ^ 2 : ℝ) : ℂ)))
      (2 * s * a ^ 2 / ((t ^ 2 : ℝ) + ((s : ℂ) * a) ^ 2)) s := by
    intro s hsl
    rw [uIcc_of_le zero_le_one] at hsl
    have h1 : HasDerivAt (fun s : ℝ => 1 + ((s : ℂ) * a) ^ 2 / ((t ^ 2 : ℝ) : ℂ))
        (2 * s * a ^ 2 / ((t ^ 2 : ℝ) : ℂ)) s := by
      have := ((((hasDerivAt_id s).ofReal_comp.mul_const a).pow 2).div_const
        ((t ^ 2 : ℝ) : ℂ)).const_add 1
      convert this using 1
      · funext u; simp
      · simp; ring
    convert h1.clog_real (one_add_mem_slitPlane ha ht hsl.1) using 1
    field_simp [hne s hsl.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (ContinuousOn.intervalIntegrable ?_)]
  · simp
  · rw [uIcc_of_le zero_le_one]
    exact ContinuousOn.div (by fun_prop) (by fun_prop) fun s hsl => hne s hsl.1

/-- `∫_0^∞ cos(xt)/(w² + t²) dt = (π/2) e^{−wx}/w` (`ℜw > 0`, `x > 0`), from row 2. -/
theorem integral_inv_sq_add_sq_cos {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), 1 / (w ^ 2 + (t : ℂ) ^ 2) * ((Real.cos (x * t) : ℝ) : ℂ) =
      (π / 2 : ℂ) * (cexp (-(w * x)) / w) := by
  have h := dlmf_table_1_14_2_r2 hw hx
  unfold dlmfFourierCos at h
  have hs : ((√(2 / π) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : √(2 / π) ≠ 0)
  have hsq : ((√(π / 2) : ℝ) : ℂ) = (π / 2 : ℂ) * ((√(2 / π) : ℝ) : ℂ) := by
    have h1 := sqrt_pi_div_two_mul
    have h2 : ((√(π / 2) : ℝ) : ℂ) * ((√(π / 2) : ℝ) : ℂ) = (π / 2 : ℂ) := by
      rw [← ofReal_mul, Real.mul_self_sqrt (by positivity)]; push_cast; ring
    calc ((√(π / 2) : ℝ) : ℂ) = ((√(π / 2) : ℝ) : ℂ) * (((√(π / 2) : ℝ) : ℂ) *
          ((√(2 / π) : ℝ) : ℂ)) := by rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, h2]
  rw [hsq] at h
  exact mul_left_cancel₀ hs (h.trans (by ring))

theorem integral_Ioi_inv_sq_add_sq_le {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), (t ^ 2 + c ^ 2)⁻¹ ≤ π / c := by
  have hint : Integrable fun t : ℝ => (t ^ 2 + c ^ 2)⁻¹ := by
    have := (integrable_inv_one_add_sq.comp_div hc.ne').div_const (c ^ 2)
    refine this.congr (ae_of_all _ fun t => ?_)
    simp only; field_simp; ring
  calc ∫ t in Ioi (0 : ℝ), (t ^ 2 + c ^ 2)⁻¹ ≤ ∫ t, (t ^ 2 + c ^ 2)⁻¹ :=
        setIntegral_le_integral hint (ae_of_all _ fun t => by positivity)
    _ = π / c := by
        have h := Measure.integral_comp_div (fun t : ℝ => (1 + t ^ 2)⁻¹) c
        rw [integral_univ_inv_one_add_sq, abs_of_pos hc, smul_eq_mul] at h
        have e : (fun t : ℝ => (t ^ 2 + c ^ 2)⁻¹) = fun t => (1 + (t / c) ^ 2)⁻¹ / c ^ 2 := by
          funext t; field_simp; ring
        rw [e, integral_div, h]
        field_simp

theorem ofReal_sq_add_ne_zero {a : ℂ} (ha : 0 < a.re) {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) :
    ((t ^ 2 : ℝ) : ℂ) + ((s : ℂ) * a) ^ 2 ≠ 0 := fun h => by
  have ht2 : ((t ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : t ^ 2 ≠ 0)
  have hm := one_add_mem_slitPlane ha ht hs
  have : 1 + ((s : ℂ) * a) ^ 2 / ((t ^ 2 : ℝ) : ℂ) = 0 := by
    rw [← mul_div_cancel_left₀ (1 + ((s : ℂ) * a) ^ 2 / ((t ^ 2 : ℝ) : ℂ)) ht2, mul_add,
      mul_div_cancel₀ _ ht2, mul_one, h, zero_div]
  rw [this] at hm; exact slitPlane_ne_zero hm rfl

/-- The core of row 9: `∫_0^∞ ln(1 + a²/t²) cos(xt) dt = π(1 − e^{−ax})/x`, with integrability
(Fubini against `ln(1 + a²/t²) = ∫_0^1 2sa²/(t² + (sa)²) ds`). -/
theorem integral_log_one_add_cos {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Complex.log (1 + a ^ 2 / (t : ℂ) ^ 2) *
        ((Real.cos (x * t) : ℝ) : ℂ)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Complex.log (1 + a ^ 2 / (t : ℂ) ^ 2) * ((Real.cos (x * t) : ℝ) : ℂ) =
        (π : ℂ) * ((1 - cexp (-(a * x))) / x) := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  set G : ℝ → ℝ → ℂ := fun s t => 2 * s * a ^ 2 / (((t ^ 2 : ℝ) : ℂ) + ((s : ℂ) * a) ^ 2) *
    ((Real.cos (x * t) : ℝ) : ℂ) with hG
  set μ := volume.restrict (Ioc (0 : ℝ) 1)
  set ν := volume.restrict (Ioi (0 : ℝ))
  have hcont : ContinuousOn (Function.uncurry G) (Ioc 0 1 ×ˢ Ioi 0) := by
    refine ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp => ?_)
      (by fun_prop)
    exact ofReal_sq_add_ne_zero ha hp.2 hp.1.1.le
  have hGm : AEStronglyMeasurable (Function.uncurry G) (μ.prod ν) := by
    rw [Measure.prod_restrict]
    exact hcont.aestronglyMeasurable (measurableSet_Ioc.prod measurableSet_Ioi)
  -- the pointwise bound
  have hbound : ∀ s ∈ Ioc (0 : ℝ) 1, ∀ t : ℝ, ‖G s t‖ ≤
      2 * s * ‖a‖ ^ 3 / a.re * (t ^ 2 + (s * ‖a‖) ^ 2)⁻¹ := by
    intro s hs t
    have hw : 0 < ((s : ℂ) * a).re := by simpa using mul_pos hs.1 ha
    have hwn : ‖(s : ℂ) * a‖ = s * ‖a‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1.le]
    have h1 := norm_sq_add_sq_ge hw t
    rw [hwn] at h1
    have hwre : ((s : ℂ) * a).re = s * a.re := by simp
    rw [hwre] at h1
    have hpos : 0 < s * a.re * (t ^ 2 + (s * ‖a‖) ^ 2) / (s * ‖a‖) := by
      have := hs.1; positivity
    simp only [hG, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs]
    rw [show ((t ^ 2 : ℝ) : ℂ) + ((s : ℂ) * a) ^ 2 = ((s : ℂ) * a) ^ 2 + (t : ℂ) ^ 2 by
      push_cast; ring]
    have hcos := Real.abs_cos_le_one (x * t)
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2, abs_of_pos hs.1, norm_pow]
    calc 2 * s * ‖a‖ ^ 2 / ‖((s : ℂ) * a) ^ 2 + (t : ℂ) ^ 2‖ * |Real.cos (x * t)|
        ≤ 2 * s * ‖a‖ ^ 2 / (s * a.re * (t ^ 2 + (s * ‖a‖) ^ 2) / (s * ‖a‖)) * 1 := by
          have := hs.1
          gcongr
      _ = _ := by have := hs.1; field_simp
  have hinner_int : ∀ s ∈ Ioc (0 : ℝ) 1, Integrable (G s) ν := by
    intro s hs
    have hw : 0 < ((s : ℂ) * a).re := by simpa using mul_pos hs.1 ha
    have := (integrableOn_mul_cos (((integrable_inv_sq_add_sq hw).const_mul (2 * s * a ^ 2)
      ).integrableOn (s := Ioi 0)) x)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [hG]; push_cast; ring
  have hC : ∀ s ∈ Ioc (0 : ℝ) 1, ∫ t, ‖G s t‖ ∂ν ≤ 2 * π * ‖a‖ ^ 2 / a.re := by
    intro s hs
    have hsa : 0 < s * ‖a‖ := mul_pos hs.1 hna
    calc ∫ t, ‖G s t‖ ∂ν ≤ ∫ t, 2 * s * ‖a‖ ^ 3 / a.re * (t ^ 2 + (s * ‖a‖) ^ 2)⁻¹ ∂ν := by
          refine integral_mono (hinner_int s hs).norm ?_ fun t => hbound s hs t
          have : Integrable (fun t : ℝ => (t ^ 2 + (s * ‖a‖) ^ 2)⁻¹) := by
            have := (integrable_inv_one_add_sq.comp_div hsa.ne').div_const ((s * ‖a‖) ^ 2)
            refine this.congr (ae_of_all _ fun t => ?_)
            have h0 := hsa.ne'
            have hs0 : s ≠ 0 := hs.1.ne'
            have ha0' : ‖a‖ ≠ 0 := hna.ne'
            simp only
            rw [div_pow, ← inv_mul_eq_div, ← mul_inv]
            congr 1
            field_simp; ring
          exact (this.const_mul _).integrableOn
      _ = 2 * s * ‖a‖ ^ 3 / a.re * ∫ t in Ioi (0 : ℝ), (t ^ 2 + (s * ‖a‖) ^ 2)⁻¹ :=
          integral_const_mul _ _
      _ ≤ 2 * s * ‖a‖ ^ 3 / a.re * (π / (s * ‖a‖)) := by
          exact mul_le_mul_of_nonneg_left (integral_Ioi_inv_sq_add_sq_le hsa)
            (by have := hs.1; positivity)
      _ = _ := by have := hs.1; field_simp
  have hGint : Integrable (Function.uncurry G) (μ.prod ν) := by
    refine (integrable_prod_iff hGm).mpr ⟨?_, ?_⟩
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs =>
        hinner_int s hs)
    · refine Integrable.mono' (integrable_const (2 * π * ‖a‖ ^ 2 / a.re))
        hGm.norm.integral_prod_right' ((ae_restrict_iff' measurableSet_Ioc).mpr
          (Eventually.of_forall fun s hs => ?_))
      rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
      exact hC s hs
  -- the two iterated integrals
  have hts : ∀ t ∈ Ioi (0 : ℝ), ∫ s, G s t ∂μ =
      Complex.log (1 + a ^ 2 / (t : ℂ) ^ 2) * ((Real.cos (x * t) : ℝ) : ℂ) := by
    intro t ht
    simp only [μ, hG]
    rw [integral_mul_const, ← intervalIntegral.integral_of_le zero_le_one,
      ← log_one_add_eq_integral ha ht]
    push_cast; rfl
  have hst : ∀ s ∈ Ioc (0 : ℝ) 1, ∫ t, G s t ∂ν = (π : ℂ) * a * cexp (-(s * a * x)) := by
    intro s hs
    have hw : 0 < ((s : ℂ) * a).re := by simpa using mul_pos hs.1 ha
    have hw0 : (s : ℂ) * a ≠ 0 := fun h => by rw [h] at hw; simp at hw
    have h := integral_inv_sq_add_sq_cos hw hx
    calc ∫ t, G s t ∂ν = 2 * s * a ^ 2 * ∫ t in Ioi (0 : ℝ),
          1 / (((s : ℂ) * a) ^ 2 + (t : ℂ) ^ 2) * ((Real.cos (x * t) : ℝ) : ℂ) := by
          rw [← integral_const_mul]
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
          simp only [hG]; push_cast; ring
      _ = _ := by
          have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.1.ne'
          rw [h]; field_simp
  have hswap := integral_integral_swap hGint
  have hL : ∫ s, ∫ t, G s t ∂ν ∂μ = (π : ℂ) * ((1 - cexp (-(a * x))) / x) := by
    rw [setIntegral_congr_fun measurableSet_Ioc hst, ← intervalIntegral.integral_of_le zero_le_one]
    have hc : -(a * x) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero ha0 (ofReal_ne_zero.mpr hx.ne'))
    have e : ∀ s : ℝ, (π : ℂ) * a * cexp (-(s * a * x)) = (π : ℂ) * a * cexp (-(a * x) * s) :=
      fun s => by ring_nf
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
    have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
    simp only [ofReal_one, mul_one, ofReal_zero, mul_zero, Complex.exp_zero]
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · have hI : IntegrableOn (fun t => ∫ s, G s t ∂μ) (Ioi 0) := hGint.integral_prod_right
    exact hI.congr_fun hts measurableSet_Ioi
  · rw [← setIntegral_congr_fun measurableSet_Ioi hts, ← hL]
    exact hswap.symm

theorem sqrt_two_div_pi_mul_pi : ((√(2 / π) : ℝ) : ℂ) * (π : ℂ) = ((√(2 * π) : ℝ) : ℂ) := by
  rw [← ofReal_mul]
  congr 1
  rw [show 2 * π = 2 / π * π ^ 2 by field_simp, Real.sqrt_mul (by positivity),
    Real.sqrt_sq Real.pi_pos.le]

/-- **DLMF Table 1.14.2, row 9**: `𝓕_c(ln(1 + a²/t²))(x) = √(2π) (1 − e^{−ax})/x`,
`ℜa > 0`, `x > 0`. -/
theorem dlmf_table_1_14_2_r9 {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    dlmfFourierCos (fun t => Complex.log (1 + a ^ 2 / (t : ℂ) ^ 2)) x =
      ((√(2 * π) : ℝ) : ℂ) * ((1 - cexp (-(a * x))) / x) := by
  unfold dlmfFourierCos
  rw [(integral_log_one_add_cos ha hx).2, ← mul_assoc, sqrt_two_div_pi_mul_pi]

theorem log_sq_add_sq_eq {a : ℂ} (ha : 0 < a.re) {t : ℝ} (ht : 0 < t) :
    Complex.log (a ^ 2 + (t : ℂ) ^ 2) =
      (Real.log (t ^ 2) : ℂ) + Complex.log (1 + a ^ 2 / (t : ℂ) ^ 2) := by
  have ht2 : (t : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (ofReal_ne_zero.mpr ht.ne')
  have hne : 1 + a ^ 2 / (t : ℂ) ^ 2 ≠ 0 := by
    have := one_add_mem_slitPlane ha ht zero_le_one
    simp only [ofReal_one, one_mul, ofReal_pow] at this
    exact slitPlane_ne_zero this
  rw [← log_ofReal_mul (by positivity) hne]
  congr 1
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  push_cast
  field_simp
  ring

/-- **DLMF Table 1.14.2, row 10** (general form): for `ℜa, ℜb > 0` and `x > 0`,
`𝓕_c(ln(a² + t²) − ln(b² + t²))(x) = √(2π) (e^{−bx} − e^{−ax})/x`. With principal logarithms
this difference is the right reading of DLMF's `ln((a² + t²)/(b² + t²))` in general: the two
differ by `2πi` e.g. for `a ≈ ε + i`, `b ≈ ε − i`; see `dlmf_table_1_14_2_r10` for the literal
quotient form when `|ph a|, |ph b| < π/4`. -/
theorem dlmf_table_1_14_2_r10_sub {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {x : ℝ}
    (hx : 0 < x) :
    dlmfFourierCos (fun t => Complex.log (a ^ 2 + (t : ℂ) ^ 2) -
        Complex.log (b ^ 2 + (t : ℂ) ^ 2)) x =
      ((√(2 * π) : ℝ) : ℂ) * ((cexp (-(b * x)) - cexp (-(a * x))) / x) := by
  have hA := integral_log_one_add_cos ha hx
  have hB := integral_log_one_add_cos hb hx
  unfold dlmfFourierCos
  have e : ∫ t in Ioi (0 : ℝ), (Complex.log (a ^ 2 + (t : ℂ) ^ 2) -
        Complex.log (b ^ 2 + (t : ℂ) ^ 2)) * ((Real.cos (x * t) : ℝ) : ℂ) =
      ∫ t in Ioi (0 : ℝ), (Complex.log (1 + a ^ 2 / (t : ℂ) ^ 2) *
        ((Real.cos (x * t) : ℝ) : ℂ) - Complex.log (1 + b ^ 2 / (t : ℂ) ^ 2) *
        ((Real.cos (x * t) : ℝ) : ℂ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [log_sq_add_sq_eq ha ht, log_sq_add_sq_eq hb ht]
    ring
  rw [e, integral_sub hA.1 hB.1, hA.2, hB.2, ← sqrt_two_div_pi_mul_pi]
  ring

theorem re_sq_pos {a : ℂ} (ha : |a.im| < a.re) : 0 < (a ^ 2).re := by
  have h0 : 0 ≤ |a.im| := abs_nonneg _
  have : a.im ^ 2 < a.re ^ 2 := by
    rw [← sq_abs a.im]; exact pow_lt_pow_left₀ ha h0 two_ne_zero
  simp only [sq, mul_re] at this ⊢
  linarith

theorem abs_arg_sq_add_lt {a : ℂ} (ha : |a.im| < a.re) (t : ℝ) :
    |arg (a ^ 2 + (t : ℂ) ^ 2)| < π / 2 := by
  refine abs_arg_lt_pi_div_two_iff.mpr (Or.inl ?_)
  have := re_sq_pos ha
  have ht : ((t : ℂ) ^ 2).re = t ^ 2 := by rw [← ofReal_pow, ofReal_re]
  rw [add_re, ht]
  positivity

/-- **DLMF Table 1.14.2, row 10** (literal form): `𝓕_c(ln((a² + t²)/(b² + t²)))(x) =
√(2π) (e^{−bx} − e^{−ax})/x` for `|ph a|, |ph b| < π/4` (i.e. `|ℑa| < ℜa`, `|ℑb| < ℜb`) and
`x > 0`. Under DLMF's stated `ℜa, ℜb > 0` the principal logarithm of the quotient can differ from
`ln(a² + t²) − ln(b² + t²)` by `±2πi` on a set of positive measure, and the formula fails; the
general statement is `dlmf_table_1_14_2_r10_sub`. -/
theorem dlmf_table_1_14_2_r10 {a b : ℂ} (ha : |a.im| < a.re) (hb : |b.im| < b.re) {x : ℝ}
    (hx : 0 < x) :
    dlmfFourierCos (fun t => Complex.log ((a ^ 2 + (t : ℂ) ^ 2) / (b ^ 2 + (t : ℂ) ^ 2))) x =
      ((√(2 * π) : ℝ) : ℂ) * ((cexp (-(b * x)) - cexp (-(a * x))) / x) := by
  have ha' : 0 < a.re := lt_of_le_of_lt (abs_nonneg _) ha
  have hb' : 0 < b.re := lt_of_le_of_lt (abs_nonneg _) hb
  rw [← dlmf_table_1_14_2_r10_sub ha' hb' hx]
  congr 1
  funext t
  have hA := abs_arg_sq_add_lt ha t
  have hB := abs_arg_sq_add_lt hb t
  have hA0 : a ^ 2 + (t : ℂ) ^ 2 ≠ 0 := fun h => by
    have := re_sq_pos ha
    have h' := congrArg Complex.re h
    rw [add_re, ← ofReal_pow, ofReal_re, zero_re] at h'
    nlinarith [sq_nonneg t]
  have hB0 : b ^ 2 + (t : ℂ) ^ 2 ≠ 0 := fun h => by
    have := re_sq_pos hb
    have h' := congrArg Complex.re h
    rw [add_re, ← ofReal_pow, ofReal_re, zero_re] at h'
    nlinarith [sq_nonneg t]
  have him : (Complex.log (a ^ 2 + (t : ℂ) ^ 2) - Complex.log (b ^ 2 + (t : ℂ) ^ 2)).im =
      arg (a ^ 2 + (t : ℂ) ^ 2) - arg (b ^ 2 + (t : ℂ) ^ 2) := by
    rw [sub_im, log_im, log_im]
  rw [abs_lt] at hA hB
  have h1 : -π < (Complex.log (a ^ 2 + (t : ℂ) ^ 2) -
      Complex.log (b ^ 2 + (t : ℂ) ^ 2)).im := by rw [him]; linarith
  have h2 : (Complex.log (a ^ 2 + (t : ℂ) ^ 2) -
      Complex.log (b ^ 2 + (t : ℂ) ^ 2)).im ≤ π := by rw [him]; linarith
  rw [← log_exp h1 h2, Complex.exp_sub, exp_log hA0, exp_log hB0]

end Azurite.DLMF
