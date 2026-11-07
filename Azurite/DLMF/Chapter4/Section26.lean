/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section14TableSinImproper
import Azurite.DLMF.Chapter3.Section5GaussChebyshev
import Azurite.DLMF.Chapter4.Section23Gudermannian

/-!
# DLMF §4.26: Integrals of trigonometric functions

Formalizations of <https://dlmf.nist.gov/4.26>. An indefinite integral `∫ f dx = F` is stated as
`F′ = f` (`HasDerivAt`).

* §4.26(i): the variables are real; "the results … can be extended to the complex plane by
  using continuous branches and avoiding singularities". Each formula of §4.26(ii) is given for
  real `x` on DLMF's interval (`dlmf_4_26_n`) and for complex `z` with the principal logarithm,
  wherever its argument lies off the cut `(−∞, 0]` (`dlmf_4_26_n_complex`).
* §4.26(ii): 4.26.1–4.26.8. For 4.26.5 the real antiderivative is `gd⁻¹` (`gdInv`, the 4.23.41
  integral); its complex extension is `ln((1 + sin z)/cos z)` (cf. 4.23.42, `gdInv_eq_log`).
  In 4.26.7–4.26.8, `a² + b² ≠ 0` (otherwise the right-hand sides are undefined).
* §4.26(iii): orthogonality 4.26.9–4.26.11 from `∫₀^π cos(kt) dt` (`integral_cos_int_mul`, §3.5);
  **errata**: 4.26.9 and 4.26.10 need `m ≠ ±n`, not just `m ≠ n` (`dlmf_4_26_9_neg`,
  `dlmf_4_26_10_neg`: `m = −n ≠ 0` gives `∓½π`). The improper integrals 4.26.12 (Dirichlet, every
  real `m`) and 4.26.13 (Fresnel) are limits of `∫₀^R`, from Chapter 1
  (`tendsto_integral_inv_mul_sin`, `tendsto_integral_sin_mul_sq`, `tendsto_integral_cos_mul_sq`).
* §4.26(iv): 4.26.14–4.26.21 for the principal values of 4.23(i) (`arcsinD`, …, `arccotD`) as
  functions of real `x` on DLMF's intervals, via Mathlib's real functions (`dlmf_4_26_n_real`)
  and `hasDerivAt_ofReal_of_eqOn`.
-/

open Set Filter Topology MeasureTheory
open scoped Real Interval

namespace Azurite.DLMF

/-! ### §4.26(ii), real variables -/

/-- **DLMF 4.26.1**: `∫ sin x dx = −cos x`. -/
theorem dlmf_4_26_1 (x : ℝ) : HasDerivAt (fun x => -Real.cos x) (Real.sin x) x := by
  convert (Real.hasDerivAt_cos x).neg using 1; simp

/-- **DLMF 4.26.2**: `∫ cos x dx = sin x`. -/
theorem dlmf_4_26_2 (x : ℝ) : HasDerivAt Real.sin (Real.cos x) x :=
  Real.hasDerivAt_sin x

/-- **DLMF 4.26.3**: `∫ tan x dx = −ln(cos x)`, `−½π < x < ½π`. -/
theorem dlmf_4_26_3 {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    HasDerivAt (fun x => -Real.log (Real.cos x)) (Real.tan x) x := by
  have hc := (Real.cos_pos_of_mem_Ioo hx).ne'
  refine ((Real.hasDerivAt_cos x).log hc).neg.congr_deriv ?_
  rw [Real.tan_eq_sin_div_cos]; ring

/-- **DLMF 4.26.4**: `∫ csc x dx = ln(tan ½x)`, `0 < x < π`. -/
theorem dlmf_4_26_4 {x : ℝ} (hx : x ∈ Ioo 0 π) :
    HasDerivAt (fun x => Real.log (Real.tan (1 / 2 * x))) (1 / Real.sin x) x := by
  have hm : 1 / 2 * x ∈ Ioo (-(π / 2)) (π / 2) :=
    ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩
  have hc := (Real.cos_pos_of_mem_Ioo hm).ne'
  have hs : Real.sin (1 / 2 * x) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.1, hx.2])).ne'
  have ht : Real.tan (1 / 2 * x) ≠ 0 := by rw [Real.tan_eq_sin_div_cos]; exact div_ne_zero hs hc
  have hl : HasDerivAt (fun x : ℝ => 1 / 2 * x) (1 / 2) x := by
    simpa using (hasDerivAt_id x).const_mul (1 / 2 : ℝ)
  refine (((Real.hasDerivAt_tan hc).comp x hl).log ht).congr_deriv ?_
  rw [Function.comp_apply, show Real.sin x = Real.sin (2 * (1 / 2 * x)) by ring_nf,
    Real.sin_two_mul, Real.tan_eq_sin_div_cos]
  field_simp

/-- **DLMF 4.26.5**: `∫ sec x dx = gd⁻¹ x`, `−½π < x < ½π`. -/
theorem dlmf_4_26_5 {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    HasDerivAt gdInv (1 / Real.cos x) x := by
  have hcont : ContinuousOn (fun t : ℝ => 1 / Real.cos t) (Ioo (-(π / 2)) (π / 2)) :=
    continuousOn_const.div Real.continuous_cos.continuousOn fun t ht =>
      (Real.cos_pos_of_mem_Ioo ht).ne'
  have hs : [[(0 : ℝ), x]] ⊆ Ioo (-(π / 2)) (π / 2) :=
    ordConnected_Ioo.uIcc_subset ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hx
  exact intervalIntegral.integral_hasDerivAt_right ((hcont.mono hs).intervalIntegrable)
    (hcont.stronglyMeasurableAtFilter isOpen_Ioo x hx)
    (hcont.continuousAt (isOpen_Ioo.mem_nhds hx))

/-- **DLMF 4.26.6**: `∫ cot x dx = ln(sin x)`, `0 < x < π`. -/
theorem dlmf_4_26_6 {x : ℝ} (hx : x ∈ Ioo 0 π) :
    HasDerivAt (fun x => Real.log (Real.sin x)) (Real.cot x) x := by
  have hs := (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne'
  refine ((Real.hasDerivAt_sin x).log hs).congr_deriv ?_
  rw [Real.cot_eq_cos_div_sin]

/-- **DLMF 4.26.7**: `∫ e^{ax} sin(bx) dx = e^{ax}/(a² + b²) (a sin(bx) − b cos(bx))`. -/
theorem dlmf_4_26_7 {a b : ℝ} (hab : a ^ 2 + b ^ 2 ≠ 0) (x : ℝ) :
    HasDerivAt (fun x => Real.exp (a * x) / (a ^ 2 + b ^ 2) *
      (a * Real.sin (b * x) - b * Real.cos (b * x))) (Real.exp (a * x) * Real.sin (b * x)) x := by
  have he := ((hasDerivAt_id x).const_mul a).exp
  have hs := ((hasDerivAt_id x).const_mul b).sin
  have hc := ((hasDerivAt_id x).const_mul b).cos
  refine ((he.div_const (a ^ 2 + b ^ 2)).mul ((hs.const_mul a).sub (hc.const_mul b))).congr_deriv
    ?_
  simp only [id, mul_one, Pi.sub_apply]
  field_simp
  ring

/-- **DLMF 4.26.8**: `∫ e^{ax} cos(bx) dx = e^{ax}/(a² + b²) (a cos(bx) + b sin(bx))`. -/
theorem dlmf_4_26_8 {a b : ℝ} (hab : a ^ 2 + b ^ 2 ≠ 0) (x : ℝ) :
    HasDerivAt (fun x => Real.exp (a * x) / (a ^ 2 + b ^ 2) *
      (a * Real.cos (b * x) + b * Real.sin (b * x))) (Real.exp (a * x) * Real.cos (b * x)) x := by
  have he := ((hasDerivAt_id x).const_mul a).exp
  have hs := ((hasDerivAt_id x).const_mul b).sin
  have hc := ((hasDerivAt_id x).const_mul b).cos
  refine ((he.div_const (a ^ 2 + b ^ 2)).mul ((hc.const_mul a).add (hs.const_mul b))).congr_deriv
    ?_
  simp only [id, mul_one, Pi.add_apply]
  field_simp
  ring

/-! ### §4.26(iii) Definite integrals (`m`, `n` integers) -/

theorem intervalIntegrable_cos_int_mul (k : ℤ) :
    IntervalIntegrable (fun t : ℝ => Real.cos (k * t)) volume 0 π :=
  (by fun_prop : Continuous fun t : ℝ => Real.cos (k * t)).intervalIntegrable _ _

theorem integral_sin_mul_sin_int (m n : ℤ) :
    ∫ t in (0 : ℝ)..π, Real.sin (m * t) * Real.sin (n * t) =
      ((if m - n = 0 then π else 0) - (if m + n = 0 then π else 0)) / 2 := by
  have h : ∀ t : ℝ, Real.sin (m * t) * Real.sin (n * t) =
      (Real.cos (((m - n : ℤ) : ℝ) * t) - Real.cos (((m + n : ℤ) : ℝ) * t)) / 2 := fun t => by
    push_cast; rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  simp_rw [h]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (intervalIntegrable_cos_int_mul _) (intervalIntegrable_cos_int_mul _),
    integral_cos_int_mul, integral_cos_int_mul]

theorem integral_cos_mul_cos_int (m n : ℤ) :
    ∫ t in (0 : ℝ)..π, Real.cos (m * t) * Real.cos (n * t) =
      ((if m - n = 0 then π else 0) + (if m + n = 0 then π else 0)) / 2 := by
  have h : ∀ t : ℝ, Real.cos (m * t) * Real.cos (n * t) =
      (Real.cos (((m - n : ℤ) : ℝ) * t) + Real.cos (((m + n : ℤ) : ℝ) * t)) / 2 := fun t => by
    push_cast; rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  simp_rw [h]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (intervalIntegrable_cos_int_mul _) (intervalIntegrable_cos_int_mul _),
    integral_cos_int_mul, integral_cos_int_mul]

/-- **DLMF 4.26.9** (corrected): `∫₀^π sin(mt) sin(nt) dt = 0` for `m ≠ ±n`. -/
theorem dlmf_4_26_9 {m n : ℤ} (h1 : m ≠ n) (h2 : m ≠ -n) :
    ∫ t in (0 : ℝ)..π, Real.sin (m * t) * Real.sin (n * t) = 0 := by
  have h3 : m + n ≠ 0 := fun h => h2 (eq_neg_of_add_eq_zero_left h)
  rw [integral_sin_mul_sin_int]
  simp [sub_ne_zero.mpr h1, h3]

/-- **DLMF 4.26.9** fails for `m = −n ≠ 0` (allowed by DLMF's "`m ≠ n`"): the integral is
`−½π`. -/
theorem dlmf_4_26_9_neg {n : ℤ} (hn : n ≠ 0) :
    ∫ t in (0 : ℝ)..π, Real.sin (((-n : ℤ) : ℝ) * t) * Real.sin (n * t) = -(π / 2) := by
  rw [integral_sin_mul_sin_int]
  simp only [show -n - n ≠ 0 by omega, show -n + n = 0 by omega, ↓reduceIte]
  ring

/-- **DLMF 4.26.10** (corrected): `∫₀^π cos(mt) cos(nt) dt = 0` for `m ≠ ±n`. -/
theorem dlmf_4_26_10 {m n : ℤ} (h1 : m ≠ n) (h2 : m ≠ -n) :
    ∫ t in (0 : ℝ)..π, Real.cos (m * t) * Real.cos (n * t) = 0 := by
  have h3 : m + n ≠ 0 := fun h => h2 (eq_neg_of_add_eq_zero_left h)
  rw [integral_cos_mul_cos_int]
  simp [sub_ne_zero.mpr h1, h3]

/-- **DLMF 4.26.10** fails for `m = −n ≠ 0`: the integral is `½π`. -/
theorem dlmf_4_26_10_neg {n : ℤ} (hn : n ≠ 0) :
    ∫ t in (0 : ℝ)..π, Real.cos (((-n : ℤ) : ℝ) * t) * Real.cos (n * t) = π / 2 := by
  rw [integral_cos_mul_cos_int]
  simp only [show -n - n ≠ 0 by omega, show -n + n = 0 by omega, ↓reduceIte]
  ring

/-- **DLMF 4.26.11**: `∫₀^π sin²(nt) dt = ∫₀^π cos²(nt) dt = ½π`, `n ≠ 0`. -/
theorem dlmf_4_26_11 {n : ℤ} (hn : n ≠ 0) :
    ∫ t in (0 : ℝ)..π, Real.sin (n * t) ^ 2 = π / 2 ∧
      ∫ t in (0 : ℝ)..π, Real.cos (n * t) ^ 2 = π / 2 := by
  have h2 : n + n ≠ 0 := by omega
  constructor
  · simp_rw [sq]
    rw [integral_sin_mul_sin_int]
    simp only [sub_self, h2, ↓reduceIte]
    ring
  · simp_rw [sq]
    rw [integral_cos_mul_cos_int]
    simp only [sub_self, h2, ↓reduceIte]
    ring

/-- **DLMF 4.26.12**: `∫₀^∞ sin(mt)/t dt = ½π, 0, −½π` for `m > 0`, `m = 0`, `m < 0` (an improper
integral, `lim_{R→∞} ∫₀^R`; proved for every real `m`). -/
theorem dlmf_4_26_12 (m : ℝ) :
    (0 < m → Tendsto (fun R => ∫ t in (0 : ℝ)..R, Real.sin (m * t) / t) atTop (𝓝 (π / 2))) ∧
      (m = 0 → Tendsto (fun R => ∫ t in (0 : ℝ)..R, Real.sin (m * t) / t) atTop (𝓝 0)) ∧
      (m < 0 → Tendsto (fun R => ∫ t in (0 : ℝ)..R, Real.sin (m * t) / t) atTop
        (𝓝 (-(π / 2)))) := by
  have e : ∀ x : ℝ, (fun R => ∫ t in (0 : ℝ)..R, Real.sin (x * t) / t) =
      fun R => ∫ t in (0 : ℝ)..R, t⁻¹ * Real.sin (x * t) := fun x => by
    funext R; congr 1; funext t; rw [div_eq_inv_mul]
  refine ⟨fun hm => by rw [e]; exact tendsto_integral_inv_mul_sin hm, fun hm => ?_, fun hm => ?_⟩
  · subst hm; simp
  · have h := (tendsto_integral_inv_mul_sin (neg_pos.mpr hm)).neg
    rw [e]
    refine h.congr fun R => ?_
    rw [← intervalIntegral.integral_neg]
    congr 1; funext t
    rw [neg_mul, Real.sin_neg, mul_neg, neg_neg]

/-- **DLMF 4.26.13**: `∫₀^∞ sin(t²) dt = ∫₀^∞ cos(t²) dt = ½√(½π)` (improper integrals). -/
theorem dlmf_4_26_13 :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, Real.sin (t ^ 2)) atTop (𝓝 (1 / 2 * √(π / 2))) ∧
      Tendsto (fun R => ∫ t in (0 : ℝ)..R, Real.cos (t ^ 2)) atTop (𝓝 (1 / 2 * √(π / 2))) := by
  have hv : √(π / 2) / (2 * √1) = 1 / 2 * √(π / 2) := by rw [Real.sqrt_one]; ring
  have hs := tendsto_integral_sin_mul_sq (a := 1) one_pos
  have hc := tendsto_integral_cos_mul_sq (a := 1) one_pos
  simp only [one_mul, hv] at hs hc
  exact ⟨hs, hc⟩

/-! ### §4.26(iv) Inverse trigonometric functions

Each formula is first proved for Mathlib's real functions (`dlmf_4_26_n_real`) and then for the
principal values of 4.23(i) (`arcsinD`, …, `arccotD`), which agree with them on the interval. -/

/-- A real derivative transfers to a complex-valued `g` that agrees with `f` on an open set. -/
theorem hasDerivAt_ofReal_of_eqOn {f : ℝ → ℝ} {g : ℝ → ℂ} {f' x : ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hx : x ∈ U) (hfg : ∀ y ∈ U, g y = f y) (hf : HasDerivAt f f' x) : HasDerivAt g f' x :=
  hf.ofReal_comp.congr_of_eventuallyEq (eventually_of_mem (hU.mem_nhds hx) hfg)

theorem arcsecD_ofReal {x : ℝ} (hx : 1 ≤ |x|) : arcsecD x = Real.arccos x⁻¹ := by
  have hb : |x⁻¹| ≤ 1 := by rw [abs_inv]; exact inv_le_one_of_one_le₀ hx
  rw [arcsecD, one_div, ← Complex.ofReal_inv, arccosD_ofReal_Icc (abs_le.mp hb)]

theorem hasDerivAt_sqrt_one_sub_sq {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x => √(1 - x ^ 2)) (-x / √(1 - x ^ 2)) x := by
  have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have h := ((hasDerivAt_pow 2 x).const_sub 1).sqrt hp.ne'
  refine h.congr_deriv ?_
  push_cast
  field_simp

theorem hasDerivAt_sqrt_sq_sub_one {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x => √(x ^ 2 - 1)) (x / √(x ^ 2 - 1)) x := by
  have hp : 0 < x ^ 2 - 1 := by nlinarith
  have h := ((hasDerivAt_pow 2 x).sub_const 1).sqrt hp.ne'
  refine h.congr_deriv ?_
  push_cast
  field_simp

theorem hasDerivAt_log_add_sqrt {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x => Real.log (x + √(x ^ 2 - 1))) (1 / √(x ^ 2 - 1)) x := by
  have hp : 0 < x ^ 2 - 1 := by nlinarith
  have hs : 0 < √(x ^ 2 - 1) := Real.sqrt_pos.mpr hp
  have hpos : 0 < x + √(x ^ 2 - 1) := by linarith
  refine (((hasDerivAt_id x).add (hasDerivAt_sqrt_sq_sub_one hx)).log hpos.ne').congr_deriv ?_
  simp only [Pi.add_apply, id]
  field_simp
  ring

theorem hasDerivAt_arcsin_inv {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x => Real.arcsin x⁻¹) (-(1 / (x * √(x ^ 2 - 1)))) x := by
  have hx0 : x ≠ 0 := by positivity
  have hi : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  have hi0 : 0 < x⁻¹ := by positivity
  have h := (Real.hasDerivAt_arcsin (by linarith) hi.ne).comp x (hasDerivAt_inv hx0)
  refine h.congr_deriv ?_
  have hp : 0 < x ^ 2 - 1 := by nlinarith
  have hq : 1 - x⁻¹ ^ 2 = (x ^ 2 - 1) / x ^ 2 := by field_simp
  rw [hq, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by linarith)]
  have hs : 0 < √(x ^ 2 - 1) := Real.sqrt_pos.mpr hp
  field_simp

theorem hasDerivAt_arccos_inv {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x => Real.arccos x⁻¹) (1 / (x * √(x ^ 2 - 1))) x := by
  have h := (hasDerivAt_arcsin_inv hx).const_sub (π / 2)
  rw [neg_neg] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  simp only [Real.arccos_eq_pi_div_two_sub_arcsin]

theorem hasDerivAt_arctan_inv {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x => Real.arctan (1 / x)) (-(1 / (1 + x ^ 2))) x := by
  have hi : HasDerivAt (fun y : ℝ => 1 / y) (-(x ^ 2)⁻¹) x := by
    simpa only [one_div] using hasDerivAt_inv hx
  have h := (Real.hasDerivAt_arctan (1 / x)).comp x hi
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **DLMF 4.26.14** (Mathlib's `arcsin`). -/
theorem dlmf_4_26_14_real {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x => x * Real.arcsin x + √(1 - x ^ 2)) (Real.arcsin x) x := by
  have hs : 0 < √(1 - x ^ 2) := Real.sqrt_pos.mpr (by nlinarith [hx.1, hx.2])
  refine (((hasDerivAt_id x).mul (Real.hasDerivAt_arcsin hx.1.ne' hx.2.ne)).add
    (hasDerivAt_sqrt_one_sub_sq hx)).congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- **DLMF 4.26.14**: `∫ arcsin x dx = x arcsin x + (1 − x²)^{1/2}`, `−1 < x < 1`. -/
theorem dlmf_4_26_14 {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x : ℝ => (x : ℂ) * arcsinD x + (√(1 - x ^ 2) : ℝ)) (arcsinD x) x := by
  rw [arcsinD_ofReal hx]
  exact hasDerivAt_ofReal_of_eqOn isOpen_Ioo hx
    (fun y hy => by rw [arcsinD_ofReal hy]; push_cast; ring) (dlmf_4_26_14_real hx)

/-- **DLMF 4.26.15** (Mathlib's `arccos`). -/
theorem dlmf_4_26_15_real {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x => x * Real.arccos x - √(1 - x ^ 2)) (Real.arccos x) x := by
  have hs : 0 < √(1 - x ^ 2) := Real.sqrt_pos.mpr (by nlinarith [hx.1, hx.2])
  refine (((hasDerivAt_id x).mul (Real.hasDerivAt_arccos hx.1.ne' hx.2.ne)).sub
    (hasDerivAt_sqrt_one_sub_sq hx)).congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- **DLMF 4.26.15**: `∫ arccos x dx = x arccos x − (1 − x²)^{1/2}`, `−1 < x < 1`. -/
theorem dlmf_4_26_15 {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x : ℝ => (x : ℂ) * arccosD x - (√(1 - x ^ 2) : ℝ)) (arccosD x) x := by
  rw [arccosD_ofReal hx]
  exact hasDerivAt_ofReal_of_eqOn isOpen_Ioo hx
    (fun y hy => by rw [arccosD_ofReal hy]; push_cast; ring) (dlmf_4_26_15_real hx)

/-- **DLMF 4.26.16** (Mathlib's `arctan`). -/
theorem dlmf_4_26_16_real (x : ℝ) :
    HasDerivAt (fun x => x * Real.arctan x - 1 / 2 * Real.log (1 + x ^ 2)) (Real.arctan x) x := by
  have hp : 0 < 1 + x ^ 2 := by positivity
  refine (((hasDerivAt_id x).mul (Real.hasDerivAt_arctan x)).sub
    ((((hasDerivAt_pow 2 x).const_add 1).log hp.ne').const_mul (1 / 2))).congr_deriv ?_
  simp only [id]
  push_cast
  field_simp
  ring

/-- **DLMF 4.26.16**: `∫ arctan x dx = x arctan x − ½ ln(1 + x²)`, `−∞ < x < ∞`. -/
theorem dlmf_4_26_16 (x : ℝ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) * arctanD x - 1 / 2 * (Real.log (1 + x ^ 2) : ℝ))
      (arctanD x) x := by
  rw [arctanD_ofReal]
  exact hasDerivAt_ofReal_of_eqOn isOpen_univ (mem_univ x)
    (fun y _ => by rw [arctanD_ofReal]; push_cast; ring) (dlmf_4_26_16_real x)

/-- **DLMF 4.26.17** (Mathlib's `arcsin`, `arccsc x = arcsin(1/x)`). -/
theorem dlmf_4_26_17_real {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x => x * Real.arcsin x⁻¹ + Real.log (x + √(x ^ 2 - 1))) (Real.arcsin x⁻¹)
      x := by
  have hs : 0 < √(x ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  have hx0 : x ≠ 0 := by positivity
  refine (((hasDerivAt_id x).mul (hasDerivAt_arcsin_inv hx)).add
    (hasDerivAt_log_add_sqrt hx)).congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- **DLMF 4.26.17**: `∫ arccsc x dx = x arccsc x + ln(x + (x² − 1)^{1/2})`, `1 < x < ∞`. -/
theorem dlmf_4_26_17 {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x : ℝ => (x : ℂ) * arccscD x + (Real.log (x + √(x ^ 2 - 1)) : ℝ))
      (arccscD x) x := by
  have h1 : ∀ {y : ℝ}, 1 < y → 1 ≤ |y| := fun hy => by rw [abs_of_pos (by linarith)]; exact hy.le
  rw [arccscD_ofReal (h1 hx)]
  exact hasDerivAt_ofReal_of_eqOn isOpen_Ioi (mem_Ioi.mpr hx)
    (fun y hy => by rw [arccscD_ofReal (h1 hy)]; push_cast; ring) (dlmf_4_26_17_real hx)

/-- **DLMF 4.26.18** (Mathlib's `arccos`, `arcsec x = arccos(1/x)`). -/
theorem dlmf_4_26_18_real {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x => x * Real.arccos x⁻¹ - Real.log (x + √(x ^ 2 - 1))) (Real.arccos x⁻¹)
      x := by
  have hs : 0 < √(x ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  have hx0 : x ≠ 0 := by positivity
  refine (((hasDerivAt_id x).mul (hasDerivAt_arccos_inv hx)).sub
    (hasDerivAt_log_add_sqrt hx)).congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- **DLMF 4.26.18**: `∫ arcsec x dx = x arcsec x − ln(x + (x² − 1)^{1/2})`, `1 < x < ∞`. -/
theorem dlmf_4_26_18 {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x : ℝ => (x : ℂ) * arcsecD x - (Real.log (x + √(x ^ 2 - 1)) : ℝ))
      (arcsecD x) x := by
  have h1 : ∀ {y : ℝ}, 1 < y → 1 ≤ |y| := fun hy => by rw [abs_of_pos (by linarith)]; exact hy.le
  rw [arcsecD_ofReal (h1 hx)]
  exact hasDerivAt_ofReal_of_eqOn isOpen_Ioi (mem_Ioi.mpr hx)
    (fun y hy => by rw [arcsecD_ofReal (h1 hy)]; push_cast; ring) (dlmf_4_26_18_real hx)

/-- **DLMF 4.26.19** (Mathlib's `arctan`, `arccot x = arctan(1/x)`). -/
theorem dlmf_4_26_19_real {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => x * Real.arctan (1 / x) + 1 / 2 * Real.log (1 + x ^ 2))
      (Real.arctan (1 / x)) x := by
  have hp : 0 < 1 + x ^ 2 := by positivity
  refine (((hasDerivAt_id x).mul (hasDerivAt_arctan_inv hx.ne')).add
    ((((hasDerivAt_pow 2 x).const_add 1).log hp.ne').const_mul (1 / 2))).congr_deriv ?_
  simp only [id]
  push_cast
  field_simp
  ring

/-- **DLMF 4.26.19**: `∫ arccot x dx = x arccot x + ½ ln(1 + x²)`, `0 < x < ∞`. -/
theorem dlmf_4_26_19 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (x : ℂ) * arccotD x + 1 / 2 * (Real.log (1 + x ^ 2) : ℝ))
      (arccotD x) x := by
  rw [arccotD_ofReal]
  exact hasDerivAt_ofReal_of_eqOn isOpen_Ioi (mem_Ioi.mpr hx)
    (fun y _ => by rw [arccotD_ofReal]; push_cast; ring) (dlmf_4_26_19_real hx)

/-- **DLMF 4.26.20** (Mathlib's `arcsin`). -/
theorem dlmf_4_26_20_real {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x => (x ^ 2 / 2 - 1 / 4) * Real.arcsin x + x / 4 * √(1 - x ^ 2))
      (x * Real.arcsin x) x := by
  have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hs : 0 < √(1 - x ^ 2) := Real.sqrt_pos.mpr hp
  have hs2 : √(1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hp.le
  refine (((((hasDerivAt_pow 2 x).div_const 2).sub_const (1 / 4)).mul
    (Real.hasDerivAt_arcsin hx.1.ne' hx.2.ne)).add
    (((hasDerivAt_id x).div_const 4).mul (hasDerivAt_sqrt_one_sub_sq hx))).congr_deriv ?_
  simp only [id]
  push_cast
  field_simp
  linear_combination 2 * hs2

/-- **DLMF 4.26.20**: `∫ x arcsin x dx = (x²/2 − 1/4) arcsin x + (x/4)(1 − x²)^{1/2}`,
`−1 < x < 1`. -/
theorem dlmf_4_26_20 {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x : ℝ => ((x : ℂ) ^ 2 / 2 - 1 / 4) * arcsinD x + (x : ℂ) / 4 *
      (√(1 - x ^ 2) : ℝ)) ((x : ℂ) * arcsinD x) x := by
  rw [arcsinD_ofReal hx, ← Complex.ofReal_mul]
  exact hasDerivAt_ofReal_of_eqOn isOpen_Ioo hx
    (fun y hy => by rw [arcsinD_ofReal hy]; push_cast; ring) (dlmf_4_26_20_real hx)

/-- **DLMF 4.26.21** (Mathlib's `arccos`). -/
theorem dlmf_4_26_21_real {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x => (x ^ 2 / 2 - 1 / 4) * Real.arccos x - x / 4 * √(1 - x ^ 2))
      (x * Real.arccos x) x := by
  have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hs : 0 < √(1 - x ^ 2) := Real.sqrt_pos.mpr hp
  have hs2 : √(1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hp.le
  refine (((((hasDerivAt_pow 2 x).div_const 2).sub_const (1 / 4)).mul
    (Real.hasDerivAt_arccos hx.1.ne' hx.2.ne)).sub
    (((hasDerivAt_id x).div_const 4).mul (hasDerivAt_sqrt_one_sub_sq hx))).congr_deriv ?_
  simp only [id]
  push_cast
  field_simp
  linear_combination (-2 : ℝ) * hs2

/-- **DLMF 4.26.21**: `∫ x arccos x dx = (x²/2 − 1/4) arccos x − (x/4)(1 − x²)^{1/2}`,
`−1 < x < 1`. -/
theorem dlmf_4_26_21 {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x : ℝ => ((x : ℂ) ^ 2 / 2 - 1 / 4) * arccosD x - (x : ℂ) / 4 *
      (√(1 - x ^ 2) : ℝ)) ((x : ℂ) * arccosD x) x := by
  rw [arccosD_ofReal hx, ← Complex.ofReal_mul]
  exact hasDerivAt_ofReal_of_eqOn isOpen_Ioo hx
    (fun y hy => by rw [arccosD_ofReal hy]; push_cast; ring) (dlmf_4_26_21_real hx)

/-! ### §4.26(i): complex extensions (principal branches, off the cut) -/

section Complex

open Complex

/-- **DLMF 4.26.1**, complex: `∫ sin z dz = −cos z`. -/
theorem dlmf_4_26_1_complex (z : ℂ) : HasDerivAt (fun z => -cos z) (sin z) z := by
  convert (hasDerivAt_cos z).neg using 1; simp

/-- **DLMF 4.26.2**, complex: `∫ cos z dz = sin z`. -/
theorem dlmf_4_26_2_complex (z : ℂ) : HasDerivAt sin (cos z) z :=
  hasDerivAt_sin z

/-- **DLMF 4.26.3**, complex: `∫ tan z dz = −ln(cos z)` where `cos z ∉ (−∞, 0]`. -/
theorem dlmf_4_26_3_complex {z : ℂ} (hz : cos z ∈ slitPlane) :
    HasDerivAt (fun z => -log (cos z)) (tan z) z := by
  refine ((hasDerivAt_cos z).clog hz).neg.congr_deriv ?_
  rw [tan_eq_sin_div_cos]; ring

/-- **DLMF 4.26.4**, complex: `∫ csc z dz = ln(tan ½z)` where `tan ½z ∉ (−∞, 0]`. -/
theorem dlmf_4_26_4_complex {z : ℂ} (hz : tan (1 / 2 * z) ∈ slitPlane) :
    HasDerivAt (fun z => log (tan (1 / 2 * z))) (1 / sin z) z := by
  have ht := slitPlane_ne_zero hz
  rw [tan_eq_sin_div_cos] at ht
  have hc : cos (1 / 2 * z) ≠ 0 := fun h => ht (by rw [h, div_zero])
  have hs : sin (1 / 2 * z) ≠ 0 := fun h => ht (by rw [h, zero_div])
  have hl : HasDerivAt (fun z : ℂ => 1 / 2 * z) (1 / 2) z := by
    simpa using (hasDerivAt_id z).const_mul (1 / 2 : ℂ)
  refine (((hasDerivAt_tan hc).comp z hl).clog hz).congr_deriv ?_
  rw [Function.comp_apply, show sin z = sin (2 * (1 / 2 * z)) by ring_nf, sin_two_mul,
    tan_eq_sin_div_cos]
  field_simp

/-- **DLMF 4.26.5**, complex: `∫ sec z dz = ln((1 + sin z)/cos z)` where
`(1 + sin z)/cos z ∉ (−∞, 0]`; for real `x ∈ (−½π, ½π)` this is `gd⁻¹ x` (`gdInv_eq_log`). -/
theorem dlmf_4_26_5_complex {z : ℂ} (hz : (1 + sin z) / cos z ∈ slitPlane) :
    HasDerivAt (fun z => log ((1 + sin z) / cos z)) (1 / cos z) z := by
  have ht := slitPlane_ne_zero hz
  have hc : cos z ≠ 0 := fun h => ht (by rw [h, div_zero])
  have hs : 1 + sin z ≠ 0 := fun h => ht (by rw [h, zero_div])
  refine ((((hasDerivAt_sin z).const_add 1).div (hasDerivAt_cos z) hc).clog hz).congr_deriv ?_
  have hsc := sin_sq_add_cos_sq z
  simp only [Pi.div_apply]
  field_simp
  linear_combination hsc

/-- On `(−½π, ½π)` the complex antiderivative of 4.26.5 is `gd⁻¹ x`, and its argument is off
the cut. -/
theorem dlmf_4_26_5_complex_ofReal {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    (1 + sin (x : ℂ)) / cos (x : ℂ) ∈ slitPlane ∧
      log ((1 + sin (x : ℂ)) / cos (x : ℂ)) = gdInv x := by
  have hm := sin_mem_Ioo hx
  have hpos : 0 < (1 + Real.sin x) / Real.cos x :=
    div_pos (by linarith [hm.1]) (Real.cos_pos_of_mem_Ioo hx)
  have he : (1 + sin (x : ℂ)) / cos (x : ℂ) = (((1 + Real.sin x) / Real.cos x : ℝ) : ℂ) := by
    push_cast; rfl
  rw [he, gdInv_eq_log hx, ← ofReal_log hpos.le]
  exact ⟨ofReal_mem_slitPlane.mpr hpos, rfl⟩

/-- **DLMF 4.26.6**, complex: `∫ cot z dz = ln(sin z)` where `sin z ∉ (−∞, 0]`. -/
theorem dlmf_4_26_6_complex {z : ℂ} (hz : sin z ∈ slitPlane) :
    HasDerivAt (fun z => log (sin z)) (cot z) z := by
  refine ((hasDerivAt_sin z).clog hz).congr_deriv ?_
  rw [cot_eq_cos_div_sin]

/-- **DLMF 4.26.7**, complex: `∫ e^{az} sin(bz) dz = e^{az}/(a² + b²) (a sin(bz) − b cos(bz))`,
`a² + b² ≠ 0`. -/
theorem dlmf_4_26_7_complex {a b : ℂ} (hab : a ^ 2 + b ^ 2 ≠ 0) (z : ℂ) :
    HasDerivAt (fun z => exp (a * z) / (a ^ 2 + b ^ 2) * (a * sin (b * z) - b * cos (b * z)))
      (exp (a * z) * sin (b * z)) z := by
  have he := ((hasDerivAt_id z).const_mul a).cexp
  have hs := ((hasDerivAt_id z).const_mul b).csin
  have hc := ((hasDerivAt_id z).const_mul b).ccos
  refine ((he.div_const (a ^ 2 + b ^ 2)).mul ((hs.const_mul a).sub (hc.const_mul b))).congr_deriv
    ?_
  simp only [id, mul_one, Pi.sub_apply]
  field_simp
  ring

/-- **DLMF 4.26.8**, complex: `∫ e^{az} cos(bz) dz = e^{az}/(a² + b²) (a cos(bz) + b sin(bz))`,
`a² + b² ≠ 0`. -/
theorem dlmf_4_26_8_complex {a b : ℂ} (hab : a ^ 2 + b ^ 2 ≠ 0) (z : ℂ) :
    HasDerivAt (fun z => exp (a * z) / (a ^ 2 + b ^ 2) * (a * cos (b * z) + b * sin (b * z)))
      (exp (a * z) * cos (b * z)) z := by
  have he := ((hasDerivAt_id z).const_mul a).cexp
  have hs := ((hasDerivAt_id z).const_mul b).csin
  have hc := ((hasDerivAt_id z).const_mul b).ccos
  refine ((he.div_const (a ^ 2 + b ^ 2)).mul ((hc.const_mul a).add (hs.const_mul b))).congr_deriv
    ?_
  simp only [id, mul_one, Pi.add_apply]
  field_simp
  ring

end Complex

end Azurite.DLMF
