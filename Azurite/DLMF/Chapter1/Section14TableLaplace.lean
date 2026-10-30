/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14Laplace
import Azurite.DLMF.Chapter1.Section14TableSinImproper

/-!
# DLMF Table 1.14.4: Laplace transforms

Rows 1–12 of <https://dlmf.nist.gov/1.14.T4> for `ℒ f(s) = ∫_0^∞ e^{−st} f(t) dt` (`laplace`).
Rows 13–16: `Section14TableLaplaceLog.lean`.

* `integral_Ioi_pow_mul_cexp_neg`: `∫_0^∞ tⁿ e^{−ct} dt = n!/c^{n+1}` (`ℜc > 0`, induction by
  parts);
  `laplace_pow_mul_cexp`: `ℒ[tⁿ e^{ct}](s) = n!/(s − c)^{n+1}`; `laplace_two_exp` (two terms).
* Rows: `dlmf_table_1_14_4_r1` (`1`), `_r2` (`tⁿ/n!`), `_r3` (`(πt)^{−1/2}`, principal root),
  `_r4` (`e^{−at}`), `_r5` (`tⁿe^{−at}/n!`), `_r6` (`(e^{−at} − e^{−bt})/(b − a)`), `_r7`–`_r12`
  (`sin`, `cos`, `sinh`, `cosh`, `t sin`, `t cos` of `at`, complex `a`), all by writing `f` as a
  combination of `tⁿ e^{ct}`.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real Nat

namespace Azurite.DLMF

/-! ### `∫_0^∞ tⁿ e^{−ct} dt = n!/c^{n+1}` -/

theorem integrableOn_Ioi_pow_mul_cexp_neg {c : ℂ} (hc : 0 < c.re) (n : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * cexp (-(c * t))) (Ioi 0) :=
  (integrableOn_Ioi_rpow_mul_cexp_neg hc (s := n) (by have := n.cast_nonneg (α := ℝ); linarith))
    |>.congr_fun (fun t ht => by
      simp only
      rw [Real.rpow_natCast, ofReal_pow]) measurableSet_Ioi

theorem tendsto_pow_mul_cexp_neg {c : ℂ} (hc : 0 < c.re) (n : ℕ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ n * cexp (-(c * t))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (tendsto_id.const_mul_atTop hc)).div_const (c.re ^ n)
  rw [zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  simp only [Function.comp, id, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht,
    Complex.norm_exp]
  have : (-(c * (t : ℂ))).re = -(c.re * t) := by simp
  rw [this, mul_pow]
  field_simp

/-- `∫_0^∞ tⁿ e^{−ct} dt = n!/c^{n+1}` for `ℜc > 0`. -/
theorem integral_Ioi_pow_mul_cexp_neg {c : ℂ} (hc : 0 < c.re) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * cexp (-(c * t)) = n ! / c ^ (n + 1) := by
  have hc0 : c ≠ 0 := fun h => by rw [h] at hc; simp at hc
  induction n with
  | zero =>
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    exact integral_Ioi_cexp_neg hc
  | succ n ih =>
    have hv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => -cexp (-(c * t)) / c) (cexp (-(c * t))) t :=
      fun t => by
        have := (((hasDerivAt_id t).ofReal_comp.const_mul c).neg.cexp.neg).div_const c
        simp only [id, Pi.neg_apply, ofReal_one, mul_one] at this
        refine this.congr_deriv ?_
        field_simp
    have hu : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) ^ (n + 1))
        (((n + 1 : ℕ) : ℂ) * (t : ℂ) ^ n) t := fun t : ℝ => by
      have := (hasDerivAt_id t).ofReal_comp.pow (n + 1)
      simp only [id, Nat.add_sub_cancel] at this
      refine this.congr_deriv ?_
      push_cast; ring
    have huv : Continuous fun t : ℝ => (t : ℂ) ^ (n + 1) * (-cexp (-(c * t)) / c) := by
      fun_prop
    have h := integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (a' := 0) (b' := 0)
      (fun t _ => hu t) (fun t _ => hv t)
      (by simpa [Pi.mul_def] using integrableOn_Ioi_pow_mul_cexp_neg hc (n + 1))
      (by
        have : IntegrableOn (fun t : ℝ => -(((n + 1 : ℕ) : ℂ)) / c *
            ((t : ℂ) ^ n * cexp (-(c * t)))) (Ioi 0) :=
          (integrableOn_Ioi_pow_mul_cexp_neg hc n).const_mul _
        refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
        simp only [Pi.mul_apply]; ring)
      (by
        have := (huv.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa [Pi.mul_def] using this)
      (by
        have := (tendsto_pow_mul_cexp_neg hc (n + 1)).neg.div_const c
        simp only [neg_zero, zero_div] at this
        refine this.congr fun t => ?_
        simp only [Pi.mul_apply]; ring)
    have e : ∫ t in Ioi (0 : ℝ), ((n + 1 : ℕ) : ℂ) * (t : ℂ) ^ n * (-cexp (-(c * t)) / c) =
        -(((n + 1 : ℕ) : ℂ) / c) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * cexp (-(c * t)) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      ring
    rw [sub_zero, zero_sub, e, ih, neg_mul, neg_neg] at h
    rw [h, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-! ### Laplace transforms of `tⁿ e^{ct}` and linearity -/

theorem integrableOn_laplace_pow_mul_cexp {s c : ℂ} (h : 0 < (s - c).re) (n : ℕ) :
    IntegrableOn (fun t : ℝ => cexp (-(s * t)) * ((t : ℂ) ^ n * cexp (c * t))) (Ioi 0) :=
  (integrableOn_Ioi_pow_mul_cexp_neg h n).congr_fun (fun t _ => by
    simp only
    rw [show -((s - c) * (t : ℂ)) = -(s * t) + c * t by ring, Complex.exp_add]; ring)
    measurableSet_Ioi

/-- `ℒ[tⁿ e^{ct}](s) = n!/(s − c)^{n+1}` for `ℜ(s − c) > 0`. -/
theorem laplace_pow_mul_cexp {s c : ℂ} (h : 0 < (s - c).re) (n : ℕ) :
    laplace (fun t => (t : ℂ) ^ n * cexp (c * t)) s = n ! / (s - c) ^ (n + 1) := by
  unfold laplace
  rw [← integral_Ioi_pow_mul_cexp_neg h n]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only
  rw [show -((s - c) * (t : ℂ)) = -(s * t) + c * t by ring, Complex.exp_add]; ring

/-- `ℒ[α tⁿ e^{c₁t} + β tⁿ e^{c₂t}](s)`. -/
theorem laplace_two_exp {s c₁ c₂ : ℂ} (α β : ℂ) (n : ℕ) (h1 : 0 < (s - c₁).re)
    (h2 : 0 < (s - c₂).re) :
    laplace (fun t => α * ((t : ℂ) ^ n * cexp (c₁ * t)) + β * ((t : ℂ) ^ n * cexp (c₂ * t))) s =
      α * (n ! / (s - c₁) ^ (n + 1)) + β * (n ! / (s - c₂) ^ (n + 1)) := by
  rw [← laplace_pow_mul_cexp h1, ← laplace_pow_mul_cexp h2]
  unfold laplace
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((integrableOn_laplace_pow_mul_cexp h1 n).const_mul α)
    ((integrableOn_laplace_pow_mul_cexp h2 n).const_mul β)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

/-! ### Rows 1–6 -/

/-- **Table 1.14.4, row 1**: `ℒ[1](s) = 1/s` (`ℜs > 0`). -/
theorem dlmf_table_1_14_4_r1 {s : ℂ} (hs : 0 < s.re) : laplace (fun _ => 1) s = 1 / s := by
  have := laplace_pow_mul_cexp (c := 0) (by simpa using hs) 0
  simp only [pow_zero, zero_mul, Complex.exp_zero, mul_one, Nat.factorial_zero, Nat.cast_one,
    sub_zero, zero_add, pow_one] at this
  exact this

/-- **Table 1.14.4, row 2**: `ℒ[tⁿ/n!](s) = 1/s^{n+1}` (`ℜs > 0`). -/
theorem dlmf_table_1_14_4_r2 {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    laplace (fun t => (t : ℂ) ^ n / n !) s = 1 / s ^ (n + 1) := by
  have := laplace_two_exp (c₁ := 0) (c₂ := 0) (1 / n ! : ℂ) 0 n (by simpa using hs)
    (by simpa using hs)
  simp only [zero_mul, Complex.exp_zero, mul_one, sub_zero, add_zero] at this
  have e : (fun t : ℝ => (t : ℂ) ^ n / n !) = fun t : ℝ => 1 / (n ! : ℂ) * (t : ℂ) ^ n := by
    funext t; ring
  rw [e, this]
  have : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- **Table 1.14.4, row 3**: `ℒ[(πt)^{−1/2}](s) = s^{−1/2}` (`ℜs > 0`, principal root). -/
theorem dlmf_table_1_14_4_r3 {s : ℂ} (hs : 0 < s.re) :
    laplace (fun t => ((1 / √(π * t) : ℝ) : ℂ)) s = 1 / s ^ (1 / 2 : ℂ) := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have h := integral_Ioi_rpow_neg_half_mul_cexp hs
  unfold laplace
  have e : ∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * ((1 / √(π * t) : ℝ) : ℂ) =
      ((√π)⁻¹ : ℂ) * ∫ t in Ioi (0 : ℝ), ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * cexp (-(s * t)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [show -(1 / 2 : ℝ) = -(1 / 2) from rfl, rpow_neg_half_eq (le_of_lt ht),
      Real.sqrt_mul Real.pi_pos.le]
    push_cast; ring
  rw [e, h]
  have harg : s.arg ≠ π := by
    intro h'; have := (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hs)); rw [h', abs_of_pos Real.pi_pos]
      at this; linarith [Real.pi_pos]
  rw [div_eq_mul_inv (π : ℂ) s, ofReal_mul_cpow_complex Real.pi_pos (inv_ne_zero hs0),
    inv_cpow _ _ harg, cpow_half_ofReal Real.pi_pos.le]
  have h1 : ((√π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

/-- **Table 1.14.4, row 4**: `ℒ[e^{−at}](s) = 1/(s + a)` (`ℜ(s + a) > 0`). -/
theorem dlmf_table_1_14_4_r4 {s a : ℂ} (h : 0 < (s + a).re) :
    laplace (fun t => cexp (-(a * t))) s = 1 / (s + a) := by
  have := laplace_pow_mul_cexp (c := -a) (by simpa using h) 0
  simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, sub_neg_eq_add, zero_add,
    pow_one, neg_mul] at this
  simpa only [neg_mul] using this

/-- **Table 1.14.4, row 5**: `ℒ[tⁿ e^{−at}/n!](s) = 1/(s + a)^{n+1}` (`ℜ(s + a) > 0`). -/
theorem dlmf_table_1_14_4_r5 {s a : ℂ} (h : 0 < (s + a).re) (n : ℕ) :
    laplace (fun t => (t : ℂ) ^ n * cexp (-(a * t)) / n !) s = 1 / (s + a) ^ (n + 1) := by
  have := laplace_two_exp (c₁ := -a) (c₂ := -a) (1 / n ! : ℂ) 0 n (by simpa using h)
    (by simpa using h)
  simp only [zero_mul, add_zero, sub_neg_eq_add] at this
  have e : (fun t : ℝ => (t : ℂ) ^ n * cexp (-(a * t)) / n !) =
      fun t : ℝ => 1 / (n ! : ℂ) * ((t : ℂ) ^ n * cexp (-a * t)) := by
    funext t; rw [neg_mul]; ring
  rw [e, this]
  have : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- **Table 1.14.4, row 6**: `ℒ[(e^{−at} − e^{−bt})/(b − a)](s) = 1/((s + a)(s + b))` (`a ≠ b`,
`ℜs > −ℜa`, `ℜs > −ℜb`). -/
theorem dlmf_table_1_14_4_r6 {s a b : ℂ} (hab : a ≠ b) (ha : 0 < (s + a).re)
    (hb : 0 < (s + b).re) :
    laplace (fun t => (cexp (-(a * t)) - cexp (-(b * t))) / (b - a)) s =
      1 / ((s + a) * (s + b)) := by
  have := laplace_two_exp (c₁ := -a) (c₂ := -b) (1 / (b - a)) (-(1 / (b - a))) 0
    (by simpa using ha) (by simpa using hb)
  have e : (fun t : ℝ => (cexp (-(a * t)) - cexp (-(b * t))) / (b - a)) =
      fun t : ℝ => 1 / (b - a) * ((t : ℂ) ^ 0 * cexp (-a * t)) +
        -(1 / (b - a)) * ((t : ℂ) ^ 0 * cexp (-b * t)) := by
    funext t; simp only [pow_zero, one_mul, neg_mul]; ring
  rw [e, this]
  have h1 : s + a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have h2 : s + b ≠ 0 := fun h => by rw [h] at hb; simp at hb
  have h3 : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  simp only [sub_neg_eq_add, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
  field_simp
  ring

/-! ### Rows 7–12: trigonometric and hyperbolic -/

theorem re_sub_mul_I_pos {s a : ℂ} (h : |a.im| < s.re) : 0 < (s - a * I).re := by
  simp only [sub_re, mul_re, I_re, mul_zero, I_im, mul_one, zero_sub, sub_neg_eq_add]
  linarith [neg_abs_le a.im]

theorem re_add_mul_I_pos {s a : ℂ} (h : |a.im| < s.re) : 0 < (s + a * I).re := by
  simp only [add_re, mul_re, I_re, mul_zero, I_im, mul_one, zero_sub]
  linarith [le_abs_self a.im]

theorem sq_add_sq_ne_zero_of_im {s a : ℂ} (h : |a.im| < s.re) : s ^ 2 + a ^ 2 ≠ 0 := by
  have h1 : s - a * I ≠ 0 := fun e => by have := re_sub_mul_I_pos h; rw [e] at this; simp at this
  have h2 : s + a * I ≠ 0 := fun e => by have := re_add_mul_I_pos h; rw [e] at this; simp at this
  have : s ^ 2 + a ^ 2 = (s - a * I) * (s + a * I) := by ring_nf; rw [I_sq]; ring
  rw [this]; exact mul_ne_zero h1 h2

theorem sin_mul_eq (a : ℂ) (t : ℝ) :
    Complex.sin (a * t) = I / 2 * ((t : ℂ) ^ 0 * cexp (-(a * I) * t)) +
      -(I / 2) * ((t : ℂ) ^ 0 * cexp ((a * I) * t)) := by
  rw [Complex.sin]; simp only [pow_zero, one_mul]; ring_nf

theorem cos_mul_eq (a : ℂ) (t : ℝ) :
    Complex.cos (a * t) = 1 / 2 * ((t : ℂ) ^ 0 * cexp ((a * I) * t)) +
      1 / 2 * ((t : ℂ) ^ 0 * cexp (-(a * I) * t)) := by
  rw [Complex.cos]; simp only [pow_zero, one_mul]; ring_nf

/-- **Table 1.14.4, row 7**: `ℒ[sin(at)](s) = a/(s² + a²)` (`ℜs > |ℑa|`). -/
theorem dlmf_table_1_14_4_r7 {s a : ℂ} (h : |a.im| < s.re) :
    laplace (fun t => Complex.sin (a * t)) s = a / (s ^ 2 + a ^ 2) := by
  have h1 := re_add_mul_I_pos h
  have h2 := re_sub_mul_I_pos h
  simp_rw [sin_mul_eq]
  rw [laplace_two_exp _ _ 0 (by simpa using h1) (by simpa using h2)]
  have hne1 : s + a * I ≠ 0 := fun e => by rw [e] at h1; simp at h1
  have hne2 : s - a * I ≠ 0 := fun e => by rw [e] at h2; simp at h2
  have e2 : s ^ 2 + a ^ 2 = (s - a * I) * (s + a * I) := by ring_nf; rw [I_sq]; ring
  rw [e2]
  simp only [sub_neg_eq_add, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
  generalize hp : s + a * I = p at *
  generalize hq : s - a * I = q at *
  have hs : s = (p + q) / 2 := by rw [← hp, ← hq]; ring
  have ha : a = -I * (p - q) / 2 := by rw [← hp, ← hq]; ring_nf; rw [I_sq]; ring
  subst hs ha
  field_simp
  ring

/-- **Table 1.14.4, row 8**: `ℒ[cos(at)](s) = s/(s² + a²)` (`ℜs > |ℑa|`). -/
theorem dlmf_table_1_14_4_r8 {s a : ℂ} (h : |a.im| < s.re) :
    laplace (fun t => Complex.cos (a * t)) s = s / (s ^ 2 + a ^ 2) := by
  have h1 := re_add_mul_I_pos h
  have h2 := re_sub_mul_I_pos h
  simp_rw [cos_mul_eq]
  rw [laplace_two_exp _ _ 0 (by simpa using h2) (by simpa using h1)]
  have hne1 : s + a * I ≠ 0 := fun e => by rw [e] at h1; simp at h1
  have hne2 : s - a * I ≠ 0 := fun e => by rw [e] at h2; simp at h2
  have e2 : s ^ 2 + a ^ 2 = (s - a * I) * (s + a * I) := by ring_nf; rw [I_sq]; ring
  rw [e2]
  simp only [sub_neg_eq_add, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
  field_simp
  ring_nf

theorem re_sub_pos_of_abs_re {s a : ℂ} (h : |a.re| < s.re) : 0 < (s - a).re := by
  simp only [sub_re]; linarith [le_abs_self a.re]

theorem re_add_pos_of_abs_re {s a : ℂ} (h : |a.re| < s.re) : 0 < (s + a).re := by
  simp only [add_re]; linarith [neg_abs_le a.re]

/-- **Table 1.14.4, row 9**: `ℒ[sinh(at)](s) = a/(s² − a²)` (`ℜs > |ℜa|`). -/
theorem dlmf_table_1_14_4_r9 {s a : ℂ} (h : |a.re| < s.re) :
    laplace (fun t => Complex.sinh (a * t)) s = a / (s ^ 2 - a ^ 2) := by
  have h1 := re_sub_pos_of_abs_re h
  have h2 := re_add_pos_of_abs_re h
  have e : (fun t : ℝ => Complex.sinh (a * t)) = fun t : ℝ =>
      1 / 2 * ((t : ℂ) ^ 0 * cexp (a * t)) + -(1 / 2) * ((t : ℂ) ^ 0 * cexp (-a * t)) := by
    funext t; rw [Complex.sinh]; simp only [pow_zero, one_mul, neg_mul]; ring
  rw [e, laplace_two_exp _ _ 0 h1 (by simpa using h2)]
  have hne1 : s - a ≠ 0 := fun e => by rw [e] at h1; simp at h1
  have hne2 : s + a ≠ 0 := fun e => by rw [e] at h2; simp at h2
  have : s ^ 2 - a ^ 2 ≠ 0 := by
    rw [show s ^ 2 - a ^ 2 = (s - a) * (s + a) by ring]; exact mul_ne_zero hne1 hne2
  simp only [sub_neg_eq_add, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
  field_simp
  ring

/-- **Table 1.14.4, row 10**: `ℒ[cosh(at)](s) = s/(s² − a²)` (`ℜs > |ℜa|`). -/
theorem dlmf_table_1_14_4_r10 {s a : ℂ} (h : |a.re| < s.re) :
    laplace (fun t => Complex.cosh (a * t)) s = s / (s ^ 2 - a ^ 2) := by
  have h1 := re_sub_pos_of_abs_re h
  have h2 := re_add_pos_of_abs_re h
  have e : (fun t : ℝ => Complex.cosh (a * t)) = fun t : ℝ =>
      1 / 2 * ((t : ℂ) ^ 0 * cexp (a * t)) + 1 / 2 * ((t : ℂ) ^ 0 * cexp (-a * t)) := by
    funext t; rw [Complex.cosh]; simp only [pow_zero, one_mul, neg_mul]; ring
  rw [e, laplace_two_exp _ _ 0 h1 (by simpa using h2)]
  have hne1 : s - a ≠ 0 := fun e => by rw [e] at h1; simp at h1
  have hne2 : s + a ≠ 0 := fun e => by rw [e] at h2; simp at h2
  have : s ^ 2 - a ^ 2 ≠ 0 := by
    rw [show s ^ 2 - a ^ 2 = (s - a) * (s + a) by ring]; exact mul_ne_zero hne1 hne2
  simp only [sub_neg_eq_add, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
  field_simp
  ring

/-- **Table 1.14.4, row 11**: `ℒ[t sin(at)](s) = 2as/(s² + a²)²` (`ℜs > |ℑa|`). -/
theorem dlmf_table_1_14_4_r11 {s a : ℂ} (h : |a.im| < s.re) :
    laplace (fun t => (t : ℂ) * Complex.sin (a * t)) s = 2 * a * s / (s ^ 2 + a ^ 2) ^ 2 := by
  have h1 := re_add_mul_I_pos h
  have h2 := re_sub_mul_I_pos h
  have e : (fun t : ℝ => (t : ℂ) * Complex.sin (a * t)) = fun t : ℝ =>
      I / 2 * ((t : ℂ) ^ 1 * cexp (-(a * I) * t)) +
        -(I / 2) * ((t : ℂ) ^ 1 * cexp ((a * I) * t)) := by
    funext t; rw [Complex.sin]; ring_nf
  rw [e, laplace_two_exp _ _ 1 (by simpa using h1) (by simpa using h2)]
  have hne1 : s + a * I ≠ 0 := fun e => by rw [e] at h1; simp at h1
  have hne2 : s - a * I ≠ 0 := fun e => by rw [e] at h2; simp at h2
  have := sq_add_sq_ne_zero_of_im h
  have e2 : s ^ 2 + a ^ 2 = (s - a * I) * (s + a * I) := by ring_nf; rw [I_sq]; ring
  rw [e2]
  simp only [sub_neg_eq_add, Nat.factorial_one, Nat.cast_one]
  generalize hp : s + a * I = p at *
  generalize hq : s - a * I = q at *
  have hs : s = (p + q) / 2 := by rw [← hp, ← hq]; ring
  have ha : a = -I * (p - q) / 2 := by rw [← hp, ← hq]; ring_nf; rw [I_sq]; ring
  subst hs ha
  field_simp
  ring

/-- **Table 1.14.4, row 12**: `ℒ[t cos(at)](s) = (s² − a²)/(s² + a²)²` (`ℜs > |ℑa|`). -/
theorem dlmf_table_1_14_4_r12 {s a : ℂ} (h : |a.im| < s.re) :
    laplace (fun t => (t : ℂ) * Complex.cos (a * t)) s =
      (s ^ 2 - a ^ 2) / (s ^ 2 + a ^ 2) ^ 2 := by
  have h1 := re_add_mul_I_pos h
  have h2 := re_sub_mul_I_pos h
  have e : (fun t : ℝ => (t : ℂ) * Complex.cos (a * t)) = fun t : ℝ =>
      1 / 2 * ((t : ℂ) ^ 1 * cexp ((a * I) * t)) + 1 / 2 * ((t : ℂ) ^ 1 * cexp (-(a * I) * t)) := by
    funext t; rw [Complex.cos]; ring_nf
  rw [e, laplace_two_exp _ _ 1 (by simpa using h2) (by simpa using h1)]
  have hne1 : s + a * I ≠ 0 := fun e => by rw [e] at h1; simp at h1
  have hne2 : s - a * I ≠ 0 := fun e => by rw [e] at h2; simp at h2
  have e2 : s ^ 2 + a ^ 2 = (s - a * I) * (s + a * I) := by ring_nf; rw [I_sq]; ring
  rw [e2]
  simp only [sub_neg_eq_add, Nat.factorial_one, Nat.cast_one]
  generalize hp : s + a * I = p at *
  generalize hq : s - a * I = q at *
  have hs : s = (p + q) / 2 := by rw [← hp, ← hq]; ring
  have ha : a = -I * (p - q) / 2 := by rw [← hp, ← hq]; ring_nf; rw [I_sq]; ring
  subst hs ha
  field_simp
  ring_nf
  rw [I_sq]
  ring

end Azurite.DLMF
