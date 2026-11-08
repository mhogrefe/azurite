/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section36
import Azurite.DLMF.Chapter4.Section40

/-!
# DLMF §4.40(iii) Definite Integrals (hyperbolic functions)

DLMF calls `a` a "real or complex constant". Each integral is stated with its integrability on
the interval and its value.

* 4.40.7 (`a ≠ 0`, real `a`): `dlmf_4_40_7`. `e^{−x}/sinh x = 2∑_{k≥1} e^{−2kx}`
  (`hasSum_exp_neg_div_sinh`), integrated term by term (`integral_tsum_of_summable_integral_norm`;
  `|sin(ax)| ≤ |a|x` gives `∫|·| ≤ 2|a|/(2k)²`) with `∫₀^∞ sin(ax)e^{−cx} dx = a/(c² + a²)`
  (`integral_sin_mul_exp_neg`). The sum `2∑ a/(4k² + a²)` is evaluated by 4.36.3 at `z = ½πa`
  (`hasSum_coth_series`). `coth = 1/tanh`.
* 4.40.8 (`−π < a < π`, real `a`): `dlmf_4_40_8`. `1/sinh(πx) = 2∑_{k≥0} e^{−(2k+1)πx}`
  (`hasSum_one_div_sinh_pi`), `∫₀^∞ sinh(ax)e^{−cx} dx = a/(c² − a²)` (`integral_sinh_mul_exp_neg`;
  `|sinh y| ≤ |y| cosh y`, `abs_sinh_le`), and `2∑ a/((2k + 1)²π² − a²) = ½ tan(½a)`, the odd part
  of 4.22.3 at `a` minus its even part (4.22.3 at `½a`) (`hasSum_cot_all`, `hasSum_odd_tan_half`,
  `half_cot_sub_cot`).
* 4.40.9 (complex `a`, `−1 < ℜa < 1`): `dlmf_4_40_9`. The substitution `s = 1/(1 + e^{−x})`
  (`logistic`, a bijection `ℝ → (0, 1)` with `ds/dx = 1/(4 cosh²(½x))`) turns the integral into
  `4 B(1 + a, 1 − a) = 4Γ(1 + a)Γ(1 − a)` (`betaIntegrand_logistic`,
  `integral_image_eq_integral_abs_deriv_smul`, `Complex.Gamma_mul_Gamma_eq_betaIntegral`), and
  `Γ(1 + a)Γ(1 − a) = πa/sin(πa)`. At `a = 0` the right-hand side `4πa/sin(πa)` is `0/0`; the
  integral is its removable value `4`.
* 4.40.10 (`a, b > 0`): `dlmf_4_40_10`. The integrand is `∫_b^a sech²(tx) dt`
  (`tanh_sub_div_eq_integral`), and `∫₀^∞ sech²(tx) dx = 1/t` (`sech_sq_integral`), so Fubini
  (`integral_integral_swap`) gives `∫_b^a dt/t = ln(a/b)`.
-/

open Set Filter Topology MeasureTheory
open scoped Real Interval

namespace Azurite.DLMF

/-! ### Tools -/

theorem integral_mul_exp_neg_Ioi {c : ℝ} (hc : 0 < c) :
    ∫ x in Ioi 0, x * Real.exp (-(c * x)) = 1 / c ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) two_pos hc
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.Gamma_two, mul_one] at h
  calc ∫ x in Ioi 0, x * Real.exp (-(c * x))
      = ∫ t in Ioi 0, t ^ (1 : ℝ) * Real.exp (-(c * t)) :=
        setIntegral_congr_fun measurableSet_Ioi fun x _ => by simp only [Real.rpow_one]
    _ = 1 / c ^ 2 := by rw [h, Real.rpow_two, div_pow, one_pow]

theorem integrableOn_mul_exp_neg_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-(c * x))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := c) (by norm_num)
    one_pos hc
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, neg_mul]

theorem integrableOn_exp_neg_mul_Ioi_zero {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => Real.exp (-(c * x))) (Ioi 0) := by
  have h := exp_neg_integrableOn_Ioi 0 hc
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [neg_mul]

/-- `∫₀^∞ sin(ax) e^{−cx} dx = a/(c² + a²)`, `c > 0`. -/
theorem integral_sin_mul_exp_neg {a c : ℝ} (hc : 0 < c) :
    ∫ x in Ioi 0, Real.sin (a * x) * Real.exp (-(c * x)) = a / (c ^ 2 + a ^ 2) := by
  set w : ℂ := -c + a * Complex.I with hw
  have hwre : w.re < 0 := by simp [w]; linarith
  have hi := integrableOn_exp_mul_complex_Ioi hwre 0
  have h := integral_exp_mul_complex_Ioi hwre 0
  have him := integral_im hi
  have e : ∀ x : ℝ, (Complex.exp (w * x)).im = Real.sin (a * x) * Real.exp (-(c * x)) :=
    fun x => by
      rw [Complex.exp_im]
      simp only [w, Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.mul_im, Complex.I_im, Complex.add_im, Complex.neg_im,
        Complex.ofReal_im]
      ring_nf
  simp only [RCLike.im_to_complex, e] at him
  rw [him, h, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hn : Complex.normSq w = c ^ 2 + a ^ 2 := by
    simp [w, Complex.normSq_apply]; ring
  rw [neg_div, Complex.neg_im, Complex.div_im, hn]
  simp [w]

/-- For `x > 0`: `e^{−x}/sinh x = 2 ∑_{k≥0} e^{−2(k+1)x}`. -/
theorem hasSum_exp_neg_div_sinh {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => 2 * Real.exp (-((2 * ((k : ℝ) + 1)) * x)))
      (Real.exp (-x) / Real.sinh x) := by
  set q := Real.exp (-(2 * x)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (2 * q)
  have hterm : ∀ k : ℕ, Real.exp (-((2 * ((k : ℝ) + 1)) * x)) = q * q ^ k := fun k => by
    rw [hq, ← pow_succ', ← Real.exp_nat_mul]; push_cast; ring_nf
  have hE := Real.exp_pos x
  have hs : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
  have hval : 2 * q * (1 - q)⁻¹ = Real.exp (-x) / Real.sinh x := by
    set E := Real.exp x
    set e := Real.exp (-x)
    have h1 : q = e * e := by rw [hq, ← Real.exp_add]; ring_nf
    have h2 : E * e = 1 := by rw [← Real.exp_add]; simp
    have he : e ≠ 0 := (Real.exp_pos _).ne'
    have hEe : E - e ≠ 0 := fun h0 => hs (by rw [Real.sinh_eq, h0, zero_div])
    rw [Real.sinh_eq, h1, show 1 - e * e = e * (E - e) by linear_combination -h2]
    field_simp
    exact (div_self hEe).symm
  rw [← hval]
  refine h.congr_fun fun k => ?_
  rw [hterm]; ring

/-- `2 ∑_{k≥1} a/(4k² + a²) = ½π coth(½πa) − 1/a` (4.36.3 at `z = ½πa`), `a ≠ 0`. -/
theorem hasSum_coth_series {a : ℝ} (ha : a ≠ 0) :
    HasSum (fun k : ℕ => 2 * (a / ((2 * ((k : ℝ) + 1)) ^ 2 + a ^ 2)))
      (1 / 2 * π * (1 / Real.tanh (1 / 2 * π * a)) - 1 / a) := by
  set z : ℂ := ((1 / 2 * π * a : ℝ) : ℂ) with hzdef
  have hz0 : (1 / 2 * π * a : ℝ) ≠ 0 := by positivity
  have hz : ∀ n : ℤ, z ≠ n * π * Complex.I := fun n h => by
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [z] at him hre
    exact ha hre
  obtain ⟨h, -⟩ := dlmf_4_36_3 hz
  have h2 := h.mul_left ((a * π ^ 2 / 2 : ℝ) : ℂ)
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hv : ((a * π ^ 2 / 2 : ℝ) : ℂ) * ((cothC z - 1 / z) / (2 * z)) =
      ((1 / 2 * π * (1 / Real.tanh (1 / 2 * π * a)) - 1 / a : ℝ) : ℂ) := by
    rw [cothC, hzdef, ← Complex.ofReal_tanh]
    push_cast
    field_simp
  rw [hv] at h2
  refine Complex.hasSum_ofReal.mp (h2.congr_fun fun n => ?_)
  rw [hzdef]
  push_cast
  have hd : ((2 * ((n : ℂ) + 1)) ^ 2 + (a : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < (2 * ((n : ℝ) + 1)) ^ 2 + a ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hd' : ((1 / 2 * π * a : ℂ)) ^ 2 + ((n : ℂ) + 1) ^ 2 * π ^ 2 ≠ 0 := by
    rw [show ((1 / 2 * π * a : ℂ)) ^ 2 + ((n : ℂ) + 1) ^ 2 * π ^ 2 =
      π ^ 2 / 4 * ((2 * ((n : ℂ) + 1)) ^ 2 + (a : ℂ) ^ 2) by ring]
    exact mul_ne_zero (div_ne_zero (pow_ne_zero 2 hπ) (by norm_num)) hd
  field_simp
  ring

/-- **DLMF 4.40.7**: `∫₀^∞ e^{−x} sin(ax)/sinh x dx = ½π coth(½πa) − 1/a`, `a ≠ 0` (real `a`;
`coth = 1/tanh`). -/
theorem dlmf_4_40_7 {a : ℝ} (ha : a ≠ 0) :
    IntegrableOn (fun x => Real.exp (-x) * Real.sin (a * x) / Real.sinh x) (Ioi 0) ∧
      ∫ x in Ioi 0, Real.exp (-x) * Real.sin (a * x) / Real.sinh x =
        1 / 2 * π * (1 / Real.tanh (1 / 2 * π * a)) - 1 / a := by
  set f := fun x : ℝ => Real.exp (-x) * Real.sin (a * x) / Real.sinh x with hf
  set c : ℕ → ℝ := fun k => 2 * ((k : ℝ) + 1) with hc
  have hc0 : ∀ k, 0 < c k := fun k => by simp only [hc]; positivity
  set F : ℕ → ℝ → ℝ := fun k x => 2 * (Real.sin (a * x) * Real.exp (-(c k * x))) with hF
  have hcontF : ∀ k, Continuous (F k) := fun k => by simp only [hF]; fun_prop
  have hsinh : ∀ x : ℝ, 0 < x → 0 < Real.sinh x := fun x hx => Real.sinh_pos_iff.mpr hx
  -- pointwise expansion
  have hsum : ∀ x ∈ Ioi (0 : ℝ), HasSum (fun k => F k x) (f x) := fun x hx => by
    have h := (hasSum_exp_neg_div_sinh hx).mul_left (Real.sin (a * x))
    convert h using 1
    · funext k; simp only [hF, hc]; ring
    · simp only [hf]; ring
  -- integrability of the terms
  have hFi : ∀ k, Integrable (F k) (volume.restrict (Ioi 0)) := fun k => by
    refine ((integrableOn_exp_neg_mul_Ioi_zero (hc0 k)).const_mul 2).mono'
      (hcontF k).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    simp only [hF, norm_mul, Real.norm_eq_abs, abs_two, abs_of_pos (Real.exp_pos _)]
    have := Real.abs_sin_le_one (a * x)
    nlinarith [Real.exp_pos (-(c k * x))]
  -- the norms of the term integrals are summable
  have hbound : ∀ k, ∫ x in Ioi 0, ‖F k x‖ ≤ 2 * |a| * (1 / c k ^ 2) := fun k => by
    rw [← integral_mul_exp_neg_Ioi (hc0 k), ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
      ((integrableOn_mul_exp_neg_Ioi (hc0 k)).const_mul _) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx' : (0 : ℝ) < x := hx
    simp only [hF, norm_mul, Real.norm_eq_abs, abs_two, abs_of_pos (Real.exp_pos _)]
    have h1 : |Real.sin (a * x)| ≤ |a| * x := by
      calc |Real.sin (a * x)| ≤ |a * x| := Real.abs_sin_le_abs
        _ = |a| * x := by rw [abs_mul, abs_of_pos hx']
    nlinarith [Real.exp_pos (-(c k * x))]
  have hsummable : Summable fun k => ∫ x in Ioi 0, ‖F k x‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _) hbound ?_
    have h : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 :=
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two) |>.congr
        fun k => by push_cast; ring
    refine (h.mul_left (2 * |a| / 4)).congr fun k => ?_
    simp only [hc]; field_simp; ring
  -- integrability of `f`
  have hfi : IntegrableOn f (Ioi 0) := by
    refine ((integrableOn_exp_neg_mul_Ioi_zero one_pos).const_mul |a|).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
      have := (hsinh x hx).ne'
      exact (by fun_prop : Continuous fun x : ℝ => Real.exp (-x) * Real.sin (a * x)).continuousAt
        |>.div Real.continuous_sinh.continuousAt this |>.continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
      have hx' : (0 : ℝ) < x := hx
      have hs := hsinh x hx'
      have h1 : |Real.sin (a * x)| ≤ |a| * x := by
        calc |Real.sin (a * x)| ≤ |a * x| := Real.abs_sin_le_abs
          _ = |a| * x := by rw [abs_mul, abs_of_pos hx']
      have h2 : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx'.le
      simp only [hf, norm_div, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_pos hs, one_mul]
      rw [div_le_iff₀ hs]
      have := Real.exp_pos (-x)
      calc Real.exp (-x) * |Real.sin (a * x)| ≤ Real.exp (-x) * (|a| * x) :=
            mul_le_mul_of_nonneg_left h1 this.le
        _ ≤ Real.exp (-x) * (|a| * Real.sinh x) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (abs_nonneg a)) this.le
        _ = |a| * Real.exp (-x) * Real.sinh x := by ring
  refine ⟨hfi, ?_⟩
  have hint := integral_tsum_of_summable_integral_norm hFi hsummable
  rw [show ∫ x in Ioi 0, f x = ∫ x in Ioi 0, ∑' k, F k x from
    setIntegral_congr_fun measurableSet_Ioi fun x hx => (hsum x hx).tsum_eq.symm, ← hint]
  rw [← (hasSum_coth_series ha).tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [hF]
  rw [integral_const_mul, integral_sin_mul_exp_neg (hc0 k)]

/-! ### 4.40.8 -/

/-- `∫₀^∞ sinh(ax) e^{−cx} dx = a/(c² − a²)`, `c > |a|`. -/
theorem integral_sinh_mul_exp_neg {a c : ℝ} (hc : |a| < c) :
    ∫ x in Ioi 0, Real.sinh (a * x) * Real.exp (-(c * x)) = a / (c ^ 2 - a ^ 2) := by
  have h1 : a - c < 0 := by linarith [le_abs_self a]
  have h2 : -a - c < 0 := by linarith [neg_abs_le a]
  have e : ∀ x : ℝ, Real.sinh (a * x) * Real.exp (-(c * x)) =
      (Real.exp ((a - c) * x) - Real.exp ((-a - c) * x)) / 2 := fun x => by
    rw [Real.sinh_eq, show (a - c) * x = a * x + -(c * x) by ring,
      show (-a - c) * x = -(a * x) + -(c * x) by ring, Real.exp_add, Real.exp_add]; ring
  simp only [e]
  rw [integral_div, integral_sub (integrableOn_exp_mul_Ioi h1 0) (integrableOn_exp_mul_Ioi h2 0),
    integral_exp_mul_Ioi h1, integral_exp_mul_Ioi h2]
  have h3 : c - a ≠ 0 := by linarith
  have h4 : c + a ≠ 0 := by linarith [neg_abs_le a]
  have h5 : c ^ 2 - a ^ 2 ≠ 0 := by
    rw [show c ^ 2 - a ^ 2 = (c - a) * (c + a) by ring]; exact mul_ne_zero h3 h4
  have h6 := h1.ne
  have h7 := h2.ne
  simp only [mul_zero, Real.exp_zero]
  field_simp
  ring

/-- For `x > 0`: `1/sinh(πx) = 2 ∑_{k≥0} e^{−(2k+1)πx}`. -/
theorem hasSum_one_div_sinh_pi {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => 2 * Real.exp (-(((2 * k + 1) * π) * x))) (1 / Real.sinh (π * x)) := by
  have h := (hasSum_exp_neg_div_sinh (mul_pos Real.pi_pos hx)).mul_left (Real.exp (π * x))
  have hval : Real.exp (π * x) * (Real.exp (-(π * x)) / Real.sinh (π * x)) =
      1 / Real.sinh (π * x) := by
    rw [← mul_div_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hval] at h
  refine h.congr_fun fun k => ?_
  rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

theorem abs_sinh_le (y : ℝ) : |Real.sinh y| ≤ |y| * Real.cosh y := by
  rw [Real.abs_sinh]
  rcases eq_or_lt_of_le (abs_nonneg y) with h | h
  · rw [← h, Real.sinh_zero]; positivity
  · have ht := tanh_lt_self h
    rw [Real.tanh_eq_sinh_div_cosh, div_lt_iff₀ (Real.cosh_pos _), Real.cosh_abs] at ht
    exact ht.le

theorem cosh_le_exp_abs (y : ℝ) : Real.cosh y ≤ Real.exp |y| := by
  rw [Real.cosh_eq]
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h]
    have : Real.exp (-y) ≤ Real.exp y := Real.exp_le_exp.mpr (by linarith)
    linarith
  · rw [abs_of_nonpos h]
    have : Real.exp y ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
    linarith

/-- `g_b(n) = 2b/(n²π² − b²)`; `∑_{n≥0} g_b(n) = −1/b − cot b` (4.22.3), `0 < |b| < π`. -/
theorem hasSum_cot_all {b : ℝ} (hb0 : b ≠ 0) (hb : |b| < π) :
    HasSum (fun n : ℕ => 2 * b / ((n : ℝ) ^ 2 * π ^ 2 - b ^ 2)) (-1 / b - Real.cot b) := by
  have hz : ∀ n : ℤ, (b : ℂ) ≠ n * π := fun n h => by
    have h' : b = n * π := by exact_mod_cast h
    rcases lt_trichotomy n 0 with hn | hn | hn
    · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr hn
      rw [h', abs_lt] at hb; nlinarith [Real.pi_pos]
    · rw [hn] at h'; simp at h'; exact hb0 h'
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [h', abs_lt] at hb; nlinarith [Real.pi_pos]
  obtain ⟨h, -⟩ := dlmf_4_22_3 hz
  have h2 := h.mul_left (-2 * (b : ℂ))
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb0
  have hv : -2 * (b : ℂ) * ((Complex.cot b - 1 / b) / (2 * b)) =
      ((1 / b - Real.cot b : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cot]; push_cast; field_simp; ring
  rw [hv] at h2
  have h3 : HasSum (fun n : ℕ => 2 * b / (((n + 1 : ℕ) : ℝ) ^ 2 * π ^ 2 - b ^ 2))
      (1 / b - Real.cot b) := by
    refine Complex.hasSum_ofReal.mp (h2.congr_fun fun n => ?_)
    have hd : ((n : ℂ) + 1) ^ 2 * π ^ 2 - (b : ℂ) ^ 2 ≠ 0 := by
      intro h0
      have : (((n : ℝ) + 1) * π) ^ 2 = b ^ 2 := by
        have : ((((n : ℝ) + 1) * π) ^ 2 : ℂ) = (b ^ 2 : ℂ) := by
          push_cast; linear_combination h0
        exact_mod_cast this
      have h5 : |b| = ((n : ℝ) + 1) * π := by
        rw [← Real.sqrt_sq_eq_abs, ← this, Real.sqrt_sq (by positivity)]
      rw [h5] at hb; nlinarith [Real.pi_pos, (n.cast_nonneg : (0 : ℝ) ≤ n)]
    have hd' : (b : ℂ) ^ 2 - ((n : ℂ) + 1) ^ 2 * π ^ 2 ≠ 0 := fun h0 =>
      hd (by linear_combination -h0)
    push_cast
    field_simp
    ring
  refine (hasSum_nat_add_iff' 1).mp ?_
  convert h3 using 1
  simp only [Finset.sum_range_one, Nat.cast_zero]; field_simp; ring

theorem sq_mul_pi_sq_sub_ne {b : ℝ} (hb0 : b ≠ 0) (hb : |b| < π) (n : ℕ) :
    (n : ℝ) ^ 2 * π ^ 2 - b ^ 2 ≠ 0 := by
  intro h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at h; exact hb0 h
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : b ^ 2 < π ^ 2 := by
      rw [← sq_abs]; exact pow_lt_pow_left₀ hb (abs_nonneg b) two_ne_zero
    have h3 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h3 (sq_nonneg π)]

/-- `½ cot(½a) − cot a = ½ tan(½a)`. -/
theorem half_cot_sub_cot {a : ℝ} (hs : Real.sin (1 / 2 * a) ≠ 0) (hc : Real.cos (1 / 2 * a) ≠ 0) :
    1 / 2 * Real.cot (1 / 2 * a) - Real.cot a = 1 / 2 * Real.tan (1 / 2 * a) := by
  have ha : a = 2 * (1 / 2 * a) := by ring
  set t := 1 / 2 * a
  rw [ha, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos,
    Real.sin_two_mul, Real.cos_two_mul]
  field_simp
  linear_combination (-1 : ℝ) * Real.sin_sq_add_cos_sq t

/-- `2 ∑_{k≥0} a/((2k + 1)²π² − a²) = ½ tan(½a)`, `0 < |a| < π` (the odd part of 4.22.3). -/
theorem hasSum_odd_tan_half {a : ℝ} (ha0 : a ≠ 0) (ha : |a| < π) :
    HasSum (fun k : ℕ => 2 * (a / (((2 * k + 1) * π) ^ 2 - a ^ 2)))
      (1 / 2 * Real.tan (1 / 2 * a)) := by
  set g := fun n : ℕ => 2 * a / ((n : ℝ) ^ 2 * π ^ 2 - a ^ 2) with hg
  have hall := hasSum_cot_all ha0 ha
  have hb0 : a / 2 ≠ 0 := div_ne_zero ha0 two_ne_zero
  have hb : |a / 2| < π := by rw [abs_div, abs_two]; linarith [abs_nonneg a]
  have hhalf := (hasSum_cot_all hb0 hb).mul_left (1 / 2)
  have heven : HasSum (fun k => g (2 * k)) (1 / 2 * (-1 / (a / 2) - Real.cot (a / 2))) := by
    refine hhalf.congr_fun fun k => ?_
    have h1 := sq_mul_pi_sq_sub_ne ha0 ha (2 * k)
    have h2 := sq_mul_pi_sq_sub_ne hb0 hb k
    simp only [hg]
    push_cast at h1 ⊢
    field_simp
  have hodd : Summable fun k => g (2 * k + 1) :=
    hall.summable.comp_injective fun i j h => by simpa using h
  have hsum := heven.even_add_odd hodd.hasSum
  have hO : ∑' k, g (2 * k + 1) =
      (-1 / a - Real.cot a) - 1 / 2 * (-1 / (a / 2) - Real.cot (a / 2)) := by
    rw [hall.unique hsum]; ring
  have hs : Real.sin (1 / 2 * a) ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
    have : |1 / 2 * a| < π := by rw [abs_mul]; norm_num; linarith [abs_nonneg a]
    rw [← hn, abs_mul, abs_of_pos Real.pi_pos] at this
    have hn0 : n = 0 := by
      have : |(n : ℝ)| < 1 := by nlinarith [Real.pi_pos]
      rw [abs_lt] at this
      have h1 : (-1 : ℤ) < n := by exact_mod_cast this.1
      have h2 : n < (1 : ℤ) := by exact_mod_cast this.2
      omega
    rw [hn0] at hn; simp at hn; exact ha0 (by linarith)
  have hc : Real.cos (1 / 2 * a) ≠ 0 := by
    refine (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩).ne' <;>
      linarith [abs_lt.mp ha, Real.pi_pos]
  have hv : (-1 / a - Real.cot a) - 1 / 2 * (-1 / (a / 2) - Real.cot (a / 2)) =
      1 / 2 * Real.tan (1 / 2 * a) := by
    rw [← half_cot_sub_cot hs hc, show a / 2 = 1 / 2 * a by ring]
    field_simp
    ring
  rw [← hv, ← hO]
  refine hodd.hasSum.congr_fun fun k => ?_
  simp only [hg]
  push_cast
  ring

theorem sinh_le_exp_mul_sinh {b x : ℝ} (hb : b ≤ π) (hx : 0 ≤ x) :
    Real.sinh (b * x) ≤ Real.exp (-((π - b) * x)) * Real.sinh (π * x) := by
  rw [Real.sinh_eq, Real.sinh_eq, mul_div_assoc', mul_sub, ← Real.exp_add, ← Real.exp_add]
  have e1 : -((π - b) * x) + π * x = b * x := by ring
  have e2 : Real.exp (-((π - b) * x) + -(π * x)) ≤ Real.exp (-(b * x)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [e1]
  linarith

theorem abs_sinh_le_exp_abs (y : ℝ) : |Real.sinh y| ≤ Real.exp |y| := by
  rw [Real.abs_sinh]
  exact (Real.sinh_lt_cosh |y|).le.trans ((cosh_le_exp_abs |y|).trans_eq (by rw [abs_abs]))

/-- **DLMF 4.40.8**: `∫₀^∞ sinh(ax)/sinh(πx) dx = ½ tan(½a)`, `−π < a < π` (real `a`). -/
theorem dlmf_4_40_8 {a : ℝ} (ha : |a| < π) :
    IntegrableOn (fun x => Real.sinh (a * x) / Real.sinh (π * x)) (Ioi 0) ∧
      ∫ x in Ioi 0, Real.sinh (a * x) / Real.sinh (π * x) = 1 / 2 * Real.tan (1 / 2 * a) := by
  set f := fun x : ℝ => Real.sinh (a * x) / Real.sinh (π * x) with hf
  have hsinh : ∀ x : ℝ, 0 < x → 0 < Real.sinh (π * x) := fun x hx =>
    Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hx)
  have hδ : 0 < π - |a| := by linarith
  have hfi : IntegrableOn f (Ioi 0) := by
    refine (integrableOn_exp_neg_mul_Ioi_zero hδ).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
      exact ((by fun_prop : Continuous fun x : ℝ => Real.sinh (a * x)).continuousAt.div
        (by fun_prop : Continuous fun x : ℝ => Real.sinh (π * x)).continuousAt
        (hsinh x hx).ne').continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
      have hx' : (0 : ℝ) < x := hx
      have hs := hsinh x hx'
      simp only [hf, norm_div, Real.norm_eq_abs, abs_of_pos hs]
      rw [div_le_iff₀ hs, Real.abs_sinh, abs_mul, abs_of_pos hx']
      exact sinh_le_exp_mul_sinh (by linarith) hx'.le
  refine ⟨hfi, ?_⟩
  rcases eq_or_ne a 0 with rfl | ha0
  · simp [hf]
  set c : ℕ → ℝ := fun k => (2 * k + 1) * π with hc
  have hc1 : ∀ k : ℕ, (π - |a|) * ((k : ℝ) + 1) ≤ c k - |a| := fun k => by
    simp only [hc]; nlinarith [Real.pi_pos, abs_nonneg a, (k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hc0 : ∀ k, 0 < c k - |a| := fun k =>
    lt_of_lt_of_le (mul_pos hδ (by positivity)) (hc1 k)
  set F : ℕ → ℝ → ℝ := fun k x => 2 * (Real.sinh (a * x) * Real.exp (-(c k * x))) with hF
  have hcontF : ∀ k, Continuous (F k) := fun k => by simp only [hF]; fun_prop
  have hexp : ∀ (k : ℕ) (x : ℝ), 0 ≤ x →
      Real.exp |a * x| * Real.exp (-(c k * x)) = Real.exp (-((c k - |a|) * x)) := fun k x hx => by
    rw [← Real.exp_add, abs_mul, abs_of_nonneg hx]; ring_nf
  have hsum : ∀ x ∈ Ioi (0 : ℝ), HasSum (fun k => F k x) (f x) := fun x hx => by
    have h := (hasSum_one_div_sinh_pi hx).mul_left (Real.sinh (a * x))
    convert h using 1
    · funext k; simp only [hF, hc]; ring
    · simp only [hf]; ring
  have hFi : ∀ k, Integrable (F k) (volume.restrict (Ioi 0)) := fun k => by
    refine ((integrableOn_exp_neg_mul_Ioi_zero (hc0 k)).const_mul 2).mono'
      (hcontF k).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx' : (0 : ℝ) < x := hx
    simp only [hF, norm_mul, Real.norm_eq_abs, abs_two, abs_of_pos (Real.exp_pos _)]
    rw [← hexp k x hx'.le]
    nlinarith [abs_sinh_le_exp_abs (a * x), Real.exp_pos (-(c k * x))]
  have hbound : ∀ k, ∫ x in Ioi 0, ‖F k x‖ ≤ 2 * |a| * (1 / (c k - |a|) ^ 2) := fun k => by
    rw [← integral_mul_exp_neg_Ioi (hc0 k), ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
      ((integrableOn_mul_exp_neg_Ioi (hc0 k)).const_mul _) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx' : (0 : ℝ) < x := hx
    simp only [hF, norm_mul, Real.norm_eq_abs, abs_two, abs_of_pos (Real.exp_pos _)]
    have h1 : |Real.sinh (a * x)| ≤ |a| * x * Real.exp |a * x| := by
      calc |Real.sinh (a * x)| ≤ |a * x| * Real.cosh (a * x) := abs_sinh_le _
        _ ≤ |a * x| * Real.exp |a * x| :=
          mul_le_mul_of_nonneg_left (cosh_le_exp_abs _) (abs_nonneg _)
        _ = |a| * x * Real.exp |a * x| := by rw [abs_mul, abs_of_pos hx']
    have h2 := hexp k x hx'.le
    calc 2 * (|Real.sinh (a * x)| * Real.exp (-(c k * x)))
        ≤ 2 * (|a| * x * Real.exp |a * x| * Real.exp (-(c k * x))) := by
          gcongr
      _ = 2 * |a| * (x * Real.exp (-((c k - |a|) * x))) := by rw [← h2]; ring
  have hsummable : Summable fun k => ∫ x in Ioi 0, ‖F k x‖ := by
    refine Summable.of_nonneg_of_le (f := fun k : ℕ => 2 * |a| / (π - |a|) ^ 2 *
      (1 / ((k : ℝ) + 1) ^ 2)) (fun k => integral_nonneg fun x => norm_nonneg _)
      (fun k => (hbound k).trans ?_) ?_
    · rw [show 2 * |a| / (π - |a|) ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) =
        2 * |a| * (1 / ((π - |a|) * ((k : ℝ) + 1)) ^ 2) by field_simp]
      exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_left₀ (by positivity) (hc1 k) 2)) (by positivity)
    · have h : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 :=
        (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two) |>.congr
          fun k => by push_cast; ring
      exact h.mul_left (2 * |a| / (π - |a|) ^ 2)
  have hint := integral_tsum_of_summable_integral_norm hFi hsummable
  rw [show ∫ x in Ioi 0, f x = ∫ x in Ioi 0, ∑' k, F k x from
    setIntegral_congr_fun measurableSet_Ioi fun x hx => (hsum x hx).tsum_eq.symm, ← hint]
  rw [← (hasSum_odd_tan_half ha0 ha).tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [hF]
  rw [integral_const_mul, integral_sinh_mul_exp_neg (by linarith [hc0 k])]

/-! ### 4.40.9 -/

/-- The logistic map `x ↦ 1/(1 + e^{−x})`, a bijection `ℝ → (0, 1)`. -/
noncomputable def logistic (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

theorem logistic_mem (x : ℝ) : logistic x ∈ Ioo (0 : ℝ) 1 := by
  have h := Real.exp_pos (-x)
  refine ⟨by unfold logistic; positivity, ?_⟩
  unfold logistic; rw [div_lt_one (by positivity)]; linarith

theorem one_sub_logistic (x : ℝ) :
    1 - logistic x = Real.exp (-x) * logistic x := by
  have h := Real.exp_pos (-x)
  unfold logistic; field_simp; ring

theorem image_logistic : logistic '' univ = Ioo (0 : ℝ) 1 := by
  ext s
  constructor
  · rintro ⟨x, -, rfl⟩; exact logistic_mem x
  · rintro ⟨h0, h1⟩
    refine ⟨Real.log (s / (1 - s)), trivial, ?_⟩
    have h2 : 0 < 1 - s := by linarith
    unfold logistic
    rw [Real.exp_neg, Real.exp_log (div_pos h0 h2)]
    field_simp
    ring

theorem hasDerivAt_logistic (x : ℝ) :
    HasDerivAt logistic (Real.exp (-x) / (1 + Real.exp (-x)) ^ 2) x := by
  have h := Real.exp_pos (-x)
  have hd := ((((hasDerivAt_id x).neg).exp).const_add 1).inv (by positivity)
  unfold logistic
  simp only [one_div]
  convert hd using 1
  · funext y; simp
  · simp

theorem injective_logistic : Function.Injective logistic := fun x y h => by
  unfold logistic at h
  have hx := Real.exp_pos (-x)
  have hy := Real.exp_pos (-y)
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  have : Real.exp (-x) = Real.exp (-y) := by linarith
  simpa using Real.exp_injective this

theorem logistic_deriv_eq (x : ℝ) :
    Real.exp (-x) / (1 + Real.exp (-x)) ^ 2 = 1 / (4 * Real.cosh (1 / 2 * x) ^ 2) := by
  have h1 : Real.exp (-x) = Real.exp (-(1 / 2 * x)) ^ 2 := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have h2 : Real.exp (1 / 2 * x) * Real.exp (-(1 / 2 * x)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [Real.cosh_eq, h1]
  set P := Real.exp (1 / 2 * x)
  set Q := Real.exp (-(1 / 2 * x))
  have h3 : 0 < P := Real.exp_pos _
  have h4 : 0 < Q := Real.exp_pos _
  field_simp
  linear_combination (4 * (P * Q + 1) + 8 * Q ^ 2) * h2

theorem betaIntegrand_logistic (a : ℂ) (x : ℝ) :
    ((logistic x : ℝ) : ℂ) ^ ((1 + a) - 1) * (1 - ((logistic x : ℝ) : ℂ)) ^ ((1 - a) - 1) =
      Complex.exp (a * x) := by
  obtain ⟨h0, h1⟩ := logistic_mem x
  have h2 : 0 < 1 - logistic x := by linarith
  have hL : ((logistic x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0.ne'
  have hL' : ((1 - logistic x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h2.ne'
  rw [show (1 + a) - 1 = a by ring, show (1 - a) - 1 = -a by ring,
    show (1 - ((logistic x : ℝ) : ℂ)) = ((1 - logistic x : ℝ) : ℂ) by push_cast; ring,
    Complex.cpow_def_of_ne_zero hL, Complex.cpow_def_of_ne_zero hL', ← Complex.exp_add,
    ← Complex.ofReal_log h0.le, ← Complex.ofReal_log h2.le, one_sub_logistic,
    Real.log_mul (Real.exp_pos _).ne' h0.ne', Real.log_exp]
  congr 1
  push_cast
  ring

/-- **DLMF 4.40.9**: `∫_{−∞}^{∞} e^{ax}/cosh²(½x) dx = 4πa/sin(πa)`, `−1 < a < 1` (here complex
`a`, `−1 < ℜa < 1`). At `a = 0` the right-hand side is its removable value `4`. Proof: the
substitution `s = 1/(1 + e^{−x})` turns the integral into `4 B(1 + a, 1 − a)`. -/
theorem dlmf_4_40_9 {a : ℂ} (ha1 : -1 < a.re) (ha2 : a.re < 1) :
    Integrable (fun x : ℝ => Complex.exp (a * x) / Complex.cosh (1 / 2 * x) ^ 2) ∧
      (a ≠ 0 → ∫ x : ℝ, Complex.exp (a * x) / Complex.cosh (1 / 2 * x) ^ 2 =
        4 * π * a / Complex.sin (π * a)) ∧
      (a = 0 → ∫ x : ℝ, Complex.exp (a * x) / Complex.cosh (1 / 2 * x) ^ 2 = 4) := by
  set g : ℝ → ℂ := fun s => (s : ℂ) ^ ((1 + a) - 1) * (1 - (s : ℂ)) ^ ((1 - a) - 1) with hg
  set L' : ℝ → ℝ := fun x => Real.exp (-x) / (1 + Real.exp (-x)) ^ 2 with hL'
  have hpos : ∀ x, 0 < L' x := fun x => by simp only [hL']; positivity
  have hder : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt logistic (L' x) univ x :=
    fun x _ => (hasDerivAt_logistic x).hasDerivWithinAt
  have hinj : InjOn logistic univ := injective_logistic.injOn
  have hfun : (fun x : ℝ => Complex.exp (a * x) / Complex.cosh (1 / 2 * x) ^ 2) =
      fun x => 4 * (|L' x| • g (logistic x)) := by
    funext x
    rw [abs_of_pos (hpos x), Complex.real_smul, hg]
    simp only
    rw [betaIntegrand_logistic]
    simp only [hL']
    rw [logistic_deriv_eq,
      show Complex.cosh (1 / 2 * x) = ((Real.cosh (1 / 2 * x) : ℝ) : ℂ) by push_cast; ring_nf]
    have := Real.cosh_pos (1 / 2 * x)
    push_cast
    field_simp
  have hre1 : 0 < (1 + a).re := by simp; linarith
  have hre2 : 0 < (1 - a).re := by simp; linarith
  have hgi : IntegrableOn g (Ioo 0 1) :=
    (Complex.betaIntegral_convergent hre1 hre2).1.mono_set Ioo_subset_Ioc_self
  have hint : Integrable (fun x => |L' x| • g (logistic x)) := by
    have := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hder hinj
      g).mp (by rw [image_logistic]; exact hgi)
    rwa [integrableOn_univ] at this
  have hval : ∫ x : ℝ, |L' x| • g (logistic x) = Complex.betaIntegral (1 + a) (1 - a) := by
    have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hder hinj g
    rw [image_logistic, setIntegral_univ] at h
    rw [← h, Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral hre1 hre2
  rw [show 1 + a + (1 - a) = 2 by ring,
    show (2 : ℂ) = 1 + 1 by norm_num, Complex.Gamma_add_one 1 one_ne_zero, Complex.Gamma_one,
    mul_one, one_mul] at hB
  refine ⟨by rw [hfun]; exact hint.const_mul 4, fun ha0 => ?_, fun ha0 => ?_⟩
  · rw [hfun, integral_const_mul, hval, ← hB, add_comm, Complex.Gamma_add_one a ha0, mul_assoc,
      Complex.Gamma_mul_Gamma_one_sub]
    ring
  · rw [hfun, integral_const_mul, hval, ← hB, ha0]
    simp


/-! ### 4.40.10 -/

theorem tendsto_tanh_atTop_one : Tendsto Real.tanh atTop (𝓝 1) := by
  have e : ∀ x : ℝ, Real.tanh x = (1 - Real.exp (-x) ^ 2) / (1 + Real.exp (-x) ^ 2) := fun x => by
    have h1 := Real.exp_pos x
    have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    have h3 : 0 < Real.exp x + Real.exp (-x) := by positivity
    rw [div_div_div_cancel_right₀ (two_ne_zero' ℝ), div_eq_div_iff h3.ne' (by positivity)]
    linear_combination (2 * Real.exp (-x)) * h2
  have h := Real.tendsto_exp_neg_atTop_nhds_zero
  have h' := (tendsto_const_nhds (x := (1 : ℝ)).sub (h.pow 2)).div
    (tendsto_const_nhds (x := (1 : ℝ)).add (h.pow 2)) (by norm_num)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, add_zero,
    div_one] at h'
  exact h'.congr fun x => (e x).symm


theorem hasDerivAt_tanh_mul_div {t : ℝ} (ht : t ≠ 0) (x : ℝ) :
    HasDerivAt (fun x => Real.tanh (t * x) / t) (1 / Real.cosh (t * x) ^ 2) x := by
  have h := ((hasDerivAt_tanh' (t * x)).comp x ((hasDerivAt_id x).const_mul t)).div_const t
  convert h using 1
  · rfl
  · field_simp

/-- `∫₀^∞ sech²(tx) dx = 1/t`, `t > 0`. -/
theorem sech_sq_integral {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x => 1 / Real.cosh (t * x) ^ 2) (Ioi 0) ∧
      ∫ x in Ioi 0, 1 / Real.cosh (t * x) ^ 2 = 1 / t := by
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x => Real.tanh (t * x) / t)
      (1 / Real.cosh (t * x) ^ 2) x := fun x _ => hasDerivAt_tanh_mul_div ht.ne' x
  have hlim : Tendsto (fun x => Real.tanh (t * x) / t) atTop (𝓝 (1 / t)) :=
    (tendsto_tanh_atTop_one.comp (tendsto_id.const_mul_atTop ht)).div_const t
  have hi := integrableOn_Ioi_deriv_of_nonneg' hd (fun x _ => by positivity) hlim
  refine ⟨hi, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hi hlim]
  simp

/-- `(tanh(ax) − tanh(bx))/x = ∫_b^a sech²(tx) dt`, `x ≠ 0`. -/
theorem tanh_sub_div_eq_integral {a b x : ℝ} (hx : x ≠ 0) :
    (Real.tanh (a * x) - Real.tanh (b * x)) / x = ∫ t in b..a, 1 / Real.cosh (t * x) ^ 2 := by
  have hd : ∀ t ∈ [[b, a]], HasDerivAt (fun t => Real.tanh (x * t) / x)
      (1 / Real.cosh (t * x) ^ 2) t := fun t _ => by
    rw [mul_comm t x]; exact hasDerivAt_tanh_mul_div hx t
  have hint : IntervalIntegrable (fun t : ℝ => 1 / Real.cosh (t * x) ^ 2) volume b a :=
    (continuous_const.div (by fun_prop) fun t =>
      (pow_pos (Real.cosh_pos _) 2).ne').intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint, mul_comm x a, mul_comm x b]
  ring

theorem dlmf_4_40_10_le {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) :
    IntegrableOn (fun x => (Real.tanh (a * x) - Real.tanh (b * x)) / x) (Ioi 0) ∧
      ∫ x in Ioi 0, (Real.tanh (a * x) - Real.tanh (b * x)) / x = Real.log (a / b) := by
  set F : ℝ × ℝ → ℝ := fun p => 1 / Real.cosh (p.2 * p.1) ^ 2 with hF
  set μ := volume.restrict (Ioi (0 : ℝ))
  set ν := volume.restrict (Ioc b a)
  have hFc : Continuous F := by
    simp only [hF]
    exact continuous_const.div (by fun_prop) fun p => (pow_pos (Real.cosh_pos _) 2).ne'
  have hnorm : ∀ y ∈ Ioc b a, ∫ x, ‖F (x, y)‖ ∂μ = 1 / y := fun y hy => by
    have hy0 : 0 < y := hb.trans hy.1
    rw [← (sech_sq_integral hy0).2]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [hF, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  have hFi : Integrable F (μ.prod ν) := by
    refine (integrable_prod_iff' hFc.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun y hy => ?_)
      exact (sech_sq_integral (hb.trans hy.1)).1
    · have hc : ContinuousOn (fun y : ℝ => 1 / y) (Icc b a) :=
        continuousOn_const.div continuousOn_id fun y hy => (hb.trans_le hy.1).ne'
      refine ((hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self).congr_fun
        (fun y hy => (hnorm y hy).symm) measurableSet_Ioc
  have hswap := integral_integral_swap (f := fun x y => F (x, y)) hFi
  have hR : ∫ y, ∫ x, F (x, y) ∂μ ∂ν = Real.log (a / b) := by
    rw [← integral_one_div (by
      rw [uIcc_of_le hba]; exact fun h => absurd h.1 (not_le.mpr hb)),
      intervalIntegral.integral_of_le hba]
    refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
    rw [← hnorm y hy]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hF, Real.norm_eq_abs]
    exact (abs_of_pos (by positivity)).symm
  have hL : ∀ x ∈ Ioi (0 : ℝ), ∫ y, F (x, y) ∂ν = (Real.tanh (a * x) - Real.tanh (b * x)) / x :=
    fun x hx => by
      rw [tanh_sub_div_eq_integral (ne_of_gt hx), intervalIntegral.integral_of_le hba]
  refine ⟨?_, ?_⟩
  · have hI : IntegrableOn (fun x => ∫ y, F (x, y) ∂ν) (Ioi 0) := hFi.integral_prod_left
    exact hI.congr_fun (fun x hx => hL x hx) measurableSet_Ioi
  · rw [← hR, ← hswap]
    exact (setIntegral_congr_fun measurableSet_Ioi fun x hx => hL x hx).symm

/-- **DLMF 4.40.10**: `∫₀^∞ (tanh(ax) − tanh(bx))/x dx = ln(a/b)`, `a > 0`, `b > 0`. Proof:
the integrand is `∫_b^a sech²(tx) dt`, and `∫₀^∞ sech²(tx) dx = 1/t` (Fubini). -/
theorem dlmf_4_40_10 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun x => (Real.tanh (a * x) - Real.tanh (b * x)) / x) (Ioi 0) ∧
      ∫ x in Ioi 0, (Real.tanh (a * x) - Real.tanh (b * x)) / x = Real.log (a / b) := by
  rcases le_total b a with h | h
  · exact dlmf_4_40_10_le hb h
  · obtain ⟨h1, h2⟩ := dlmf_4_40_10_le ha h
    have e : (fun x => (Real.tanh (a * x) - Real.tanh (b * x)) / x) =
        fun x => -((Real.tanh (b * x) - Real.tanh (a * x)) / x) := by
      funext x; ring
    rw [e]
    refine ⟨h1.neg, ?_⟩
    rw [integral_neg, h2, Real.log_div ha.ne' hb.ne', Real.log_div hb.ne' ha.ne']
    ring

end Azurite.DLMF
