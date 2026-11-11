/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section9Binet
import Azurite.DLMF.Chapter1.Section14TableSin
import Azurite.DLMF.Chapter1.Section14TableLaplace
import Azurite.DLMF.Chapter4.Section40Definite

/-!
# DLMF §5.9(i): Binet's formula (second form)

Formalizations of <https://dlmf.nist.gov/5.9>, equations 5.9.10 and 5.9.10_1, for `|ph z| < ½π`
(`ℜz > 0`), exponentiated as in `Section9Binet.lean` (Mathlib has no complex `ln Γ`):

* 5.9.10, `Ln Γ(z) = (z − ½) ln z − z + ½ ln(2π) + 2 ∫₀^∞ arctan(t/z)/(e^{2πt} − 1) dt`
  (`dlmf_5_9_10`, principal `arctan`): `arctan(t/z) = ∫₀^∞ e^{−zs} sin(ts) ds/s` (Table 1.14.3,
  row 7) and `2 ∫₀^∞ sin(st)/(e^{2πt} − 1) dt = 1/(eˢ − 1) − 1/s + ½`
  (`integral_sin_div_exp_sub_one`: geometric series, Laplace transforms of `sin`, and the partial
  fractions of `coth` from Mathlib's `cot_series_rep'` at an imaginary point,
  `hasSum_coth_series_exp`), then Fubini turns the double integral into Binet's `J(z)` of 5.9.10_2.
* 5.9.10_1, `Ln Γ(z) = (z − ½) ln z − z + ½ ln(2π) − (z/π) ∫₀^∞ ln(1 − e^{−2πt})/(t² + z²) dt`
  (`dlmf_5_9_10_1`): integration by parts in 5.9.10 (`d ln(1 − e^{−2πt}) = 2π dt/(e^{2πt} − 1)`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-! ### The partial fractions of `coth` -/

/-- `∑_{m≥1} 2s/(s² + 4π²m²) = 1/(eˢ − 1) − 1/s + ½` (`s > 0`). -/
theorem hasSum_coth_series_exp {s : ℝ} (hs : 0 < s) :
    HasSum (fun n : ℕ => 2 * s / (s ^ 2 + 4 * π ^ 2 * ((n : ℝ) + 1) ^ 2))
      (1 / (Real.exp s - 1) - 1 / s + 1 / 2) := by
  set r : ℝ := s / (2 * π) with hr
  have hr0 : r ≠ 0 := by rw [hr]; positivity
  set x : ℂ := (r : ℂ) * I with hx
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hZ : x ∈ integerComplement := by
    rintro ⟨n, hn⟩
    have := congrArg im hn
    simp [hx] at this
    exact hr0 this.symm
  have hC := (summable_cotTerm hZ).hasSum
  rw [← cot_series_rep' hZ] at hC
  have hC' := hC.mul_left (I / (2 * π))
  rw [← Complex.hasSum_ofReal]
  have hterm : ∀ n : ℕ, I / (2 * π) * cotTerm x n =
      ((2 * s / (s ^ 2 + 4 * π ^ 2 * ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) := by
    intro n
    have hden : (s : ℂ) ^ 2 + 4 * π ^ 2 * ((n : ℂ) + 1) ^ 2 ≠ 0 := by
      have : (0 : ℝ) < s ^ 2 + 4 * π ^ 2 * ((n : ℝ) + 1) ^ 2 := by positivity
      exact_mod_cast this.ne'
    have h1 : (r : ℂ) * I - ((n : ℂ) + 1) ≠ 0 := fun h => by
      have := congrArg im h; simp at this; exact hr0 this
    have h2 : (r : ℂ) * I + ((n : ℂ) + 1) ≠ 0 := fun h => by
      have := congrArg im h; simp at this; exact hr0 this
    simp only [cotTerm, hx]
    rw [one_div_add_one_div h1 h2]
    push_cast
    rw [hr]
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring_nf
    have hd2 : (s : ℂ) ^ 2 + (π : ℂ) ^ 2 * 4 + (π : ℂ) ^ 2 * n * 8 + (π : ℂ) ^ 2 * n ^ 2 * 4 ≠ 0 :=
      by
      convert hden using 1; ring
    have hd3 : -(s : ℂ) ^ 2 - (π : ℂ) ^ 2 * 4 - (π : ℂ) ^ 2 * n * 8 - (π : ℂ) ^ 2 * n ^ 2 * 4 ≠ 0 :=
      by
      convert neg_ne_zero.mpr hden using 1; ring
    field_simp
    ring_nf
    rw [show -(s : ℂ) ^ 2 - (π : ℂ) ^ 2 * 4 - (π : ℂ) ^ 2 * n * 8 - (π : ℂ) ^ 2 * n ^ 2 * 4 =
      -((s : ℂ) ^ 2 + (π : ℂ) ^ 2 * 4 + (π : ℂ) ^ 2 * n * 8 + (π : ℂ) ^ 2 * n ^ 2 * 4) by ring,
      inv_neg, neg_neg]
  simp_rw [hterm] at hC'
  convert hC' using 1
  -- the value: `(i/2π)(π cot(πx) − 1/x) = ½ coth(s/2) − 1/s`
  have hpx : (π : ℂ) * x = (s / 2 : ℝ) * I := by rw [hx, hr]; push_cast; field_simp
  rw [hpx, Complex.cot, Complex.cos_mul_I, Complex.sin_mul_I, Complex.cosh, Complex.sinh]
  push_cast
  rw [← Complex.ofReal_exp]
  set E := cexp ((s : ℂ) / 2) with hE
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  have hes : ((Real.exp s : ℝ) : ℂ) = E * E := by
    rw [ofReal_exp, hE, ← Complex.exp_add]; ring_nf
  have hFE : cexp (-((s : ℂ) / 2)) = E⁻¹ := by rw [hE, Complex.exp_neg]
  have he1 : E * E - 1 ≠ 0 := by
    rw [← hes]
    exact_mod_cast (sub_pos.mpr (Real.one_lt_exp_iff.mpr hs)).ne'
  have he2 : E - E⁻¹ ≠ 0 := by
    intro h
    apply he1
    have : E * (E - E⁻¹) = E * E - 1 := by field_simp
    rw [← this, h, mul_zero]
  rw [hes, hFE, hx, hr]
  push_cast
  field_simp
  ring_nf
  have he3 : -1 + E ^ 2 ≠ 0 := by convert he1 using 1; ring
  field_simp
  ring

/-! ### `2 ∫₀^∞ sin(st)/(e^{2πt} − 1) dt = 1/(eˢ − 1) − 1/s + ½` -/

theorem integrableOn_sin_mul_exp_neg (s : ℝ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Real.sin (s * t) * Real.exp (-(c * t))) (Ioi 0) := by
  refine Integrable.mono' (exp_neg_integrableOn_Ioi 0 hc) (by fun_prop : Continuous fun t : ℝ =>
    Real.sin (s * t) * Real.exp (-(c * t))).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_sin_le_one _)

theorem integral_mul_exp_neg {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-(c * t)) = 1 / c ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) two_pos hc
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.Gamma_two, mul_one] at h
  simp only [Real.rpow_one] at h
  rw [h, Real.rpow_two, one_div, inv_pow, one_div]

theorem integral_sin_div_exp_sub_one {s : ℝ} (hs : 0 < s) :
    2 * ∫ t in Ioi (0 : ℝ), Real.sin (s * t) / (Real.exp (2 * π * t) - 1) =
      1 / (Real.exp s - 1) - 1 / s + 1 / 2 := by
  set c : ℕ → ℝ := fun m => 2 * π * ((m : ℝ) + 1) with hc
  have hc0 : ∀ m, 0 < c m := fun m => by rw [hc]; positivity
  set F : ℕ → ℝ → ℝ := fun m t => Real.sin (s * t) * Real.exp (-(c m * t)) with hF
  have hint : ∀ m, Integrable (F m) (volume.restrict (Ioi 0)) := fun m =>
    integrableOn_sin_mul_exp_neg s (hc0 m)
  have hnorm : ∀ m, ∫ t in Ioi (0 : ℝ), ‖F m t‖ ≤ s / (4 * π ^ 2) * (1 / ((m : ℝ) + 1) ^ 2) :=
    fun m => by
    have hb : IntegrableOn (fun t : ℝ => s * (t * Real.exp (-(c m * t)))) (Ioi 0) := by
      have := integrableOn_rpow_mul_exp_neg_mul (s := 1) (by norm_num) (hc0 m)
      simp only [Real.rpow_one] at this
      exact this.const_mul s
    calc ∫ t in Ioi (0 : ℝ), ‖F m t‖ ≤ ∫ t in Ioi (0 : ℝ), s * (t * Real.exp (-(c m * t))) := by
          refine setIntegral_mono_on (hint m).norm hb measurableSet_Ioi fun t ht => ?_
          have ht' : (0 : ℝ) < t := ht
          rw [Real.norm_eq_abs, hF, abs_mul, abs_of_pos (Real.exp_pos _)]
          have h1 : |Real.sin (s * t)| ≤ s * t := by
            have := Real.abs_sin_le_abs (x := s * t)
            rwa [abs_of_pos (mul_pos hs ht')] at this
          nlinarith [Real.exp_pos (-(c m * t))]
      _ = s / (4 * π ^ 2) * (1 / ((m : ℝ) + 1) ^ 2) := by
          rw [integral_const_mul, integral_mul_exp_neg (hc0 m), hc]
          field_simp
          ring
  have hsum : Summable fun m => ∫ t in Ioi (0 : ℝ), ‖F m t‖ :=
    (summable_one_div_natCast_add_one_sq.mul_left (s / (4 * π ^ 2))).of_nonneg_of_le
      (fun m => integral_nonneg fun t => norm_nonneg _) hnorm
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hval : ∀ m, ∫ t in Ioi (0 : ℝ), F m t = 2 * s / (s ^ 2 + 4 * π ^ 2 * ((m : ℝ) + 1) ^ 2) /
      2 := fun m => by
    rw [hF, integral_sin_mul_exp_neg (hc0 m), hc]
    field_simp
    ring
  simp_rw [hval] at h
  have hpt : ∫ t in Ioi (0 : ℝ), ∑' m, F m t =
      ∫ t in Ioi (0 : ℝ), Real.sin (s * t) / (Real.exp (2 * π * t) - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    set q := Real.exp (-(2 * π * t)) with hq
    have hq0 : 0 ≤ q := (Real.exp_pos _).le
    have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; nlinarith)
    have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (Real.sin (s * t) * q)
    have e : ∀ m : ℕ, F m t = Real.sin (s * t) * q * q ^ m := fun m => by
      rw [hF, hq, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add, hc]
      simp only
      congr 2
      ring
    simp_rw [e]
    rw [hg.tsum_eq]
    have he : Real.exp (2 * π * t) - 1 ≠ 0 :=
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by have := Real.pi_pos; positivity))).ne'
    have hE : Real.exp (2 * π * t) ≠ 0 := (Real.exp_pos _).ne'
    rw [hq, Real.exp_neg]
    field_simp
  rw [hpt] at h
  have h2 := (hasSum_coth_series_exp hs).div_const 2
  rw [h.unique h2]
  ring

/-! ### Binet's second formula -/

theorem arctan_div_eq_integral {z : ℂ} (hz : 0 < z.re) {t : ℝ} (ht : 0 < t) :
    Complex.arctan (t / z) =
      ∫ s in Ioi (0 : ℝ), cexp (-(z * s)) / s * ((Real.sin (t * s) : ℝ) : ℂ) := by
  have h := dlmf_table_1_14_3_r7 hz ht
  unfold dlmfFourierSin at h
  have hc : ((√(2 / π) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < √(2 / π) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  exact (mul_left_cancel₀ hc h).symm

theorem two_mul_div_exp_sub_one_le {t : ℝ} (ht : 0 < t) :
    2 * t / (Real.exp (2 * π * t) - 1) ≤ 2 / π * Real.exp (-(π * t)) := by
  have hπ := Real.pi_pos
  have h1 : π * t * Real.exp (π * t) ≤ Real.exp (2 * π * t) - 1 := by
    have e1 := Real.add_one_le_exp (π * t)
    have e2 : Real.exp (2 * π * t) = Real.exp (π * t) * Real.exp (π * t) := by
      rw [← Real.exp_add]; ring_nf
    have e3 : 1 ≤ Real.exp (π * t) := Real.one_le_exp (by positivity)
    nlinarith
  have hpos : 0 < π * t * Real.exp (π * t) := by positivity
  rw [div_le_iff₀ (lt_of_lt_of_le hpos h1)]
  have hm : Real.exp (-(π * t)) * Real.exp (π * t) = 1 := by rw [← Real.exp_add]; simp
  calc 2 * t = 2 / π * Real.exp (-(π * t)) * (π * t * Real.exp (π * t)) := by
        rw [show 2 / π * Real.exp (-(π * t)) * (π * t * Real.exp (π * t)) =
          2 * t * (Real.exp (-(π * t)) * Real.exp (π * t)) * (π / π) by ring,
          div_self hπ.ne', hm]
        ring
    _ ≤ _ := by gcongr

/-- `2 ∫₀^∞ arctan(t/z)/(e^{2πt} − 1) dt = J(z)`. -/
theorem integral_arctan_eq_binetJ {z : ℂ} (hz : 0 < z.re) :
    2 * ∫ t in Ioi (0 : ℝ), Complex.arctan (t / z) / ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ) =
      binetJ z := by
  have hπ := Real.pi_pos
  set G : ℝ → ℝ → ℂ := fun t s => ((2 / (Real.exp (2 * π * t) - 1) : ℝ) : ℂ) *
    (cexp (-(z * s)) / s * ((Real.sin (t * s) : ℝ) : ℂ)) with hG
  have hL : 2 * ∫ t in Ioi (0 : ℝ), Complex.arctan (t / z) / ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ)
      = ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), G t s := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [hG, integral_const_mul, ← arctan_div_eq_integral hz ht]
    push_cast
    ring
  have hint : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    have hb : Integrable (fun p : ℝ × ℝ => 2 / π * Real.exp (-(π * p.1)) *
        Real.exp (-(z.re * p.2))) ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) :=
      Integrable.mul_prod (f := fun t : ℝ => 2 / π * Real.exp (-(π * t)))
        (g := fun s : ℝ => Real.exp (-(z.re * s)))
        (((exp_neg_integrableOn_Ioi 0 hπ).const_mul (2 / π)).congr
          (ae_of_all _ fun t => by simp only [neg_mul]))
        ((exp_neg_integrableOn_Ioi 0 hz).congr (ae_of_all _ fun t => by simp only [neg_mul]))
    rw [Measure.prod_restrict] at hb ⊢
    refine hb.mono' ?_ ((ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)).mpr
      (ae_of_all _ fun p hp => ?_))
    · refine ContinuousOn.aestronglyMeasurable (fun p hp => ?_)
        (measurableSet_Ioi.prod measurableSet_Ioi)
      have h1 : (0 : ℝ) < p.1 := hp.1
      have h2 : (0 : ℝ) < p.2 := hp.2
      have he : Real.exp (2 * π * p.1) - 1 ≠ 0 :=
        (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))).ne'
      have h2' : (p.2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr h2.ne'
      simp only [hG]
      refine ContinuousAt.continuousWithinAt ?_
      fun_prop (disch := assumption)
    · have h1 : (0 : ℝ) < p.1 := hp.1
      have h2 : (0 : ℝ) < p.2 := hp.2
      have hb1 := two_mul_div_exp_sub_one_le h1
      show ‖G p.1 p.2‖ ≤ _
      simp only [hG]
      rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Complex.norm_real,
        Complex.norm_exp, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      have he : 0 < Real.exp (2 * π * p.1) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr
        (by positivity))
      have hre : (-(z * (p.2 : ℂ))).re = -(z.re * p.2) := by simp
      rw [hre, abs_of_pos (div_pos two_pos he), abs_of_pos h2]
      have hsin : |Real.sin (p.1 * p.2)| ≤ p.1 * p.2 := by
        have := Real.abs_sin_le_abs (x := p.1 * p.2)
        rwa [abs_of_pos (mul_pos h1 h2)] at this
      have hEe := Real.exp_pos (-(z.re * p.2))
      calc 2 / (Real.exp (2 * π * p.1) - 1) * (Real.exp (-(z.re * p.2)) / p.2 *
            |Real.sin (p.1 * p.2)|)
          ≤ 2 / (Real.exp (2 * π * p.1) - 1) * (Real.exp (-(z.re * p.2)) / p.2 * (p.1 * p.2)) := by
            gcongr
        _ = 2 * p.1 / (Real.exp (2 * π * p.1) - 1) * Real.exp (-(z.re * p.2)) := by
            field_simp
        _ ≤ 2 / π * Real.exp (-(π * p.1)) * Real.exp (-(z.re * p.2)) := by gcongr
  rw [hL, integral_integral_swap hint, binetJ, laplace]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs' : (0 : ℝ) < s := hs
  have hfac : ∀ t : ℝ, G t s = (cexp (-(z * s)) / s) *
      ((2 * (Real.sin (s * t) / (Real.exp (2 * π * t) - 1)) : ℝ) : ℂ) := fun t => by
    simp only [hG]
    rw [mul_comm t s]
    push_cast
    ring
  simp_rw [hfac]
  rw [integral_const_mul, integral_complex_ofReal, integral_const_mul,
    integral_sin_div_exp_sub_one hs', binetPhi]
  push_cast
  field_simp

/-- **DLMF 5.9.10** (Binet's second formula): for `ℜz > 0`,
`Γ(z) = exp((z − ½) ln z − z + ½ ln(2π) + 2 ∫₀^∞ arctan(t/z)/(e^{2πt} − 1) dt)`, principal
`arctan`; i.e. the exponent is a value of `Ln Γ(z)`. -/
theorem dlmf_5_9_10 {z : ℂ} (hz : 0 < z.re) :
    Gamma z = cexp ((z - 1 / 2) * Complex.log z - z + 1 / 2 * Complex.log (2 * π) +
      2 * ∫ t in Ioi (0 : ℝ), Complex.arctan (t / z) / ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ)) := by
  rw [integral_arctan_eq_binetJ hz, dlmf_5_9_10_2 hz]
  rfl

/-! ### 5.9.10_1 by integration by parts -/

theorem re_sq_le_norm_sq_add_sq {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    z.re ^ 2 ≤ ‖z ^ 2 + (t : ℂ) ^ 2‖ := by
  have e : z ^ 2 + (t : ℂ) ^ 2 = (z - t * I) * (z + t * I) := by ring_nf; rw [I_sq]; ring
  rw [e, norm_mul, sq]
  have h1 : z.re ≤ ‖z - t * I‖ := by
    have := Complex.abs_re_le_norm (z - t * I); simp at this; linarith [le_abs_self z.re]
  have h2 : z.re ≤ ‖z + t * I‖ := by
    have := Complex.abs_re_le_norm (z + t * I); simp at this; linarith [le_abs_self z.re]
  exact mul_le_mul h1 h2 hz.le (norm_nonneg _)

theorem norm_div_sq_add_sq_le {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    ‖z / (z ^ 2 + (t : ℂ) ^ 2)‖ ≤ ‖z‖ / z.re ^ 2 := by
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (re_sq_le_norm_sq_add_sq hz t)

theorem norm_arctan_div_le {z : ℂ} (hz : 0 < z.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.arctan (t / z)‖ ≤ ‖z‖ / z.re ^ 2 * t := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => Complex.arctan (s / z)) (a := 0) (b := t)
    (fun s hs => hasDerivAt_complex_arctan_div hz (by rw [uIcc_of_le ht] at hs; exact hs.1))
    ((continuous_const.div (by fun_prop) fun s => sq_add_sq_ne_zero hz s).intervalIntegrable _ _)
  simp only [ofReal_zero, zero_div, show Complex.arctan 0 = 0 by simp [Complex.arctan],
    sub_zero] at h
  rw [← h]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (C := ‖z‖ / z.re ^ 2) (f := fun s : ℝ => z / (z ^ 2 + (s : ℂ) ^ 2))
    (fun s _ => norm_div_sq_add_sq_le hz s)
  rwa [sub_zero, abs_of_nonneg ht] at this

/-- `ln(1 − e^{−2πt})`. -/
noncomputable def binetLog (t : ℝ) : ℝ := Real.log (1 - Real.exp (-(2 * π * t)))

theorem hasDerivAt_binetLog {t : ℝ} (ht : 0 < t) :
    HasDerivAt binetLog (2 * π / (Real.exp (2 * π * t) - 1)) t := by
  have hπ := Real.pi_pos
  have hq : Real.exp (-(2 * π * t)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have h1 : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(2 * π * t)))
      (2 * π * Real.exp (-(2 * π * t))) t := by
    have h0 : HasDerivAt (fun t : ℝ => -(2 * π * t)) (-(2 * π)) t := by
      have := ((hasDerivAt_id t).const_mul (2 * π)).neg
      simp only [mul_one] at this
      exact this
    have := (h0.exp).const_sub 1
    convert this using 1
    ring
  refine (h1.log (by linarith)).congr_deriv ?_
  have hE : Real.exp (2 * π * t) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))).ne'
  have hm : Real.exp (-(2 * π * t)) * Real.exp (2 * π * t) = 1 := by
    rw [← Real.exp_add]; simp
  have h1' : 1 - Real.exp (-(2 * π * t)) ≠ 0 := by linarith
  field_simp
  linear_combination hm

theorem binetLog_neg {t : ℝ} (ht : 0 < t) : binetLog t < 0 := by
  have hπ := Real.pi_pos
  have hq0 := Real.exp_pos (-(2 * π * t))
  have hq : Real.exp (-(2 * π * t)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  exact Real.log_neg (by linarith) (by linarith)

/-- `|ln(1 − e^{−2πt})| ≤ ln 2 − ln t` on `(0, 1]`. -/
theorem abs_binetLog_le_small {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |binetLog t| ≤ Real.log 2 - Real.log t := by
  have hπ := Real.pi_pos
  rw [abs_of_neg (binetLog_neg ht), binetLog]
  set x := 2 * π * t with hx
  have hx0 : 0 < x := by positivity
  -- `1 − e^{−x} ≥ x/(1 + x) ≥ t/2`
  have h1 : x / (1 + x) ≤ 1 - Real.exp (-x) := by
    have := Real.add_one_le_exp x
    have hm : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Real.exp_pos (-x)]
  have h2 : t / 2 ≤ x / (1 + x) := by
    rw [div_le_div_iff₀ two_pos (by linarith), hx]
    nlinarith [Real.pi_gt_three]
  have h3 : 0 < t / 2 := by positivity
  have := Real.log_le_log h3 (h2.trans h1)
  rw [Real.log_div ht.ne' two_ne_zero] at this
  linarith

/-- `|ln(1 − e^{−2πt})| ≤ 2 e^{−t}` on `[1, ∞)`. -/
theorem abs_binetLog_le_large {t : ℝ} (ht : 1 ≤ t) : |binetLog t| ≤ 2 * Real.exp (-t) := by
  have hπ := Real.pi_pos
  have ht0 : 0 < t := by linarith
  rw [abs_of_neg (binetLog_neg ht0), binetLog]
  set q := Real.exp (-(2 * π * t)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q ≤ Real.exp (-t) / 2 := by
    rw [hq, le_div_iff₀ two_pos]
    have e1 : Real.exp (-(2 * π * t)) * 2 ≤ Real.exp (-(2 * π * t)) * Real.exp t := by
      gcongr
      have := Real.add_one_le_exp t
      linarith
    have e2 : Real.exp (-(2 * π * t)) * Real.exp t ≤ Real.exp (-t) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
    linarith
  have hqh : q ≤ 1 / 2 := by
    have : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  -- `−ln(1 − q) ≤ q/(1 − q) ≤ 2q`
  have h1 := Real.one_sub_inv_le_log_of_pos (x := 1 - q) (by linarith)
  have h2 : (1 - q)⁻¹ - 1 ≤ 2 * q := by
    rw [inv_eq_one_div, div_sub_one (by linarith), div_le_iff₀ (by linarith)]
    nlinarith
  linarith

theorem integrableOn_binetLog : IntegrableOn binetLog (Ioi 0) := by
  have hcont : ContinuousOn binetLog (Ioi 0) := fun t ht =>
    (hasDerivAt_binetLog ht).continuousAt.continuousWithinAt
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · have hb : IntegrableOn (fun t => Real.log 2 - Real.log t) (Ioc 0 1) := by
      have := (intervalIntegrable_const (c := Real.log 2)).sub
        (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this
    refine hb.mono' (hcont.mono Ioc_subset_Ioi_self |>.aestronglyMeasurable measurableSet_Ioc)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_))
    rw [Real.norm_eq_abs]
    exact abs_binetLog_le_small ht.1 ht.2
  · refine ((exp_neg_integrableOn_Ioi 1 one_pos).const_mul 2).mono'
      (hcont.mono (Ioi_subset_Ioi zero_le_one) |>.aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
    rw [Real.norm_eq_abs, neg_one_mul]
    exact abs_binetLog_le_large (le_of_lt ht)

/-- `2 ∫₀^∞ arctan(t/z)/(e^{2πt} − 1) dt = −(z/π) ∫₀^∞ ln(1 − e^{−2πt})/(t² + z²) dt`. -/
theorem integral_arctan_eq_integral_log {z : ℂ} (hz : 0 < z.re) :
    2 * ∫ t in Ioi (0 : ℝ), Complex.arctan (t / z) / ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ) =
      -(z / π) * ∫ t in Ioi (0 : ℝ),
        ((Real.log (1 - Real.exp (-(2 * π * t))) : ℝ) : ℂ) / ((t : ℂ) ^ 2 + z ^ 2) := by
  have hπ := Real.pi_pos
  have hπ' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr hπ.ne'
  set u : ℝ → ℂ := fun t => Complex.arctan (t / z) with hu
  set u' : ℝ → ℂ := fun t => z / (z ^ 2 + (t : ℂ) ^ 2) with hu'
  set v : ℝ → ℂ := fun t => ((binetLog t / π : ℝ) : ℂ) with hv
  set v' : ℝ → ℂ := fun t => ((2 / (Real.exp (2 * π * t) - 1) : ℝ) : ℂ) with hv'
  set C := ‖z‖ / z.re ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have hud : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt u (u' t) t := fun t ht =>
    hasDerivAt_complex_arctan_div hz (le_of_lt ht)
  have hvd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt v (v' t) t := fun t ht => by
    have := ((hasDerivAt_binetLog ht).div_const π).ofReal_comp
    refine this.congr_deriv ?_
    have hE : Real.exp (2 * π * t) - 1 ≠ 0 :=
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by have := ht.out; positivity))).ne'
    simp only [hv']
    push_cast
    field_simp
  have hcu : ContinuousOn u (Ioi 0) := fun t ht => (hud t ht).continuousAt.continuousWithinAt
  have hcv : ContinuousOn v (Ioi 0) := fun t ht => (hvd t ht).continuousAt.continuousWithinAt
  have hcv' : ContinuousOn v' (Ioi 0) := fun t ht => by
    have hE : Real.exp (2 * π * t) - 1 ≠ 0 :=
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by have := ht.out; positivity))).ne'
    have hc : ContinuousAt (fun t : ℝ => 2 / (Real.exp (2 * π * t) - 1)) t :=
      continuousAt_const.div (by fun_prop) hE
    exact (continuous_ofReal.continuousAt.comp hc).continuousWithinAt
  have hcu' : Continuous u' := continuous_const.div (by fun_prop) fun s => sq_add_sq_ne_zero hz s
  -- `u v'`
  have huv' : IntegrableOn (u * v') (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 hπ).const_mul (C * (2 / π))).mono'
      ((hcu.mul hcv').aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
    have ht' : (0 : ℝ) < t := ht
    have hE : 0 < Real.exp (2 * π * t) - 1 :=
      sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
    simp only [Pi.mul_apply, hu, hv', norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos two_pos hE)]
    have h1 := norm_arctan_div_le hz ht'.le
    have h2 := two_mul_div_exp_sub_one_le ht'
    calc ‖Complex.arctan (t / z)‖ * (2 / (Real.exp (2 * π * t) - 1))
        ≤ C * t * (2 / (Real.exp (2 * π * t) - 1)) := by gcongr
      _ = C * (2 * t / (Real.exp (2 * π * t) - 1)) := by ring
      _ ≤ C * (2 / π * Real.exp (-(π * t))) := by gcongr
      _ = C * (2 / π) * Real.exp (-π * t) := by ring_nf
  -- `u' v`
  have hu'v : IntegrableOn (u' * v) (Ioi 0) := by
    refine ((integrableOn_binetLog.norm.const_mul (C / π))).mono'
      ((hcu'.continuousOn.mul hcv).aestronglyMeasurable measurableSet_Ioi)
      (ae_of_all _ fun t => ?_)
    simp only [Pi.mul_apply, hu', hv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos hπ]
    have := norm_div_sq_add_sq_le hz t
    calc ‖z / (z ^ 2 + (t : ℂ) ^ 2)‖ * (|binetLog t| / π) ≤ C * (|binetLog t| / π) := by gcongr
      _ = C / π * |binetLog t| := by ring
  -- boundary terms
  have h0 : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun t : ℝ => C / π * (Real.log 2 * t - Real.log t * t ^ (1 : ℝ)))
        (𝓝[>] 0) (𝓝 0) := by
      have h1 := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos
      have h2 : Tendsto (fun t : ℝ => Real.log 2 * t) (𝓝[>] 0) (𝓝 0) := by
        have hc : Continuous (fun t : ℝ => Real.log 2 * t) := by fun_prop
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using (h2.sub h1).const_mul (C / π)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    simp only [Pi.mul_apply, hu, hv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos hπ, Real.rpow_one]
    have h1 := norm_arctan_div_le hz ht.1.le
    have h2 := abs_binetLog_le_small ht.1 ht.2.le
    calc ‖Complex.arctan (t / z)‖ * (|binetLog t| / π) ≤ C * t * ((Real.log 2 - Real.log t) / π) :=
          mul_le_mul h1 (div_le_div_of_nonneg_right h2 hπ.le) (by positivity)
            (mul_nonneg hC0 ht.1.le)
      _ = C / π * (Real.log 2 * t - Real.log t * t) := by ring
  have hinf : Tendsto (u * v) atTop (𝓝 0) := by
    have hlim : Tendsto (fun t : ℝ => C / π * 2 * (t ^ 1 * Real.exp (-t))) atTop (𝓝 0) := by
      simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul (C / π * 2)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with t ht
    simp only [Pi.mul_apply, hu, hv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos hπ, pow_one]
    have h1 := norm_arctan_div_le hz (by linarith : (0 : ℝ) ≤ t)
    have h2 := abs_binetLog_le_large ht
    calc ‖Complex.arctan (t / z)‖ * (|binetLog t| / π) ≤ C * t * (2 * Real.exp (-t) / π) :=
          mul_le_mul h1 (div_le_div_of_nonneg_right h2 hπ.le) (by positivity)
            (mul_nonneg hC0 (by linarith))
      _ = C / π * 2 * (t * Real.exp (-t)) := by ring
  have hparts := integral_Ioi_mul_deriv_eq_deriv_mul hud hvd huv' hu'v h0 hinf
  simp only [sub_zero, zero_sub] at hparts
  -- assemble
  have e1 : 2 * ∫ t in Ioi (0 : ℝ), Complex.arctan (t / z) / ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ) =
      ∫ t in Ioi (0 : ℝ), u t * v' t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hu, hv']
    push_cast
    ring
  have e2 : ∫ t in Ioi (0 : ℝ), u' t * v t = (z / π) * ∫ t in Ioi (0 : ℝ),
      ((Real.log (1 - Real.exp (-(2 * π * t))) : ℝ) : ℂ) / ((t : ℂ) ^ 2 + z ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hu', hv, binetLog]
    push_cast
    have := sq_add_sq_ne_zero hz t
    have h' : (t : ℂ) ^ 2 + z ^ 2 ≠ 0 := by rwa [add_comm]
    field_simp
    ring
  rw [e1, hparts, e2]
  ring

/-- **DLMF 5.9.10_1**: for `ℜz > 0`,
`Γ(z) = exp((z − ½) ln z − z + ½ ln(2π) − (z/π) ∫₀^∞ ln(1 − e^{−2πt})/(t² + z²) dt)`. -/
theorem dlmf_5_9_10_1 {z : ℂ} (hz : 0 < z.re) :
    Gamma z = cexp ((z - 1 / 2) * Complex.log z - z + 1 / 2 * Complex.log (2 * π) -
      z / π * ∫ t in Ioi (0 : ℝ),
        ((Real.log (1 - Real.exp (-(2 * π * t))) : ℝ) : ℂ) / ((t : ℂ) ^ 2 + z ^ 2)) := by
  rw [dlmf_5_9_10 hz, integral_arctan_eq_integral_log hz]
  congr 1
  ring

end Azurite.DLMF
