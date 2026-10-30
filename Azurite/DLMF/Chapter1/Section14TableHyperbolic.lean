/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14TableFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# DLMF Table 1.14.1: Fourier transforms (hyperbolic rows)

* Partial fractions of the tangent from Mathlib's cotangent series (`cot_series_rep'`):
  `hasSum_tan_half` (`∑_{n ≥ 0} (1/((2n+1)π − w) − 1/((2n+1)π + w)) = tan(w/2)/2`,
  `−π < ℜw < π`), with `hasSum_telescope_inv`, `cot_pi_div_two_sub`.
* `sinh(at)/sinh(πt) = ∑ (e^{−((2n+1)π − a)t} − e^{−((2n+1)π + a)t})` (`hasSum_sinh_div_sinh`),
  `|sinh(at)/sinh(πt)| ≤ e^{−(π − |a|)t}` (`abs_sinh_div_sinh_le`); termwise integration
  (`hasSum_integral_Ioi_sinh_ratio`); `tan_add_tan_half`.
* **`dlmf_table_1_14_1_r6`** (`sinh(at)/sinh(πt)`, `−π < a < π`).
* **`dlmf_table_1_14_1_r7`** (`cosh(at)/cosh(πt)`) from row 6 through
  `cosh(at)/cosh(πt) = (sinh((a+π)t) − sinh((a−π)t))/sinh(2πt)` (`cosh_ratio_eq`) and `t ↦ 2t`.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real

namespace Azurite.DLMF

/-! ### Partial fractions of the tangent -/

theorem norm_add_nat_ge (X : ℂ) (n : ℕ) :
    min X.re 1 * (n + 1) ≤ ‖X + n‖ := by
  have h1 : (X + n).re ≤ ‖X + n‖ := Complex.re_le_norm _
  simp only [add_re, natCast_re] at h1
  have h2 : min X.re 1 ≤ X.re := min_le_left _ _
  have h3 : min X.re 1 ≤ 1 := min_le_right _ _
  have h4 : 0 ≤ (n : ℝ) := n.cast_nonneg
  nlinarith

/-- The telescoping series `∑ (1/(X+n) − 1/(X+n+1)) = 1/X` for `ℜX > 0`. -/
theorem hasSum_telescope_inv {X : ℂ} (hX : 0 < X.re) :
    HasSum (fun n : ℕ => 1 / (X + n) - 1 / (X + (n + 1))) (1 / X) := by
  set m := min X.re 1
  have hm : 0 < m := lt_min hX one_pos
  have hne : ∀ n : ℕ, X + n ≠ 0 := fun n h => by
    have := norm_add_nat_ge X n; rw [h, norm_zero] at this
    have : 0 < m * (n + 1) := by positivity
    linarith
  have hbound : ∀ n : ℕ,
      ‖1 / (X + n) - 1 / (X + (n + 1))‖ ≤ 1 / m ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro n
    have h1 := norm_add_nat_ge X n
    have h2 := norm_add_nat_ge X (n + 1)
    push_cast at h2
    have hne' : X + (n + 1) ≠ 0 := by exact_mod_cast hne (n + 1)
    rw [div_sub_div _ _ (hne n) hne', show 1 * (X + (n + 1)) - (X + n) * 1 = 1 by ring, norm_div,
      norm_one, norm_mul]
    have hpos : 0 < m * (n + 1) := by positivity
    have : m * (n + 1) * (m * (n + 1)) ≤ ‖X + n‖ * ‖X + (n + 1)‖ :=
      mul_le_mul h1 (le_trans (by nlinarith [hm]) h2) hpos.le (norm_nonneg _)
    calc 1 / (‖X + n‖ * ‖X + (n + 1)‖) ≤ 1 / (m * (n + 1) * (m * (n + 1))) :=
          one_div_le_one_div_of_le (by positivity) this
      _ = _ := by field_simp
  have hsum : Summable fun n : ℕ => 1 / (X + n) - 1 / (X + (n + 1)) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => 1 / m ^ 2 * (1 / ((n : ℝ) + 1) ^ 2)) ?_
      hbound
    refine Summable.mul_left _ ?_
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using this
  refine hsum.hasSum_iff_tendsto_nat.mpr ?_
  have htel : ∀ N : ℕ, ∑ i ∈ Finset.range N, (1 / (X + i) - 1 / (X + (i + 1))) =
      1 / X - 1 / (X + N) := fun N => by
    have := Finset.sum_range_sub' (fun i : ℕ => 1 / (X + i)) N
    simpa using this
  simp_rw [htel]
  have hlim : Tendsto (fun N : ℕ => 1 / (X + N)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) (by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / m))
    rw [norm_div, norm_one]
    have := norm_add_nat_ge X N
    calc 1 / ‖X + N‖ ≤ 1 / (m * (N + 1)) := one_div_le_one_div_of_le (by positivity) this
      _ = m⁻¹ * ((N : ℝ) + 1)⁻¹ := by field_simp
  simpa using (tendsto_const_nhds (x := 1 / X)).sub hlim

theorem cot_pi_div_two_sub (z : ℂ) : Complex.cot (π / 2 - z) = Complex.tan z := by
  rw [Complex.cot_eq_cos_div_sin, Complex.cos_pi_div_two_sub, Complex.sin_pi_div_two_sub,
    Complex.tan_eq_sin_div_cos]

/-- **Partial fractions of the tangent**: for `−π < ℜw < π`,
`∑_{n ≥ 0} (1/((2n+1)π − w) − 1/((2n+1)π + w)) = tan(w/2)/2`. -/
theorem hasSum_tan_half {w : ℂ} (hw1 : -π < w.re) (hw2 : w.re < π) :
    HasSum (fun n : ℕ => 1 / ((2 * n + 1) * π - w) - 1 / ((2 * n + 1) * π + w))
      (Complex.tan (w / 2) / 2) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  set X : ℂ := 1 / 2 - w / (2 * π) with hXdef
  have hXre : X.re = 1 / 2 - w.re / (2 * π) := by
    simp only [hXdef, sub_re, div_re]
    simp [Complex.normSq_apply]
    field_simp
  have hX0 : 0 < X.re := by
    rw [hXre]; have := Real.pi_pos
    rw [sub_pos, div_lt_iff₀ (by positivity)]; linarith
  have hX1 : X.re < 1 := by
    rw [hXre]; have := Real.pi_pos
    have : -(1 / 2) < w.re / (2 * π) := by rw [lt_div_iff₀ (by positivity)]; linarith
    linarith
  have hXZ : X ∈ integerComplement := by
    rintro ⟨n, hn⟩
    have h := congrArg Complex.re hn
    simp only [intCast_re] at h
    rw [← h] at hX0 hX1
    have h1 : (0 : ℤ) < n := by exact_mod_cast hX0
    have h2 : n < (1 : ℤ) := by exact_mod_cast hX1
    omega
  have hcot : HasSum (fun n : ℕ => cotTerm X n) (π * Complex.cot (π * X) - 1 / X) := by
    rw [cot_series_rep' hXZ]; exact (summable_cotTerm hXZ).hasSum
  have hu := hcot.add (hasSum_telescope_inv hX0)
  rw [sub_add_cancel] at hu
  have hπX : (π : ℂ) * X = π / 2 - w / 2 := by rw [hXdef]; field_simp
  rw [hπX, cot_pi_div_two_sub] at hu
  convert hu.div_const (2 * π) using 1
  · funext n
    have hA : (2 * n + 1) * (π : ℂ) - w = 2 * π * (X + n) := by rw [hXdef]; field_simp; ring
    have hB : (2 * n + 1) * (π : ℂ) + w = -(2 * π * (X - (n + 1))) := by
      rw [hXdef]; field_simp; ring
    rw [hA, hB]
    simp only [cotTerm]
    have h1 : X + n ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith [n.cast_nonneg (α := ℝ)]
    have h2 : X - (n + 1) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith [n.cast_nonneg (α := ℝ)]
    have h3 : X + (n + 1) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith [n.cast_nonneg (α := ℝ)]
    field_simp
    ring
  · field_simp

/-! ### `sinh(at)/sinh(πt)` on `t > 0` -/

theorem sinh_div_sinh_le {α t : ℝ} (hαπ : α ≤ π) (ht : 0 < t) :
    Real.sinh (α * t) / Real.sinh (π * t) ≤ Real.exp (-((π - α) * t)) := by
  have hs : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
  rw [div_le_iff₀ hs, Real.sinh_eq, Real.sinh_eq]
  have h1 : Real.exp (-((π - α) * t)) * Real.exp (π * t) = Real.exp (α * t) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-((π - α) * t)) * Real.exp (-(π * t)) ≤ Real.exp (-(α * t)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
  have e : Real.exp (-((π - α) * t)) * ((Real.exp (π * t) - Real.exp (-(π * t))) / 2) =
      (Real.exp (-((π - α) * t)) * Real.exp (π * t) -
        Real.exp (-((π - α) * t)) * Real.exp (-(π * t))) / 2 := by ring
  rw [e]
  linarith

theorem abs_sinh_div_sinh_le {a t : ℝ} (ha : |a| < π) (ht : 0 < t) :
    |Real.sinh (a * t) / Real.sinh (π * t)| ≤ Real.exp (-((π - |a|) * t)) := by
  have hs : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
  rw [abs_div, abs_of_pos hs]
  have : |Real.sinh (a * t)| = Real.sinh (|a| * t) := by
    rw [Real.abs_sinh, abs_mul, abs_of_pos ht]
  rw [this]
  exact sinh_div_sinh_le ha.le ht

/-- `sinh(at)/sinh(πt) = ∑ (e^{−((2n+1)π − a)t} − e^{−((2n+1)π + a)t})` for `t > 0`. -/
theorem hasSum_sinh_div_sinh {a t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => Real.exp (-(((2 * n + 1) * π - a) * t)) -
      Real.exp (-(((2 * n + 1) * π + a) * t))) (Real.sinh (a * t) / Real.sinh (π * t)) := by
  set q := Real.exp (-(2 * π * t))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left
    (Real.exp ((a - π) * t) - Real.exp (-((a + π) * t)))
  have hterm : ∀ n : ℕ, (Real.exp ((a - π) * t) - Real.exp (-((a + π) * t))) * q ^ n =
      Real.exp (-(((2 * n + 1) * π - a) * t)) - Real.exp (-(((2 * n + 1) * π + a) * t)) := by
    intro n
    simp only [q]
    rw [← Real.exp_nat_mul, sub_mul, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  convert h using 1
  · funext n; rw [hterm]
  · have hs : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
    have h1q : 0 < 1 - q := by linarith
    rw [Real.sinh_eq, Real.sinh_eq, ← div_eq_mul_inv]
    rw [div_eq_div_iff (by rw [Real.sinh_eq] at hs; linarith) h1q.ne']
    simp only [q]
    have e1 : Real.exp ((a - π) * t) = Real.exp (a * t) * Real.exp (-(π * t)) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-((a + π) * t)) = Real.exp (-(a * t)) * Real.exp (-(π * t)) := by
      rw [← Real.exp_add]; ring_nf
    have e3 : Real.exp (-(2 * π * t)) = Real.exp (-(π * t)) * Real.exp (-(π * t)) := by
      rw [← Real.exp_add]; ring_nf
    have e4 : Real.exp (π * t) * Real.exp (-(π * t)) = 1 := by rw [← Real.exp_add]; simp
    rw [e1, e2, e3]
    linear_combination (-(Real.exp (a * t)) / 2 + Real.exp (-(a * t)) / 2) * e4

theorem integral_Ioi_exp_neg_real {b : ℝ} (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(b * t)) = 1 / b := by
  have h := integral_exp_mul_Ioi (a := -b) (by linarith) 0
  simp only [neg_mul, mul_zero, Real.exp_zero] at h
  rw [h]; field_simp

theorem integrableOn_Ioi_cexp_neg {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (fun t : ℝ => cexp (-(c * t))) (Ioi 0) :=
  (integrableOn_exp_mul_complex_Ioi (a := -c) (by simpa using hc) 0).congr_fun
    (fun t _ => by ring_nf) measurableSet_Ioi

/-- `|e^{−(c−a)t} − e^{−(c+a)t}| = e^{−(c−|a|)t} − e^{−(c+|a|)t}` for `t ≥ 0`. -/
theorem abs_exp_sub_exp {c a t : ℝ} (ht : 0 ≤ t) :
    |Real.exp (-((c - a) * t)) - Real.exp (-((c + a) * t))| =
      Real.exp (-((c - |a|) * t)) - Real.exp (-((c + |a|) * t)) := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg]
    rw [sub_nonneg]; exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [abs_of_nonpos h, abs_of_nonpos]
    · ring_nf
    · rw [sub_nonpos]; exact Real.exp_le_exp.mpr (by nlinarith)

theorem continuous_sinh_ratio (a : ℝ) :
    Measurable fun t : ℝ => Real.sinh (a * t) / Real.sinh (π * t) := by fun_prop

/-- The transform of `sinh(at)/sinh(πt)` over `t > 0` as a series. -/
theorem hasSum_integral_Ioi_sinh_ratio {a : ℝ} (ha : |a| < π) (y : ℝ) :
    HasSum (fun n : ℕ => 1 / ((((2 * n + 1) * π - a : ℝ) : ℂ) - I * y) -
        1 / ((((2 * n + 1) * π + a : ℝ) : ℂ) - I * y))
      (∫ t in Ioi (0 : ℝ),
        ((Real.sinh (a * t) / Real.sinh (π * t) : ℝ) : ℂ) * cexp (I * y * t)) := by
  have hpi := Real.pi_pos
  have ha0 := abs_nonneg a
  set cm : ℕ → ℝ := fun n => (2 * n + 1) * π - a
  set cp : ℕ → ℝ := fun n => (2 * n + 1) * π + a
  have hcm : ∀ n : ℕ, 0 < cm n := fun n => by
    simp only [cm]; have := abs_lt.mp ha; nlinarith [n.cast_nonneg (α := ℝ)]
  have hcp : ∀ n : ℕ, 0 < cp n := fun n => by
    simp only [cp]; have := abs_lt.mp ha; nlinarith [n.cast_nonneg (α := ℝ)]
  set F : ℕ → ℝ → ℂ := fun n t =>
    (((Real.exp (-(cm n * t)) - Real.exp (-(cp n * t)) : ℝ)) : ℂ) * cexp (I * y * t)
  have hF : ∀ n, F n = fun t : ℝ => cexp (-(((cm n : ℂ) - I * y) * t)) -
      cexp (-(((cp n : ℂ) - I * y) * t)) :=
    fun n => by
      funext t; simp only [F]; push_cast
      rw [sub_mul, ← Complex.exp_add, ← Complex.exp_add]; ring_nf
  have hre : ∀ c : ℝ, 0 < c → 0 < ((c : ℂ) - I * y).re := fun c hc => by simpa using hc
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n => by
    rw [hF]
    refine Integrable.sub ?_ ?_
    · exact integrableOn_Ioi_cexp_neg (hre _ (hcm n))
    · exact integrableOn_Ioi_cexp_neg (hre _ (hcp n))
  have hval : ∀ n, ∫ t in Ioi (0 : ℝ), F n t =
      1 / ((cm n : ℂ) - I * y) - 1 / ((cp n : ℂ) - I * y) := fun n => by
    rw [hF, integral_sub, integral_Ioi_cexp_neg (hre _ (hcm n)),
      integral_Ioi_cexp_neg (hre _ (hcp n))]
    · exact integrableOn_Ioi_cexp_neg (hre _ (hcm n))
    · exact integrableOn_Ioi_cexp_neg (hre _ (hcp n))
  set c : ℕ → ℝ := fun n => (2 * n + 1) * π
  have hnorm : ∀ n, ∫ t in Ioi (0 : ℝ), ‖F n t‖ = 1 / (c n - |a|) - 1 / (c n + |a|) := fun n => by
    have hc1 : 0 < c n - |a| := by simp only [c]; nlinarith [n.cast_nonneg (α := ℝ)]
    have hc2 : 0 < c n + |a| := by simp only [c]; nlinarith [n.cast_nonneg (α := ℝ)]
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t => Real.exp (-((c n - |a|) * t)) -
        Real.exp (-((c n + |a|) * t))) fun t ht => by
      simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [show ‖cexp (I * y * t)‖ = 1 by rw [Complex.norm_exp]; simp, mul_one]
      exact abs_exp_sub_exp (c := c n) (mem_Ioi.mp ht).le]
    rw [integral_sub, integral_Ioi_exp_neg_real hc1, integral_Ioi_exp_neg_real hc2]
    · exact (exp_neg_integrableOn_Ioi 0 hc1).congr_fun (fun t _ => by ring_nf) measurableSet_Ioi
    · exact (exp_neg_integrableOn_Ioi 0 hc2).congr_fun (fun t _ => by ring_nf) measurableSet_Ioi
  have hsum : Summable fun n => ∫ t in Ioi (0 : ℝ), ‖F n t‖ := by
    simp_rw [hnorm]
    set K := 2 * |a| / ((π - |a|) * π)
    have hπa : 0 < π - |a| := by linarith
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      (((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left K)
    · have hc1 : 0 < c n - |a| := by simp only [c]; nlinarith [n.cast_nonneg (α := ℝ)]
      have : 1 / (c n + |a|) ≤ 1 / (c n - |a|) :=
        one_div_le_one_div_of_le hc1 (by linarith)
      linarith
    · have hn := n.cast_nonneg (α := ℝ)
      have h1 : (π - |a|) * (n + 1) ≤ c n - |a| := by simp only [c]; nlinarith
      have h2 : π * (n + 1) ≤ c n + |a| := by simp only [c]; nlinarith
      have hc1 : 0 < c n - |a| := lt_of_lt_of_le (by positivity) h1
      rw [div_sub_div _ _ hc1.ne' (by linarith), show 1 * (c n + |a|) - (c n - |a|) * 1 = 2 * |a| by
        ring]
      push_cast
      calc 2 * |a| / ((c n - |a|) * (c n + |a|))
          ≤ 2 * |a| / ((π - |a|) * (n + 1) * (π * (n + 1))) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity)
              (mul_le_mul h1 h2 (by positivity) hc1.le)
        _ = K * (1 / ((n : ℝ) + 1) ^ 2) := by simp only [K]; field_simp
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  simp_rw [hval] at h
  convert h using 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have hS := hasSum_sinh_div_sinh (a := a) (mem_Ioi.mp ht)
  have hS' : HasSum (fun n => F n t)
      (((Real.sinh (a * t) / Real.sinh (π * t) : ℝ) : ℂ) * cexp (I * y * t)) := by
    have := (Complex.hasSum_ofReal.mpr hS).mul_right (cexp (I * y * t))
    convert this using 1
  exact hS'.tsum_eq.symm

theorem cosh_add_cos_pos {a : ℝ} (ha : |a| < π) (x : ℝ) : 0 < Real.cosh x + Real.cos a := by
  have h1 := Real.one_le_cosh x
  have h2 : Real.cos π < Real.cos |a| :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg a) le_rfl ha
  rw [Real.cos_pi, Real.cos_abs] at h2
  linarith

/-- `(tan((a + ix)/2) + tan((a − ix)/2))/2 = sin a/(cosh x + cos a)`. -/
theorem tan_add_tan_half {a : ℝ} (ha : |a| < π) (x : ℝ) :
    (Complex.tan ((a + I * x) / 2) / 2 + Complex.tan ((a - I * x) / 2) / 2) =
      ((Real.sin a / (Real.cosh x + Real.cos a) : ℝ) : ℂ) := by
  set u : ℂ := (a + I * x) / 2
  set v : ℂ := (a - I * x) / 2
  have huv : u + v = a := by simp only [u, v]; ring
  have huv' : u - v = x * I := by simp only [u, v]; ring
  have hprod : Complex.cos u * Complex.cos v = ((Real.cosh x + Real.cos a) / 2 : ℝ) := by
    have h1 := Complex.cos_add u v
    have h2 := Complex.cos_sub u v
    rw [huv] at h1; rw [huv', Complex.cos_mul_I] at h2
    push_cast
    rw [← ofReal_cosh, ← ofReal_cos] at *
    linear_combination (-1 / 2 : ℂ) * h1 + (-1 / 2 : ℂ) * h2
  have hpos := cosh_add_cos_pos ha x
  have hne : Complex.cos u * Complex.cos v ≠ 0 := by
    rw [hprod]; exact_mod_cast (by positivity : (Real.cosh x + Real.cos a) / 2 ≠ 0)
  have hu : Complex.cos u ≠ 0 := left_ne_zero_of_mul hne
  have hv : Complex.cos v ≠ 0 := right_ne_zero_of_mul hne
  have hsin : Complex.sin u * Complex.cos v + Complex.cos u * Complex.sin v = Real.sin a := by
    rw [← Complex.sin_add, huv]; exact (ofReal_sin a).symm
  rw [Complex.tan_eq_sin_div_cos, Complex.tan_eq_sin_div_cos]
  have e : Complex.sin u / Complex.cos u / 2 + Complex.sin v / Complex.cos v / 2 =
      (Complex.sin u * Complex.cos v + Complex.cos u * Complex.sin v) /
        (2 * (Complex.cos u * Complex.cos v)) := by
    field_simp
  rw [e, hsin, hprod]
  have hc : ((Real.cosh x + Real.cos a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  push_cast at hc ⊢
  field_simp

theorem sinh_ratio_neg (a t : ℝ) :
    Real.sinh (a * -t) / Real.sinh (π * -t) = Real.sinh (a * t) / Real.sinh (π * t) := by
  rw [mul_neg, mul_neg, Real.sinh_neg, Real.sinh_neg, neg_div_neg_eq]

theorem integrableOn_sinh_ratio {a : ℝ} (ha : |a| < π) (y : ℝ) :
    IntegrableOn (fun t : ℝ => ((Real.sinh (a * t) / Real.sinh (π * t) : ℝ) : ℂ) * cexp (I * y * t))
      (Ioi 0) := by
  have hb : 0 < π - |a| := by linarith
  have hI : IntegrableOn (fun t : ℝ => Real.exp (-((π - |a|) * t))) (Ioi 0) := by
    exact (exp_neg_integrableOn_Ioi 0 hb).congr_fun (fun t _ => by ring_nf) measurableSet_Ioi
  refine Integrable.mono' hI ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  · exact ((continuous_sinh_ratio a).complex_ofReal.aestronglyMeasurable.mul
      (by fun_prop : Continuous fun t : ℝ => cexp (I * y * t)).aestronglyMeasurable)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show ‖cexp (I * y * t)‖ = 1 by rw [Complex.norm_exp]; simp, mul_one]
    exact abs_sinh_div_sinh_le ha (mem_Ioi.mp ht)

/-- **Table 1.14.1, row 6**: `𝓕[sinh(at)/sinh(πt)](x) = (2π)^{−1/2} sin a/(cosh x + cos a)`
(`−π < a < π`). -/
theorem dlmf_table_1_14_1_r6 {a : ℝ} (ha1 : -π < a) (ha2 : a < π) (x : ℝ) :
    dlmfFourier (fun t => ((Real.sinh (a * t) / Real.sinh (π * t) : ℝ) : ℂ)) x =
      ((1 / √(2 * π) * (Real.sin a / (Real.cosh x + Real.cos a)) : ℝ) : ℂ) := by
  have ha : |a| < π := abs_lt.mpr ⟨ha1, ha2⟩
  have hneg : EqOn (fun t : ℝ => ((Real.sinh (a * -t) / Real.sinh (π * -t) : ℝ) : ℂ) *
      cexp (-(I * x * t)))
      (fun t : ℝ => ((Real.sinh (a * t) / Real.sinh (π * t) : ℝ) : ℂ) * cexp (I * (-x : ℝ) * t))
      (Ioi 0) := fun t _ => by
    simp only; rw [sinh_ratio_neg]; push_cast; ring_nf
  rw [dlmfFourier_split (integrableOn_sinh_ratio ha x)
    ((integrableOn_sinh_ratio ha (-x)).congr_fun hneg.symm measurableSet_Ioi),
    setIntegral_congr_fun measurableSet_Ioi hneg]
  have hJ := (hasSum_integral_Ioi_sinh_ratio ha x).add (hasSum_integral_Ioi_sinh_ratio ha (-x))
  have hT := (hasSum_tan_half (w := a + I * x) (by simpa using ha1) (by simpa using ha2)).add
    (hasSum_tan_half (w := a - I * x) (by simpa using ha1) (by simpa using ha2))
  have heq := hJ.unique (hT.congr_fun fun n => by push_cast; ring)
  rw [heq, tan_add_tan_half ha x]
  push_cast
  ring

/-! ### Row 7 from row 6 -/

theorem integrable_of_Ioi_neg {g : ℝ → ℂ} (hpos : IntegrableOn g (Ioi 0))
    (hneg : IntegrableOn (fun t => g (-t)) (Ioi 0)) : Integrable g := by
  have hI : IntegrableOn g (Iic 0) := by
    have := ((integrableOn_Ici_iff_integrableOn_Ioi).mpr (by simpa using hneg)).comp_neg_Iic
      (c := (0 : ℝ)) (f := fun t => g (-t))
    simpa using this
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hI.union hpos

theorem integrable_sinh_ratio {b : ℝ} (hb : |b| < π) (y : ℝ) :
    Integrable fun t : ℝ => ((Real.sinh (b * t) / Real.sinh (π * t) : ℝ) : ℂ) * cexp (I * y * t) :=
  integrable_of_Ioi_neg (integrableOn_sinh_ratio hb y)
    ((integrableOn_sinh_ratio hb (-y)).congr_fun (fun t _ => by
      simp only; rw [sinh_ratio_neg]; push_cast; ring_nf) measurableSet_Ioi)

theorem cosh_ratio_eq {a t : ℝ} (ht : t ≠ 0) :
    Real.cosh (a * t) / Real.cosh (π * t) =
      Real.sinh ((a + π) / 2 * (2 * t)) / Real.sinh (π * (2 * t)) -
        Real.sinh ((a - π) / 2 * (2 * t)) / Real.sinh (π * (2 * t)) := by
  have hs : Real.sinh (π * t) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero ht
  have hc : Real.cosh (π * t) ≠ 0 := (Real.cosh_pos _).ne'
  rw [← sub_div, show (a + π) / 2 * (2 * t) = a * t + π * t by ring,
    show (a - π) / 2 * (2 * t) = a * t - π * t by ring, show π * (2 * t) = 2 * (π * t) by ring,
    Real.sinh_add, Real.sinh_sub, Real.sinh_two_mul]
  field_simp
  ring

/-- **Table 1.14.1, row 7**: `𝓕[cosh(at)/cosh(πt)](x) = √(2/π) cos(a/2) cosh(x/2)/(cosh x + cos a)`
(`−π < a < π`). -/
theorem dlmf_table_1_14_1_r7 {a : ℝ} (ha1 : -π < a) (ha2 : a < π) (x : ℝ) :
    dlmfFourier (fun t => ((Real.cosh (a * t) / Real.cosh (π * t) : ℝ) : ℂ)) x =
      ((√(2 / π) * (Real.cos (a / 2) * Real.cosh (x / 2) /
        (Real.cosh x + Real.cos a)) : ℝ) : ℂ) := by
  have ha : |a| < π := abs_lt.mpr ⟨ha1, ha2⟩
  set bp := (a + π) / 2
  set bm := (a - π) / 2
  have hbp : |bp| < π := abs_lt.mpr ⟨by simp only [bp]; linarith, by simp only [bp]; linarith⟩
  have hbm : |bm| < π := abs_lt.mpr ⟨by simp only [bm]; linarith, by simp only [bm]; linarith⟩
  set φ : ℝ → ℂ := fun u => (((Real.sinh (bp * u) / Real.sinh (π * u) -
    Real.sinh (bm * u) / Real.sinh (π * u)) : ℝ) : ℂ) * cexp (I * (x / 2 : ℝ) * u)
  have hint : ∫ t, ((Real.cosh (a * t) / Real.cosh (π * t) : ℝ) : ℂ) * cexp (I * x * t) =
      ∫ t, φ (2 * t) := by
    refine integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume 0] with t ht
    simp only [φ, bp, bm]
    rw [cosh_ratio_eq ht]
    push_cast; ring_nf
  have hsplit : ∫ u, φ u = (∫ u, ((Real.sinh (bp * u) / Real.sinh (π * u) : ℝ) : ℂ) *
      cexp (I * (x / 2 : ℝ) * u)) - ∫ u, ((Real.sinh (bm * u) / Real.sinh (π * u) : ℝ) : ℂ) *
      cexp (I * (x / 2 : ℝ) * u) := by
    rw [← integral_sub (integrable_sinh_ratio hbp _) (integrable_sinh_ratio hbm _)]
    congr 1; funext u; simp only [φ]; push_cast; ring
  have hF : ∀ b : ℝ, |b| < π → ∫ u, ((Real.sinh (b * u) / Real.sinh (π * u) : ℝ) : ℂ) *
      cexp (I * (x / 2 : ℝ) * u) =
      ((Real.sin b / (Real.cosh (x / 2) + Real.cos b) : ℝ) : ℂ) := by
    intro b hb
    have h := dlmf_table_1_14_1_r6 (abs_lt.mp hb).1 (abs_lt.mp hb).2 (x / 2)
    unfold dlmfFourier at h
    have hs : ((√(2 * π) : ℝ) : ℂ) ≠ 0 := sqrt_two_pi_ne_zero
    have hs' : (√(2 * π) : ℝ) ≠ 0 := by exact_mod_cast hs
    have := congrArg (fun z => ((√(2 * π) : ℝ) : ℂ) * z) h
    simp only [← mul_assoc, mul_inv_cancel₀ hs, one_mul] at this
    rw [this]
    push_cast
    field_simp
  unfold dlmfFourier
  rw [hint, Measure.integral_comp_mul_left, hsplit, hF bp hbp, hF bm hbm]
  -- trigonometry
  have e1 : Real.sin bp = Real.cos (a / 2) := by
    simp only [bp]; rw [show (a + π) / 2 = a / 2 + π / 2 by ring, Real.sin_add_pi_div_two]
  have e2 : Real.cos bp = -Real.sin (a / 2) := by
    simp only [bp]; rw [show (a + π) / 2 = a / 2 + π / 2 by ring, Real.cos_add_pi_div_two]
  have e3 : Real.sin bm = -Real.cos (a / 2) := by
    simp only [bm]; rw [show (a - π) / 2 = a / 2 - π / 2 by ring, Real.sin_sub_pi_div_two]
  have e4 : Real.cos bm = Real.sin (a / 2) := by
    simp only [bm]; rw [show (a - π) / 2 = a / 2 - π / 2 by ring, Real.cos_sub_pi_div_two]
  rw [e1, e2, e3, e4]
  set C := Real.cosh (x / 2)
  set sn := Real.sin (a / 2)
  have hcx : Real.cosh x = 2 * C ^ 2 - 1 := by
    have := Real.cosh_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring] at this
    rw [this, ← Real.cosh_sq_sub_sinh_sq (x / 2)]; simp only [C]; ring_nf
  have hca : Real.cos a = 1 - 2 * sn ^ 2 := by
    have h1 := Real.cos_two_mul (a / 2)
    rw [show 2 * (a / 2) = a by ring] at h1
    have h2 := Real.cos_sq_add_sin_sq (a / 2)
    simp only [sn]; linarith
  have hpos := cosh_add_cos_pos ha x
  rw [hcx, hca] at hpos ⊢
  have hC1 : 1 ≤ C := Real.one_le_cosh _
  have hprod : 0 < (C - sn) * (C + sn) := by nlinarith
  have hsn1 : sn ≤ 1 := Real.sin_le_one _
  have hsn2 : -1 ≤ sn := Real.neg_one_le_sin _
  have h1 : 0 < C - sn := by
    rcases (mul_pos_iff.mp hprod) with h | h
    · exact h.1
    · linarith [h.2]
  have h2 : 0 < C + sn := by
    rcases (mul_pos_iff.mp hprod) with h | h
    · exact h.2
    · linarith [h.1]
  rw [← two_div_sqrt_two_pi]
  have hs : (√(2 * π) : ℝ) ≠ 0 := by positivity
  push_cast
  have hc1 : ((C : ℂ) + -(sn : ℂ)) ≠ 0 := by exact_mod_cast (by linarith : C + -sn ≠ 0)
  have hc2 : ((C : ℂ) + (sn : ℂ)) ≠ 0 := by exact_mod_cast h2.ne'
  have hc3 : (2 * (C : ℂ) ^ 2 - 1 + (1 - 2 * (sn : ℂ) ^ 2)) ≠ 0 := by
    exact_mod_cast (by nlinarith : 2 * C ^ 2 - 1 + (1 - 2 * sn ^ 2) ≠ 0)
  have hs' : ((√(2 * π) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  simp only [abs_inv, abs_two]
  rw [Complex.real_smul]
  push_cast
  field_simp
  ring

end Azurite.DLMF
