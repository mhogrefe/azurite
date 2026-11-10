/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section7Zeta
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.NumberTheory.ZetaValues

/-!
# DLMF 5.7.3: the Maclaurin series of `ln Γ(1 + z)`

Formalization of <https://dlmf.nist.gov/5.7> (part 3).

* 5.7.3, `ln Γ(1 + z) = −ln(1 + z) + z(1 − γ) + ∑_{k≥2} (−1)ᵏ (ζ(k) − 1) zᵏ/k`, `|z| < 2`.
  Mathlib has no complex `ln Γ`, so the complex statement is exponentiated, `z ≠ −1`
  (`dlmf_5_7_3`), with the series convergent (`summable_lnGammaTerm`); on the real interval
  `(−1, 2)` it is the real logarithm (`dlmf_5_7_3_real`).
* The proof: `ψ(2 + z) = 1 − γ + ∑_{k≥2} (−1)ᵏ (ζ(k) − 1) z^{k−1}` on `|z| < 2`
  (`hasSum_digamma_two_add`, the 5.7.4 double-series argument on the terms `n ≥ 2` of 5.7.6),
  term-by-term differentiation (`hasDerivAt_lnGammaSeries`, with `|ζ(k) − 1| ≤ 3 · 2^{2−k}`,
  `norm_zeta_sub_one_le`), and `Γ(2 + z) e^{−L(z)}` constant on the disc
  (`Gamma_two_add_eq_exp`).
-/

open Complex Filter Topology Set Finset Metric
open scoped Real

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-- `ζ(j + 2) − 1 = ∑_{m≥0} 1/(m + 2)^{j+2}`. -/
theorem hasSum_zeta_sub_one_succ (j : ℕ) :
    HasSum (fun m : ℕ => 1 / ((m : ℂ) + 2) ^ (j + 2)) (riemannZeta (j + 2) - 1) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_zeta_add_two j)
  simp only [sum_range_one, Nat.cast_zero, zero_add, one_pow, div_one] at h
  convert h using 1
  funext m
  push_cast
  ring_nf

/-- `|ζ(j + 2) − 1| ≤ 3 · 2^{−j}`. -/
theorem norm_zeta_sub_one_le (j : ℕ) : ‖riemannZeta (j + 2) - 1‖ ≤ 3 * (1 / 2) ^ j := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  rw [sum_range_one, Nat.cast_zero, zero_pow two_ne_zero, div_zero, sub_zero] at h
  push_cast at h
  have hb := (hasSum_zeta_sub_one_succ j).norm_le_of_bounded (h.mul_left ((1 / 2 : ℝ) ^ j))
    (fun m => by
      rw [norm_div, norm_one, norm_pow, norm_natCast_add_two]
      have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      calc 1 / ((m : ℝ) + 2) ^ (j + 2) = (1 / ((m : ℝ) + 2)) ^ j * (1 / ((m : ℝ) + 2) ^ 2) := by
            rw [pow_add, div_pow, one_pow, one_div_mul_one_div]
        _ ≤ (1 / 2) ^ j * (1 / ((m : ℝ) + 1) ^ 2) := by
            gcongr
            · linarith
            · linarith)
  have hp : π ^ 2 / 6 ≤ 3 := by nlinarith [Real.pi_le_four, Real.pi_pos]
  calc _ ≤ _ := hb
    _ ≤ (1 / 2) ^ j * 3 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 3 * (1 / 2) ^ j := by ring

/-- `∑_{k≥0} (1/(k + 1) − 1/(k + 2)) = 1`. -/
theorem hasSum_telescope_succ :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 2)) 1 := by
  have hs : Summable (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 2)) := by
    refine Summable.of_norm_bounded summable_inv_succ_sq fun k => ?_
    have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hk2 : (k : ℂ) + 2 ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_natCast_add_two]; positivity
    rw [show 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 2)
        = ((1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) : ℝ) : ℂ) by push_cast; field_simp; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  refine hs.hasSum_iff_tendsto_nat.mpr ?_
  have hsum : ∀ n : ℕ, ∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / ((i : ℂ) + 2))
      = 1 - 1 / ((n : ℂ) + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring
  simp_rw [hsum]
  have h0 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  push_cast at h0
  simpa using (tendsto_const_nhds (x := (1 : ℂ))).sub h0

theorem two_add_not_mem_gammaPoles {z : ℂ} (hz : ‖z‖ < 2) : 2 + z ∉ gammaPoles := by
  rintro ⟨m, hm⟩
  have hzm : z = -((m : ℂ) + 2) := by linear_combination -hm
  rw [hzm, norm_neg, norm_natCast_add_two] at hz
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- `ψ(2 + z) = 1 − γ + ∑_{j≥0} (−1)ʲ (ζ(j + 2) − 1) z^{j+1}`, `|z| < 2`. -/
theorem hasSum_digamma_two_add {z : ℂ} (hz : ‖z‖ < 2) :
    HasSum (fun j : ℕ => (-1 : ℂ) ^ j * (riemannZeta (j + 2) - 1) * z ^ (j + 1))
      (digamma (2 + z) + γ - 1) := by
  set f : ℕ × ℕ → ℂ := fun p => (-1 : ℂ) ^ p.2 * z ^ (p.2 + 1) / ((p.1 : ℂ) + 2) ^ (p.2 + 2)
    with hf
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hsum : Summable f := by
    have hg : Summable fun j : ℕ => (‖z‖ / 2) ^ j :=
      summable_geometric_of_lt_one (by positivity) (by rw [div_lt_one (by norm_num)]; exact hz)
    have hprod := (summable_inv_succ_sq.mul_of_nonneg hg (fun k => by positivity)
      (fun j => by positivity)).mul_left ‖z‖
    refine Summable.of_norm_bounded hprod fun p => ?_
    obtain ⟨m, j⟩ := p
    simp only [hf, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_natCast_add_two]
    have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h2 : (2 : ℝ) ≤ (m : ℝ) + 2 := by linarith
    calc ‖z‖ ^ (j + 1) / ((m : ℝ) + 2) ^ (j + 2)
        = ‖z‖ * (‖z‖ / ((m : ℝ) + 2)) ^ j * (1 / ((m : ℝ) + 2) ^ 2) := by
          rw [div_pow]
          field_simp
          ring
      _ ≤ ‖z‖ * (‖z‖ / 2) ^ j * (1 / ((m : ℝ) + 1) ^ 2) := by
          gcongr
          linarith
      _ = ‖z‖ * (1 / ((m : ℝ) + 1) ^ 2 * (‖z‖ / 2) ^ j) := by ring
  have hi : ∀ m : ℕ, HasSum (fun j => f (m, j)) (1 / ((m : ℂ) + 2) - 1 / ((m : ℂ) + 2 + z)) := by
    intro m
    have hm2 : (m : ℂ) + 2 ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_natCast_add_two]; positivity
    have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hr : ‖-z / ((m : ℂ) + 2)‖ < 1 := by
      rw [norm_div, norm_neg, norm_natCast_add_two, div_lt_one (by positivity)]
      linarith
    have hmz : (m : ℂ) + 2 + z ≠ 0 := by
      intro h
      have := two_add_not_mem_gammaPoles hz
      exact this ⟨m, by linear_combination -h⟩
    have hg := (hasSum_geometric_of_norm_lt_one hr).mul_left (z / ((m : ℂ) + 2) ^ 2)
    convert hg using 1
    · funext j
      simp only [hf]
      rw [div_pow, neg_pow]
      field_simp
      ring
    · rw [show 1 - -z / ((m : ℂ) + 2) = ((m : ℂ) + 2 + z) / ((m : ℂ) + 2) by
          field_simp; ring, inv_div]
      field_simp
      ring
  have hk : ∀ j : ℕ, HasSum (fun m => f (m, j))
      ((-1 : ℂ) ^ j * (riemannZeta (j + 2) - 1) * z ^ (j + 1)) := by
    intro j
    have := (hasSum_zeta_sub_one_succ j).mul_left ((-1 : ℂ) ^ j * z ^ (j + 1))
    convert this using 1
    · funext m
      simp only [hf]
      ring
    · ring
  have hA := hsum.hasSum.prod_fiberwise hi
  have hB := ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hsum.hasSum).prod_fiberwise
    (fun j => by simpa using hk j)
  have hC := (dlmf_5_7_6 (two_add_not_mem_gammaPoles hz)).sub hasSum_telescope_succ
  have hC' : HasSum (fun m : ℕ => 1 / ((m : ℂ) + 2) - 1 / ((m : ℂ) + 2 + z))
      (digamma (2 + z) + γ - 1) := by
    convert hC using 1
    funext m
    ring_nf
  rw [hC'.unique hA]
  exact hB

/-- The terms `(−1)ᵏ (ζ(k) − 1) zᵏ/k` of 5.7.3, indexed by `k = j + 2`. -/
noncomputable def lnGammaTerm (j : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ j * (riemannZeta (j + 2) - 1) * z ^ (j + 2) / ((j : ℂ) + 2)

/-- `L(z) = z(1 − γ) + ∑_{k≥2} (−1)ᵏ (ζ(k) − 1) zᵏ/k`, so that `Γ(2 + z) = e^{L(z)}`. -/
noncomputable def lnGammaSeries (z : ℂ) : ℂ := z * (1 - γ) + ∑' j : ℕ, lnGammaTerm j z

theorem natCast_add_two_ne_zero (j : ℕ) : (j : ℂ) + 2 ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_natCast_add_two]; positivity

theorem summable_lnGammaTerm {z : ℂ} (hz : ‖z‖ < 2) : Summable fun j => lnGammaTerm j z := by
  have hg : Summable fun j : ℕ => 3 * ‖z‖ ^ 2 * (‖z‖ / 2) ^ j :=
    (summable_geometric_of_lt_one (by positivity)
      (by rw [div_lt_one (by norm_num)]; exact hz)).mul_left _
  refine Summable.of_norm_bounded hg fun j => ?_
  unfold lnGammaTerm
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
    norm_natCast_add_two]
  have h1 : (1 : ℝ) ≤ (j : ℝ) + 2 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  rw [div_le_iff₀ (by positivity)]
  calc ‖riemannZeta (j + 2) - 1‖ * ‖z‖ ^ (j + 2)
      ≤ 3 * (1 / 2) ^ j * ‖z‖ ^ (j + 2) := by
        gcongr
        exact norm_zeta_sub_one_le j
    _ = 3 * ‖z‖ ^ 2 * (‖z‖ / 2) ^ j := by
      rw [one_div, div_eq_mul_inv ‖z‖ 2, mul_pow, pow_add]; ring
    _ ≤ 3 * ‖z‖ ^ 2 * (‖z‖ / 2) ^ j * ((j : ℝ) + 2) := le_mul_of_one_le_right (by positivity) h1

theorem hasDerivAt_lnGammaTerm (j : ℕ) (y : ℂ) :
    HasDerivAt (lnGammaTerm j) ((-1 : ℂ) ^ j * (riemannZeta (j + 2) - 1) * y ^ (j + 1)) y := by
  have h := ((hasDerivAt_pow (j + 2) y).const_mul
    ((-1 : ℂ) ^ j * (riemannZeta (j + 2) - 1))).div_const ((j : ℂ) + 2)
  have hj := natCast_add_two_ne_zero j
  convert h using 1
  · funext w
    simp only [lnGammaTerm]
  · push_cast
    field_simp

/-- `L′(z) = ψ(2 + z)`, `|z| < 2`. -/
theorem hasDerivAt_lnGammaSeries {z : ℂ} (hz : ‖z‖ < 2) :
    HasDerivAt lnGammaSeries (digamma (2 + z)) z := by
  set r := (‖z‖ + 2) / 2 with hr
  have hr2 : r < 2 := by rw [hr]; linarith
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hzr : z ∈ ball (0 : ℂ) r := by rw [mem_ball_zero_iff, hr]; linarith
  have hu : Summable fun j : ℕ => 3 * r * (r / 2) ^ j :=
    (summable_geometric_of_lt_one (by positivity)
      (by rw [div_lt_one (by norm_num)]; exact hr2)).mul_left _
  have hT := hasDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball (0 : ℂ) r).isPreconnected
    (fun j y _ => hasDerivAt_lnGammaTerm j y)
    (fun j y hy => by
      rw [mem_ball_zero_iff] at hy
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
      calc ‖riemannZeta (j + 2) - 1‖ * ‖y‖ ^ (j + 1) ≤ 3 * (1 / 2) ^ j * r ^ (j + 1) := by
            gcongr
            exact norm_zeta_sub_one_le j
        _ = 3 * r * (r / 2) ^ j := by
          rw [one_div, div_eq_mul_inv r 2, mul_pow, pow_succ]; ring)
    (mem_ball_self (by linarith [norm_nonneg z] : (0 : ℝ) < r))
    (by simp [lnGammaTerm]) hzr
  rw [(hasSum_digamma_two_add hz).tsum_eq] at hT
  have h := ((hasDerivAt_id z).mul_const (1 - (γ : ℂ))).add hT
  convert h using 1
  · funext w
    simp [lnGammaSeries]
  · ring

/-- `Γ(2 + z) = e^{L(z)}`, `|z| < 2`. -/
theorem Gamma_two_add_eq_exp {z : ℂ} (hz : ‖z‖ < 2) : Gamma (2 + z) = exp (lnGammaSeries z) := by
  set H : ℂ → ℂ := fun w => Gamma (2 + w) * exp (-lnGammaSeries w) with hH
  have hd : ∀ w ∈ ball (0 : ℂ) 2, HasDerivAt H 0 w := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    have hp := two_add_not_mem_gammaPoles hw
    have hG : HasDerivAt (fun w => Gamma (2 + w)) (Gamma (2 + w) * digamma (2 + w)) w := by
      have h := (differentiableAt_Gamma _ (not_mem_gammaPoles.mp hp)).hasDerivAt.comp w
        ((hasDerivAt_id w).const_add 2)
      rw [deriv_Gamma_eq_mul_digamma hp, mul_one] at h
      exact h
    have hE := (hasDerivAt_lnGammaSeries hw).neg.cexp
    convert hG.mul hE using 1
    ring
  have hc := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 2).isPreconnected
    (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hd w hw).deriv) (mem_ball_zero_iff.mpr hz) (mem_ball_self two_pos)
  have h0 : lnGammaSeries 0 = 0 := by simp [lnGammaSeries, lnGammaTerm]
  simp only [hH, add_zero, h0, neg_zero, exp_zero, mul_one] at hc
  have hG2 : Gamma 2 = 1 := by
    have := Complex.Gamma_ofReal 2
    rw [Real.Gamma_two] at this
    exact_mod_cast this
  rw [hG2] at hc
  rw [exp_neg, mul_inv_eq_one₀ (exp_ne_zero _)] at hc
  exact hc

/-- **DLMF 5.7.3**: `ln Γ(1 + z) = −ln(1 + z) + z(1 − γ) + ∑_{k=2}^∞ (−1)ᵏ (ζ(k) − 1) zᵏ/k`,
`|z| < 2`, exponentiated (`z ≠ −1`; the series converges, `summable_lnGammaTerm`). -/
theorem dlmf_5_7_3 {z : ℂ} (hz : ‖z‖ < 2) (h1 : z ≠ -1) :
    Gamma (1 + z) = exp (-log (1 + z) + (z * (1 - γ) + ∑' j : ℕ, lnGammaTerm j z)) := by
  have hne : 1 + z ≠ 0 := fun h => h1 (by linear_combination h)
  rw [exp_add, exp_neg, exp_log hne, ← lnGammaSeries, ← Gamma_two_add_eq_exp hz,
    show 2 + z = (1 + z) + 1 by ring, Complex.Gamma_add_one _ hne]
  field_simp

/-- **DLMF 5.7.3** on the real interval `(−1, 2)`, with the real logarithm:
`ln Γ(1 + x) + ln(1 + x) − x(1 − γ) = ∑_{k=2}^∞ (−1)ᵏ (ζ(k) − 1) xᵏ/k`. -/
theorem dlmf_5_7_3_real {x : ℝ} (h1 : -1 < x) (h2 : x < 2) :
    HasSum (fun j : ℕ => (-1 : ℝ) ^ j * ((riemannZeta (j + 2)).re - 1) * x ^ (j + 2) / (j + 2))
      (Real.log (Real.Gamma (1 + x)) + Real.log (1 + x) - x * (1 - γ)) := by
  have hz : ‖(x : ℂ)‖ < 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have hx1 : (x : ℂ) ≠ -1 := by
    intro h
    have : x = -1 := by exact_mod_cast h
    linarith
  have hpos : 0 < 1 + x := by linarith
  have h := congrArg norm (dlmf_5_7_3 hz hx1)
  rw [show (1 : ℂ) + x = ((1 + x : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.Gamma_pos_of_pos hpos),
    Complex.norm_exp, add_re, neg_re, Complex.log_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpos] at h
  have hS := Complex.hasSum_re (summable_lnGammaTerm hz).hasSum
  rw [h, Real.log_exp]
  convert hS using 1
  · funext j
    rw [show lnGammaTerm j x
        = (((-1 : ℝ) ^ j * x ^ (j + 2) / ((j : ℝ) + 2) : ℝ) : ℂ) * (riemannZeta (j + 2) - 1) by
          simp only [lnGammaTerm]; push_cast; ring,
      re_ofReal_mul, sub_re, one_re]
    ring
  · rw [add_re, show (x : ℂ) * (1 - (γ : ℂ)) = ((x * (1 - γ) : ℝ) : ℂ) by push_cast; ring,
      ofReal_re]
    ring

end Azurite.DLMF
