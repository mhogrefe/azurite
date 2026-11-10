/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section6
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# DLMF 5.6.2 and 5.6.3: `1/Γ(x) + 1/Γ(1/x) ≤ 2` and `1/Γ(x)² + 1/Γ(1/x)² ≤ 2`

`dlmf_5_6_3` implies `dlmf_5_6_2` (`(a + b)² ≤ 2(a² + b²)`).  By the symmetry `x ↔ 1/x` it is
enough to take `x ≥ 1`.

* For `x ≥ 3/2` both `1/Γ(x)²` and `1/Γ(1/x)²` decrease (`ψ > 0` on `[3/2, ∞)`, `ψ < 0` on
  `(0, 1]`), so the sum is at most its value at `3/2`.
* On `[1, 3/2]`: strong convexity of `ln Γ` with explicit constants, from the limit form of 5.7.6
  term by term (`psiR_sub_one_ge`: `ψ(t) − ψ(1) ≥ (6/5)(t − 1)` on `[1, 3/2]`, as
  `ψ(3/2) − ψ(1) = 2 − 2 ln 2`; `psiR_one_sub_ge`: `ψ(1) − ψ(t) ≥ (8/5)(1 − t)` on `(0, 1]`, by
  Basel's `∑ 1/(k + 1)² = π²/6`), integrated (`neg_log_Gamma_le_right`,
  `neg_log_Gamma_le_left`): `1/Γ(x)² ≤ e^A`, `1/Γ(1/x)² ≤ e^B` with
  `A = 2γε − (6/5)ε²`, `B = −2γd − (8/5)d²`, `ε = x − 1`, `d = 1 − 1/x`; then
  `e^A + e^B = 2e^{(A+B)/2} cosh((A − B)/2) ≤ 2e^{(A+B)/2 + (A−B)²/8}` (`exp_add_exp_le_two`), and
  `(A + B)/2 + (A − B)²/8 = ε² Q(ε, γ)/(8x⁴)` with a quartic `Q < 0` on `[0, ½]`
  (`recip_poly_nonpos`, `nlinarith` with `0.57721 < γ < 0.57722`).
-/

open Complex Filter Topology Set Finset
open scoped Real

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-! ### Values and differences of `ψ` -/

theorem psiR_one : psiR 1 = -γ := by
  simp [psiR, digamma_one]

theorem psiR_three_halves : psiR (3 / 2) = 2 - 2 * Real.log 2 - γ := by
  unfold psiR
  rw [show ((3 / 2 : ℝ) : ℂ) = 3 / 2 by push_cast; rfl, digamma_three_halves, sub_re, sub_re,
    mul_re, ofReal_re, ofReal_im, ofReal_re]
  norm_num

/-- `ψ(b) − ψ(a) = lim ∑_{k<N} (b − a)/((a + k)(b + k))`. -/
theorem tendsto_psiR_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ => ∑ k ∈ range N, (b - a) / ((a + k) * (b + k))) atTop
      (𝓝 (psiR b - psiR a)) := by
  refine ((tendsto_psiR_series hb).sub (tendsto_psiR_series ha)).congr fun N => ?_
  rw [sub_sub_sub_cancel_left, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : a + k ≠ 0 := by positivity
  have h2 : b + k ≠ 0 := by positivity
  field_simp
  ring

/-- `ψ(t) − ψ(1) ≥ (6/5)(t − 1)` for `1 ≤ t ≤ 3/2`. -/
theorem psiR_sub_one_ge {t : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ 3 / 2) :
    6 / 5 * (t - 1) ≤ psiR t - psiR 1 := by
  rcases eq_or_lt_of_le h1 with rfl | h1
  · simp
  have hf := (tendsto_psiR_sub (a := 1) (b := 3 / 2) one_pos (by norm_num)).const_mul (2 * (t - 1))
  have hg := tendsto_psiR_sub (a := 1) (b := t) one_pos (by linarith)
  have hle := le_of_tendsto_of_tendsto hf hg (Eventually.of_forall fun N => by
    dsimp only
    rw [mul_sum]
    refine sum_le_sum fun k _ => ?_
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [show 2 * (t - 1) * ((3 / 2 - 1) / ((1 + k) * (3 / 2 + k)))
      = (t - 1) / ((1 + k) * (3 / 2 + k)) by ring]
    exact div_le_div_of_nonneg_left (by linarith) (by positivity)
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity)))
  rw [psiR_three_halves, psiR_one] at hle
  rw [psiR_one]
  have := Real.log_two_lt_d9
  have h3 : 6 / 5 * (t - 1) ≤ 2 * (t - 1) * (2 - 2 * Real.log 2) := by
    nlinarith [sub_pos.mpr h1]
  linarith

/-- `∑_{k<N} 1/(k + 1)² → π²/6` (Mathlib's `hasSum_zeta_two`). -/
theorem tendsto_basel : Tendsto (fun N : ℕ => ∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ 2) atTop
    (𝓝 (π ^ 2 / 6)) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simp only [sum_range_one, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at h
  exact h.tendsto_sum_nat

/-- `ψ(1) − ψ(t) ≥ (8/5)(1 − t)` for `0 < t ≤ 1`. -/
theorem psiR_one_sub_ge {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    8 / 5 * (1 - t) ≤ psiR 1 - psiR t := by
  have hf := tendsto_basel.const_mul (1 - t)
  have hg := tendsto_psiR_sub (a := t) (b := 1) h0 one_pos
  have hle := le_of_tendsto_of_tendsto hf hg (Eventually.of_forall fun N => by
    dsimp only
    rw [mul_sum]
    refine sum_le_sum fun k _ => ?_
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (by linarith) (by positivity)
      (by nlinarith))
  have hπ : (9.6 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_d2]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hπ)]

/-! ### Strong convexity of `ln Γ` near `1` -/

theorem hasDerivAt_logGamma {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => Real.log (Real.Gamma t)) (psiR t) t :=
  hasDerivAt_log_Gamma_real ht

/-- `−ln Γ(x) ≤ γ(x − 1) − (3/5)(x − 1)²` for `1 ≤ x ≤ 3/2`. -/
theorem neg_log_Gamma_le_right {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 3 / 2) :
    -Real.log (Real.Gamma x) ≤ γ * (x - 1) - 3 / 5 * (x - 1) ^ 2 := by
  set h : ℝ → ℝ := fun t => Real.log (Real.Gamma t) + γ * (t - 1) - 3 / 5 * (t - 1) ^ 2 with hh
  have hd : ∀ t, 0 < t → HasDerivAt h (psiR t + γ - 6 / 5 * (t - 1)) t := by
    intro t ht
    have := ((hasDerivAt_logGamma ht).add (((hasDerivAt_id t).sub_const 1).const_mul γ)).sub
      ((((hasDerivAt_id t).sub_const 1).pow 2).const_mul (3 / 5))
    convert this using 1
    · funext s
      simp only [hh, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id]
    · simp
      ring
  have hmono : MonotoneOn h (Icc 1 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 1 x)
    · exact fun t ht => (hd t (by linarith [ht.1])).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      exact fun t ht => (hd t (by linarith [ht.1])).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hd t (by linarith [ht.1])).deriv]
      have := psiR_sub_one_ge ht.1.le (by linarith [ht.2])
      rw [psiR_one] at this
      linarith
  have := hmono (left_mem_Icc.mpr h1) (right_mem_Icc.mpr h1) h1
  simp only [hh, Real.Gamma_one, Real.log_one, sub_self, mul_zero, zero_add,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
  linarith

/-- `−ln Γ(y) ≤ −γ(1 − y) − (4/5)(1 − y)²` for `0 < y ≤ 1`. -/
theorem neg_log_Gamma_le_left {y : ℝ} (h0 : 0 < y) (h1 : y ≤ 1) :
    -Real.log (Real.Gamma y) ≤ -(γ * (1 - y)) - 4 / 5 * (1 - y) ^ 2 := by
  set h : ℝ → ℝ := fun t => Real.log (Real.Gamma t) - γ * (1 - t) - 4 / 5 * (1 - t) ^ 2 with hh
  have hd : ∀ t, 0 < t → HasDerivAt h (psiR t + γ + 8 / 5 * (1 - t)) t := by
    intro t ht
    have := ((hasDerivAt_logGamma ht).sub (((hasDerivAt_id t).const_sub 1).const_mul γ)).sub
      ((((hasDerivAt_id t).const_sub 1).pow 2).const_mul (4 / 5))
    convert this using 1
    · funext s
      simp only [hh, Pi.sub_apply, Pi.pow_apply, id]
    · simp
      ring
  have hanti : AntitoneOn h (Icc y 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc y 1)
    · exact fun t ht => (hd t (by linarith [ht.1])).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      exact fun t ht => (hd t (by linarith [ht.1])).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hd t (by linarith [ht.1])).deriv]
      have := psiR_one_sub_ge (by linarith [ht.1]) ht.2.le
      rw [psiR_one] at this
      linarith
  have := hanti (left_mem_Icc.mpr h1) (right_mem_Icc.mpr h1) h1
  simp only [hh, Real.Gamma_one, Real.log_one, sub_self, mul_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
  linarith

/-! ### The elementary inequality -/

theorem exp_add_exp_le_two {A B : ℝ} (h : (A + B) / 2 + ((A - B) / 2) ^ 2 / 2 ≤ 0) :
    Real.exp A + Real.exp B ≤ 2 := by
  set s := (A + B) / 2
  set d := (A - B) / 2
  have e : Real.exp A + Real.exp B = 2 * Real.exp s * Real.cosh d := by
    rw [Real.cosh_eq, show A = s + d by ring, show B = s + -d by ring, Real.exp_add,
      Real.exp_add]
    ring
  rw [e]
  calc 2 * Real.exp s * Real.cosh d ≤ 2 * Real.exp s * Real.exp (d ^ 2 / 2) := by
        gcongr; exact Real.cosh_le_exp_half_sq d
    _ = 2 * Real.exp (s + d ^ 2 / 2) := by rw [Real.exp_add]; ring
    _ ≤ 2 * Real.exp 0 := by gcongr
    _ = 2 := by simp

/-- The quartic `Q(ε, γ) ≤ 0` on `[0, ½]`. -/
theorem recip_poly_nonpos {e g : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 2) (hg0 : 0.57721 < g)
    (hg1 : g < 0.57722) :
    8 * g * (1 + e) ^ 3 - 4 * (6 / 5) * (1 + e) ^ 4 - 4 * (8 / 5) * (1 + e) ^ 2
      + (2 * g * (2 + e) * (1 + e) - 6 / 5 * e * (1 + e) ^ 2 + 8 / 5 * e) ^ 2 ≤ 0 := by
  nlinarith [mul_nonneg he0 (sub_nonneg.mpr he1),
    mul_nonneg (mul_nonneg he0 he0) (sub_nonneg.mpr he1), mul_nonneg (mul_nonneg he0 he0) he0,
    sq_nonneg (g - 0.57721), mul_pos (sub_pos.mpr hg0) (sub_pos.mpr hg1),
    mul_nonneg he0 (sub_pos.mpr hg0).le, mul_nonneg he0 (sub_pos.mpr hg1).le,
    mul_nonneg (mul_nonneg he0 he0) (sub_pos.mpr hg1).le]

theorem one_div_Gamma_sq_eq {x : ℝ} (hx : 0 < x) :
    1 / Real.Gamma x ^ 2 = Real.exp (2 * -Real.log (Real.Gamma x)) := by
  have hG := Real.Gamma_pos_of_pos hx
  rw [show 2 * -Real.log (Real.Gamma x) = -(2 * Real.log (Real.Gamma x)) by ring, Real.exp_neg,
    show 2 * Real.log (Real.Gamma x) = Real.log (Real.Gamma x ^ 2) by
      rw [Real.log_pow]; push_cast; ring,
    Real.exp_log (by positivity), one_div]

/-- The sum on `[1, 3/2]`. -/
theorem recip_sq_sum_le_two_of_le {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 3 / 2) :
    1 / Real.Gamma x ^ 2 + 1 / Real.Gamma (1 / x) ^ 2 ≤ 2 := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < 1 / x := by positivity
  have hy1 : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact h1
  set A := 2 * (γ * (x - 1) - 3 / 5 * (x - 1) ^ 2) with hA
  set B := 2 * (-(γ * (1 - 1 / x)) - 4 / 5 * (1 - 1 / x) ^ 2) with hB
  have hxA : 1 / Real.Gamma x ^ 2 ≤ Real.exp A := by
    rw [one_div_Gamma_sq_eq hx0, Real.exp_le_exp, hA]
    linarith [neg_log_Gamma_le_right h1 h2]
  have hyB : 1 / Real.Gamma (1 / x) ^ 2 ≤ Real.exp B := by
    rw [one_div_Gamma_sq_eq hy0, Real.exp_le_exp, hB]
    linarith [neg_log_Gamma_le_left hy0 hy1]
  refine (add_le_add hxA hyB).trans (exp_add_exp_le_two ?_)
  obtain ⟨hg0, hg1⟩ := dlmf_3_12_4_partial
  have hQ := recip_poly_nonpos (e := x - 1) (g := γ) (by linarith) (by linarith) hg0 hg1
  rw [show 1 + (x - 1) = x by ring, show 2 + (x - 1) = x + 1 by ring] at hQ
  have key : (A + B) / 2 + ((A - B) / 2) ^ 2 / 2
      = (x - 1) ^ 2 * (8 * γ * x ^ 3 - 4 * (6 / 5) * x ^ 4 - 4 * (8 / 5) * x ^ 2
        + (2 * γ * (x + 1) * x - 6 / 5 * (x - 1) * x ^ 2 + 8 / 5 * (x - 1)) ^ 2) / (8 * x ^ 4) := by
    rw [hA, hB]
    field_simp
    ring
  rw [key]
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hQ)
    (by positivity)

/-! ### Monotonicity for `x ≥ 3/2` -/

theorem log_Gamma_monotoneOn : MonotoneOn (fun t => Real.log (Real.Gamma t)) (Ici (3 / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · exact fun t ht =>
      (hasDerivAt_logGamma (by linarith [mem_Ici.mp ht])).continuousAt.continuousWithinAt
  · rw [interior_Ici]
    exact fun t ht =>
      (hasDerivAt_logGamma (by linarith [mem_Ioi.mp ht])).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro t ht
    have ht' := mem_Ioi.mp ht
    rw [(hasDerivAt_logGamma (by linarith)).deriv]
    have h32 : 0 < psiR (3 / 2) := digamma_three_halves_re_pos
    exact (h32.trans_le (psiR_mono (mem_Ioi.mpr (by norm_num)) (mem_Ioi.mpr (by linarith))
      ht'.le)).le

theorem log_Gamma_antitoneOn : AntitoneOn (fun t => Real.log (Real.Gamma t)) (Ioc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioc _ _)
  · exact fun t ht => (hasDerivAt_logGamma ht.1).continuousAt.continuousWithinAt
  · rw [interior_Ioc]
    exact fun t ht => (hasDerivAt_logGamma ht.1).differentiableAt.differentiableWithinAt
  · rw [interior_Ioc]
    intro t ht
    rw [(hasDerivAt_logGamma ht.1).deriv]
    have := psiR_mono (mem_Ioi.mpr ht.1) (mem_Ioi.mpr one_pos) ht.2.le
    rw [psiR_one] at this
    linarith [Real.one_half_lt_eulerMascheroniConstant]

theorem one_div_Gamma_sq_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : Real.log (Real.Gamma a) ≤ Real.log (Real.Gamma b)) :
    1 / Real.Gamma b ^ 2 ≤ 1 / Real.Gamma a ^ 2 := by
  rw [one_div_Gamma_sq_eq ha, one_div_Gamma_sq_eq hb, Real.exp_le_exp]
  linarith

/-! ### The main results -/

theorem recip_sq_sum_le_two_of_one_le {x : ℝ} (h1 : 1 ≤ x) :
    1 / Real.Gamma x ^ 2 + 1 / Real.Gamma (1 / x) ^ 2 ≤ 2 := by
  rcases le_or_gt x (3 / 2) with h2 | h2
  · exact recip_sq_sum_le_two_of_le h1 h2
  · have hx0 : 0 < x := by linarith
    have h32 := recip_sq_sum_le_two_of_le (x := 3 / 2) (by norm_num) le_rfl
    have hA := one_div_Gamma_sq_le (by norm_num) hx0
      (log_Gamma_monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr h2.le) h2.le)
    have hy : 1 / x ≤ 1 / (3 / 2) := one_div_le_one_div_of_le (by norm_num) h2.le
    have hB := one_div_Gamma_sq_le (a := 1 / (3 / 2)) (b := 1 / x) (by norm_num)
      (one_div_pos.mpr hx0) (log_Gamma_antitoneOn ⟨one_div_pos.mpr hx0, hy.trans (by norm_num)⟩
        ⟨by norm_num, by norm_num⟩ hy)
    linarith

/-- **DLMF 5.6.3**: `1/Γ(x)² + 1/Γ(1/x)² ≤ 2`, `x > 0`. -/
theorem dlmf_5_6_3 {x : ℝ} (hx : 0 < x) :
    1 / Real.Gamma x ^ 2 + 1 / Real.Gamma (1 / x) ^ 2 ≤ 2 := by
  rcases le_or_gt 1 x with h1 | h1
  · exact recip_sq_sum_le_two_of_one_le h1
  · have h := recip_sq_sum_le_two_of_one_le (x := 1 / x) (by rw [le_div_iff₀ hx]; linarith)
    rw [one_div_one_div] at h
    linarith

/-- **DLMF 5.6.2**: `1/Γ(x) + 1/Γ(1/x) ≤ 2`, `x > 0` (from 5.6.3). -/
theorem dlmf_5_6_2 {x : ℝ} (hx : 0 < x) : 1 / Real.Gamma x + 1 / Real.Gamma (1 / x) ≤ 2 := by
  have h := dlmf_5_6_3 hx
  have ha : 0 < 1 / Real.Gamma x := one_div_pos.mpr (Real.Gamma_pos_of_pos hx)
  have hb : 0 < 1 / Real.Gamma (1 / x) :=
    one_div_pos.mpr (Real.Gamma_pos_of_pos (by positivity))
  rw [show 1 / Real.Gamma x ^ 2 = (1 / Real.Gamma x) ^ 2 by rw [one_div_pow],
    show 1 / Real.Gamma (1 / x) ^ 2 = (1 / Real.Gamma (1 / x)) ^ 2 by rw [one_div_pow]] at h
  nlinarith [sq_nonneg (1 / Real.Gamma x - 1 / Real.Gamma (1 / x))]

end Azurite.DLMF
