/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section4Series
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Convex.Deriv

/-!
# DLMF §5.6: Inequalities

Formalizations of <https://dlmf.nist.gov/5.6>.

## §5.6(i) Real Variables (`x > 0`)

* 5.6.1, `1 < (2π)^{−1/2} x^{1/2−x} eˣ Γ(x) < e^{1/(12x)}` (`dlmf_5_6_1`): with
  `μ(x) = ln Γ(x) − (x − ½) ln x + x − ½ ln(2π)` (`stirlingMu`), `μ(x) − μ(x + 1) = g(x)` with
  `0 < g(t) < 1/(12t) − 1/(12(t + 1))` (`stirlingG_pos`, `stirlingG_lt`, from the series of
  `ln(1 + 1/t)`), and `μ(x + N) → 0` (`tendsto_stirlingMu`, from Mathlib's Stirling sequence and
  Bohr–Mollerup sequence).
* 5.6.2 and 5.6.3 (`1/Γ(x) + 1/Γ(1/x) ≤ 2`, `1/Γ(x)² + 1/Γ(1/x)² ≤ 2`): `dlmf_5_6_2`,
  `dlmf_5_6_3` in `Section6Reciprocal.lean`.
* 5.6.4 (Gautschi's inequality, `dlmf_5_6_4`), from the strict log-convexity of `Γ` on `(0, ∞)`
  (`strictConvexOn_log_Gamma`, since `ψ` is strictly increasing there, `psiR_strictMonoOn_pos`,
  by the limit form of 5.7.6).
* 5.6.5 (Kershaw's inequality, `dlmf_5_6_5`): `ln Γ(x + 1) − ln Γ(x + s) − (1 − s)ψ(x + c)` is
  `∑_k φ_c(x + k)` (`tendsto_kershaw_sum`), and the terms have a sign for `c = s^{1/2}` and
  `c = ½(s + 1)` because the logarithmic mean lies between the geometric and arithmetic means
  (`log_sub_log_le_div_sqrt`, `two_mul_div_le_log_sub_log`).

## §5.6(ii) Complex Variables

* 5.6.6, `|Γ(x + iy)| ≤ |Γ(x)|` (`dlmf_5_6_6`, `x` real, not a pole), and 5.6.7,
  `|Γ(x + iy)| ≥ (sech(πy))^{1/2} Γ(x)` for `x ≥ ½` (`dlmf_5_6_7`), both from Euler's limit
  `Γ(s) = lim nˢ n!/(s(s + 1)⋯(s + n))` (Mathlib's `GammaSeq`) termwise.
* 5.6.8 (`|Γ(z + a)/Γ(z + b)| ≤ |z|^{a−b}`) and 5.6.9 (the complex Stirling bound): DEFERRED to
  §5.11/§5.12 (they need a rotated Beta integral and Binet's/Stieltjes' error bound; plans in
  `docs/dlmf_plan.md`).
-/

open Complex Filter Topology Set Finset
open scoped Real Nat

namespace Azurite.DLMF

/-! ### §5.6(ii): `|Γ(x + iy)|` against `Γ(x)` -/

theorem norm_GammaSeq_eq {s : ℂ} {n : ℕ} (hn : 1 ≤ n) :
    ‖GammaSeq s n‖ = (n : ℝ) ^ s.re * n ! / ∏ j ∈ range (n + 1), ‖s + j‖ := by
  rw [GammaSeq, norm_div, norm_mul, norm_prod, norm_natCast_cpow_of_pos (by omega)]
  simp

theorem abs_GammaSeq_eq {x : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    |Real.GammaSeq x n| = (n : ℝ) ^ x * n ! / ∏ j ∈ range (n + 1), |x + j| := by
  rw [Real.GammaSeq, abs_div, abs_mul, abs_prod, abs_of_pos (Real.rpow_pos_of_pos
    (by exact_mod_cast (show 0 < n by omega)) x), Nat.abs_cast]

theorem prod_abs_pos {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) (n : ℕ) :
    0 < ∏ j ∈ range (n + 1), |x + j| :=
  prod_pos fun j _ => abs_pos.mpr fun h => hx j (by linarith)

theorem abs_add_le_norm (x y : ℝ) (j : ℕ) : |x + j| ≤ ‖((x : ℂ) + y * I) + j‖ := by
  have := abs_re_le_norm (((x : ℂ) + y * I) + j)
  simpa using this

/-- **DLMF 5.6.6**: `|Γ(x + iy)| ≤ |Γ(x)|`, `x` real (not a pole), `y` real. -/
theorem dlmf_5_6_6 {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) (y : ℝ) :
    ‖Gamma (x + y * I)‖ ≤ |Real.Gamma x| := by
  refine le_of_tendsto_of_tendsto (GammaSeq_tendsto_Gamma _).norm
    (Real.GammaSeq_tendsto_Gamma x).abs ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [norm_GammaSeq_eq hn, abs_GammaSeq_eq hn]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero]
  apply div_le_div_of_nonneg_left (by positivity) (prod_abs_pos hx n)
  exact prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => abs_add_le_norm x y j

theorem norm_mul_le_norm_mul {x y : ℝ} (hx : 1 / 2 ≤ x) (j : ℕ) :
    ‖((x : ℂ) + y * I) + j‖ * |(1 / 2 : ℝ) + j| ≤ ‖(((1 / 2 : ℝ) : ℂ) + y * I) + j‖ * |x + j| := by
  have e1 : ((x : ℂ) + y * I) + j = ((x + j : ℝ) : ℂ) + y * I := by push_cast; ring
  have e2 : (((1 / 2 : ℝ) : ℂ) + y * I) + j = ((1 / 2 + j : ℝ) : ℂ) + y * I := by push_cast; ring
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rw [e1, e2, norm_add_mul_I, norm_add_mul_I, abs_of_pos (by linarith),
    abs_of_pos (by linarith)]
  have hL : 0 ≤ √((x + j) ^ 2 + y ^ 2) * (1 / 2 + j) := by positivity
  have hR : 0 ≤ √((1 / 2 + j) ^ 2 + y ^ 2) * (x + j) := by
    have : (0 : ℝ) ≤ x + j := by linarith
    positivity
  apply (pow_le_pow_iff_left₀ hL hR two_ne_zero).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have h1 : (1 / 2 + (j : ℝ)) ^ 2 ≤ (x + j) ^ 2 := by nlinarith
  nlinarith [sq_nonneg y]

/-- **DLMF 5.6.7**: `|Γ(x + iy)| ≥ (sech(πy))^{1/2} Γ(x)`, `x ≥ ½`, `y` real. -/
theorem dlmf_5_6_7 {x : ℝ} (hx : 1 / 2 ≤ x) (y : ℝ) :
    √(1 / Real.cosh (π * y)) * Real.Gamma x ≤ ‖Gamma (x + y * I)‖ := by
  have hx0 : 0 < x := by linarith
  have hxp : ∀ m : ℕ, x ≠ -m := fun m h => by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  have hhp : ∀ m : ℕ, (1 / 2 : ℝ) ≠ -m := fun m h => by
    have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  -- `‖Γ(½ + iy)‖ Γ(x) ≤ ‖Γ(x + iy)‖ Γ(½)` from Euler's limit
  have key : ‖Gamma (((1 / 2 : ℝ) : ℂ) + y * I)‖ * |Real.Gamma x|
      ≤ ‖Gamma (x + y * I)‖ * |Real.Gamma (1 / 2)| := by
    refine le_of_tendsto_of_tendsto ((GammaSeq_tendsto_Gamma _).norm.mul
      (Real.GammaSeq_tendsto_Gamma x).abs) ((GammaSeq_tendsto_Gamma _).norm.mul
      (Real.GammaSeq_tendsto_Gamma (1 / 2)).abs) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [norm_GammaSeq_eq hn, norm_GammaSeq_eq hn, abs_GammaSeq_eq hn, abs_GammaSeq_eq hn]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    have hA := prod_abs_pos hxp n
    have hB := prod_abs_pos hhp n
    have hC : 0 < ∏ j ∈ range (n + 1), ‖((x : ℂ) + y * I) + j‖ :=
      lt_of_lt_of_le hA (prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => abs_add_le_norm x y j)
    have hD : 0 < ∏ j ∈ range (n + 1), ‖(((1 / 2 : ℝ) : ℂ) + y * I) + j‖ :=
      lt_of_lt_of_le hB (prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ =>
        abs_add_le_norm (1 / 2) y j)
    have hprod : (∏ j ∈ range (n + 1), ‖((x : ℂ) + y * I) + j‖)
          * ∏ j ∈ range (n + 1), |(1 / 2 : ℝ) + j|
        ≤ (∏ j ∈ range (n + 1), ‖(((1 / 2 : ℝ) : ℂ) + y * I) + j‖)
          * ∏ j ∈ range (n + 1), |x + j| := by
      rw [← prod_mul_distrib, ← prod_mul_distrib]
      exact prod_le_prod₀ (fun j _ => by positivity) fun j _ => norm_mul_le_norm_mul hx j
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [div_mul_div_comm, div_mul_div_comm, div_le_div_iff₀ (mul_pos hD hA) (mul_pos hC hB)]
    have hpos : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) * n ! * ((n : ℝ) ^ x * n !) := by positivity
    calc (n : ℝ) ^ (1 / 2 : ℝ) * n ! * ((n : ℝ) ^ x * n !)
          * ((∏ j ∈ range (n + 1), ‖((x : ℂ) + y * I) + j‖)
            * ∏ j ∈ range (n + 1), |(1 / 2 : ℝ) + j|)
        ≤ (n : ℝ) ^ (1 / 2 : ℝ) * n ! * ((n : ℝ) ^ x * n !)
          * ((∏ j ∈ range (n + 1), ‖(((1 / 2 : ℝ) : ℂ) + y * I) + j‖)
            * ∏ j ∈ range (n + 1), |x + j|) := mul_le_mul_of_nonneg_left hprod hpos
      _ = _ := by ring
  -- the values at `½`
  have hG2 : |Real.Gamma (1 / 2)| = √π := by
    rw [Real.Gamma_one_half_eq, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hnorm : ‖Gamma (((1 / 2 : ℝ) : ℂ) + y * I)‖ = √(π / Real.cosh (π * y)) := by
    have h1 := dlmf_5_4_4_norm y
    rw [dlmf_5_4_4 y] at h1
    have h2 : ‖Gamma (1 / 2 + I * y)‖ ^ 2 = π / Real.cosh (π * y) := by exact_mod_cast h1.symm
    rw [show ((1 / 2 : ℝ) : ℂ) + y * I = 1 / 2 + I * y by push_cast; ring, ← h2,
      Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm, hG2, abs_of_pos (Real.Gamma_pos_of_pos hx0)] at key
  have hsp : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  rw [show √(π / Real.cosh (π * y)) = √π * √(1 / Real.cosh (π * y)) by
    rw [← Real.sqrt_mul Real.pi_pos.le]; congr 1; ring] at key
  nlinarith

/-! ### `ψ` is strictly increasing; `ln Γ` is strictly convex -/

/-- `ψ` is strictly increasing on `(0, ∞)`. -/
theorem psiR_strictMonoOn_pos : StrictMonoOn psiR (Ioi 0) := by
  intro a ha b hb hab
  have ha0 := mem_Ioi.mp ha
  have hb0 := mem_Ioi.mp hb
  set S : ℕ → ℝ := fun N => ∑ k ∈ range N, (1 / (a + k) - 1 / (b + k)) with hS
  have hlim : Tendsto S atTop (𝓝 (psiR b - psiR a)) := by
    refine ((tendsto_psiR_series hb0).sub (tendsto_psiR_series ha0)).congr fun N => ?_
    simp only [hS, sum_sub_distrib]
    ring
  have hterm : ∀ k : ℕ, 0 ≤ 1 / (a + k) - 1 / (b + k) := fun k => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hmono : Monotone S := monotone_nat_of_le_succ fun N => by
    simp only [hS, sum_range_succ]
    linarith [hterm N]
  have h1 := hmono.ge_of_tendsto hlim 1
  simp only [hS, sum_range_one, Nat.cast_zero, add_zero] at h1
  have : 1 / b < 1 / a := one_div_lt_one_div_of_lt ha0 hab
  linarith

theorem deriv_log_Gamma {x : ℝ} (hx : 0 < x) : deriv (Real.log ∘ Real.Gamma) x = psiR x :=
  (hasDerivAt_log_Gamma_real hx).deriv

/-- `ln Γ` is strictly convex on `(0, ∞)`. -/
theorem strictConvexOn_log_Gamma : StrictConvexOn ℝ (Ioi 0) (Real.log ∘ Real.Gamma) := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi 0)
  · exact fun x hx => (hasDerivAt_log_Gamma_real (mem_Ioi.mp hx)).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro a ha b hb hab
    rw [deriv_log_Gamma (mem_Ioi.mp ha), deriv_log_Gamma (mem_Ioi.mp hb)]
    exact psiR_strictMonoOn_pos ha hb hab

theorem log_Gamma_add_one {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma (x + 1)) = Real.log x + Real.log (Real.Gamma x) := by
  rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']

/-- **DLMF 5.6.4** (Gautschi's inequality): `x^{1−s} < Γ(x + 1)/Γ(x + s) < (x + 1)^{1−s}`,
`x > 0`, `0 < s < 1`. -/
theorem dlmf_5_6_4 {x s : ℝ} (hx : 0 < x) (hs0 : 0 < s) (hs1 : s < 1) :
    x ^ (1 - s) < Real.Gamma (x + 1) / Real.Gamma (x + s) ∧
      Real.Gamma (x + 1) / Real.Gamma (x + s) < (x + 1) ^ (1 - s) := by
  have hc := strictConvexOn_log_Gamma
  have hxs : 0 < x + s := by linarith
  have hGs := Real.Gamma_pos_of_pos hxs
  have hG1 := Real.Gamma_pos_of_pos (show 0 < x + 1 by linarith)
  have hratio : Real.Gamma (x + 1) / Real.Gamma (x + s)
      = Real.exp (Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma (x + s))) := by
    rw [Real.exp_sub, Real.exp_log hG1, Real.exp_log hGs]
  constructor
  · -- `x + s = (1 − s) x + s (x + 1)`
    have h := hc.2 (mem_Ioi.mpr hx) (mem_Ioi.mpr (by linarith : (0 : ℝ) < x + 1))
      (by linarith : x ≠ x + 1) (by linarith : (0 : ℝ) < 1 - s) hs0 (by ring)
    simp only [smul_eq_mul, Function.comp] at h
    rw [show (1 - s) * x + s * (x + 1) = x + s by ring, log_Gamma_add_one hx] at h
    rw [hratio, Real.rpow_def_of_pos hx, Real.exp_lt_exp, log_Gamma_add_one hx]
    nlinarith
  · -- `x + 1 = s (x + s) + (1 − s)(x + s + 1)`
    have h := hc.2 (mem_Ioi.mpr hxs) (mem_Ioi.mpr (by linarith : (0 : ℝ) < x + s + 1))
      (by linarith : x + s ≠ x + s + 1) hs0 (by linarith : (0 : ℝ) < 1 - s) (by ring)
    simp only [smul_eq_mul, Function.comp] at h
    rw [show s * (x + s) + (1 - s) * (x + s + 1) = x + 1 by ring, log_Gamma_add_one hxs] at h
    rw [hratio]
    calc Real.exp (Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma (x + s)))
        < Real.exp ((1 - s) * Real.log (x + s)) := by rw [Real.exp_lt_exp]; nlinarith
      _ = (x + s) ^ (1 - s) := by rw [Real.rpow_def_of_pos hxs, mul_comm]
      _ < (x + 1) ^ (1 - s) := Real.rpow_lt_rpow hxs.le (by linarith) (by linarith)

/-! ### 5.6.1: Stirling's bounds -/

/-- `μ(x) = ln Γ(x) − (x − ½) ln x + x − ½ ln(2π)`. -/
noncomputable def stirlingMu (x : ℝ) : ℝ :=
  Real.log (Real.Gamma x) - (x - 1 / 2) * Real.log x + x - 1 / 2 * Real.log (2 * π)

/-- `g(t) = (t + ½) ln(1 + 1/t) − 1 = μ(t) − μ(t + 1)`. -/
noncomputable def stirlingG (t : ℝ) : ℝ := (t + 1 / 2) * Real.log (1 + 1 / t) - 1

theorem stirlingMu_sub {t : ℝ} (ht : 0 < t) : stirlingMu t - stirlingMu (t + 1) = stirlingG t := by
  unfold stirlingMu stirlingG
  rw [log_Gamma_add_one ht, show 1 + 1 / t = (t + 1) / t by field_simp,
    Real.log_div (by positivity) ht.ne']
  ring

/-- `g(t) = ∑_{k≥0} (u²)^{k+1}/(2k + 3)`, `u = 1/(2t + 1)`. -/
theorem hasSum_stirlingG {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ => ((1 / (2 * t + 1)) ^ 2) ^ (k + 1) / (2 * (k : ℝ) + 3)) (stirlingG t) := by
  have h := (Real.hasSum_log_one_add_inv ht).mul_left (t + 1 / 2)
  have hone : (t + 1 / 2) * 2 * (1 / (2 * t + 1)) = 1 := by field_simp
  have hterm : ∀ k : ℕ,
      (t + 1 / 2) * (2 * (1 / (2 * (k : ℝ) + 1)) * (1 / (2 * t + 1)) ^ (2 * k + 1))
        = ((1 / (2 * t + 1)) ^ 2) ^ k / (2 * (k : ℝ) + 1) := by
    intro k
    rw [pow_succ, pow_mul]
    calc (t + 1 / 2)
          * (2 * (1 / (2 * (k : ℝ) + 1)) * (((1 / (2 * t + 1)) ^ 2) ^ k * (1 / (2 * t + 1))))
        = ((t + 1 / 2) * 2 * (1 / (2 * t + 1)))
          * (((1 / (2 * t + 1)) ^ 2) ^ k / (2 * (k : ℝ) + 1)) := by ring
      _ = _ := by rw [hone, one_mul]
  simp only [hterm] at h
  rw [show (1 : ℝ) + t⁻¹ = 1 + 1 / t by rw [one_div]] at h
  have h2 := (hasSum_nat_add_iff' 1).mpr h
  simp only [sum_range_one, pow_zero, Nat.cast_zero, mul_zero, zero_add, div_one] at h2
  unfold stirlingG
  convert h2 using 1
  funext k
  push_cast
  ring_nf

theorem stirlingG_pos {t : ℝ} (ht : 0 < t) : 0 < stirlingG t := by
  have h := hasSum_stirlingG ht
  have hu : 0 < 1 / (2 * t + 1) := by positivity
  have := sum_le_hasSum (range 1) (fun k _ => by positivity) h
  simp only [sum_range_one, Nat.cast_zero, mul_zero, zero_add, pow_one] at this
  have h0 : 0 < (1 / (2 * t + 1)) ^ 2 / 3 := by positivity
  linarith

theorem stirlingG_lt {t : ℝ} (ht : 0 < t) : stirlingG t < 1 / (12 * t) - 1 / (12 * (t + 1)) := by
  set u := 1 / (2 * t + 1) with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u < 1 := by rw [hu, div_lt_one (by linarith)]; linarith
  have hr0 : 0 ≤ u ^ 2 := by positivity
  have hr1 : u ^ 2 < 1 := by nlinarith
  have hgeo := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (u ^ 2 / 3)
  have hlt := hasSum_lt (f := fun k : ℕ => (u ^ 2) ^ (k + 1) / (2 * (k : ℝ) + 3))
    (g := fun k : ℕ => u ^ 2 / 3 * (u ^ 2) ^ k) (i := 1)
    (fun k => by
      show (u ^ 2) ^ (k + 1) / (2 * (k : ℝ) + 3) ≤ u ^ 2 / 3 * (u ^ 2) ^ k
      rw [pow_succ, div_le_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have : 0 ≤ (u ^ 2) ^ k * u ^ 2 := by positivity
      nlinarith)
    (by
      show (u ^ 2) ^ (1 + 1) / (2 * ((1 : ℕ) : ℝ) + 3) < u ^ 2 / 3 * (u ^ 2) ^ 1
      have : 0 < u ^ 4 := by positivity
      push_cast
      nlinarith)
    (hasSum_stirlingG ht) hgeo
  refine hlt.trans_le (le_of_eq ?_)
  have h1 : 1 - u ^ 2 = 4 * t * (t + 1) / (2 * t + 1) ^ 2 := by rw [hu]; field_simp; ring
  have ht1 : t + 1 ≠ 0 := by positivity
  have ht2 : 2 * t + 1 ≠ 0 := by positivity
  rw [h1, hu]
  field_simp
  ring

/-- `ln Γ(x + N) = ln Γ(x) + ∑_{k<N} ln(x + k)`. -/
theorem log_Gamma_add_nat {x : ℝ} (hx : 0 < x) (N : ℕ) :
    Real.log (Real.Gamma (x + N)) = Real.log (Real.Gamma x) + ∑ k ∈ range N, Real.log (x + k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.cast_succ, ← add_assoc, log_Gamma_add_one (by positivity), ih, sum_range_succ]
    ring

/-- `μ(x) = ∑_{k<N} g(x + k) + μ(x + N)`. -/
theorem stirlingMu_eq_sum {x : ℝ} (hx : 0 < x) (N : ℕ) :
    stirlingMu x = ∑ k ∈ range N, stirlingG (x + k) + stirlingMu (x + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, sum_range_succ, show x + ((N + 1 : ℕ) : ℝ) = x + N + 1 by push_cast; ring,
      ← stirlingMu_sub (show 0 < x + N by positivity)]
    ring

/-- The decomposition of `μ(x + N)` into three vanishing parts. -/
theorem stirlingMu_add_nat_eq {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) :
    stirlingMu (x + N)
      = (Real.log (Real.Gamma x) - Real.BohrMollerup.logGammaSeq x N)
        + (Real.log (Stirling.stirlingSeq N) - 1 / 2 * Real.log π)
        + (-((N : ℝ) * Real.log (1 + x / N)) - (x + 1 / 2) * Real.log (1 + x / N) + x) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold stirlingMu Real.BohrMollerup.logGammaSeq
  rw [log_Gamma_add_nat hx, Stirling.log_stirlingSeq_formula, sum_range_succ,
    show 1 + x / N = (x + N) / N by field_simp; ring, Real.log_div (by positivity) hN0.ne',
    Real.log_div hN0.ne' (Real.exp_pos 1).ne', Real.log_exp, Real.log_mul two_ne_zero hN0.ne',
    Real.log_mul two_ne_zero Real.pi_ne_zero]
  ring

theorem tendsto_stirlingMu {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ => stirlingMu (x + N)) atTop (𝓝 0) := by
  -- the Bohr–Mollerup sequence
  have h1 : Tendsto (fun N : ℕ => Real.log (Real.Gamma x) - Real.BohrMollerup.logGammaSeq x N)
      atTop (𝓝 0) := by
    have := Real.BohrMollerup.tendsto_logGammaSeq Real.convexOn_log_Gamma
      (fun {y} hy => by simp only [Function.comp]; rw [log_Gamma_add_one hy]; ring) hx
    simp only [Function.comp, Real.Gamma_one, Real.log_one, sub_zero] at this
    have h := (tendsto_const_nhds (x := Real.log (Real.Gamma x))).sub this
    rwa [sub_self] at h
  -- Stirling's sequence
  have h2 : Tendsto (fun N : ℕ => Real.log (Stirling.stirlingSeq N) - 1 / 2 * Real.log π)
      atTop (𝓝 0) := by
    have := ((Real.continuousAt_log (Real.sqrt_pos.mpr Real.pi_pos).ne').tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi).sub_const (1 / 2 * Real.log π)
    rw [Real.log_sqrt Real.pi_pos.le, show Real.log π / 2 - 1 / 2 * Real.log π = 0 by ring]
      at this
    exact this
  -- `N ln(1 + x/N) → x`
  have h3 : Tendsto (fun N : ℕ => -((N : ℝ) * Real.log (1 + x / N))
      - (x + 1 / 2) * Real.log (1 + x / N) + x) atTop (𝓝 0) := by
    have hA := (Real.tendsto_mul_log_one_add_div_atTop x).comp tendsto_natCast_atTop_atTop
    have hB : Tendsto (fun N : ℕ => Real.log (1 + x / N)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun N : ℕ => 1 + x / (N : ℝ)) atTop (𝓝 (1 + 0)) :=
        (tendsto_const_div_atTop_nhds_zero_nat x).const_add 1
      rw [add_zero] at h0
      have := (Real.continuousAt_log one_ne_zero).tendsto.comp h0
      rwa [Real.log_one] at this
    have := ((hA.neg).sub (hB.const_mul (x + 1 / 2))).add_const x
    rw [mul_zero, sub_zero, neg_add_cancel] at this
    exact this
  have h := (h1.add h2).add h3
  rw [add_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [stirlingMu_add_nat_eq hx hN]

theorem stirlingMu_bounds {x : ℝ} (hx : 0 < x) :
    0 ≤ stirlingMu x ∧ stirlingMu x ≤ 1 / (12 * x) := by
  have hlim : Tendsto (fun N : ℕ => ∑ k ∈ range N, stirlingG (x + k)) atTop (𝓝 (stirlingMu x)) := by
    have h := (tendsto_const_nhds (x := stirlingMu x)).sub (tendsto_stirlingMu hx)
    rw [sub_zero] at h
    refine h.congr fun N => ?_
    rw [stirlingMu_eq_sum hx N]
    ring
  have htel : ∀ N : ℕ, ∑ k ∈ range N, (1 / (12 * (x + k)) - 1 / (12 * (x + k + 1)))
      = 1 / (12 * x) - 1 / (12 * (x + N)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring
  constructor
  · refine ge_of_tendsto hlim (Eventually.of_forall fun N => ?_)
    exact sum_nonneg fun k _ => (stirlingG_pos (by positivity)).le
  · refine le_of_tendsto hlim (Eventually.of_forall fun N => ?_)
    calc ∑ k ∈ range N, stirlingG (x + k)
        ≤ ∑ k ∈ range N, (1 / (12 * (x + k)) - 1 / (12 * (x + k + 1))) :=
          sum_le_sum fun k _ => (stirlingG_lt (by positivity)).le
      _ = 1 / (12 * x) - 1 / (12 * (x + N)) := htel N
      _ ≤ 1 / (12 * x) := by
          have : 0 ≤ 1 / (12 * (x + N)) := by positivity
          linarith

theorem stirlingMu_strict {x : ℝ} (hx : 0 < x) :
    0 < stirlingMu x ∧ stirlingMu x < 1 / (12 * x) := by
  have h := stirlingMu_eq_sum hx 1
  simp only [sum_range_one, Nat.cast_zero, add_zero, Nat.cast_one] at h
  obtain ⟨h0, h1⟩ := stirlingMu_bounds (show 0 < x + 1 by linarith)
  have hg0 := stirlingG_pos hx
  have hg1 := stirlingG_lt hx
  constructor <;> linarith

/-- **DLMF 5.6.1**: `1 < (2π)^{−1/2} x^{1/2−x} eˣ Γ(x) < e^{1/(12x)}`, `x > 0`. -/
theorem dlmf_5_6_1 {x : ℝ} (hx : 0 < x) :
    1 < (2 * π) ^ (-(1 / 2) : ℝ) * x ^ (1 / 2 - x) * Real.exp x * Real.Gamma x ∧
      (2 * π) ^ (-(1 / 2) : ℝ) * x ^ (1 / 2 - x) * Real.exp x * Real.Gamma x
        < Real.exp (1 / (12 * x)) := by
  have he : (2 * π) ^ (-(1 / 2) : ℝ) * x ^ (1 / 2 - x) * Real.exp x * Real.Gamma x
      = Real.exp (stirlingMu x) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos hx,
      ← Real.exp_log (Real.Gamma_pos_of_pos hx), ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
      stirlingMu]
    congr 1
    ring
  rw [he]
  obtain ⟨h0, h1⟩ := stirlingMu_strict hx
  refine ⟨?_, Real.exp_lt_exp.mpr h1⟩
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr h0

/-! ### 5.6.5: Kershaw's inequality -/

/-- The logarithmic mean is at least the geometric mean: `ln b − ln a ≤ (b − a)/√(ab)`,
`0 < a ≤ b`. -/
theorem log_sub_log_le_div_sqrt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log b - Real.log a ≤ (b - a) / √(a * b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set w := (Real.log b - Real.log a) / 2 with hw
  have hw0 : 0 ≤ w := by rw [hw]; linarith [Real.log_le_log ha hab]
  have hsa : Real.exp (Real.log a / 2) = √a := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ha]; ring_nf
  have hsb : Real.exp (Real.log b / 2) = √b := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hb]; ring_nf
  have hew : Real.exp w = √b / √a := by
    rw [hw, show (Real.log b - Real.log a) / 2 = Real.log b / 2 - Real.log a / 2 by ring,
      Real.exp_sub, hsa, hsb]
  have hemw : Real.exp (-w) = √a / √b := by
    rw [Real.exp_neg, hew, inv_div]
  have hsinh : 2 * Real.sinh w = (b - a) / √(a * b) := by
    rw [Real.sinh_eq, hew, hemw, Real.sqrt_mul ha.le]
    have hsa0 : 0 < √a := Real.sqrt_pos.mpr ha
    have hsb0 : 0 < √b := Real.sqrt_pos.mpr hb
    field_simp
    rw [Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
  have := Real.self_le_sinh_iff.mpr hw0
  linarith

/-- The logarithmic mean is at most the arithmetic mean: `2(b − a)/(a + b) ≤ ln b − ln a`,
`0 < a ≤ b`. -/
theorem two_mul_div_le_log_sub_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    2 * (b - a) / (a + b) ≤ Real.log b - Real.log a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set u := (b - a) / (a + b) with hu
  have hu0 : 0 ≤ u := by rw [hu]; exact div_nonneg (by linarith) (by linarith)
  have hu1 : u < 1 := by rw [hu, div_lt_one (by linarith)]; linarith
  have h := Real.hasSum_log_sub_log_of_abs_lt_one
    (show |u| < 1 by rw [abs_of_nonneg hu0]; exact hu1)
  have hle := sum_le_hasSum (range 1) (fun k _ => by positivity) h
  simp only [sum_range_one, Nat.cast_zero, mul_zero, zero_add, div_one, pow_one, mul_one] at hle
  have h1 : 1 + u = 2 * b / (a + b) := by rw [hu]; field_simp; ring
  have h2 : 1 - u = 2 * a / (a + b) := by rw [hu]; field_simp; ring
  rw [h1, h2, Real.log_div (by positivity) (by positivity), Real.log_div (by positivity)
    (by positivity), Real.log_mul two_ne_zero hb.ne', Real.log_mul two_ne_zero ha.ne'] at hle
  rw [mul_div_assoc]
  linarith

/-- The terms `φ_c(y) = (1 − s)/(y + c) − (ln(y + 1) − ln(y + s))`. -/
noncomputable def kershawPhi (s c y : ℝ) : ℝ :=
  (1 - s) / (y + c) - (Real.log (y + 1) - Real.log (y + s))

theorem kershawPhi_sqrt_nonneg {s y : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hy : 0 < y) :
    0 ≤ kershawPhi s (√s) y := by
  unfold kershawPhi
  have h := log_sub_log_le_div_sqrt (show 0 < y + s by linarith) (show y + s ≤ y + 1 by linarith)
  have hss : √s * √s = s := Real.mul_self_sqrt hs0.le
  have hs' : 0 ≤ √s := Real.sqrt_nonneg s
  have hge : y + √s ≤ √((y + s) * (y + 1)) := by
    rw [show y + √s = √((y + √s) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    have : 0 ≤ y * (1 - √s) ^ 2 := by positivity
    nlinarith
  have hpos : 0 < y + √s := by positivity
  have : (y + 1 - (y + s)) / √((y + s) * (y + 1)) ≤ (1 - s) / (y + √s) := by
    rw [show y + 1 - (y + s) = 1 - s by ring]
    exact div_le_div_of_nonneg_left (by linarith) hpos hge
  linarith

theorem kershawPhi_mid_nonpos {s y : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hy : 0 < y) :
    kershawPhi s ((s + 1) / 2) y ≤ 0 := by
  unfold kershawPhi
  have h := two_mul_div_le_log_sub_log (show 0 < y + s by linarith)
    (show y + s ≤ y + 1 by linarith)
  have : (1 - s) / (y + (s + 1) / 2) = 2 * (y + 1 - (y + s)) / (y + s + (y + 1)) := by
    field_simp; ring
  rw [this]
  linarith

/-- `ln Γ(x + 1) − ln Γ(x + s) − (1 − s)ψ(x + c) = lim ∑_{k<N} φ_c(x + k)`. -/
theorem tendsto_kershaw_sum {x s c : ℝ} (hx : 0 < x) (hs0 : 0 < s) (hc : 0 < c) :
    Tendsto (fun N : ℕ => ∑ k ∈ range N, kershawPhi s c (x + k)) atTop
      (𝓝 (Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma (x + s))
        - (1 - s) * psiR (x + c))) := by
  have hBM : ∀ {y : ℝ}, 0 < y →
      Tendsto (Real.BohrMollerup.logGammaSeq y) atTop (𝓝 (Real.log (Real.Gamma y))) := by
    intro y hy
    have := Real.BohrMollerup.tendsto_logGammaSeq Real.convexOn_log_Gamma
      (fun {y} hy => by simp only [Function.comp]; rw [log_Gamma_add_one hy]; ring) hy
    simpa only [Function.comp, Real.Gamma_one, Real.log_one, sub_zero] using this
  have hD := ((hBM (show 0 < x + 1 by linarith)).sub (hBM (show 0 < x + s by linarith))).sub
    ((tendsto_psiR_series (show 0 < x + c by linarith)).const_mul (1 - s))
  have hE : Tendsto (fun N : ℕ => Real.log (x + 1 + N) - Real.log (x + s + N)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => (x + 1 + N) / (x + s + N)) atTop (𝓝 1) := by
      have h1 : Tendsto (fun N : ℕ => (1 - s) / (x + s + N)) atTop (𝓝 0) := by
        have := ((tendsto_atTop_add_const_left atTop (x + s)
          (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop).const_mul (1 - s)
        rw [mul_zero] at this
        exact this.congr fun N => by rw [div_eq_mul_inv]; rfl
      have := h1.const_add 1
      rw [add_zero] at this
      refine this.congr fun N => ?_
      have : (0 : ℝ) < x + s + N := by positivity
      field_simp
      ring
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp h0
    rw [Real.log_one] at this
    refine this.congr fun N => ?_
    simp only [Function.comp]
    rw [Real.log_div (by positivity) (by positivity)]
  have h := hD.add hE
  rw [add_zero] at h
  refine h.congr fun N => ?_
  simp only [Real.BohrMollerup.logGammaSeq, kershawPhi, sum_range_succ, sum_sub_distrib]
  have : ∀ k ∈ range N, (1 - s) / (x + k + c) = (1 - s) * (1 / (x + c + k)) := fun k _ => by
    rw [show x + k + c = x + c + k by ring]; ring
  rw [sum_congr rfl this, ← mul_sum]
  have e1 : ∀ m : ℕ, Real.log (x + 1 + m) = Real.log (x + m + 1) := fun m => by ring_nf
  have e2 : ∀ m : ℕ, Real.log (x + s + m) = Real.log (x + m + s) := fun m => by ring_nf
  simp only [e1, e2]
  ring

/-- **DLMF 5.6.5** (Kershaw's inequality):
`exp((1 − s)ψ(x + s^{1/2})) ≤ Γ(x + 1)/Γ(x + s) ≤ exp((1 − s)ψ(x + ½(s + 1)))`, `x > 0`,
`0 < s < 1` (`psiR` is `ψ` on the real line). -/
theorem dlmf_5_6_5 {x s : ℝ} (hx : 0 < x) (hs0 : 0 < s) (hs1 : s < 1) :
    Real.exp ((1 - s) * psiR (x + √s)) ≤ Real.Gamma (x + 1) / Real.Gamma (x + s) ∧
      Real.Gamma (x + 1) / Real.Gamma (x + s) ≤ Real.exp ((1 - s) * psiR (x + (s + 1) / 2)) := by
  have hGs := Real.Gamma_pos_of_pos (show 0 < x + s by linarith)
  have hG1 := Real.Gamma_pos_of_pos (show 0 < x + 1 by linarith)
  have hratio : Real.Gamma (x + 1) / Real.Gamma (x + s)
      = Real.exp (Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma (x + s))) := by
    rw [Real.exp_sub, Real.exp_log hG1, Real.exp_log hGs]
  rw [hratio]
  constructor
  · rw [Real.exp_le_exp]
    have hlim := tendsto_kershaw_sum hx hs0 (Real.sqrt_pos.mpr hs0)
    have := ge_of_tendsto hlim (Eventually.of_forall fun N =>
      sum_nonneg fun k _ => kershawPhi_sqrt_nonneg hs0 hs1 (by positivity))
    linarith
  · rw [Real.exp_le_exp]
    have hlim := tendsto_kershaw_sum hx hs0 (show 0 < (s + 1) / 2 by linarith)
    have := le_of_tendsto hlim (Eventually.of_forall fun N =>
      sum_nonpos fun k _ => kershawPhi_mid_nonpos hs0 hs1 (by positivity))
    linarith

end Azurite.DLMF

