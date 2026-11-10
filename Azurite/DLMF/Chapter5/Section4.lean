/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section3
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# DLMF §5.4: Special Values and Extrema

Formalizations of <https://dlmf.nist.gov/5.4>.  `Γ` is `Complex.Gamma` / `Real.Gamma`, `ψ` is
`Complex.digamma`, `ψ′` is `deriv digamma`, `n!!` is `Nat.doubleFactorial`, `coth` and `tanh`
are written `cosh/sinh` and `Real.tanh`.

## §5.4(i) Gamma Function

* 5.4.1 (`dlmf_5_4_1_one`, `dlmf_5_4_1`), 5.4.2 (`dlmf_5_4_2_even`, `dlmf_5_4_2_odd`, and "the
  second line … also applies when `n = −1`", `dlmf_5_4_2_neg_one`, DLMF's `(−1)!! = 1`).
* 5.4.3, `|Γ(iy)| = (π/(y sinh(πy)))^{1/2}` (`dlmf_5_4_3`; at `y = 0` both sides are `0` with
  Mathlib's junk values), from `Γ(iy) Γ(−iy) = π/(y sinh(πy))` (`Gamma_I_mul_Gamma_neg_I_mul`).
* 5.4.4 (`dlmf_5_4_4`, `dlmf_5_4_4_norm`), 5.4.5 (`dlmf_5_4_5`), from the reflection formula.
* 5.4.6, `Γ(½) = π^{1/2}` (`dlmf_5_4_6`).  Its 20 decimals `1.77245 38509 05516 02729…` and the
  values 5.4.7–5.4.10 (`Γ(⅓)`, `Γ(⅔)`, `Γ(¼)`, `Γ(¾)` to 20 decimals) are numerical: NOTED for a
  later backfill (`docs/dlmf_plan.md`).
* 5.4.11, `Γ′(1) = −γ` (`dlmf_5_4_11`, `dlmf_5_4_11_real`).

## §5.4(ii) Psi Function

* 5.4.12, `ψ(1) = −γ`, `ψ′(1) = π²/6` (`dlmf_5_4_12`, `dlmf_5_4_12_deriv`); 5.4.13,
  `ψ(½) = −γ − 2 ln 2`, `ψ′(½) = π²/2` (`dlmf_5_4_13`, `dlmf_5_4_13_deriv`).  The derivatives
  come from differentiating the reflection formula at `½` (`ψ′(½) + ψ′(½) = π²/sin²(π/2)`) and
  the duplication formula at `½` (`2ψ′(1) = ½(ψ′(½) + ψ′(1))`).
* 5.4.14 (`dlmf_5_4_14`), 5.4.15 (`dlmf_5_4_15`, every `n ≥ 0`).
* 5.4.16–5.4.18, the imaginary parts on the lines `ℜz = 0, ½, 1` (`dlmf_5_4_16`,
  `dlmf_5_4_17`, `dlmf_5_4_18`; `y ≠ 0` where `1/(2y)` and `coth` appear), from the reflection
  formula, the recurrence and `ψ(z̄) = conj ψ(z)` (`digamma_conj`, §5.3).
* 5.4.19 (Gauss's digamma theorem): `dlmf_5_4_19` in `Section4Gauss.lean`, from the limit form
  of 5.7.6 (`tendsto_psiR_series`, `Section4Series.lean`).

## §5.4(iii) Extrema

* The zeros `xₙ` of `ψ` (= of `Γ′`) on the negative axis, one in each `(−n, −n + 1)`, and 5.4.20
  (`xₙ = −n + π⁻¹ arctan(π/ln n) + O(1/(n (ln n)²))`, with the explicit constant `4` for
  `n ≥ 3`): `Section4Zeros.lean` (`dlmf_5_4_iii_zero`, `dlmf_5_4_iii_all`, `dlmf_5_4_20`,
  `dlmf_5_4_20_bound`).
* Table 5.4.1 (`xₙ`, `Γ(xₙ)` for `n = 0, …, 10` to 20 decimals): numerical, NOTED for a later
  backfill; the row `n = 0` is the minimum `x₀` of §5.3 (`dlmf_5_3_F1_min`, `ψ(x₀) = 0`).
-/

open Complex Filter Topology Set
open scoped Real ComplexConjugate Nat

namespace Azurite.DLMF

/-! ### §5.4(i): Gamma function -/

/-- **DLMF 5.4.1**: `Γ(1) = 1`. -/
theorem dlmf_5_4_1_one : Gamma 1 = 1 := Gamma_one

/-- **DLMF 5.4.1**: `n! = Γ(n + 1)`. -/
theorem dlmf_5_4_1 (n : ℕ) : (n ! : ℂ) = Gamma (n + 1) := (Gamma_nat_eq_factorial n).symm

/-- **DLMF 5.4.2**, `n` even: `n!! = 2^{n/2} Γ(½n + 1)`. -/
theorem dlmf_5_4_2_even {n : ℕ} (hn : Even n) :
    ((n‼ : ℕ) : ℝ) = 2 ^ ((n : ℝ) / 2) * Real.Gamma ((n : ℝ) / 2 + 1) := by
  obtain ⟨m, rfl⟩ := hn
  rw [show m + m = 2 * m by ring, Nat.doubleFactorial_two_mul,
    show ((2 * m : ℕ) : ℝ) / 2 = (m : ℕ) by push_cast; ring, Real.rpow_natCast,
    Real.Gamma_nat_eq_factorial]
  push_cast
  ring

theorem rpow_neg_half_mul_sqrt_pi : π ^ (-(1 / 2 : ℝ)) * √π = 1 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos]
  norm_num

/-- **DLMF 5.4.2**, `n` odd: `n!! = π^{−1/2} 2^{(n+1)/2} Γ(½n + 1)`. -/
theorem dlmf_5_4_2_odd {n : ℕ} (hn : Odd n) :
    ((n‼ : ℕ) : ℝ)
      = π ^ (-(1 / 2 : ℝ)) * 2 ^ (((n : ℝ) + 1) / 2) * Real.Gamma ((n : ℝ) / 2 + 1) := by
  obtain ⟨m, rfl⟩ := hn
  rw [show ((2 * m + 1 : ℕ) : ℝ) / 2 + 1 = (m : ℝ) + 1 + 1 / 2 by push_cast; ring,
    show (((2 * m + 1 : ℕ) : ℝ) + 1) / 2 = ((m + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, Real.Gamma_nat_add_one_add_half]
  have h2 : (2 : ℝ) ^ (m + 1) ≠ 0 := by positivity
  have e : π ^ (-(1 / 2 : ℝ)) * 2 ^ (m + 1) * (((2 * m + 1)‼ : ℕ) * √π / 2 ^ (m + 1))
      = (π ^ (-(1 / 2 : ℝ)) * √π) * ((2 * m + 1)‼ : ℕ) := by
    field_simp
  rw [e, rpow_neg_half_mul_sqrt_pi, one_mul]

/-- **DLMF 5.4.2**: "The second line of Formula (5.4.2) also applies when `n = −1`", with DLMF's
convention `(−1)!! = 1`. -/
theorem dlmf_5_4_2_neg_one :
    π ^ (-(1 / 2 : ℝ)) * (2 : ℝ) ^ (((-1 : ℝ) + 1) / 2) * Real.Gamma ((-1 : ℝ) / 2 + 1) = 1 := by
  rw [show ((-1 : ℝ) + 1) / 2 = 0 by norm_num, Real.rpow_zero, mul_one,
    show (-1 : ℝ) / 2 + 1 = 1 / 2 by norm_num, Real.Gamma_one_half_eq, rpow_neg_half_mul_sqrt_pi]

/-- `Γ(iy) Γ(−iy) = π/(y sinh(πy))`, `y ≠ 0`. -/
theorem Gamma_I_mul_Gamma_neg_I_mul {y : ℝ} (hy : y ≠ 0) :
    Gamma (I * y) * Gamma (-(I * y)) = ((π / (y * Real.sinh (π * y)) : ℝ) : ℂ) := by
  have hz : -(I * (y : ℂ)) ≠ 0 := by
    simp [hy]
  have hsh : Real.sinh (π * y) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero hy
  have hr := Gamma_mul_Gamma_one_sub (I * y)
  rw [show (1 : ℂ) - I * y = -(I * y) + 1 by ring, Gamma_add_one _ hz,
    show (π : ℂ) * (I * y) = ((π * y : ℝ) : ℂ) * I by push_cast; ring, sin_mul_I,
    ← ofReal_sinh] at hr
  set G := Gamma (I * y) * Gamma (-(I * y)) with hG
  have key : (-(I * (y : ℂ))) * G = π / ((Real.sinh (π * y) : ℂ) * I) := by
    rw [← hr, hG]; ring
  have k2 : G * ((y : ℂ) * (Real.sinh (π * y) : ℂ)) = π := by
    have h := congrArg (· * ((Real.sinh (π * y) : ℂ) * I)) key
    beta_reduce at h
    rw [div_mul_cancel₀ _ (mul_ne_zero (ofReal_ne_zero.mpr hsh) I_ne_zero)] at h
    linear_combination h + G * y * (Real.sinh (π * y) : ℂ) * I_sq
  rw [ofReal_div, ofReal_mul, eq_div_iff (mul_ne_zero (ofReal_ne_zero.mpr hy)
    (ofReal_ne_zero.mpr hsh))]
  exact k2

theorem conj_I_mul_ofReal (y : ℝ) : conj (I * (y : ℂ)) = -(I * y) := by
  simp

/-- **DLMF 5.4.3**: `|Γ(iy)| = (π/(y sinh(πy)))^{1/2}`, `y` real (at `y = 0` both sides are `0`
with Mathlib's junk values `Γ(0) = 0`, `π/0 = 0`). -/
theorem dlmf_5_4_3 (y : ℝ) : ‖Gamma (I * y)‖ = √(π / (y * Real.sinh (π * y))) := by
  by_cases hy : y = 0
  · simp [hy, Gamma_zero]
  have h := Gamma_I_mul_Gamma_neg_I_mul hy
  rw [← conj_I_mul_ofReal, Gamma_conj, mul_conj, normSq_eq_norm_sq] at h
  have h' : ‖Gamma (I * y)‖ ^ 2 = π / (y * Real.sinh (π * y)) := by exact_mod_cast h
  rw [← h', Real.sqrt_sq (norm_nonneg _)]

/-- **DLMF 5.4.4**: `Γ(½ + iy) Γ(½ − iy) = π/cosh(πy)`, `y` real. -/
theorem dlmf_5_4_4 (y : ℝ) :
    Gamma (1 / 2 + I * y) * Gamma (1 / 2 - I * y) = ((π / Real.cosh (π * y) : ℝ) : ℂ) := by
  have hr := Gamma_mul_Gamma_one_sub (1 / 2 + I * y)
  rw [show (1 : ℂ) - (1 / 2 + I * y) = 1 / 2 - I * y by ring,
    show (π : ℂ) * (1 / 2 + I * y) = π / 2 + ((π * y : ℝ) : ℂ) * I by push_cast; ring,
    sin_add, sin_pi_div_two, cos_pi_div_two, cos_mul_I, ← ofReal_cosh] at hr
  rw [hr]
  push_cast
  ring

/-- **DLMF 5.4.4**: `Γ(½ + iy) Γ(½ − iy) = |Γ(½ + iy)|²`. -/
theorem dlmf_5_4_4_norm (y : ℝ) :
    Gamma (1 / 2 + I * y) * Gamma (1 / 2 - I * y) = ((‖Gamma (1 / 2 + I * y)‖ ^ 2 : ℝ) : ℂ) := by
  have hc : conj (1 / 2 + I * (y : ℂ)) = 1 / 2 - I * y := by
    apply Complex.ext <;> simp
  rw [← hc, Gamma_conj, mul_conj, normSq_eq_norm_sq]

/-- **DLMF 5.4.5**: `Γ(¼ + iy) Γ(¾ − iy) = π √2 / (cosh(πy) + i sinh(πy))`, `y` real. -/
theorem dlmf_5_4_5 (y : ℝ) :
    Gamma (1 / 4 + I * y) * Gamma (3 / 4 - I * y)
      = (π : ℂ) * (√2 : ℝ) / ((Real.cosh (π * y) : ℂ) + I * (Real.sinh (π * y) : ℂ)) := by
  have hr := Gamma_mul_Gamma_one_sub (1 / 4 + I * y)
  have hs4 : sin ((π : ℂ) / 4) = ((√2 / 2 : ℝ) : ℂ) := by
    rw [← Real.sin_pi_div_four, ofReal_sin]; push_cast; ring_nf
  have hc4 : cos ((π : ℂ) / 4) = ((√2 / 2 : ℝ) : ℂ) := by
    rw [← Real.cos_pi_div_four, ofReal_cos]; push_cast; ring_nf
  rw [show (1 : ℂ) - (1 / 4 + I * y) = 3 / 4 - I * y by ring,
    show (π : ℂ) * (1 / 4 + I * y) = π / 4 + ((π * y : ℝ) : ℂ) * I by push_cast; ring,
    sin_add, hs4, hc4, cos_mul_I, sin_mul_I, ← ofReal_cosh, ← ofReal_sinh] at hr
  rw [hr]
  have hch := Real.cosh_pos (π * y)
  have hD2 : (Real.cosh (π * y) : ℂ) + I * (Real.sinh (π * y) : ℂ) ≠ 0 := by
    intro h
    have := congrArg re h
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero,
      add_zero, zero_re] at this
    linarith
  have h2 : ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) = 2 := by
    rw [← ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs2 : ((√2 : ℝ) : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]; positivity
  have hD1 : ((√2 / 2 : ℝ) : ℂ) * (Real.cosh (π * y) : ℂ)
      + ((√2 / 2 : ℝ) : ℂ) * ((Real.sinh (π * y) : ℂ) * I) ≠ 0 := by
    rw [show ((√2 / 2 : ℝ) : ℂ) * (Real.cosh (π * y) : ℂ)
      + ((√2 / 2 : ℝ) : ℂ) * ((Real.sinh (π * y) : ℂ) * I)
      = ((√2 / 2 : ℝ) : ℂ) * ((Real.cosh (π * y) : ℂ) + I * (Real.sinh (π * y) : ℂ)) by ring]
    refine mul_ne_zero ?_ hD2
    push_cast
    exact div_ne_zero hs2 two_ne_zero
  rw [div_eq_div_iff hD1 hD2, show ((√2 / 2 : ℝ) : ℂ) = ((√2 : ℝ) : ℂ) / 2 by push_cast; rfl]
  linear_combination
    (-(π : ℂ) / 2 * ((Real.cosh (π * y) : ℂ) + I * (Real.sinh (π * y) : ℂ))) * h2

/-- **DLMF 5.4.6**: `Γ(½) = π^{1/2}` (Mathlib's `Real.Gamma_one_half_eq`; the 20 decimals
`1.77245 38509 05516 02729…` are noted for a later backfill). -/
theorem dlmf_5_4_6 : Real.Gamma (1 / 2) = √π := Real.Gamma_one_half_eq

/-- **DLMF 5.4.11**: `Γ′(1) = −γ` (Mathlib's `Complex.hasDerivAt_Gamma_one`). -/
theorem dlmf_5_4_11 : deriv Gamma 1 = -(Real.eulerMascheroniConstant : ℂ) :=
  Complex.hasDerivAt_Gamma_one.deriv

/-- **DLMF 5.4.11** on the real line. -/
theorem dlmf_5_4_11_real : deriv Real.Gamma 1 = -Real.eulerMascheroniConstant :=
  Real.hasDerivAt_Gamma_one.deriv

/-! ### §5.4(ii): Psi function -/

/-- **DLMF 5.4.12**: `ψ(1) = −γ` (Mathlib's `Complex.digamma_one`). -/
theorem dlmf_5_4_12 : digamma 1 = -(Real.eulerMascheroniConstant : ℂ) := digamma_one

/-- **DLMF 5.4.13**: `ψ(½) = −γ − 2 ln 2`. -/
theorem dlmf_5_4_13 :
    digamma (1 / 2) = -(Real.eulerMascheroniConstant : ℂ) - 2 * (Real.log 2 : ℝ) := by
  rw [digamma_one_half, ofReal_log (by norm_num)]
  push_cast
  ring

theorem hasDerivAt_digamma {z : ℂ} (hz : z ∉ gammaPoles) :
    HasDerivAt digamma (deriv digamma z) z :=
  (dlmf_5_2_2_analytic z hz).differentiableAt.hasDerivAt

theorem half_not_mem_gammaPoles : (1 / 2 : ℂ) ∉ gammaPoles :=
  not_mem_gammaPoles_of_re_pos (by norm_num)

theorem one_not_mem_gammaPoles : (1 : ℂ) ∉ gammaPoles :=
  not_mem_gammaPoles_of_re_pos (by norm_num)

/-- Near `½` no point is an integer. -/
theorem not_int_of_dist_half {s : ℂ} (hs : dist s (1 / 2) < 1 / 2) : ∀ n : ℤ, s ≠ n := by
  intro n hn
  rw [hn, dist_eq_norm] at hs
  have hre := (abs_re_le_norm ((n : ℂ) - 1 / 2)).trans_lt hs
  simp only [sub_re, intCast_re, div_re, one_re, re_ofNat, im_ofNat, mul_zero] at hre
  norm_num at hre
  rw [abs_lt] at hre
  obtain ⟨h1, h2⟩ := hre
  have h1' : (0 : ℝ) < n := by linarith
  have h2' : (n : ℝ) < 1 := by linarith
  have : (0 : ℤ) < n := by exact_mod_cast h1'
  have : n < 1 := by exact_mod_cast h2'
  omega

/-- **DLMF 5.4.13**: `ψ′(½) = π²/2`, by differentiating the reflection formula
`ψ(1 − s) = ψ(s) + π cot(πs)` at `s = ½`. -/
theorem dlmf_5_4_13_deriv : deriv digamma (1 / 2) = (π : ℂ) ^ 2 / 2 := by
  set a := deriv digamma (1 / 2) with ha
  have hψ := hasDerivAt_digamma half_not_mem_gammaPoles
  -- `s ↦ ψ(1 − s)`
  have h1 : HasDerivAt (fun s : ℂ => digamma (1 - s)) (a * (-1)) (1 / 2) := by
    have hψ' : HasDerivAt digamma a (1 - 1 / 2) := by
      rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]; exact hψ
    exact hψ'.comp (1 / 2) ((hasDerivAt_id (1 / 2 : ℂ)).const_sub 1)
  -- `s ↦ ψ(s) + π cos(πs)/sin(πs)`
  have hlin : HasDerivAt (fun s : ℂ => (π : ℂ) * s) π (1 / 2) := by
    simpa using (hasDerivAt_id (1 / 2 : ℂ)).const_mul (π : ℂ)
  have hcos := (hasDerivAt_cos ((π : ℂ) * (1 / 2))).comp (1 / 2) hlin
  have hsin := (hasDerivAt_sin ((π : ℂ) * (1 / 2))).comp (1 / 2) hlin
  have hπ2 : (π : ℂ) * (1 / 2) = π / 2 := by ring
  simp only [hπ2, cos_pi_div_two, sin_pi_div_two] at hcos hsin
  have hq := hcos.div hsin (by
    show sin ((π : ℂ) * (1 / 2)) ≠ 0
    rw [hπ2, sin_pi_div_two]; exact one_ne_zero)
  have h2 := hψ.add (hq.const_mul (π : ℂ))
  have h3 : HasDerivAt (fun s : ℂ => digamma (1 - s)) _ (1 / 2) := h2.congr_of_eventuallyEq (by
    filter_upwards [Metric.ball_mem_nhds (1 / 2 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
    rw [digamma_one_sub (not_int_of_dist_half hs), cot_eq_cos_div_sin]
    rfl)
  have := h1.unique h3
  simp only [Function.comp, hπ2, cos_pi_div_two, sin_pi_div_two] at this
  rw [← ha] at this
  linear_combination (-1 / 2 : ℂ) * this

/-- **DLMF 5.4.12**: `ψ′(1) = π²/6`, by differentiating the duplication formula
`ψ(2s) = ½(ψ(s) + ψ(s + ½)) + ln 2` at `s = ½`. -/
theorem dlmf_5_4_12_deriv : deriv digamma 1 = (π : ℂ) ^ 2 / 6 := by
  set b := deriv digamma 1 with hb
  have hψ1 := hasDerivAt_digamma one_not_mem_gammaPoles
  have hψh := hasDerivAt_digamma half_not_mem_gammaPoles
  have h1 : HasDerivAt (fun s : ℂ => digamma (2 * s)) (b * 2) (1 / 2) := by
    have h' : HasDerivAt digamma b (2 * (1 / 2)) := by
      rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num]; exact hψ1
    have hl : HasDerivAt (fun s : ℂ => 2 * s) 2 (1 / 2) := by
      simpa using (hasDerivAt_id (1 / 2 : ℂ)).const_mul (2 : ℂ)
    exact h'.comp (1 / 2) hl
  have h2 : HasDerivAt (fun s : ℂ => (1 / 2) * (digamma s + digamma (s + 1 / 2)) + log 2)
      ((1 / 2) * (deriv digamma (1 / 2) + b)) (1 / 2) := by
    have h' : HasDerivAt digamma b (1 / 2 + 1 / 2) := by
      rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num]; exact hψ1
    have hl : HasDerivAt (fun s : ℂ => s + 1 / 2) 1 (1 / 2) :=
      (hasDerivAt_id' (1 / 2 : ℂ)).add_const (1 / 2)
    have hs : HasDerivAt (fun s : ℂ => digamma (s + 1 / 2)) b (1 / 2) := by
      simpa only [mul_one, Function.comp_def] using
        HasDerivAt.comp (h := fun s : ℂ => s + 1 / 2) (1 / 2) h' hl
    exact ((hψh.add hs).const_mul (1 / 2)).add_const _
  have heq : (fun s : ℂ => (1 / 2) * (digamma s + digamma (s + 1 / 2)) + log 2)
      =ᶠ[𝓝 (1 / 2)] fun s => digamma (2 * s) := by
    have hU : {s : ℂ | 0 < s.re} ∈ 𝓝 (1 / 2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hU] with s hs
    refine (digamma_two_mul fun m h => ?_).symm
    have := congrArg re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have := h1.unique (h2.congr_of_eventuallyEq heq.symm)
  rw [dlmf_5_4_13_deriv] at this
  linear_combination (2 / 3 : ℂ) * this

/-- **DLMF 5.4.14**: `ψ(n + 1) = ∑_{k=1}^{n} 1/k − γ` (Mathlib's `Complex.digamma_nat_add_one`). -/
theorem dlmf_5_4_14 (n : ℕ) :
    digamma (n + 1) = ∑ k ∈ Finset.Icc 1 n, (1 / k : ℂ) - Real.eulerMascheroniConstant := by
  rw [digamma_nat_add_one, harmonic_eq_sum_Icc]
  push_cast
  simp [one_div]

/-- **DLMF 5.4.15**: `ψ(n + ½) = −γ − 2 ln 2 + 2(1 + ⅓ + ⋯ + 1/(2n − 1))` (DLMF: `n ≥ 1`; the
`n = 0` case is 5.4.13). -/
theorem dlmf_5_4_15 (n : ℕ) :
    digamma (n + 1 / 2) = -(Real.eulerMascheroniConstant : ℂ) - 2 * (Real.log 2 : ℝ)
      + 2 * ∑ k ∈ Finset.range n, (1 / (2 * k + 1) : ℂ) := by
  have hs : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -m := fun m h =>
    half_not_mem_gammaPoles ⟨m, h.symm⟩
  rw [add_comm, digamma_apply_add_nat hs n, ← dlmf_5_4_13, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (1 / 2 + (k : ℂ)) = (2 * k + 1) / 2 by ring, inv_div]
  ring

/-! ### Imaginary parts on vertical lines -/

theorem I_mul_not_int {y : ℝ} (hy : y ≠ 0) : ∀ n : ℤ, I * (y : ℂ) ≠ n := by
  intro n h
  have := congrArg im h
  simp at this
  exact hy this

theorem I_mul_not_mem_gammaPoles {y : ℝ} (hy : y ≠ 0) : I * (y : ℂ) ∉ gammaPoles := by
  rintro ⟨m, h⟩
  have := congrArg im h
  simp at this
  exact hy this.symm

theorem cot_pi_I_mul (y : ℝ) :
    (π : ℂ) * cot (π * (I * y))
      = ((-(π * (Real.cosh (π * y) / Real.sinh (π * y))) : ℝ) : ℂ) * I := by
  rw [cot_eq_cos_div_sin, show (π : ℂ) * (I * y) = ((π * y : ℝ) : ℂ) * I by push_cast; ring,
    cos_mul_I, sin_mul_I, ← ofReal_cosh, ← ofReal_sinh, div_eq_mul_inv, mul_inv, inv_I]
  push_cast
  ring

/-- **DLMF 5.4.16**: `ℑψ(iy) = 1/(2y) + ½π coth(πy)`, `y` real, `y ≠ 0`. -/
theorem dlmf_5_4_16 {y : ℝ} (hy : y ≠ 0) :
    (digamma (I * y)).im = 1 / (2 * y) + π / 2 * (Real.cosh (π * y) / Real.sinh (π * y)) := by
  have hrefl := digamma_one_sub (I_mul_not_int hy)
  have hneg : -(I * (y : ℂ)) ∉ gammaPoles := by
    rintro ⟨m, h⟩
    have := congrArg im h
    simp at this
    exact hy (by linarith)
  have hrec := digamma_apply_add_one _ (not_mem_gammaPoles.mp hneg)
  rw [show -(I * (y : ℂ)) + 1 = 1 - I * y by ring, ← conj_I_mul_ofReal, digamma_conj] at hrec
  rw [hrec, cot_pi_I_mul] at hrefl
  have h := congrArg im hrefl
  have i2 : ((conj (I * (y : ℂ)))⁻¹).im = 1 / y := by
    rw [conj_I_mul_ofReal, inv_neg, mul_inv, inv_I]
    simp
  rw [add_im, add_im, conj_im, i2] at h
  simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, add_zero, mul_one] at h
  have e : 1 / (2 * y) = (1 / y) / 2 := by field_simp
  rw [e]
  linarith

/-- **DLMF 5.4.17**: `ℑψ(½ + iy) = ½π tanh(πy)`, `y` real. -/
theorem dlmf_5_4_17 (y : ℝ) : (digamma (1 / 2 + I * y)).im = π / 2 * Real.tanh (π * y) := by
  have hnot : ∀ n : ℤ, (1 / 2 + I * (y : ℂ)) ≠ n := by
    intro n h
    have := congrArg re h
    simp at this
    have h1 : (0 : ℝ) < n := by linarith
    have h2 : (n : ℝ) < 1 := by linarith
    have : (0 : ℤ) < n := by exact_mod_cast h1
    have : n < 1 := by exact_mod_cast h2
    omega
  have hrefl := digamma_one_sub hnot
  have hc : (1 : ℂ) - (1 / 2 + I * y) = conj (1 / 2 + I * (y : ℂ)) := by
    apply Complex.ext <;> norm_num
  have hcot : (π : ℂ) * cot (π * (1 / 2 + I * y))
      = ((-(π * (Real.sinh (π * y) / Real.cosh (π * y)))) : ℝ) * I := by
    rw [cot_eq_cos_div_sin,
      show (π : ℂ) * (1 / 2 + I * y) = π / 2 + ((π * y : ℝ) : ℂ) * I by push_cast; ring,
      cos_add, sin_add, cos_pi_div_two, sin_pi_div_two, cos_mul_I, sin_mul_I, ← ofReal_cosh,
      ← ofReal_sinh]
    have hch : (Real.cosh (π * y) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
    field_simp
    push_cast
    ring
  rw [hc, digamma_conj, hcot] at hrefl
  have h := congrArg im hrefl
  rw [conj_im, add_im] at h
  simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, add_zero, mul_one] at h
  rw [Real.tanh_eq_sinh_div_cosh]
  linarith

/-- **DLMF 5.4.18**: `ℑψ(1 + iy) = −1/(2y) + ½π coth(πy)`, `y` real, `y ≠ 0`. -/
theorem dlmf_5_4_18 {y : ℝ} (hy : y ≠ 0) :
    (digamma (1 + I * y)).im = -1 / (2 * y) + π / 2 * (Real.cosh (π * y) / Real.sinh (π * y)) := by
  have hrec := digamma_apply_add_one _ (not_mem_gammaPoles.mp (I_mul_not_mem_gammaPoles hy))
  rw [add_comm] at hrec
  rw [hrec, add_im, dlmf_5_4_16 hy]
  have : ((I * (y : ℂ))⁻¹).im = -(1 / y) := by
    rw [mul_inv, inv_I]
    simp
  rw [this]
  have e : -1 / (2 * y) = 1 / (2 * y) - 1 / y := by field_simp; ring
  rw [e]
  ring

end Azurite.DLMF
