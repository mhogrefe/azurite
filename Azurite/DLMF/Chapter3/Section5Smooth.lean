/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# DLMF §3.5(i): a smooth periodic function with a slowly decaying trapezoidal error

A counterexample to the remark after 3.5.4 that for `k = ∞` "the error term is an
exponentially-small function of `1/h`": `smoothPeriodic`, `f(x) = ∑_{m ≥ 1} e^{−√m} cos(2πmx)`, is
`C^∞` (`contDiff_smoothPeriodic`, by `contDiff_tsum`: `(m+1)ᵏ e^{−√(m+1)} ≤ (2k+4)!/(m+1)²`) and
`1`-periodic (`periodic_smoothPeriodic`), with `∫₀¹ f = 0` (`integral_smoothPeriodic`, termwise).
By aliasing (`sum_cos_two_pi_mul_div`: `∑_{k<n} cos(2πMk/n) = n·[n ∣ M]`) the trapezoidal sum is
`∑_{n ∣ m} e^{−√m}` (`trapezoidSum_smoothPeriodic`), so `E_n(f) ≤ −e^{−√n}`
(`trapError_smoothPeriodic_le`) and `E_n(f) ≠ O(e^{−cn})` for every `c > 0`
(`smoothPeriodic_not_exponentially_small`). Exponential smallness needs analyticity (a strip of
analyticity); `C^∞` gives `O(hᵏ)` for every `k` (3.5.4).
-/

open Real Finset Filter MeasureTheory intervalIntegral

namespace Azurite.DLMF

/-- The coefficients `e^{−√(m+1)}`. -/
noncomputable def smoothCoeff (m : ℕ) : ℝ := Real.exp (-√((m : ℝ) + 1))

/-- The frequencies `2π(m + 1)`. -/
noncomputable def smoothFreq (m : ℕ) : ℝ := 2 * π * ((m : ℝ) + 1)

/-- The terms `e^{−√(m+1)} cos(2π(m + 1)x)`. -/
noncomputable def smoothTerm (m : ℕ) (x : ℝ) : ℝ := smoothCoeff m * Real.cos (smoothFreq m * x)

/-- `f(x) = ∑_{m ≥ 1} e^{−√m} cos(2πmx)`: `C^∞`, `1`-periodic, not analytic. -/
noncomputable def smoothPeriodic (x : ℝ) : ℝ := ∑' m, smoothTerm m x

theorem smoothCoeff_pos (m : ℕ) : 0 < smoothCoeff m := Real.exp_pos _

theorem smoothFreq_pos (m : ℕ) : 0 < smoothFreq m := by unfold smoothFreq; positivity

theorem abs_iteratedDeriv_cos_le (n : ℕ) (y : ℝ) : |iteratedDeriv n Real.cos y| ≤ 1 := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [iteratedDeriv_even_cos]
    simp [abs_mul, abs_cos_le_one]
  · rw [iteratedDeriv_add_one_cos, iteratedDeriv_even_sin]
    simp [abs_mul, abs_sin_le_one]

/-- `(m + 1)ᵏ e^{−√(m+1)} ≤ (2k + 4)!/(m + 1)²`. -/
theorem pow_mul_smoothCoeff_le (k m : ℕ) :
    ((m : ℝ) + 1) ^ k * smoothCoeff m ≤ (2 * k + 4).factorial / ((m : ℝ) + 1) ^ 2 := by
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hs := Real.pow_div_factorial_le_exp _ (Real.sqrt_nonneg ((m : ℝ) + 1)) (2 * k + 4)
  rw [show (2 * k + 4) = 2 * (k + 2) by ring, pow_mul, Real.sq_sqrt hx.le] at hs
  have hF : (0 : ℝ) < (2 * (k + 2)).factorial := by positivity
  rw [smoothCoeff, Real.exp_neg, show (2 * k + 4) = 2 * (k + 2) by ring,
    le_div_iff₀ (by positivity)]
  rw [div_le_iff₀ hF] at hs
  have hE := Real.exp_pos √((m : ℝ) + 1)
  calc ((m : ℝ) + 1) ^ k * (Real.exp √((m : ℝ) + 1))⁻¹ * ((m : ℝ) + 1) ^ 2
      = ((m : ℝ) + 1) ^ (k + 2) * (Real.exp √((m : ℝ) + 1))⁻¹ := by ring
    _ ≤ Real.exp √((m : ℝ) + 1) * (2 * (k + 2)).factorial * (Real.exp √((m : ℝ) + 1))⁻¹ :=
        mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr hE.le)
    _ = _ := by field_simp

theorem summable_smoothBound (k : ℕ) :
    Summable fun m : ℕ => smoothCoeff m * smoothFreq m ^ k := by
  have hsum : Summable fun m : ℕ => (2 * π) ^ k * ((2 * k + 4).factorial / ((m : ℝ) + 1) ^ 2) := by
    refine Summable.mul_left _ (Summable.mul_left _ ?_)
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [Nat.cast_add, Nat.cast_one] using this
  refine Summable.of_nonneg_of_le (fun m => (mul_pos (smoothCoeff_pos m)
    (pow_pos (smoothFreq_pos m) k)).le) (fun m => ?_) hsum
  rw [smoothFreq, mul_pow, show smoothCoeff m * ((2 * π) ^ k * ((m : ℝ) + 1) ^ k) =
    (2 * π) ^ k * (((m : ℝ) + 1) ^ k * smoothCoeff m) by ring]
  exact mul_le_mul_of_nonneg_left (pow_mul_smoothCoeff_le k m) (by positivity)

theorem iteratedDeriv_smoothTerm (k m : ℕ) (x : ℝ) :
    iteratedDeriv k (smoothTerm m) x =
      smoothCoeff m * (smoothFreq m ^ k * iteratedDeriv k Real.cos (smoothFreq m * x)) := by
  have h1 : smoothTerm m = fun x => smoothCoeff m * (fun y => Real.cos (smoothFreq m * y)) x := rfl
  rw [h1, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (Real.contDiff_cos.of_le le_top)]

/-- `f` is `C^∞`. -/
theorem contDiff_smoothPeriodic : ContDiff ℝ (⊤ : ℕ∞) smoothPeriodic := by
  refine contDiff_tsum (v := fun k m => smoothCoeff m * smoothFreq m ^ k)
    (fun m => by unfold smoothTerm; fun_prop) (fun k _ => summable_smoothBound k)
    fun k m x _ => ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_smoothTerm, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_of_pos (smoothCoeff_pos m), abs_pow, abs_of_pos (smoothFreq_pos m)]
  have := abs_iteratedDeriv_cos_le k (smoothFreq m * x)
  have hc := (smoothCoeff_pos m).le
  have hf := pow_pos (smoothFreq_pos m) k
  calc smoothCoeff m * (smoothFreq m ^ k * |iteratedDeriv k Real.cos (smoothFreq m * x)|)
      ≤ smoothCoeff m * (smoothFreq m ^ k * 1) := by gcongr
    _ = _ := by ring

theorem summable_smoothTerm (x : ℝ) : Summable fun m => smoothTerm m x :=
  Summable.of_norm_bounded (summable_smoothBound 0) fun m => by
    rw [smoothTerm, Real.norm_eq_abs, abs_mul, abs_of_pos (smoothCoeff_pos m), pow_zero, mul_one]
    exact mul_le_of_le_one_right (smoothCoeff_pos m).le (abs_cos_le_one _)

/-- `f` is `1`-periodic. -/
theorem periodic_smoothPeriodic : Function.Periodic smoothPeriodic 1 := fun x => by
  unfold smoothPeriodic
  refine tsum_congr fun m => ?_
  rw [smoothTerm, smoothTerm, show smoothFreq m * (x + 1) = smoothFreq m * x + (m + 1 : ℕ) * (2 * π)
    by unfold smoothFreq; push_cast; ring, Real.cos_add_nat_mul_two_pi]

/-- `∑_{k<n} cos(2πMk/n) = n` if `n ∣ M`, else `0`. -/
theorem sum_cos_two_pi_mul_div (n M : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range n, Real.cos (2 * π * M * k / n) = if n ∣ M then (n : ℝ) else 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  split_ifs with hd
  · obtain ⟨q, rfl⟩ := hd
    have : ∀ k ∈ range n, Real.cos (2 * π * ((n * q : ℕ) : ℝ) * k / n) = 1 := fun k _ => by
      rw [show 2 * π * ((n * q : ℕ) : ℝ) * k / n = ((q * k : ℕ) : ℝ) * (2 * π) by
        push_cast; field_simp, Real.cos_nat_mul_two_pi]
    rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul, mul_one]
  · set ω : ℂ := Complex.exp (2 * π * M / n * Complex.I)
    have hω : ω ≠ 1 := by
      intro h
      obtain ⟨j, hj⟩ := Complex.exp_eq_one_iff.mp h
      have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have h3 : (2 * π * Complex.I) * ((M : ℂ) / n) = (2 * π * Complex.I) * j := by
        linear_combination hj
      have h4 : (M : ℂ) / n = j := mul_left_cancel₀ Complex.two_pi_I_ne_zero h3
      have : (M : ℂ) = j * n := by rw [div_eq_iff hnC] at h4; exact h4
      have hM : (M : ℤ) = j * n := by exact_mod_cast this
      exact hd ⟨j.toNat, by
        have hj0 : 0 ≤ j := by
          by_contra hneg; push Not at hneg
          have hn' : (0 : ℤ) < n := Nat.cast_pos.mpr (by omega)
          have : (M : ℤ) < 0 := by rw [hM]; nlinarith
          omega
        zify; rw [hM, Int.toNat_of_nonneg hj0]; ring⟩
    have hωn : ω ^ n = 1 := by
      have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [← Complex.exp_nat_mul, show (n : ℂ) * (2 * π * M / n * Complex.I) =
        (M : ℕ) * (2 * π * Complex.I) by field_simp, Complex.exp_nat_mul_two_pi_mul_I]
    have hgeom : ∑ k ∈ range n, ω ^ k = 0 := by
      rw [geom_sum_eq hω, hωn, sub_self, zero_div]
    have hre := congrArg Complex.re hgeom
    rw [Complex.re_sum, Complex.zero_re] at hre
    rw [← hre]
    refine sum_congr rfl fun k _ => ?_
    rw [← Complex.exp_nat_mul, show (k : ℂ) * (2 * π * M / n * Complex.I) =
      ((2 * π * M * k / n : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_ofReal_mul_I_re]

theorem continuous_smoothTerm (m : ℕ) : Continuous (smoothTerm m) := by
  unfold smoothTerm; fun_prop

theorem integral_smoothTerm (m : ℕ) : ∫ x in (0 : ℝ)..1, smoothTerm m x = 0 := by
  unfold smoothTerm
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) (smoothFreq_pos m).ne',
    integral_cos, mul_zero, mul_one, Real.sin_zero, sub_zero,
    show smoothFreq m = ((2 * (m + 1) : ℕ) : ℝ) * π by unfold smoothFreq; push_cast; ring,
    Real.sin_nat_mul_pi, smul_zero, mul_zero]

/-- `∫₀¹ f = 0`. -/
theorem integral_smoothPeriodic : ∫ x in (0 : ℝ)..1, smoothPeriodic x = 0 := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  unfold smoothPeriodic
  have hint : ∀ m, Integrable (smoothTerm m) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    fun m => (continuous_smoothTerm m).integrableOn_Ioc
  have hsum : Summable fun m => ∫ x in Set.Ioc (0 : ℝ) 1, ‖smoothTerm m x‖ := by
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun x => norm_nonneg _)
      (fun m => ?_) (summable_smoothBound 0)
    calc ∫ x in Set.Ioc (0 : ℝ) 1, ‖smoothTerm m x‖ ≤ ∫ x in Set.Ioc (0 : ℝ) 1, smoothCoeff m :=
          setIntegral_mono_on (hint m).norm (integrable_const _) measurableSet_Ioc fun x _ => by
            rw [smoothTerm, Real.norm_eq_abs, abs_mul, abs_of_pos (smoothCoeff_pos m)]
            exact mul_le_of_le_one_right (smoothCoeff_pos m).le (abs_cos_le_one _)
      _ = smoothCoeff m * smoothFreq m ^ 0 := by simp
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  have h0 : ∀ m, ∫ x in Set.Ioc (0 : ℝ) 1, smoothTerm m x = 0 := fun m => by
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_smoothTerm]
  simp [h0]

theorem summable_smoothCoeff_ite (n : ℕ) :
    Summable fun m => smoothCoeff m * (if n ∣ m + 1 then (1 : ℝ) else 0) :=
  Summable.of_nonneg_of_le (f := smoothCoeff)
    (fun m => by split_ifs <;> simp [(smoothCoeff_pos m).le])
    (fun m => by split_ifs <;> simp [(smoothCoeff_pos m).le])
    (by simpa using summable_smoothBound 0)

/-- The trapezoidal sum with `n` points: `T_n = ∑_{n ∣ m} e^{−√m}` (aliasing). -/
theorem trapezoidSum_smoothPeriodic {n : ℕ} (hn : 1 ≤ n) :
    trapezoidSum smoothPeriodic 0 1 n =
      ∑' m, smoothCoeff m * (if n ∣ m + 1 then (1 : ℝ) else 0) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hend : smoothPeriodic (0 + n * ((1 - 0) / n)) = smoothPeriodic 0 := by
    rw [show (0 : ℝ) + n * ((1 - 0) / n) = 0 + 1 by simp [hn0], periodic_smoothPeriodic]
  rw [trapezoidSum, hend, sum_range_succ, hend]
  have hsw : ∑ k ∈ range n, smoothPeriodic (0 + k * ((1 - 0) / n)) =
      ∑' m, ∑ k ∈ range n, smoothTerm m (k / n) := by
    unfold smoothPeriodic
    rw [Summable.tsum_finsetSum fun k _ => summable_smoothTerm _]
    exact sum_congr rfl fun k _ => by rw [zero_add, sub_zero, one_div, ← div_eq_mul_inv]
  have hterm : ∀ m, ∑ k ∈ range n, smoothTerm m (k / n) =
      smoothCoeff m * (if n ∣ m + 1 then (n : ℝ) else 0) := fun m => by
    simp only [smoothTerm, ← mul_sum]
    rw [← sum_cos_two_pi_mul_div n (m + 1) hn]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    congr 1; unfold smoothFreq; push_cast; ring
  have hAB : ∀ A B : ℝ, A + B - B / 2 - B / 2 = A := fun A B => by ring
  rw [hAB, hsw, tsum_congr hterm, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  split_ifs <;> field_simp <;> simp

/-- `|E_n(f)| ≥ e^{−√n}`: the trapezoidal error is `−∑_{n ∣ m} e^{−√m} ≤ −e^{−√n}`. -/
theorem trapError_smoothPeriodic_le {n : ℕ} (hn : 1 ≤ n) :
    trapError smoothPeriodic 0 1 n ≤ -Real.exp (-√n) := by
  rw [trapError, integral_smoothPeriodic, trapezoidSum_smoothPeriodic hn, zero_sub, neg_le_neg_iff]
  have := (summable_smoothCoeff_ite n).le_tsum (n - 1) fun j _ => by
    split_ifs <;> simp [(smoothCoeff_pos j).le]
  simp only [show n ∣ n - 1 + 1 by rw [Nat.sub_add_cancel hn], ↓reduceIte, mul_one,
    smoothCoeff] at this
  rw [
    show ((n - 1 : ℕ) : ℝ) + 1 = n by rw [Nat.cast_sub hn]; push_cast; ring] at this
  exact this

/-- **Erratum to §3.5(i)** ("when `k = ∞` the error term is an exponentially-small function of
`1/h`"): `f` is `C^∞` and `1`-periodic, but `E_n(f)` is not `O(e^{−c/h}) = O(e^{−cn})` for any
`c > 0` (it is at least `e^{−√n}` in absolute value). -/
theorem smoothPeriodic_not_exponentially_small :
    ¬ ∃ c > 0, ∃ C, ∀ n : ℕ, 1 ≤ n →
      |trapError smoothPeriodic 0 1 n| ≤ C * Real.exp (-c * n) := by
  rintro ⟨c, hc, C, hC⟩
  set C' := max C 1
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hL : 0 ≤ Real.log C' := Real.log_nonneg hC'1
  set N : ℕ := ⌈4 / c ^ 2 + 2 * Real.log C' / c⌉₊ + 1
  have hN1 : 1 ≤ N := by omega
  have hNbig : 4 / c ^ 2 + 2 * Real.log C' / c < N := by
    have := Nat.le_ceil (4 / c ^ 2 + 2 * Real.log C' / c)
    simp only [N]; push_cast; linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set sN := √(N : ℝ)
  have hs2 : sN ^ 2 = N := Real.sq_sqrt hNpos.le
  have hs0 : 0 ≤ sN := Real.sqrt_nonneg _
  have h4 : 4 / c ^ 2 ≤ N := by
    have : 0 ≤ 2 * Real.log C' / c := by positivity
    linarith
  have hcs : 2 ≤ c * sN := by
    have h4' : 4 ≤ c ^ 2 * N := by rwa [div_le_iff₀ (by positivity), mul_comm] at h4
    have hsq : 4 ≤ (c * sN) ^ 2 := by rw [mul_pow, hs2]; exact h4'
    have hcs0 : 0 ≤ c * sN := mul_nonneg hc.le hs0
    by_contra hlt
    push Not at hlt
    nlinarith
  have hsN : sN ≤ c * N / 2 := by
    have : c * N = (c * sN) * sN := by rw [mul_assoc, ← sq, hs2]
    rw [this]
    nlinarith
  have hlog : Real.log C' < c * N / 2 := by
    have : 2 * Real.log C' / c < N := by
      have : 0 ≤ 4 / c ^ 2 := by positivity
      linarith
    rw [div_lt_iff₀ hc] at this
    linarith
  -- `e^{−√N} ≤ C' e^{−cN}`
  have hb := (abs_of_nonpos ((trapError_smoothPeriodic_le hN1).trans
    (neg_nonpos.mpr (Real.exp_pos _).le)) ▸ hC N hN1)
  have hlow := trapError_smoothPeriodic_le hN1
  have h1 : Real.exp (-sN) ≤ C' * Real.exp (-c * N) := by
    calc Real.exp (-sN) ≤ -trapError smoothPeriodic 0 1 N := by linarith
      _ ≤ C * Real.exp (-c * N) := hb
      _ ≤ C' * Real.exp (-c * N) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  have h2 : Real.exp (c * N - sN) ≤ C' := by
    rw [show c * N - sN = -sN + c * N by ring, Real.exp_add]
    calc Real.exp (-sN) * Real.exp (c * N) ≤ C' * Real.exp (-c * N) * Real.exp (c * N) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = C' := by rw [mul_assoc, ← Real.exp_add]; simp
  have h3 := (Real.le_log_iff_exp_le (by linarith)).mpr h2
  linarith

end Azurite.DLMF
