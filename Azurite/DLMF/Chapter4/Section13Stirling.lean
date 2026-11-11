/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13Series
import Azurite.DLMF.Chapter5.Section11LaplaceAsymp

/-!
# DLMF §4.13: 4.13.9

Formalization of <https://dlmf.nist.gov/4.13#E9>: `1·3·5⋯(2n + 1) c_{2n+1} = gₙ`, where the
`cₙ` are the coefficients of 4.13.6 (`lambertC`) and the `gₙ` those of Stirling's formula 5.11.3
(`BZ.stirlingCoeff`).

With `τ = −W(−e^{−1−t²/2})` and `t = √2 w`: `τ − 1 − ln τ = w²`, which is the defining
relation of the `aₖ` of 5.11.6. Algebraically: `bₖ = (k + 1) c_{k+1} (√2)^{k+1}/2` satisfies the
recursion 5.11.6 exactly when the `cₙ` satisfy 4.13.8 (`lambertB_rec`), so `bₖ = aₖ`
(`eq_stirlingA_of_rec`), and 5.11.5 (`gₙ = √2 (½)ₙ a_{2n}`) gives 4.13.9 with
`2ⁿ (½)ₙ (2n + 1) = (2n + 1)!!` (`two_pow_mul_ascPochhammer_half`).
-/

open Finset
open scoped Real Nat

namespace Azurite.DLMF

/-- `bₖ = (k + 1) c_{k+1} (√2)^{k+1}/2`. -/
noncomputable def lambertB (k : ℕ) : ℂ :=
  ((k : ℂ) + 1) * lambertC (k + 1) * ((Real.sqrt 2 : ℝ) : ℂ) ^ (k + 1) / 2

theorem sqrt_two_sq_complex : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- 4.13.8 as `∑_{i=1}^{n} cᵢ c_{n+1−i} = 2c_{n−1}/(n + 1)` (`n = k + 2`). -/
theorem lambertC_conv (k : ℕ) :
    ((k : ℂ) + 3) * ∑ j ∈ range (k + 2), lambertC (j + 1) * lambertC (k + 2 - j) =
      2 * lambertC (k + 1) := by
  have h8 := dlmf_4_13_8 (k + 2) (by omega)
  rw [show k + 2 - 1 = k + 1 by omega, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range,
    show k + 1 + 1 - 2 = k by omega] at h8
  have hc1 : lambertC 1 = 1 := dlmf_4_13_7.2.1
  rw [Finset.sum_range_succ, Finset.sum_range_succ', show k + 2 - (k + 1) = 1 by omega,
    show k + 2 - 0 = k + 2 by omega, hc1]
  have hmid : ∑ j ∈ range k, lambertC (j + 1 + 1) * lambertC (k + 2 - (j + 1)) =
      ∑ j ∈ range k, lambertC (2 + j) * lambertC (k + 2 + 1 - (2 + j)) :=
    Finset.sum_congr rfl fun j _ => by
      rw [show j + 1 + 1 = 2 + j by omega, show k + 2 - (j + 1) = k + 2 + 1 - (2 + j) by omega]
  rw [hmid]
  generalize ∑ j ∈ range k, lambertC (2 + j) * lambertC (k + 2 + 1 - (2 + j)) = S at h8 ⊢
  have h3 : ((k + 2 : ℕ) : ℂ) + 1 ≠ 0 := by norm_cast
  push_cast at h8 h3
  rw [h8]
  field_simp
  ring

/-- The weighted sum `∑ (k + 2 − j) c_{j+1} c_{k+2−j}` is `c_{k+1}`. -/
theorem lambertC_wconv (k : ℕ) :
    ∑ j ∈ range (k + 2), ((k : ℂ) + 2 - j) * lambertC (j + 1) * lambertC (k + 2 - j) =
      lambertC (k + 1) := by
  have hrefl := Finset.sum_range_reflect
    (fun j => ((j : ℂ) + 1) * lambertC (j + 1) * lambertC (k + 2 - j)) (k + 2)
  have hr : ∑ j ∈ range (k + 2), ((k : ℂ) + 2 - j) * lambertC (j + 1) * lambertC (k + 2 - j) =
      ∑ j ∈ range (k + 2), ((j : ℂ) + 1) * lambertC (j + 1) * lambertC (k + 2 - j) := by
    rw [← hrefl]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [show k + 2 - 1 - j + 1 = k + 2 - j by omega, show k + 2 - (k + 2 - 1 - j) = j + 1 by omega,
      Nat.cast_sub (by omega)]
    push_cast
    ring
  have hsum : 2 * ∑ j ∈ range (k + 2), ((k : ℂ) + 2 - j) * lambertC (j + 1) * lambertC (k + 2 - j)
      = ((k : ℂ) + 3) * ∑ j ∈ range (k + 2), lambertC (j + 1) * lambertC (k + 2 - j) := by
    rw [two_mul]
    nth_rewrite 2 [hr]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [lambertC_conv] at hsum
  linear_combination hsum / 2

/-- The `bₖ` satisfy the recursion 5.11.6. -/
theorem lambertB_rec (k : ℕ) :
    ∑ j ∈ range (k + 2), lambertB j * lambertB (k + 1 - j) / ((j : ℂ) + 1) =
      lambertB k / ((k : ℂ) + 1) := by
  set s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
  have hterm : ∀ j ∈ range (k + 2), lambertB j * lambertB (k + 1 - j) / ((j : ℂ) + 1) =
      ((k : ℂ) + 2 - j) * lambertC (j + 1) * lambertC (k + 2 - j) * s ^ (k + 3) / 4 :=
    fun j hj => by
      have hj' := Finset.mem_range.mp hj
      have hpow : s ^ (j + 1) * s ^ (k + 2 - j) = s ^ (k + 3) := by
        rw [← pow_add]; congr 1; omega
      have hj1 : (j : ℂ) + 1 ≠ 0 := by norm_cast
      simp only [lambertB]
      rw [show k + 1 - j + 1 = k + 2 - j by omega, Nat.cast_sub (by omega : j ≤ k + 1)]
      field_simp
      rw [← hpow]
      push_cast
      ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Finset.sum_mul, lambertC_wconv]
  have hk1 : (k : ℂ) + 1 ≠ 0 := by norm_cast
  simp only [lambertB]
  rw [show s ^ (k + 3) = s ^ (k + 1) * s ^ 2 by rw [← pow_add], sqrt_two_sq_complex]
  field_simp
  ring

theorem lambertB_eq_stirlingA (k : ℕ) : lambertB k = (stirlingA k : ℂ) := by
  refine eq_stirlingA_of_rec ?_ lambertB_rec k
  rw [lambertB, stirlingA_zero, dlmf_4_13_7.2.1]
  push_cast
  ring

/-- `2ⁿ (½)ₙ (2n + 1) = (2n + 1)!!`. -/
theorem two_pow_mul_ascPochhammer_half (n : ℕ) :
    2 ^ n * (ascPochhammer ℝ n).eval (1 / 2) * (2 * n + 1) = ((2 * n + 1)‼ : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring,
      Nat.doubleFactorial_add_two, Nat.cast_mul, ← ih]
    push_cast
    ring

/-- **DLMF 4.13.9**: `1·3·5⋯(2n + 1) c_{2n+1} = gₙ`. -/
theorem dlmf_4_13_9 (n : ℕ) :
    ((2 * n + 1)‼ : ℂ) * lambertC (2 * n + 1) = (BZ.stirlingCoeff n : ℂ) := by
  have h5 := dlmf_5_11_5 n
  have hb := lambertB_eq_stirlingA (2 * n)
  have hd := two_pow_mul_ascPochhammer_half n
  have hg : (BZ.stirlingCoeff n : ℂ) = (((BZ.stirlingCoeff n : ℝ)) : ℂ) := by push_cast; rfl
  rw [hg, h5]
  push_cast
  rw [← hb, lambertB]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ (2 * n + 1) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 * 2 ^ n := by
    rw [← pow_succ, show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul, sqrt_two_sq_complex,
      pow_succ]
    ring
  have hd' : ((2 * n + 1)‼ : ℂ) = 2 ^ n * (((ascPochhammer ℝ n).eval (1 / 2) : ℝ) : ℂ) *
      (2 * n + 1) := by
    exact_mod_cast hd.symm
  rw [hd']
  push_cast
  linear_combination (-((((ascPochhammer ℝ n).eval (1 / 2) : ℝ) : ℂ) * ((2 * n : ℂ) + 1) *
    lambertC (2 * n + 1) / 2)) * hs

end Azurite.DLMF
