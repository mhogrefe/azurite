/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# DLMF §1.11(iv): Roots of Unity and of Other Constants

Formalizations of <https://dlmf.nist.gov/1.11.iv>. Each root set is given in three forms: a
complete factorization `zⁿ − c = ∏_{k=0}^{n−1} (z − rₖ)`, the characterization
`zⁿ = c ↔ z = rₖ` for some `k < n`, and distinctness of the `rₖ`.

* 1.11.21 (`dlmf_1_11_21`): `zⁿ − 1 = (z − 1)(z^{n−1} + ⋯ + 1)`, with roots `e^{2kπi/n}`.
* `zⁿ + 1 = 0` (`dlmf_1_11_iv_neg_one`): the roots are `e^{(2k+1)πi/n}`.
* 1.11.22–1.11.23 (`dlmf_1_11_23`): the roots of `zⁿ = a + ib` are
  `ⁿ√R (cos((α + 2kπ)/n) + i sin((α + 2kπ)/n))`, with `R = (a² + b²)^{1/2}` and `α` the principal
  phase. They are distinct when `a + ib ≠ 0`.

All three follow from `pow_sub_eq_prod`: if `βⁿ = c`, then
`zⁿ − c = ∏ (z − β e^{2πik/n})`. That lemma is Mathlib's `X_pow_sub_C_eq_prod` with the
primitive root `Complex.isPrimitiveRoot_exp`.
-/

open Complex Polynomial Finset
open scoped Real

namespace Azurite.DLMF

theorem exp_two_pi_I_div_pow (n k : ℕ) :
    exp (2 * π * I / n) ^ k = exp (2 * π * I * k / n) := by
  rw [← exp_nat_mul]
  ring_nf

/-- If `βⁿ = c`, then `zⁿ − c = ∏_{k=0}^{n−1} (z − β e^{2πik/n})`. -/
theorem pow_sub_eq_prod {n : ℕ} (hn : 0 < n) {β c : ℂ} (hβ : β ^ n = c) (z : ℂ) :
    z ^ n - c = ∏ k ∈ range n, (z - β * exp (2 * π * I * k / n)) := by
  have h := congrArg (eval z)
    (X_pow_sub_C_eq_prod (isPrimitiveRoot_exp n hn.ne') hn hβ)
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_prod] at h
  rw [h]
  exact prod_congr rfl fun k _ => by rw [exp_two_pi_I_div_pow, mul_comm]

/-- The roots `β e^{2πik/n}` (`k < n`) are distinct when `β ≠ 0`. -/
theorem roots_injOn {n : ℕ} (hn : 0 < n) {β : ℂ} (hβ : β ≠ 0) :
    Set.InjOn (fun k : ℕ => β * exp (2 * π * I * k / n)) (Set.Iio n) := by
  intro i hi j hj hij
  have h := mul_left_cancel₀ hβ hij
  rw [← exp_two_pi_I_div_pow, ← exp_two_pi_I_div_pow] at h
  exact (isPrimitiveRoot_exp n hn.ne').pow_inj hi hj h

theorem pow_eq_iff_of_prod {n : ℕ} {c : ℂ} {r : ℕ → ℂ}
    (h : ∀ z : ℂ, z ^ n - c = ∏ k ∈ range n, (z - r k)) (z : ℂ) :
    z ^ n = c ↔ ∃ k < n, z = r k := by
  rw [← sub_eq_zero, h, prod_eq_zero_iff]
  simp only [mem_range, sub_eq_zero]

/-- **DLMF 1.11.21**: `zⁿ − 1 = (z − 1)(z^{n−1} + ⋯ + z + 1)`, and its roots are
`1, e^{2πi/n}, …, e^{(2n−2)πi/n}` (distinct): `zⁿ − 1 = ∏_{k=0}^{n−1} (z − e^{2kπi/n})`. -/
theorem dlmf_1_11_21 {n : ℕ} (hn : 0 < n) :
    (∀ z : ℂ, z ^ n - 1 = (z - 1) * ∑ k ∈ range n, z ^ k) ∧
    (∀ z : ℂ, z ^ n - 1 = ∏ k ∈ range n, (z - exp (2 * k * π * I / n))) ∧
    (∀ z : ℂ, z ^ n = 1 ↔ ∃ k < n, z = exp (2 * k * π * I / n)) ∧
    Set.InjOn (fun k : ℕ => exp (2 * k * π * I / n)) (Set.Iio n) := by
  have hp := pow_sub_eq_prod (β := 1) hn (one_pow n)
  have heq : ∀ k : ℕ, (1 : ℂ) * exp (2 * π * I * k / n) = exp (2 * k * π * I / n) :=
    fun k => by rw [one_mul]; ring_nf
  simp only [heq] at hp
  refine ⟨fun z => (mul_geom_sum z n).symm, hp, pow_eq_iff_of_prod hp, ?_⟩
  have := roots_injOn hn one_ne_zero
  simpa only [heq] using this

/-- DLMF §1.11(iv): the roots of `zⁿ + 1 = 0` are `e^{πi/n}, e^{3πi/n}, …, e^{(2n−1)πi/n}`
(distinct): `zⁿ + 1 = ∏_{k=0}^{n−1} (z − e^{(2k+1)πi/n})`. -/
theorem dlmf_1_11_iv_neg_one {n : ℕ} (hn : 0 < n) :
    (∀ z : ℂ, z ^ n + 1 = ∏ k ∈ range n, (z - exp ((2 * k + 1) * π * I / n))) ∧
    (∀ z : ℂ, z ^ n + 1 = 0 ↔ ∃ k < n, z = exp ((2 * k + 1) * π * I / n)) ∧
    Set.InjOn (fun k : ℕ => exp ((2 * k + 1) * π * I / n)) (Set.Iio n) := by
  have hβ : exp (π * I / n) ^ n = -1 := by
    rw [← exp_nat_mul, show (n : ℂ) * (π * I / n) = π * I by
      field_simp [Nat.cast_ne_zero.mpr hn.ne'], exp_pi_mul_I]
  have heq : ∀ k : ℕ, exp (π * I / n) * exp (2 * π * I * k / n) =
      exp ((2 * k + 1) * π * I / n) := fun k => by
    rw [← exp_add]
    ring_nf
  have hp := pow_sub_eq_prod hn hβ
  simp only [heq, sub_neg_eq_add] at hp
  refine ⟨hp, fun z => ?_, ?_⟩
  · rw [← sub_neg_eq_add, sub_eq_zero]
    exact pow_eq_iff_of_prod (fun z => by rw [sub_neg_eq_add]; exact hp z) z
  · have := roots_injOn hn (exp_ne_zero (π * I / n))
    simpa only [heq] using this

/-- **DLMF 1.11.22–1.11.23**: for real `a`, `b`, the roots of `zⁿ = a + ib` are
`ⁿ√R (cos((α + 2kπ)/n) + i sin((α + 2kπ)/n))`, `k = 0, 1, …, n − 1`, where
`R = (a² + b²)^{1/2}` and `α = ph(a + ib)` (principal value); they are distinct when
`a + ib ≠ 0`. -/
theorem dlmf_1_11_23 {n : ℕ} (hn : 0 < n) (a b : ℝ) :
    let R : ℝ := Real.sqrt (a ^ 2 + b ^ 2)
    let α : ℝ := arg (a + b * I)
    let root : ℕ → ℂ := fun k => (R ^ ((n : ℝ)⁻¹) : ℝ) *
      (Real.cos ((α + 2 * k * π) / n) + Real.sin ((α + 2 * k * π) / n) * I)
    (∀ z : ℂ, z ^ n - (a + b * I) = ∏ k ∈ range n, (z - root k)) ∧
    (∀ z : ℂ, z ^ n = a + b * I ↔ ∃ k < n, z = root k) ∧
    ((a : ℂ) + b * I ≠ 0 → Set.InjOn root (Set.Iio n)) := by
  intro R α root
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hR : ‖(a : ℂ) + b * I‖ = R := by
    rw [norm_eq_sqrt_sq_add_sq]
    simp [R]
  set β : ℂ := (R ^ ((n : ℝ)⁻¹) : ℝ) * exp (α / n * I) with hβdef
  have hβ : β ^ n = a + b * I := by
    rw [hβdef, mul_pow, ← ofReal_pow, Real.rpow_inv_natCast_pow (Real.sqrt_nonneg _) hn.ne',
      ← exp_nat_mul, show (n : ℂ) * (α / n * I) = α * I by field_simp]
    have := norm_mul_exp_arg_mul_I ((a : ℂ) + b * I)
    rw [hR] at this
    exact this
  have heq : ∀ k : ℕ, β * exp (2 * π * I * k / n) = root k := fun k => by
    simp only [hβdef, root, mul_assoc]
    congr 1
    rw [← exp_add, show (α : ℂ) / n * I + 2 * (π * (I * k)) / n = ((α + 2 * k * π) / n : ℝ) * I by
      push_cast; ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin, mul_assoc 2 (k : ℝ) π]
  have hp := pow_sub_eq_prod hn hβ
  simp only [heq] at hp
  refine ⟨hp, pow_eq_iff_of_prod hp, fun h0 => ?_⟩
  have hβ0 : β ≠ 0 := fun h => h0 (by rw [← hβ, h, zero_pow hn.ne'])
  have := roots_injOn hn hβ0
  simpa only [heq] using this

end Azurite.DLMF
