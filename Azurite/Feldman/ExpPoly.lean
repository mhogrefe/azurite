/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Feldman.Interpolation
import Azurite.Feldman.Liouville

/-!
# Tools for the auxiliary function of Fel'dman's Theorem 3

* More on the `ℓ¹` norm: `l1_shiftD_pow_le` (`‖(D + l)^s P‖₁ ≤ (d + |l|)^s ‖P‖₁` for
  `deg P ≤ d`), `norm_eval_le_l1` (`|P(z)| ≤ ‖P‖₁ R^d` for `|z| ≤ R`), `norm_eval_sub_le`
  (`|P(u) − P(v)| ≤ |u − v| d ‖P‖₁ R^d`).
* Integrality: `shiftDZ`, the operator `D + l` on `ℤ[X]`, with `toC_shiftDZ_pow` — the
  polynomials `(D + l)^s X^k` have integer coefficients.
* `reI`, `imI`: the real and imaginary parts of `i^j` as integers (`I_pow_eq`).
-/

namespace Azurite.Feldman

open Polynomial Finset

/-! ### The `ℓ¹` norm, continued -/

theorem l1_shiftD_le {P : ℂ[X]} {d : ℕ} (h : P.natDegree ≤ d) (l : ℂ) :
    l1 (shiftD l P) ≤ (d + ‖l‖) * l1 P := by
  rw [shiftD_apply]
  refine (l1_add_le _ _).trans ?_
  rw [l1_smul, add_mul]
  exact add_le_add (l1_derivative_le h) le_rfl

theorem l1_shiftD_pow_le {P : ℂ[X]} {d : ℕ} (h : P.natDegree ≤ d) (l : ℂ) (s : ℕ) :
    l1 ((shiftD l ^ s) P) ≤ (d + ‖l‖) ^ s * l1 P := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ, mul_assoc, mul_comm ((d + ‖l‖) ^ s),
      mul_assoc]
    refine (l1_shiftD_le (natDegree_shiftD_pow_le l h s) l).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [mul_comm]
    exact ih

/-- `|P(z)| ≤ ‖P‖₁ R^d` for `deg P ≤ d`, `|z| ≤ R`, `R ≥ 1`. -/
theorem norm_eval_le_l1 {P : ℂ[X]} {d : ℕ} (h : P.natDegree ≤ d) {z : ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) : ‖P.eval z‖ ≤ l1 P * R ^ d := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le h), l1_eq_sum_range (Nat.lt_succ_of_le h),
    Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [norm_mul, norm_pow]
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (mem_range.mp hi)
  exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg z) hz i).trans
    (pow_le_pow_right₀ hR hi')) (norm_nonneg _)

theorem norm_pow_sub_pow_le {u v : ℂ} {R : ℝ} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) (k : ℕ) :
    ‖u ^ k - v ^ k‖ ≤ ‖u - v‖ * (k * R ^ (k - 1)) := by
  have hR : 0 ≤ R := (norm_nonneg u).trans hu
  induction k with
  | zero => simp
  | succ k ih =>
    have e : u ^ (k + 1) - v ^ (k + 1) = u * (u ^ k - v ^ k) + (u - v) * v ^ k := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow, Nat.add_sub_cancel]
    have h1 : ‖u‖ * ‖u ^ k - v ^ k‖ ≤ R * (‖u - v‖ * (k * R ^ (k - 1))) :=
      mul_le_mul hu ih (norm_nonneg _) hR
    have h2 : ‖u - v‖ * ‖v‖ ^ k ≤ ‖u - v‖ * R ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg v) hv k) (norm_nonneg _)
    have h3 : R * (‖u - v‖ * (k * R ^ (k - 1))) ≤ ‖u - v‖ * (k * R ^ k) := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · have : R * R ^ (k - 1) = R ^ k := by
          rw [← pow_succ', Nat.sub_add_cancel hk]
        exact le_of_eq (by rw [← this]; ring)
    push_cast
    linarith

/-- `|P(u) − P(v)| ≤ |u − v| d ‖P‖₁ R^d` for `deg P ≤ d`, `|u|, |v| ≤ R`, `R ≥ 1`. -/
theorem norm_eval_sub_le {P : ℂ[X]} {d : ℕ} (h : P.natDegree ≤ d) {u v : ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖P.eval u - P.eval v‖ ≤ ‖u - v‖ * (d * (l1 P * R ^ d)) := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le h), eval_eq_sum_range' (Nat.lt_succ_of_le h),
    ← Finset.sum_sub_distrib, l1_eq_sum_range (Nat.lt_succ_of_le h), Finset.sum_mul,
    Finset.mul_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [← mul_sub, norm_mul]
  have h1 := norm_pow_sub_pow_le hu hv i
  have h2 : (i : ℝ) * R ^ (i - 1) ≤ d * R ^ d :=
    mul_le_mul (by exact_mod_cast hi') (pow_le_pow_right₀ hR (by omega)) (by positivity)
      (Nat.cast_nonneg d)
  calc ‖P.coeff i‖ * ‖u ^ i - v ^ i‖ ≤ ‖P.coeff i‖ * (‖u - v‖ * (d * R ^ d)) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)))
          (norm_nonneg _)
    _ = ‖u - v‖ * (d * (‖P.coeff i‖ * R ^ d)) := by ring

/-! ### Integrality of `(D + l)^s` -/

/-- The operator `D + l` on integer polynomials. -/
noncomputable def shiftDZ (l : ℤ) : Module.End ℤ ℤ[X] := derivative + l • (1 : Module.End ℤ ℤ[X])

theorem toC_shiftDZ (l : ℤ) (P : ℤ[X]) : toC (shiftDZ l P) = shiftD (l : ℂ) (toC P) := by
  unfold shiftDZ toC
  rw [shiftD_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Polynomial.map_add, derivative_map]
  congr 1
  rw [zsmul_eq_mul, Polynomial.map_mul, Polynomial.map_intCast, smul_eq_C_mul]
  simp

theorem toC_shiftDZ_pow (l : ℤ) (s : ℕ) (P : ℤ[X]) :
    toC ((shiftDZ l ^ s) P) = (shiftD (l : ℂ) ^ s) (toC P) := by
  induction s with
  | zero => simp
  | succ s ih => rw [pow_succ', Module.End.mul_apply, toC_shiftDZ, ih, pow_succ',
      Module.End.mul_apply]

/-! ### The powers of `i` -/

/-- The real part of `i^j`. -/
def reI (j : ℕ) : ℤ := if j % 4 = 0 then 1 else if j % 4 = 2 then -1 else 0

/-- The imaginary part of `i^j`. -/
def imI (j : ℕ) : ℤ := if j % 4 = 1 then 1 else if j % 4 = 3 then -1 else 0

theorem I_pow_eq (j : ℕ) : Complex.I ^ j = (reI j : ℂ) + Complex.I * (imI j : ℂ) := by
  have h4 : j % 4 < 4 := Nat.mod_lt _ (by norm_num)
  conv_lhs => rw [← Nat.div_add_mod j 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]
  unfold reI imI
  interval_cases h : j % 4 <;> simp [pow_succ]

theorem abs_reI_le (j : ℕ) : |reI j| ≤ 1 := by
  unfold reI
  split_ifs <;> simp

theorem abs_imI_le (j : ℕ) : |imI j| ≤ 1 := by
  unfold imI
  split_ifs <;> simp

end Azurite.Feldman
