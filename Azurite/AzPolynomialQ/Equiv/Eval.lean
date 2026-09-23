/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomialQ.Eval
import Azurite.AzPolynomialQ.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Eval
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.FieldSimp

/-!
# AzPolynomialQ.eval ↔ Polynomial.eval Equivalence

This module proves the bidirectional equivalence between `AzPolynomialQ.eval`
(which uses BPR Algorithm 8.8 special evaluation in `ℤ`) and Mathlib's
`Polynomial.eval` on the corresponding `Polynomial ℚ`.

## Main results

- `AzPolynomialQ.eval_eq_toPoly_eval` — `p.eval x = p.toPoly.eval x`
- `AzPolynomialQ.toPoly_eval_eq` — `p.toPoly.eval x = p.eval x`
-/

namespace Azurite

open Polynomial Finset _root_.Azurite.AzPolynomial

/-! ## Helper lemma -/

-- Each summand of the evalSpecial sum, after scaling by `d · c^p`,
-- matches the corresponding summand of the polynomial evaluation sum.
-- The key identity is `x.num = x * x.den` (i.e., `Rat.mul_den_eq_num`),
-- which lets us convert `x.num^k` to `x^k · x.den^k` without
-- destructuring `x` into its canonical `num/den` form.
private lemma evalSpecial_summand_eq (n : ℤ) (d : ℕ) (x : ℚ) (p k : ℕ)
    (hd : (d : ℚ) ≠ 0) (hkp : k ≤ p) :
    (n : ℚ) * (x.num : ℚ) ^ k * (x.den : ℚ) ^ (p - k) =
    ((n : ℚ) / d) * x ^ k * ((d : ℚ) * (x.den : ℚ) ^ p) := by
  rw [show (x.num : ℚ) ^ k = (x * (x.den : ℚ)) ^ k from by rw [Rat.mul_den_eq_num],
      mul_pow, mul_assoc, mul_assoc, ← pow_add, Nat.add_sub_cancel' hkp]
  field_simp

/-! ## Main equivalence -/

/-- **Correctness of `AzPolynomialQ.eval`.**
    `eval p x` equals the Mathlib `Polynomial.eval` of `p.toPoly` at `x`.

    The proof unfolds both sides to sums
    (`evalSpecial_eq_sum` and `Polynomial.eval_eq_sum_range`)
    and shows each summand matches via `evalSpecial_summand_eq`. -/
@[simp] theorem AzPolynomialQ.eval_eq_toPoly_eval (p : AzPolynomialQ) (x : ℚ) :
    p.eval x = p.toPoly.eval x := by
  unfold AzPolynomialQ.eval; simp only
  have hd : (p.denom : ℚ) ≠ 0 := by exact_mod_cast p.denom_pos.ne'
  have hc : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.pos.ne'
  have hdcp : ((p.denom : ℤ) * (x.den : ℤ) ^ p.natDegree : ℚ) ≠ 0 := by
    push_cast; exact mul_ne_zero hd (pow_ne_zero _ hc)
  rw [div_eq_iff hdcp]
  -- Unfold evalSpecial and refold so we can apply evalSpecial_eq_sum
  simp only [AzPolynomial.evalSpecial]
  rw [show (p.numerators.foldr
        (fun a x_1 => (a * x_1.2 + x_1.1 * x.num, x_1.2 * ↑x.den)) (0, 1)).1
    = (⟨p.numerators, p.last_ne_zero⟩ : AzPolynomial ℤ).evalSpecial x.num ↑x.den from rfl]
  rw [AzPolynomial.evalSpecial_eq_sum]; push_cast
  -- Unfold the RHS via Polynomial.eval_eq_sum_range
  rw [eval_eq_sum_range, AzPolynomialQ.natDegree_toPoly, Finset.sum_mul]
  -- Match ranges and summands
  by_cases hp : p.numerators.size = 0
  · -- Zero polynomial: both sums collapse
    have hnd : p.natDegree = 0 := by simp [AzPolynomialQ.natDegree, hp]
    rw [hp, hnd]; simp [AzPolynomialQ.coeff_toPoly_eq, AzPolynomialQ.coeff, hp]
  · -- Nonzero: size = natDegree + 1
    rw [show p.numerators.size = p.natDegree + 1 from by
       simp [AzPolynomialQ.natDegree]; omega]
    apply Finset.sum_congr rfl; intro k hk
    rw [Finset.mem_range] at hk; rw [AzPolynomialQ.coeff_toPoly_eq]
    simp only [AzPolynomial.coeff, AzPolynomialQ.coeff, AzPolynomial.natDegree,
               show p.numerators.size - 1 = p.natDegree from rfl]
    exact evalSpecial_summand_eq (p.numerators[k]?.getD 0)
      p.denom x p.natDegree k hd (by omega)

/-- **Mathlib → AzPolynomialQ direction.**
    Evaluating `p.toPoly` via Mathlib equals `p.eval`. -/
@[simp] theorem AzPolynomialQ.toPoly_eval_eq (p : AzPolynomialQ) (x : ℚ) :
    p.toPoly.eval x = p.eval x := (eval_eq_toPoly_eval p x).symm

end Azurite
