/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# DLMF §1.2: Elementary Algebra

Formalizations of the equations of the NIST Digital Library of Mathematical Functions,
<https://dlmf.nist.gov/1.2>, one theorem per equation, named `dlmf_1_2_N`.  Each is either a
thin restatement of a Mathlib lemma (named in the docstring) or proven here.  The ledger
`docs/dlmf_plan.md` maps every equation to its theorem.

## §1.2(i) Binomial coefficients

* 1.2.1 `dlmf_1_2_1`, `dlmf_1_2_1_cast`, `dlmf_1_2_1_symm`:
  `C(n, k) = n! / ((n − k)! k!) = C(n, n − k)` (`Nat.choose_eq_factorial_div_factorial`,
  `Nat.cast_choose`, `Nat.choose_symm`).
* 1.2.2 `dlmf_1_2_2`: the binomial theorem (`add_pow`).
* 1.2.3 `dlmf_1_2_3`: `∑ C(n, k) = 2^n` (`Nat.sum_range_choose`).
* 1.2.4 `dlmf_1_2_4`: the alternating sum vanishes for `n ≥ 1`
  (`Int.alternating_sum_range_choose_of_ne`).
* 1.2.5 `dlmf_1_2_5`: the even-index sum is `2^(n−1)` for `n ≥ 1` (from 1.2.3 and 1.2.4).
* 1.2.6 `dlmf_1_2_6`, `dlmf_1_2_6_asc`, `dlmf_1_2_6_neg`: the generalized binomial coefficient
  `C(z, k) = z (z − 1) ⋯ (z − k + 1) / k! = (−1)^k (−z)_k / k! = (−1)^k C(k − z − 1, k)` for
  complex `z`, with Mathlib's `Ring.choose` (`descPochhammer`, `ascPochhammer`).
* 1.2.7 `dlmf_1_2_7`: Pascal's rule `C(z + 1, k) = C(z, k) + C(z, k − 1)` (`Ring.choose_succ_succ`).
* 1.2.8 `dlmf_1_2_8`: `∑_{k ≤ m} C(z + k, k) = C(z + m + 1, m)`.
* 1.2.9 `dlmf_1_2_9`: `∑_{k ≤ m} (−1)^k C(z, k) = (−1)^m C(z − 1, m)`.

Mathlib's `Ring.choose z k` agrees with `Nat.choose` on the natural numbers
(`Ring.choose_natCast`), so the complex-argument statements specialize to the integer ones.
-/

namespace Azurite.DLMF

open Finset Polynomial

/-! ### §1.2(i) Binomial coefficients -/

/-- **DLMF 1.2.1**, first equality, in `ℕ`: `C(n, k) = n! / ((n − k)! k!)` for `k ≤ n`; the
division is exact (`Nat.choose_mul_factorial_mul_factorial`).  Mathlib:
`Nat.choose_eq_factorial_div_factorial`. -/
theorem dlmf_1_2_1 (n k : ℕ) (hk : k ≤ n) :
    n.choose k = n.factorial / ((n - k).factorial * k.factorial) := by
  rw [Nat.choose_eq_factorial_div_factorial hk, mul_comm]

/-- **DLMF 1.2.1**, first equality, as complex numbers (any division semiring of characteristic
zero would do).  Mathlib: `Nat.cast_choose`. -/
theorem dlmf_1_2_1_cast (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℂ) = n.factorial / ((n - k).factorial * k.factorial) := by
  rw [Nat.cast_choose ℂ hk, mul_comm]

/-- **DLMF 1.2.1**, second equality: `C(n, k) = C(n, n − k)`.  Mathlib: `Nat.choose_symm`. -/
theorem dlmf_1_2_1_symm (n k : ℕ) (hk : k ≤ n) : n.choose k = n.choose (n - k) :=
  (Nat.choose_symm hk).symm

/-- **DLMF 1.2.2**, the binomial theorem
`(a + b)^n = a^n + C(n, 1) a^(n−1) b + ⋯ + C(n, n − 1) a b^(n−1) + b^n`, written as the sum
over `k = 0, …, n` of `C(n, k) a^(n−k) b^k`, in any commutative semiring.  Mathlib: `add_pow`. -/
theorem dlmf_1_2_2 {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) :
    (a + b) ^ n = ∑ k ∈ range (n + 1), (n.choose k : R) * a ^ (n - k) * b ^ k := by
  rw [add_comm, add_pow]
  refine sum_congr rfl fun k _ => ?_
  ring

/-- **DLMF 1.2.3**: `C(n, 0) + C(n, 1) + ⋯ + C(n, n) = 2^n`.  Mathlib: `Nat.sum_range_choose`. -/
theorem dlmf_1_2_3 (n : ℕ) : ∑ k ∈ range (n + 1), n.choose k = 2 ^ n :=
  Nat.sum_range_choose n

/-- **DLMF 1.2.4**: `C(n, 0) − C(n, 1) + ⋯ + (−1)^n C(n, n) = 0` for `n ≥ 1`.  Mathlib:
`Int.alternating_sum_range_choose_of_ne`. -/
theorem dlmf_1_2_4 (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * n.choose k = 0 :=
  Int.alternating_sum_range_choose_of_ne (by omega)

/-- **DLMF 1.2.5**: `C(n, 0) + C(n, 2) + C(n, 4) + ⋯ = 2^(n−1)` for `n ≥ 1`, the sum over the
even `k ≤ n`: half of 1.2.3, since the alternating sum 1.2.4 vanishes. -/
theorem dlmf_1_2_5 (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ (range (n + 1)).filter Even, n.choose k = 2 ^ (n - 1) := by
  -- in `ℤ`: `E + O = 2^n` and `E − O = 0`
  have hsplit := sum_filter_add_sum_filter_not (range (n + 1)) Even fun k => (n.choose k : ℤ)
  have halt := dlmf_1_2_4 n hn
  rw [← sum_filter_add_sum_filter_not (range (n + 1)) Even] at halt
  have hE : ∑ k ∈ (range (n + 1)).filter Even, (-1 : ℤ) ^ k * n.choose k
      = ∑ k ∈ (range (n + 1)).filter Even, (n.choose k : ℤ) := by
    refine sum_congr rfl fun k hk => ?_
    rw [(mem_filter.mp hk).2.neg_one_pow, one_mul]
  have hO : ∑ k ∈ (range (n + 1)).filter (fun k => ¬ Even k), (-1 : ℤ) ^ k * n.choose k
      = -∑ k ∈ (range (n + 1)).filter (fun k => ¬ Even k), (n.choose k : ℤ) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [(Nat.not_even_iff_odd.mp (mem_filter.mp hk).2).neg_one_pow, neg_one_mul]
  rw [hE, hO] at halt
  have htot : ∑ k ∈ range (n + 1), (n.choose k : ℤ) = 2 ^ n := by
    exact_mod_cast dlmf_1_2_3 n
  rw [htot] at hsplit
  have h2 : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hZ : ∑ k ∈ (range (n + 1)).filter Even, (n.choose k : ℤ) = 2 ^ (n - 1) := by
    linarith
  exact_mod_cast hZ

/-- `(descPochhammer ℤ k).smeval z = z (z − 1) ⋯ (z − k + 1)` on the complex numbers. -/
theorem descPochhammer_smeval_eq_prod (z : ℂ) (k : ℕ) :
    (descPochhammer ℤ k).smeval z = ∏ j ∈ range k, (z - j) := by
  rw [descPochhammer_smeval_eq_ascPochhammer, ascPochhammer_smeval_eq_eval,
    ← descPochhammer_eval_eq_ascPochhammer, descPochhammer_eval_eq_prod_range]

/-- **DLMF 1.2.6**, first equality: `C(z, k) = z (z − 1) ⋯ (z − k + 1) / k!` for complex `z`
(Mathlib's `Ring.choose`; `Ring.descPochhammer_eq_factorial_smul_choose`). -/
theorem dlmf_1_2_6 (z : ℂ) (k : ℕ) :
    Ring.choose z k = (∏ j ∈ range k, (z - j)) / k.factorial := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose z k
  rw [descPochhammer_smeval_eq_prod, nsmul_eq_mul] at h
  rw [h, mul_div_cancel_left₀ _ (by exact_mod_cast k.factorial_ne_zero)]

/-- **DLMF 1.2.6**, second equality: `C(z, k) = (−1)^k (−z)_k / k!`, with the rising factorial
`(−z)_k = (−z)(−z + 1) ⋯ (−z + k − 1)` (`ascPochhammer`). -/
theorem dlmf_1_2_6_asc (z : ℂ) (k : ℕ) :
    Ring.choose z k = (-1) ^ k * (ascPochhammer ℂ k).eval (-z) / k.factorial := by
  rw [dlmf_1_2_6, ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_prod_range,
    ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/-- **DLMF 1.2.6**, third equality: `C(z, k) = (−1)^k C(k − z − 1, k)`. -/
theorem dlmf_1_2_6_neg (z : ℂ) (k : ℕ) :
    Ring.choose z k = (-1) ^ k * Ring.choose (k - z - 1) k := by
  rw [dlmf_1_2_6, dlmf_1_2_6, ← mul_div_assoc]
  congr 1
  rw [← prod_range_reflect (fun j => ((k : ℂ) - z - 1 - j)) k,
    show ((-1 : ℂ)) ^ k = ∏ _j ∈ range k, (-1 : ℂ) by rw [prod_const, card_range],
    ← prod_mul_distrib]
  refine prod_congr rfl fun j hj => ?_
  have hj' : j < k := mem_range.mp hj
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

/-- **DLMF 1.2.7**, Pascal's rule `C(z + 1, k) = C(z, k) + C(z, k − 1)` for `k ≥ 1` (written with
`k + 1`).  Mathlib: `Ring.choose_succ_succ`. -/
theorem dlmf_1_2_7 (z : ℂ) (k : ℕ) :
    Ring.choose (z + 1) (k + 1) = Ring.choose z (k + 1) + Ring.choose z k := by
  rw [Ring.choose_succ_succ, add_comm]

/-- **DLMF 1.2.8**: `∑_{k = 0}^{m} C(z + k, k) = C(z + m + 1, m)`. -/
theorem dlmf_1_2_8 (z : ℂ) (m : ℕ) :
    ∑ k ∈ range (m + 1), Ring.choose (z + k) k = Ring.choose (z + m + 1) m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    have h := dlmf_1_2_7 (z + m + 1) m
    push_cast
    rw [← add_assoc z (m : ℂ) 1, h, add_comm]

/-- **DLMF 1.2.9**: `C(z, 0) − C(z, 1) + ⋯ + (−1)^m C(z, m) = (−1)^m C(z − 1, m)`. -/
theorem dlmf_1_2_9 (z : ℂ) (m : ℕ) :
    ∑ k ∈ range (m + 1), (-1) ^ k * Ring.choose z k = (-1) ^ m * Ring.choose (z - 1) m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    have h := dlmf_1_2_7 (z - 1) m
    rw [sub_add_cancel] at h
    rw [h]
    ring

end Azurite.DLMF
