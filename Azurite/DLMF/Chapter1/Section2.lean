/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Roots

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

## §1.2(ii) Finite series

* 1.2.10 `dlmf_1_2_10_two_mul` (any commutative ring, `1/2` cleared), `dlmf_1_2_10`,
  `dlmf_1_2_10_last` (field of characteristic zero): the arithmetic progression.
* 1.2.11 `dlmf_1_2_11`: the geometric progression (`geom_sum_eq`).

## §1.2(iii) Partial fractions

* 1.2.12 `dlmf_1_2_12` (existence), 1.2.13 `dlmf_1_2_13` (the coefficients
  `Aⱼ = f(αⱼ) / ∏_{k ≠ j} (αⱼ − αₖ)`), from the polynomial identity `partialFractions_poly`.
* 1.2.14 `dlmf_1_2_14` (existence), 1.2.15 `dlmf_1_2_15` (`Bⱼ = f^{(n−j)}(α) / (n − j)!`), from
  the Taylor expansion (`sum_taylor_eq`, `taylor_coeff`, `factorial_smul_hasseDeriv`).
* 1.2.16 `dlmf_1_2_16`: the decomposition with multiplicities
  (`eq_quo_mul_prod_add_sum_rem_mul_prod`; the quotient vanishes by degrees).

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

/-! ### §1.2(ii) Finite series -/

/-- **DLMF 1.2.10**, the arithmetic progression, in any commutative ring with the factor `1/2`
cleared: `2 (a + (a + d) + ⋯ + (a + (n − 1) d)) = 2 n a + n (n − 1) d`. -/
theorem dlmf_1_2_10_two_mul {R : Type*} [CommRing R] (a d : R) (n : ℕ) :
    2 * ∑ k ∈ range n, (a + k * d) = 2 * n * a + n * (n - 1) * d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- **DLMF 1.2.10**, the arithmetic progression
`a + (a + d) + ⋯ + (a + (n − 1) d) = n a + n (n − 1) d / 2`, in a field of characteristic zero. -/
theorem dlmf_1_2_10 {K : Type*} [Field K] [CharZero K] (a d : K) (n : ℕ) :
    ∑ k ∈ range n, (a + k * d) = n * a + n * (n - 1) * d / 2 := by
  have h := dlmf_1_2_10_two_mul a d n
  field_simp
  linear_combination h

/-- **DLMF 1.2.10**, second equality: the sum is `n (a + ℓ) / 2` with `ℓ = a + (n − 1) d` the
last term. -/
theorem dlmf_1_2_10_last {K : Type*} [Field K] [CharZero K] (a d : K) (n : ℕ) :
    ∑ k ∈ range n, (a + k * d) = n * (a + (a + (n - 1) * d)) / 2 := by
  rw [dlmf_1_2_10]
  ring

/-- **DLMF 1.2.11**, the geometric progression
`a + a x + a x² + ⋯ + a x^(n−1) = a (1 − x^n) / (1 − x)` for `x ≠ 1`, in a division ring.
Mathlib: `geom_sum_eq`. -/
theorem dlmf_1_2_11 {K : Type*} [DivisionRing K] (a x : K) (hx : x ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, a * x ^ k = a * (1 - x ^ n) / (1 - x) := by
  rw [← mul_sum, geom_sum_eq hx, mul_div_assoc, ← neg_sub 1 (x ^ n), ← neg_sub 1 x,
    neg_div_neg_eq]

/-! ### §1.2(iii) Partial fractions

Let `α₁, …, αₙ` be distinct constants and `f` a polynomial of degree less than `n`.  The
statements are over an arbitrary field `K` (the DLMF has complex constants); the rational
functions are evaluated at points `x` different from the poles, so the identities are between
elements of `K`. -/

/-- A polynomial of negative degree is zero. -/
theorem eq_zero_of_degree_lt_zero {K : Type*} [Field K] {f : K[X]} (hf : f.degree < 0) :
    f = 0 :=
  degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp hf)

/-- The polynomial identity behind DLMF 1.2.12–1.2.13: for distinct `α` and `deg f < n`,
`f = ∑ⱼ Aⱼ ∏_{k ≠ j} (X − αₖ)` with `Aⱼ = f(αⱼ) / ∏_{k ≠ j} (αⱼ − αₖ)`, by comparing values at
the `n` points `αⱼ` (`eq_zero_of_natDegree_lt_card_of_eval_eq_zero`). -/
theorem partialFractions_poly {K : Type*} [Field K] {n : ℕ} (α : Fin n → K)
    (hα : Function.Injective α) (f : K[X]) (hf : f.degree < n) :
    f = ∑ j, C (f.eval (α j) / ∏ k ∈ univ.erase j, (α j - α k))
      * ∏ k ∈ univ.erase j, (X - C (α k)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [eq_zero_of_degree_lt_zero (f := f) (by exact_mod_cast hf)]
    simp
  set S : K[X] := ∑ j, C (f.eval (α j) / ∏ k ∈ univ.erase j, (α j - α k))
      * ∏ k ∈ univ.erase j, (X - C (α k)) with hS
  have hprod0 : ∀ j, ∏ k ∈ univ.erase j, (α j - α k) ≠ 0 := fun j =>
    prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr fun h => (mem_erase.mp hk).1 (hα h).symm
  -- `S` takes the values of `f` at the `αᵢ`
  have hSeval : ∀ i, S.eval (α i) = f.eval (α i) := by
    intro i
    rw [hS, eval_finsetSum, sum_eq_single i]
    · rw [eval_mul, eval_C, eval_prod]
      simp only [eval_sub, eval_X, eval_C]
      rw [div_mul_cancel₀ _ (hprod0 i)]
    · intro j _ hji
      rw [eval_mul, eval_prod, prod_eq_zero (s := univ.erase j)
        (f := fun k => eval (α i) (X - C (α k))) (mem_erase.mpr ⟨fun h => hji h.symm, mem_univ i⟩)
        (by simp), mul_zero]
    · intro h; exact absurd (mem_univ i) h
  -- degrees: `natDegree S ≤ n − 1`, `natDegree f < n`
  have hSdeg : S.natDegree ≤ n - 1 := by
    rw [hS]
    refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
    simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one, card_erase_of_mem (mem_univ j),
      card_univ, Fintype.card_fin, le_refl]
  have hfdeg : f.natDegree < n := by
    rcases eq_or_ne f 0 with h0 | h0
    · rw [h0, natDegree_zero]; exact hn
    · exact (natDegree_lt_iff_degree_lt h0).mpr hf
  have hzero : f - S = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero (f - S) hα (fun i => ?_) ?_
    · rw [eval_sub, hSeval, sub_self]
    · rw [Fintype.card_fin]
      exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hfdeg (by omega))
  exact sub_eq_zero.mp hzero

/-- **DLMF 1.2.13** (with 1.2.12): for distinct `α₁, …, αₙ`, `deg f < n` and `x` not a pole,
`f(x) / ((x − α₁) ⋯ (x − αₙ)) = ∑ⱼ Aⱼ / (x − αⱼ)` with `Aⱼ = f(αⱼ) / ∏_{k ≠ j} (αⱼ − αₖ)`. -/
theorem dlmf_1_2_13 {K : Type*} [Field K] {n : ℕ} (α : Fin n → K) (hα : Function.Injective α)
    (f : K[X]) (hf : f.degree < n) (x : K) (hx : ∀ j, x ≠ α j) :
    f.eval x / ∏ k, (x - α k)
      = ∑ j, (f.eval (α j) / ∏ k ∈ univ.erase j, (α j - α k)) / (x - α j) := by
  have hx0 : ∀ k, x - α k ≠ 0 := fun k => sub_ne_zero.mpr (hx k)
  conv_lhs => rw [partialFractions_poly α hα f hf]
  rw [eval_finsetSum, Finset.sum_div]
  refine sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, eval_prod, ← mul_prod_erase univ _ (mem_univ j)]
  simp only [eval_sub, eval_X, eval_C]
  have hpe : ∏ k ∈ univ.erase j, (x - α k) ≠ 0 := prod_ne_zero_iff.mpr fun k _ => hx0 k
  rw [mul_div_mul_right _ _ hpe]

/-- **DLMF 1.2.12**: the partial fraction decomposition
`f(x) / ((x − α₁) ⋯ (x − αₙ)) = A₁ / (x − α₁) + ⋯ + Aₙ / (x − αₙ)` exists (the constants
`Aⱼ` are those of 1.2.13). -/
theorem dlmf_1_2_12 {K : Type*} [Field K] {n : ℕ} (α : Fin n → K) (hα : Function.Injective α)
    (f : K[X]) (hf : f.degree < n) :
    ∃ A : Fin n → K, ∀ x, (∀ j, x ≠ α j) → f.eval x / ∏ k, (x - α k) = ∑ j, A j / (x - α j) :=
  ⟨fun j => f.eval (α j) / ∏ k ∈ univ.erase j, (α j - α k),
    fun x hx => dlmf_1_2_13 α hα f hf x hx⟩

/-- The evaluation of the iterated derivative at `α` is `k!` times that of the Hasse derivative
(`factorial_smul_hasseDeriv`). -/
theorem eval_iterate_derivative_eq_factorial_mul {K : Type*} [Field K] (f : K[X]) (α : K)
    (k : ℕ) : (derivative^[k] f).eval α = (k.factorial : K) * (hasseDeriv k f).eval α := by
  have h := congrFun (factorial_smul_hasseDeriv (R := K) k) f
  rw [LinearMap.smul_apply] at h
  rw [← h, eval_smul, nsmul_eq_mul]

/-- **DLMF 1.2.15** (with 1.2.14): for `deg f < n` and `x ≠ α`,
`f(x) / (x − α)^n = B₁ / (x − α) + B₂ / (x − α)² + ⋯ + Bₙ / (x − α)^n` with
`Bⱼ = f^{(n−j)}(α) / (n − j)!` (here `j = i + 1`, `i < n`), by the Taylor expansion of `f` at `α`
(`sum_taylor_eq`, `taylor_coeff`). -/
theorem dlmf_1_2_15 {K : Type*} [Field K] [CharZero K] (α : K) (f : K[X]) (n : ℕ)
    (hf : f.degree < n) (x : K) (hx : x ≠ α) :
    f.eval x / (x - α) ^ n
      = ∑ i ∈ range n,
          ((derivative^[n - (i + 1)] f).eval α / (n - (i + 1)).factorial) / (x - α) ^ (i + 1) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [eq_zero_of_degree_lt_zero (f := f) (by exact_mod_cast hf)]
    simp
  have hfdeg : f.natDegree < n := by
    rcases eq_or_ne f 0 with h0 | h0
    · rw [h0, natDegree_zero]; exact hn
    · exact (natDegree_lt_iff_degree_lt h0).mpr hf
  -- the Taylor expansion `f = ∑_{i < n} cᵢ (X − α)^i`, `cᵢ = (hasseDeriv i f)(α)`
  have htaylor : f = ∑ i ∈ range n, C ((hasseDeriv i f).eval α) * (X - C α) ^ i := by
    conv_lhs => rw [← sum_taylor_eq f α]
    rw [sum_over_range' _ (fun i => by simp) n (by rw [natDegree_taylor]; exact hfdeg)]
    simp only [taylor_coeff]
  have hx0 : x - α ≠ 0 := sub_ne_zero.mpr hx
  conv_lhs => rw [htaylor]
  rw [eval_finsetSum, Finset.sum_div, ← sum_range_reflect]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < n := mem_range.mp hi
  have hpow : (x - α) ^ n = (x - α) ^ (i + 1) * (x - α) ^ (n - 1 - i) := by
    rw [← pow_add]; congr 1; omega
  rw [eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_C,
    eval_iterate_derivative_eq_factorial_mul,
    mul_div_cancel_left₀ _ (by exact_mod_cast (n - (i + 1)).factorial_ne_zero),
    show n - (i + 1) = n - 1 - i by omega, hpow, mul_div_mul_right _ _ (pow_ne_zero _ hx0)]

/-- **DLMF 1.2.14**: the partial fraction decomposition of `f(x) / (x − α)^n` for `deg f < n`
exists: `B₁ / (x − α) + ⋯ + Bₙ / (x − α)^n` (the `Bⱼ` are those of 1.2.15). -/
theorem dlmf_1_2_14 {K : Type*} [Field K] [CharZero K] (α : K) (f : K[X]) (n : ℕ)
    (hf : f.degree < n) :
    ∃ B : ℕ → K, ∀ x, x ≠ α →
      f.eval x / (x - α) ^ n = ∑ i ∈ range n, B (i + 1) / (x - α) ^ (i + 1) :=
  ⟨fun j => (derivative^[n - j] f).eval α / (n - j).factorial,
    fun x hx => dlmf_1_2_15 α f n hf x hx⟩

/-- **DLMF 1.2.16**: for distinct `α₁, …, αₙ`, positive integers `m₁, …, mₙ` and
`deg f < ∑ mⱼ`, there are polynomials `fⱼ` with `deg fⱼ < mⱼ` such that
`f(x) / ((x − α₁)^{m₁} ⋯ (x − αₙ)^{mₙ}) = f₁(x) / (x − α₁)^{m₁} + ⋯ + fₙ(x) / (x − αₙ)^{mₙ}`.
From Mathlib's `eq_quo_mul_prod_add_sum_rem_mul_prod` (the quotient vanishes by degrees). -/
theorem dlmf_1_2_16 {K : Type*} [Field K] {n : ℕ} (α : Fin n → K) (hα : Function.Injective α)
    (m : Fin n → ℕ) (hm : ∀ j, 0 < m j) (f : K[X]) (hf : f.degree < ∑ j, m j) :
    ∃ g : Fin n → K[X], (∀ j, (g j).degree < m j) ∧ ∀ x, (∀ j, x ≠ α j) →
      f.eval x / ∏ j, (x - α j) ^ m j = ∑ j, (g j).eval x / (x - α j) ^ m j := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨fun j => 0, fun j => j.elim0, fun x _ => ?_⟩
    rw [eq_zero_of_degree_lt_zero (f := f) (by simpa using hf)]
    simp
  set g : Fin n → K[X] := fun j => (X - C (α j)) ^ m j with hg
  have hgdeg : ∀ j, (g j).degree = m j := fun j => by
    rw [hg]; simp only [degree_pow, degree_X_sub_C, nsmul_eq_mul, mul_one]
  have hmon : ∀ j ∈ (univ : Finset (Fin n)), (g j).Monic := fun j _ => (monic_X_sub_C _).pow _
  have hcop : Set.Pairwise (↑(univ : Finset (Fin n))) fun i j => IsCoprime (g i) (g j) :=
    fun i _ j _ hij => (pairwise_coprime_X_sub_C hα hij).pow
  obtain ⟨q, r, hr, hfq⟩ := eq_quo_mul_prod_add_sum_rem_mul_prod f hmon hcop
  have hrdeg : ∀ j, (r j).degree < m j := fun j => by
    have := hr j (mem_univ j); rwa [hgdeg] at this
  -- the quotient is zero: `deg f < ∑ mⱼ = deg ∏ gⱼ`
  have hsum : (∑ j, m j : ℕ) = ∑ j ∈ univ, (g j).natDegree := by
    refine sum_congr rfl fun j _ => ?_
    rw [hg]; simp only [natDegree_pow, natDegree_X_sub_C, mul_one]
  have hprodnat : (∏ j, g j).natDegree = ∑ j, m j := by
    rw [natDegree_prod _ _ fun j _ => (hmon j (mem_univ j)).ne_zero, hsum]
  have hSdeg : (∑ i, r i * ∏ k ∈ univ.erase i, g k).natDegree < ∑ j, m j := by
    have hpos : 0 < ∑ j, m j := by
      have := hm ⟨0, hn⟩
      exact lt_of_lt_of_le this (single_le_sum (fun j _ => Nat.zero_le _) (mem_univ _))
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := ∑ j, m j - 1) fun i _ => ?_)
      (by omega)
    refine (natDegree_mul_le).trans ?_
    have h1 : (r i).natDegree ≤ m i - 1 := by
      rcases eq_or_ne (r i) 0 with h0 | h0
      · rw [h0, natDegree_zero]; exact Nat.zero_le _
      · have := (natDegree_lt_iff_degree_lt h0).mpr (hrdeg i); omega
    have h2 : (∏ k ∈ univ.erase i, g k).natDegree ≤ ∑ k ∈ univ.erase i, m k := by
      refine (natDegree_prod_le _ _).trans (le_of_eq (sum_congr rfl fun k _ => ?_))
      rw [hg]; simp only [natDegree_pow, natDegree_X_sub_C, mul_one]
    have h3 : m i + ∑ k ∈ univ.erase i, m k = ∑ j, m j := add_sum_erase _ _ (mem_univ i)
    have := hm i
    omega
  have hq : q = 0 := by
    by_contra hq0
    have hfdeg : f.natDegree < ∑ j, m j := by
      rcases eq_or_ne f 0 with h0 | h0
      · rw [h0, natDegree_zero]
        exact lt_of_lt_of_le (hm ⟨0, hn⟩) (single_le_sum (fun j _ => Nat.zero_le _) (mem_univ _))
      · exact (natDegree_lt_iff_degree_lt h0).mpr hf
    have hqdeg : (q * ∏ j, g j).natDegree = q.natDegree + ∑ j, m j := by
      rw [natDegree_mul hq0 (monic_prod_of_monic _ _ hmon).ne_zero, hprodnat]
    have : (q * ∏ j, g j).natDegree < ∑ j, m j := by
      rw [show q * ∏ j, g j = f - ∑ i, r i * ∏ k ∈ univ.erase i, g k by rw [hfq]; ring]
      exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hfdeg hSdeg)
    omega
  rw [hq, zero_mul, zero_add] at hfq
  refine ⟨r, hrdeg, fun x hx => ?_⟩
  have hx0 : ∀ k, (x - α k) ^ m k ≠ 0 := fun k => pow_ne_zero _ (sub_ne_zero.mpr (hx k))
  conv_lhs => rw [hfq]
  rw [eval_finsetSum, Finset.sum_div]
  refine sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_prod, ← mul_prod_erase univ _ (mem_univ j)]
  simp only [hg, eval_pow, eval_sub, eval_X, eval_C]
  have hpe : ∏ k ∈ univ.erase j, (x - α k) ^ m k ≠ 0 := prod_ne_zero_iff.mpr fun k _ => hx0 k
  rw [mul_div_mul_right _ _ hpe]

end Azurite.DLMF
