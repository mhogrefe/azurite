/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.SeriesReduction

/-!
# Brent–Zimmermann §4.4.3: Rectangular series splitting

Once the number `d` of terms is fixed, the problem is to evaluate the polynomial
`P(x) = ∑_{j<d} a_j x^j` at an `n`-bit `x`.  The coefficients (or their ratios) are small rationals
of `O(log n)` bits, so a *scalar* multiplication (coefficient times an `n`-bit number) is cheap,
while a *non-scalar* multiplication (two `n`-bit numbers) costs `M(n)`.  `P(x)` can be evaluated
with `O(√n)` non-scalar multiplications, `O(n)` scalar ones and `O(n)` additions.

**Classical splitting.**  With `d = jk` and `y = x^k`,

  `P(x) = ∑_{ℓ<j} y^ℓ P_ℓ(x)`,  `P_ℓ(x) = ∑_{m<k} a_{kℓ+m} x^m`:

compute `x², …, x^k = y` (`k − 1` non-scalar products, even powers by squaring), evaluate each
`P_ℓ` with scalar products against the stored powers (not by Horner, which would be non-scalar),
and combine by Horner in `y` (`j − 1` non-scalar products).  Example `d = 12`, `j = 3`, `k = 4`:
five non-scalar products instead of the `d − 2 = 10` of Horner's rule on `P`.

**Modular splitting.**  Transposing the array (a generalized odd–even scheme), with `y = x^j`,

  `P(x) = ∑_{ℓ<j} x^ℓ P_ℓ(y)`,  `P_ℓ(y) = ∑_{m<k} a_{jm+ℓ} y^m`:

compute `y, y², …, y^(k−1)`, accumulate the row sums `S_ℓ = P_ℓ(y)` with scalar products
`a_{jm+ℓ} y^m`, and finish with `P(x) = ∑ x^ℓ S_ℓ` (Horner).  The complexities are almost the
same (Exercise 4.12); in the example, six non-scalar products (four for `y` and its powers, two
for the final combination).

* `polyEval`, `innerPoly`, `polyEval_split` — the splitting identity, over any commutative
  semiring.
* `hornerEval`, `hornerEval_eq`, `polyEval_eq_horner` — the outer Horner evaluation in `y`.
* `classicalNonscalar`, `classicalNonscalar_le_horner`, `classicalNonscalar_example`,
  `two_sqrt_le_classicalNonscalar_add_two` — the count `(k − 1) + (j − 1)` of non-scalar
  products, at most `d − 2` for `j, k ≥ 2`, equal to `5` in the example, and at least
  `2√d − 2` (attained near `j = k = √d`); `pow_two_mul_eq_sq` — even powers by squaring.
* `modularPoly`, `polyEval_modular_split`, `polyEval_eq_horner_modular` — the modular
  splitting and its Horner form; `modularNonscalar`, `modularNonscalar_example` — the count
  `(j − 1) + (k − 2) + (j − 1)`, equal to `6` in the example.
-/

namespace Azurite

namespace BZ

open Finset

section Splitting

variable {α : Type*} [CommSemiring α]

/-- `P(x) = ∑_{i<d} a_i x^i`. -/
def polyEval (a : ℕ → α) (d : ℕ) (x : α) : α := ∑ i ∈ range d, a i * x ^ i

/-- The inner polynomials `P_ℓ(x) = ∑_{m<k} a_{kℓ+m} x^m`. -/
def innerPoly (a : ℕ → α) (k ℓ : ℕ) (x : α) : α := ∑ m ∈ range k, a (k * ℓ + m) * x ^ m

/-- The classical splitting: for `d = jk`, `P(x) = ∑_{ℓ<j} (x^k)^ℓ P_ℓ(x)`. -/
theorem polyEval_split (a : ℕ → α) (j k : ℕ) (x : α) :
    polyEval a (j * k) x = ∑ ℓ ∈ range j, (x ^ k) ^ ℓ * innerPoly a k ℓ x := by
  induction j with
  | zero => simp [polyEval]
  | succ j ih =>
    rw [sum_range_succ, ← ih, polyEval, polyEval, add_mul, one_mul, sum_range_add, innerPoly,
      mul_sum]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    rw [← pow_mul, pow_add, mul_comm k j]
    ring

/-- Horner's rule: `hornerEval c n y = c_0 + y (c_1 + y (… + y c_{n−1}))`. -/
def hornerEval (c : ℕ → α) : ℕ → α → α
  | 0, _ => 0
  | n + 1, y => c 0 + y * hornerEval (fun i => c (i + 1)) n y

theorem hornerEval_eq (c : ℕ → α) (n : ℕ) (y : α) :
    hornerEval c n y = ∑ i ∈ range n, c i * y ^ i := by
  induction n generalizing c with
  | zero => simp [hornerEval]
  | succ n ih =>
    rw [hornerEval, ih, sum_range_succ', pow_zero, mul_one, add_comm, mul_sum]
    congr 1
    exact sum_congr rfl fun i _ => by ring

/-- The splitting evaluated by Horner in `y = x^k` on the inner values. -/
theorem polyEval_eq_horner (a : ℕ → α) (j k : ℕ) (x : α) :
    polyEval a (j * k) x = hornerEval (fun ℓ => innerPoly a k ℓ x) j (x ^ k) := by
  rw [polyEval_split, hornerEval_eq]
  exact sum_congr rfl fun ℓ _ => mul_comm _ _

/-- Even powers by squaring: `x^(2m) = (x^m)²`. -/
theorem pow_two_mul_eq_sq (x : α) (m : ℕ) : x ^ (2 * m) = (x ^ m) ^ 2 := by
  rw [← pow_mul, mul_comm]

/-- The row polynomials of the modular splitting, `P_ℓ(y) = ∑_{m<k} a_{jm+ℓ} y^m`. -/
def modularPoly (a : ℕ → α) (j k ℓ : ℕ) (y : α) : α := ∑ m ∈ range k, a (j * m + ℓ) * y ^ m

/-- The modular splitting: for `d = jk`, `P(x) = ∑_{ℓ<j} x^ℓ P_ℓ(x^j)`. -/
theorem polyEval_modular_split (a : ℕ → α) (j k : ℕ) (x : α) :
    polyEval a (j * k) x = ∑ ℓ ∈ range j, x ^ ℓ * modularPoly a j k ℓ (x ^ j) := by
  induction k with
  | zero => simp [polyEval, modularPoly]
  | succ k ih =>
    rw [Nat.mul_succ, polyEval, sum_range_add, ← polyEval, ih]
    simp only [modularPoly, sum_range_succ, mul_add, sum_add_distrib]
    congr 1
    refine sum_congr rfl fun ℓ _ => ?_
    rw [← pow_mul, pow_add]
    ring

/-- The modular splitting finished by Horner in `x` on the row sums. -/
theorem polyEval_eq_horner_modular (a : ℕ → α) (j k : ℕ) (x : α) :
    polyEval a (j * k) x = hornerEval (fun ℓ => modularPoly a j k ℓ (x ^ j)) j x := by
  rw [polyEval_modular_split, hornerEval_eq]
  exact sum_congr rfl fun ℓ _ => mul_comm _ _

/-- The transposition behind the modular splitting: the classical scheme (inner polynomials of
length `k`, outer sum over `j` of them) and the modular scheme with the roles of `j` and `k`
exchanged add up the same `j × k` array `a_{kℓ+m} x^{kℓ+m}`, row by row and column by column. -/
theorem classical_split_eq_modular_transpose (a : ℕ → α) (j k : ℕ) (x : α) :
    ∑ ℓ ∈ range j, (x ^ k) ^ ℓ * innerPoly a k ℓ x
      = ∑ ℓ ∈ range k, x ^ ℓ * modularPoly a k j ℓ (x ^ k) := by
  simp only [innerPoly, modularPoly, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun ℓ _ => sum_congr rfl fun m _ => ?_
  ring

end Splitting

/-! ### Counting the non-scalar multiplications -/

/-- The non-scalar products of the classical splitting: `k − 1` for the powers `x², …, x^k`
(an upper bound; squarings replace some of them) and `j − 1` for the outer Horner rule. -/
def classicalNonscalar (j k : ℕ) : ℕ := (k - 1) + (j - 1)

/-- For `j, k ≥ 2` the splitting uses at most the `d − 2` non-scalar products of Horner's rule
on `P` (whose first product `a_{d−1} x` is scalar). -/
theorem classicalNonscalar_le_horner {j k : ℕ} (hj : 2 ≤ j) (hk : 2 ≤ k) :
    classicalNonscalar j k ≤ j * k - 2 := by
  unfold classicalNonscalar
  have : j + k ≤ j * k := by nlinarith
  omega

/-- The example `d = 12 = 3 · 4`: five non-scalar products against ten. -/
theorem classicalNonscalar_example : classicalNonscalar 3 4 = 5 ∧ 3 * 4 - 2 = 10 := by decide

/-- The count is at least `2√d − 2`, with `d = jk`: the optimum is near `j = k = √d`, giving
`O(√d) = O(√n)` non-scalar products. -/
theorem two_sqrt_le_classicalNonscalar_add_two {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    2 * Real.sqrt ((j * k : ℕ) : ℝ) ≤ (classicalNonscalar j k : ℝ) + 2 := by
  unfold classicalNonscalar
  have h := two_sqrt_le_add_div (n := ((j * k : ℕ) : ℝ)) (k := (k : ℝ)) (by positivity)
    (by exact_mod_cast hk)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hdiv : ((j * k : ℕ) : ℝ) / (k : ℝ) = j := by push_cast; field_simp
  rw [hdiv] at h
  have hcast : ((k - 1 + (j - 1) : ℕ) : ℝ) + 2 = (k : ℝ) + j := by
    rw [Nat.cast_add, Nat.cast_sub hk, Nat.cast_sub hj]; push_cast; ring
  rw [hcast]
  linarith

/-- The non-scalar products of the modular splitting: `j − 1` for `y = x^j`, `k − 2` for
`y², …, y^(k−1)`, and `j − 1` for the final Horner rule in `x`. -/
def modularNonscalar (j k : ℕ) : ℕ := (j - 1) + (k - 2) + (j - 1)

/-- The example `d = 12 = 3 · 4`: six non-scalar products. -/
theorem modularNonscalar_example : modularNonscalar 3 4 = 6 := by decide

/-- The two counts differ by `j − 2` (modular has it extra); each splitting can be taken with
the roles of `j` and `k` exchanged, which is why the complexities are "almost the same". -/
theorem modularNonscalar_eq (j k : ℕ) (hj : 2 ≤ j) (hk : 2 ≤ k) :
    modularNonscalar j k = classicalNonscalar j k + (j - 2) := by
  unfold modularNonscalar classicalNonscalar
  omega

end BZ

end Azurite
