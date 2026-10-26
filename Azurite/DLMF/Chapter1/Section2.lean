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
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

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

## §1.2(iv) Means

* 1.2.17–1.2.19 `arithMean`, `geomMean`, `harmMean` (`dlmf_1_2_17`–`dlmf_1_2_19`).
* 1.2.20 `IsWeights` (`dlmf_1_2_20`), 1.2.21–1.2.22 `weightedMean` (`dlmf_1_2_21`,
  `dlmf_1_2_22`: the convention `M(r) = 0` for `r < 0` and a vanishing `aⱼ`).
* 1.2.23 `dlmf_1_2_23` (`M(r) → max` as `r → ∞`, a squeeze), 1.2.24 `dlmf_1_2_24`
  (`M(r) → min` as `r → −∞`, through the reciprocals).
* 1.2.25 `dlmf_1_2_25_arith`, `dlmf_1_2_25_harm` (`M(1) = A`, `M(−1) = H` for `pⱼ = 1/n`),
  1.2.26 `dlmf_1_2_26` (`M(r) → G` as `r → 0`, by the derivative of `log S` at `0`).

## §1.2(v) Matrices, vectors, scalar products, and norms

* 1.2.27–1.2.30 `dlmf_1_2_27`–`dlmf_1_2_30`: the matrix `[aᵢⱼ]` (`Matrix.of`), the transpose,
  the complex conjugate and the Hermitian conjugate (`conjTranspose`), entrywise.
* 1.2.31–1.2.33 `dlmf_1_2_31`–`dlmf_1_2_33`: scalar multiplication, commutativity and
  associativity of addition.
* 1.2.34–1.2.37 `dlmf_1_2_34`–`dlmf_1_2_37`: the row-times-column rule (`Matrix.mul_apply`),
  associativity (`Matrix.mul_assoc`), distributivity (`Matrix.mul_add`), the transpose of a
  product (`Matrix.transpose_mul`).
* 1.2.38–1.2.39 `dlmf_1_2_38`, `dlmf_1_2_39`: column and row vectors (`replicateCol`,
  `replicateRow`).
* 1.2.40–1.2.44 `scalarProduct` (`⟨u, v⟩ = ∑ uᵢ v̅ᵢ = vᴴ u`), `dlmf_1_2_41` (conjugate symmetry),
  `dlmf_1_2_42` (sesquilinearity), `dlmf_1_2_43` (`⟨v, v⟩ = 0 ↔ v = 0`), `Orthogonal`
  (`dlmf_1_2_44`).
* 1.2.45–1.2.48 `lpNorm` (`dlmf_1_2_45`), `dlmf_1_2_46` (`‖v‖₂ = √⟨v, v⟩`), `dlmf_1_2_47` (`ℓ¹`),
  `linfNorm` (`dlmf_1_2_48`).
* 1.2.49 `dlmf_1_2_49` (conjugate exponents, `Real.HolderConjugate`), 1.2.50 `dlmf_1_2_50`
  (Hölder, `Real.inner_le_Lp_mul_Lq_of_nonneg`), 1.2.51 `dlmf_1_2_51` and `dlmf_1_2_51_eq`
  (Cauchy–Schwarz and its equality case, `norm_inner_eq_norm_iff`), 1.2.52 `dlmf_1_2_52`
  (the triangle inequality, `norm_add_le`); the bridge `toE`, `scalarProduct_eq_inner`,
  `lpNorm_two_eq_norm` to `EuclideanSpace ℂ (Fin n)`.

## §1.2(vi) Square matrices

* 1.2.53–1.2.57 `dlmf_1_2_53` (the identity `[δᵢⱼ]`, `Matrix.one_apply`), `dlmf_1_2_54`
  (diagonal, `Matrix.IsDiag`), `dlmf_1_2_55` (real symmetric, `Matrix.IsSymm`), `dlmf_1_2_56`
  (Hermitian, `Matrix.IsHermitian`), `IsTridiagonal` (`dlmf_1_2_57`).
* 1.2.58–1.2.59 `dlmf_1_2_58` (the determinant in index form for orders `1`–`3`), `dlmf_1_2_59`
  (the Leibniz formula, `Matrix.det_apply'`).
* 1.2.60 `dlmf_1_2_60` (`A A⁻¹ = A⁻¹ A = I` for `det A ≠ 0`), `dlmf_1_2_60_unique`,
  `dlmf_1_2_60_cancel`, `dlmf_1_2_60_singular` (uniqueness, cancellation, and its failure for
  singular `A`).
* 1.2.61 `dlmf_1_2_61`, `dlmf_1_2_61_unique` (`A b = c ↔ b = A⁻¹ c`), `dlmf_1_2_61_singular`
  (no or infinitely many solutions), `dlmf_1_2_61_particular` (particular plus homogeneous).
* 1.2.62–1.2.66 `dlmf_1_2_62`–`dlmf_1_2_65` (the trace and its linearity, `tr(AB) = tr(BA)`),
  `dlmf_1_2_66` (the commutator `⁅A, B⁆`, `Ring.lie_def`).
* 1.2.67–1.2.69 `dlmf_1_2_67` (the `ℓ²` operator norm as the two maxima, via
  `Matrix.l2_opNorm_def`, the bridge `toCLM`, `lpNorm_mulVec_le` and the attainment
  `exists_lpNorm_eq_one_norm_mulVec_eq` on the compact unit sphere), `dlmf_1_2_68`
  (`‖AB‖ ≤ ‖A‖ ‖B‖`, `Matrix.l2_opNorm_mul`), `dlmf_1_2_69` (`norm_add_le`).
* 1.2.70–1.2.72 `dlmf_1_2_70` (eigenpairs, `Module.End.HasEigenvector (toLin' A)`),
  `dlmf_1_2_70_real` (a real matrix with only complex eigenvalues), `dlmf_1_2_71`,
  `dlmf_1_2_71_charpoly` (eigenvalues as roots of `det(A − λI) = 0` and of the characteristic
  polynomial), `dlmf_1_2_72` (`(A − λI) a = 0`).
* 1.2.73 `dlmf_1_2_73_linearIndependent`, `IsNonDefective`, `dlmf_1_2_73` (non-defective iff
  diagonalizable `Λ = S⁻¹ A S`), `dlmf_1_2_73_columns` (columns of `S` are eigenvectors),
  `dlmf_1_2_73_multiplicity`, `dlmf_1_2_73_sum_multiplicity` (multiplicities of the diagonal
  entries, summing to `n`).
* 1.2.74–1.2.75 `dlmf_1_2_74`, `dlmf_1_2_75` (`det A = ∏ λᵢ`, `tr A = ∑ λᵢ` through the
  similarity), `dlmf_1_2_74_roots`, `dlmf_1_2_75_roots` (for every `A`, with multiplicities;
  `Matrix.det_eq_prod_roots_charpoly`, `trace_eq_sum_roots_charpoly`).
* 1.2.76–1.2.77 `dlmf_1_2_76`, `dlmf_1_2_76_apply` (the exponential series, in norm and
  entrywise), `etr`, `dlmf_1_2_77` (`det(exp A) = exp(tr A)` for non-defective `A`),
  `dlmf_1_2_77_general` (for every square matrix, by Jacobi's formula along `t ↦ exp(tA)`:
  `detCML`, `hasDerivAt_det_of_hasDerivAt`, `hasDerivAt_exp_smul_pi`, `hasDerivAt_det_exp_smul`).

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

/-! ### §1.2(iv) Means

For `n` numbers `a₁, …, aₙ` (indexed by `Fin n`, with `n ≥ 1` wherever a maximum or minimum is
taken) and weights `p₁, …, pₙ`. -/

open Filter Topology

/-- **DLMF 1.2.17**: the arithmetic mean `A = (a₁ + a₂ + ⋯ + aₙ) / n`. -/
noncomputable def arithMean {n : ℕ} (a : Fin n → ℝ) : ℝ := (∑ i, a i) / n

theorem dlmf_1_2_17 {n : ℕ} (a : Fin n → ℝ) : arithMean a = (∑ i, a i) / n := rfl

/-- **DLMF 1.2.18**: the geometric mean `G = (a₁ a₂ ⋯ aₙ)^(1/n)` of positive numbers. -/
noncomputable def geomMean {n : ℕ} (a : Fin n → ℝ) : ℝ := (∏ i, a i) ^ (1 / n : ℝ)

theorem dlmf_1_2_18 {n : ℕ} (a : Fin n → ℝ) : geomMean a = (∏ i, a i) ^ (1 / n : ℝ) := rfl

/-- **DLMF 1.2.19**: the harmonic mean `H` of positive numbers,
`1 / H = (1 / n) (1 / a₁ + 1 / a₂ + ⋯ + 1 / aₙ)`. -/
noncomputable def harmMean {n : ℕ} (a : Fin n → ℝ) : ℝ := ((1 / n : ℝ) * ∑ i, (a i)⁻¹)⁻¹

theorem dlmf_1_2_19 {n : ℕ} (a : Fin n → ℝ) : (harmMean a)⁻¹ = (1 / n : ℝ) * ∑ i, (a i)⁻¹ :=
  inv_inv _

/-- **DLMF 1.2.20**: weights are `n` positive numbers `p₁, …, pₙ` with `p₁ + ⋯ + pₙ = 1`. -/
def IsWeights {n : ℕ} (p : Fin n → ℝ) : Prop := (∀ i, 0 < p i) ∧ ∑ i, p i = 1

theorem dlmf_1_2_20 {n : ℕ} {p : Fin n → ℝ} (hp : IsWeights p) : ∑ i, p i = 1 := hp.2

/-- The uniform weights `pⱼ = 1 / n`. -/
theorem isWeights_const {n : ℕ} [NeZero n] : IsWeights (fun _ : Fin n => (1 / n : ℝ)) := by
  refine ⟨fun _ => one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))), ?_⟩
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div_cancel]
  exact_mod_cast NeZero.ne n

/-- **DLMF 1.2.21–1.2.22**: the weighted mean `M(r) = (p₁ a₁^r + ⋯ + pₙ aₙ^r)^(1/r)` of
nonnegative numbers for `r ≠ 0`, with the convention `M(r) = 0` when `r < 0` and some `aⱼ = 0`
(1.2.22). -/
noncomputable def weightedMean {n : ℕ} (p a : Fin n → ℝ) (r : ℝ) : ℝ :=
  if r < 0 ∧ ∃ i, a i = 0 then 0 else (∑ i, p i * a i ^ r) ^ (1 / r)

/-- **DLMF 1.2.21**: outside the exceptional case of 1.2.22,
`M(r) = (p₁ a₁^r + p₂ a₂^r + ⋯ + pₙ aₙ^r)^(1/r)`. -/
theorem dlmf_1_2_21 {n : ℕ} (p a : Fin n → ℝ) (r : ℝ) (h : ¬ (r < 0 ∧ ∃ i, a i = 0)) :
    weightedMean p a r = (∑ i, p i * a i ^ r) ^ (1 / r) := by
  unfold weightedMean
  rw [ite_eq_right h]

/-- **DLMF 1.2.22**: `M(r) = 0` for `r < 0` when `a₁ a₂ ⋯ aₙ = 0`. -/
theorem dlmf_1_2_22 {n : ℕ} (p a : Fin n → ℝ) (r : ℝ) (hr : r < 0) (h : ∏ i, a i = 0) :
    weightedMean p a r = 0 := by
  unfold weightedMean
  obtain ⟨i, -, hi⟩ := prod_eq_zero_iff.mp h
  rw [ite_eq_left ⟨hr, i, hi⟩]

/-- **DLMF 1.2.23**: `M(r) → max(a₁, …, aₙ)` as `r → ∞`, for nonnegative `aⱼ` and weights `p`:
squeezed between `pⱼ₀^(1/r) · max` (the term of the maximum) and `max`. -/
theorem dlmf_1_2_23 {n : ℕ} [NeZero n] {p : Fin n → ℝ} (hp : IsWeights p) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    Tendsto (weightedMean p a) atTop (𝓝 (univ.sup' univ_nonempty a)) := by
  obtain ⟨hp0, hp1⟩ := hp
  set m := univ.sup' univ_nonempty a with hm
  obtain ⟨i₀, -, hi₀⟩ := exists_mem_eq_sup' univ_nonempty a
  have hle : ∀ i, a i ≤ m := fun i => le_sup' a (mem_univ i)
  have hm0 : 0 ≤ m := (ha i₀).trans (hle i₀)
  -- the two bounds for `r > 0`
  have hupper : ∀ r, 0 < r → weightedMean p a r ≤ m := by
    intro r hr
    rw [dlmf_1_2_21 p a r (fun h => lt_asymm hr h.1), one_div]
    have hsum : ∑ i, p i * a i ^ r ≤ m ^ r := by
      calc ∑ i, p i * a i ^ r ≤ ∑ i, p i * m ^ r :=
            sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (ha i) (hle i) hr.le) (hp0 i).le
        _ = m ^ r := by rw [← sum_mul, hp1, one_mul]
    calc (∑ i, p i * a i ^ r) ^ r⁻¹ ≤ (m ^ r) ^ r⁻¹ :=
          Real.rpow_le_rpow
            (sum_nonneg fun i _ => mul_nonneg (hp0 i).le (Real.rpow_nonneg (ha i) r))
            hsum (by positivity)
      _ = m := Real.rpow_rpow_inv hm0 hr.ne'
  have hlower : ∀ r, 0 < r → p i₀ ^ r⁻¹ * m ≤ weightedMean p a r := by
    intro r hr
    rw [dlmf_1_2_21 p a r (fun h => lt_asymm hr h.1), one_div]
    have hsum : p i₀ * m ^ r ≤ ∑ i, p i * a i ^ r := by
      rw [hm, hi₀]
      exact single_le_sum (fun i _ => mul_nonneg (hp0 i).le (Real.rpow_nonneg (ha i) r))
        (mem_univ i₀)
    calc p i₀ ^ r⁻¹ * m = (p i₀ * m ^ r) ^ r⁻¹ := by
          rw [Real.mul_rpow (hp0 i₀).le (Real.rpow_nonneg hm0 r), Real.rpow_rpow_inv hm0 hr.ne']
      _ ≤ (∑ i, p i * a i ^ r) ^ r⁻¹ :=
          Real.rpow_le_rpow (mul_nonneg (hp0 i₀).le (Real.rpow_nonneg hm0 r)) hsum (by positivity)
  -- the lower bound tends to `m`
  have hg : Tendsto (fun r : ℝ => p i₀ ^ r⁻¹ * m) atTop (𝓝 m) := by
    have h1 : Tendsto (fun r : ℝ => p i₀ ^ r⁻¹) atTop (𝓝 (p i₀ ^ (0 : ℝ))) :=
      (Real.continuousAt_const_rpow (hp0 i₀).ne').tendsto.comp tendsto_inv_atTop_zero
    rw [Real.rpow_zero] at h1
    simpa using h1.mul_const m
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hg tendsto_const_nhds
    ((eventually_gt_atTop 0).mono fun r hr => hlower r hr)
    ((eventually_gt_atTop 0).mono fun r hr => hupper r hr)

/-- The maximum of the reciprocals of positive numbers is the reciprocal of the minimum. -/
theorem sup'_inv_eq_inv_inf' {n : ℕ} [NeZero n] (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    univ.sup' univ_nonempty (fun i => (a i)⁻¹) = (univ.inf' univ_nonempty a)⁻¹ := by
  obtain ⟨j, -, hj⟩ := exists_mem_eq_inf' univ_nonempty a
  rw [hj]
  apply le_antisymm
  · refine sup'_le _ _ fun i _ => ?_
    have : a j ≤ a i := hj ▸ inf'_le a (mem_univ i)
    exact inv_anti₀ (ha j) this
  · exact le_sup' (fun i => (a i)⁻¹) (mem_univ j)

/-- **DLMF 1.2.24**: `M(r) → min(a₁, …, aₙ)` as `r → −∞`, for nonnegative `aⱼ` and weights
`p`: when some `aⱼ = 0` the mean is `0` for `r < 0` by 1.2.22, and otherwise
`M(r) = 1 / M'(−r)` for the mean `M'` of the reciprocals, so 1.2.23 applies. -/
theorem dlmf_1_2_24 {n : ℕ} [NeZero n] {p : Fin n → ℝ} (hp : IsWeights p) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    Tendsto (weightedMean p a) atBot (𝓝 (univ.inf' univ_nonempty a)) := by
  by_cases h0 : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := h0
    have hinf : univ.inf' univ_nonempty a = 0 :=
      le_antisymm (hi ▸ inf'_le a (mem_univ i)) (le_inf' _ _ fun j _ => ha j)
    rw [hinf]
    refine tendsto_const_nhds.congr' ((eventually_lt_atBot 0).mono fun r hr => ?_)
    unfold weightedMean
    rw [ite_eq_left ⟨hr, i, hi⟩]
  push Not at h0
  have hapos : ∀ i, 0 < a i := fun i => lt_of_le_of_ne (ha i) (Ne.symm (h0 i))
  -- the mean of the reciprocals
  set b : Fin n → ℝ := fun i => (a i)⁻¹ with hb
  have hb0 : ∀ i, 0 ≤ b i := fun i => (inv_pos.mpr (hapos i)).le
  have hsup := dlmf_1_2_23 hp b hb0
  rw [show univ.sup' univ_nonempty b = (univ.inf' univ_nonempty a)⁻¹ from
    sup'_inv_eq_inv_inf' a hapos] at hsup
  have hinf0 : univ.inf' univ_nonempty a ≠ 0 := by
    obtain ⟨j, -, hj⟩ := exists_mem_eq_inf' univ_nonempty a
    rw [hj]; exact (hapos j).ne'
  have hcomp := (hsup.comp tendsto_neg_atBot_atTop).inv₀ (inv_ne_zero hinf0)
  rw [inv_inv] at hcomp
  refine hcomp.congr' ((eventually_lt_atBot 0).mono fun r hr => ?_)
  -- `M(r) = (M'(−r))⁻¹` for `r < 0`
  show (weightedMean p b (-r))⁻¹ = weightedMean p a r
  rw [dlmf_1_2_21 p b (-r) (fun h => lt_asymm hr (by linarith [h.1])),
    dlmf_1_2_21 p a r (fun h => h0 h.2.choose h.2.choose_spec)]
  have hterm : ∀ i, p i * b i ^ (-r) = p i * a i ^ r := fun i => by
    rw [hb]; simp only []
    rw [Real.inv_rpow (ha i), ← Real.rpow_neg (ha i), neg_neg]
  simp only [hterm]
  rw [← Real.rpow_neg (sum_nonneg fun i _ => mul_nonneg (hp.1 i).le (Real.rpow_nonneg (ha i) r))]
  congr 1
  rw [one_div, one_div, inv_neg, neg_neg]

/-- **DLMF 1.2.25**, first part: with the uniform weights `pⱼ = 1 / n`, `M(1) = A`. -/
theorem dlmf_1_2_25_arith {n : ℕ} [NeZero n] (a : Fin n → ℝ) :
    weightedMean (fun _ => (1 / n : ℝ)) a 1 = arithMean a := by
  rw [dlmf_1_2_21 _ _ _ (fun h => lt_irrefl _ (h.1.trans zero_lt_one)), div_one, Real.rpow_one]
  simp only [Real.rpow_one, ← mul_sum, arithMean]
  ring

/-- **DLMF 1.2.25**, second part: with the uniform weights `pⱼ = 1 / n` and positive `aⱼ`,
`M(−1) = H`. -/
theorem dlmf_1_2_25_harm {n : ℕ} [NeZero n] (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    weightedMean (fun _ => (1 / n : ℝ)) a (-1) = harmMean a := by
  rw [dlmf_1_2_21 _ _ _ (fun h => (ha h.2.choose).ne' h.2.choose_spec), div_neg, div_one,
    Real.rpow_neg_one]
  simp only [Real.rpow_neg_one, ← mul_sum, harmMean]

/-- **DLMF 1.2.26**: with the uniform weights `pⱼ = 1 / n` and positive `aⱼ`, `M(r) → G` as
`r → 0`: `log M(r) = log S(r) / r` with `S(r) = (1/n) ∑ aⱼ^r`, `S(0) = 1`, and `log S` has
derivative `(1/n) ∑ log aⱼ = log G` at `0`. -/
theorem dlmf_1_2_26 {n : ℕ} [NeZero n] (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    Tendsto (weightedMean (fun _ => (1 / n : ℝ)) a) (𝓝[≠] 0) (𝓝 (geomMean a)) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  -- `S(r) = (1/n) ∑ exp (r log aⱼ)` and its derivative at `0`
  set S : ℝ → ℝ := fun r => ∑ i, (1 / n : ℝ) * Real.exp (r * Real.log (a i)) with hS
  have hS0 : S 0 = 1 := by
    rw [hS]; simp only [zero_mul, Real.exp_zero, mul_one, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have hSpos : ∀ r, 0 < S r := fun r =>
    sum_pos (fun i _ => by positivity) univ_nonempty
  have hSa : ∀ r, S r = ∑ i, (1 / n : ℝ) * a i ^ r := fun r => by
    rw [hS]; simp only []
    refine sum_congr rfl fun i _ => ?_
    rw [Real.rpow_def_of_pos (ha i), mul_comm r]
  have hSderiv : HasDerivAt S (∑ i, (1 / n : ℝ) * Real.log (a i)) 0 := by
    have h : ∀ i ∈ (univ : Finset (Fin n)),
        HasDerivAt (fun r : ℝ => (1 / n : ℝ) * Real.exp (r * Real.log (a i)))
          ((1 / n : ℝ) * Real.log (a i)) 0 := by
      intro i _
      have := (((hasDerivAt_id (0 : ℝ)).mul_const (Real.log (a i))).exp).const_mul (1 / n : ℝ)
      simpa using this
    have := HasDerivAt.sum h
    convert this using 1
    funext r
    rw [hS]
    simp only [Finset.sum_apply]
  have hlog : HasDerivAt (fun r => Real.log (S r)) (∑ i, (1 / n : ℝ) * Real.log (a i)) 0 := by
    have := hSderiv.log (hSpos 0).ne'
    rwa [hS0, div_one] at this
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hlog
  simp only [zero_add, hS0, Real.log_one, sub_zero, smul_eq_mul] at hslope
  -- `G = exp ((1/n) ∑ log aⱼ)`
  have hG : geomMean a = Real.exp (∑ i, (1 / n : ℝ) * Real.log (a i)) := by
    unfold geomMean
    rw [Real.rpow_def_of_pos (prod_pos fun i _ => ha i), Real.log_prod fun i _ => (ha i).ne',
      sum_mul]
    congr 1
    exact sum_congr rfl fun i _ => by ring
  rw [hG]
  refine (Real.continuous_exp.continuousAt.tendsto.comp hslope).congr' ?_
  refine eventually_of_mem self_mem_nhdsWithin fun r hr => ?_
  have hr : r ≠ 0 := hr
  show Real.exp (r⁻¹ * Real.log (S r)) = weightedMean (fun _ => (1 / n : ℝ)) a r
  rw [dlmf_1_2_21 _ _ _ (fun h => (ha h.2.choose).ne' h.2.choose_spec), ← hSa,
    Real.rpow_def_of_pos (hSpos r), one_div, mul_comm]

/-! ### §1.2(v) Matrices, vectors, scalar products, and norms

An `m × n` matrix with complex entries is `Matrix (Fin m) (Fin n) ℂ`, with `A i j` the entry
`aᵢⱼ`; `Aᵀ` is the transpose and `Aᴴ` the Hermitian conjugate (Mathlib's `conjTranspose`). -/

open Matrix

/-- **DLMF 1.2.27**: the `m × n` matrix `A = [aᵢⱼ]` with entries `aᵢⱼ ∈ ℂ` (`Matrix.of`). -/
theorem dlmf_1_2_27 {m n : ℕ} (a : Fin m → Fin n → ℂ) (i : Fin m) (j : Fin n) :
    (Matrix.of a : Matrix (Fin m) (Fin n) ℂ) i j = a i j :=
  of_apply a i j

/-- **DLMF 1.2.28**: the transpose `Aᵀ = [aⱼᵢ]`, an `n × m` matrix (`Matrix.transpose_apply`). -/
theorem dlmf_1_2_28 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin n) (j : Fin m) :
    Aᵀ i j = A j i :=
  transpose_apply A i j

/-- **DLMF 1.2.29**: the complex conjugate `A̅ = [a̅ᵢⱼ]`, entrywise (`Matrix.map` with the
conjugation `starRingEnd ℂ`). -/
theorem dlmf_1_2_29 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    A.map (starRingEnd ℂ) i j = starRingEnd ℂ (A i j) :=
  map_apply

/-- **DLMF 1.2.30**: the Hermitian conjugate `Aᴴ = [a̅ⱼᵢ]`, an `n × m` matrix
(`Matrix.conjTranspose_apply`). -/
theorem dlmf_1_2_30 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin n) (j : Fin m) :
    Aᴴ i j = starRingEnd ℂ (A j i) :=
  conjTranspose_apply A j i

/-- **DLMF 1.2.31**: multiplication by a scalar, `αA = Aα = [α aᵢⱼ]` (`Matrix.smul_apply`; the
right multiplication is the same since `ℂ` is commutative). -/
theorem dlmf_1_2_31 {m n : ℕ} (α : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    (α • A) i j = α * A i j ∧ (α • A) i j = A i j * α :=
  ⟨Matrix.smul_apply α A i j, by rw [Matrix.smul_apply, smul_eq_mul, mul_comm]⟩

/-- **DLMF 1.2.32**: matrix addition is commutative and entrywise,
`A + B = B + A = [aᵢⱼ + bᵢⱼ]` (`add_comm`, `Matrix.add_apply`). -/
theorem dlmf_1_2_32 {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) :
    A + B = B + A ∧ ∀ i j, (A + B) i j = A i j + B i j :=
  ⟨add_comm A B, fun i j => Matrix.add_apply A B i j⟩

/-- **DLMF 1.2.33**: matrix addition is associative,
`A + B + C = (A + B) + C = A + (B + C) = [aᵢⱼ + bᵢⱼ + cᵢⱼ]` (`add_assoc`, `Matrix.add_apply`). -/
theorem dlmf_1_2_33 {m n : ℕ} (A B C : Matrix (Fin m) (Fin n) ℂ) :
    A + B + C = A + (B + C) ∧ ∀ i j, (A + B + C) i j = A i j + B i j + C i j :=
  ⟨add_assoc A B C, fun i j => by rw [Matrix.add_apply, Matrix.add_apply]⟩

/-- **DLMF 1.2.34**: the product `C = AB` of an `m × n` by an `n × p` matrix is the `m × p`
matrix with `cᵢⱼ = ∑ₖ aᵢₖ bₖⱼ` (the row-times-column rule; `Matrix.mul_apply`). -/
theorem dlmf_1_2_34 {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p) ℂ)
    (i : Fin m) (j : Fin p) : (A * B) i j = ∑ k, A i k * B k j :=
  mul_apply

/-- **DLMF 1.2.35**: matrix multiplication is associative, `A(BC) = (AB)C`, whenever the
products are defined (`Matrix.mul_assoc`). -/
theorem dlmf_1_2_35 {m n p q : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p) ℂ)
    (C : Matrix (Fin p) (Fin q) ℂ) : A * (B * C) = A * B * C :=
  (Matrix.mul_assoc A B C).symm

/-- **DLMF 1.2.36**: multiplication distributes over addition, `A(B + C) = AB + AC`
(`Matrix.mul_add`). -/
theorem dlmf_1_2_36 {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (B C : Matrix (Fin n) (Fin p) ℂ) :
    A * (B + C) = A * B + A * C :=
  Matrix.mul_add A B C

/-- **DLMF 1.2.37**: the transpose of a product, `(AB)ᵀ = Bᵀ Aᵀ` (`Matrix.transpose_mul`). -/
theorem dlmf_1_2_37 {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p) ℂ) :
    (A * B)ᵀ = Bᵀ * Aᵀ :=
  transpose_mul A B

/-! #### Vectors, scalar products and norms

A vector of length `n` is `v : Fin n → ℂ`; the column vector of 1.2.38 is the `n × 1` matrix
`replicateCol (Fin 1) v`.  The DLMF scalar product `⟨u, v⟩ = ∑ uᵢ v̅ᵢ` is linear in its first
argument; Mathlib's `inner ℂ x y` is conjugate-linear in the first, so `⟨u, v⟩ = inner ℂ v u`
on `EuclideanSpace ℂ (Fin n)` (`scalarProduct_eq_inner`), which gives the Cauchy–Schwarz and
triangle inequalities. -/

/-- **DLMF 1.2.38**: a column vector of length `n` is an `n × 1` matrix
(`replicateCol (Fin 1) v`, entries `vᵢ`). -/
theorem dlmf_1_2_38 {n : ℕ} (v : Fin n → ℂ) (i : Fin n) (j : Fin 1) :
    replicateCol (Fin 1) v i j = v i :=
  replicateCol_apply v i j

/-- **DLMF 1.2.39**: its transpose is the row vector `vᵀ = [v₁ v₂ ⋯ vₙ]`, a `1 × n` matrix
(`Matrix.transpose_replicateCol`). -/
theorem dlmf_1_2_39 {n : ℕ} (v : Fin n → ℂ) :
    (replicateCol (Fin 1) v)ᵀ = replicateRow (Fin 1) v ∧
      ∀ (i : Fin 1) (j : Fin n), replicateRow (Fin 1) v i j = v j :=
  ⟨transpose_replicateCol v, fun i j => replicateRow_apply v i j⟩

/-- **DLMF 1.2.40**: the scalar product `⟨u, v⟩ = ∑ᵢ uᵢ v̅ᵢ` of two column vectors. -/
noncomputable def scalarProduct {n : ℕ} (u v : Fin n → ℂ) : ℂ :=
  ∑ i, u i * starRingEnd ℂ (v i)

/-- **DLMF 1.2.40**: `⟨u, v⟩ = ∑ᵢ uᵢ v̅ᵢ = vᴴ u` (the `1 × 1` matrix product). -/
theorem dlmf_1_2_40 {n : ℕ} (u v : Fin n → ℂ) :
    scalarProduct u v = ∑ i, u i * starRingEnd ℂ (v i) ∧
      scalarProduct u v = ((replicateCol (Fin 1) v)ᴴ * replicateCol (Fin 1) u) 0 0 := by
  refine ⟨rfl, ?_⟩
  unfold scalarProduct
  rw [Matrix.mul_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [conjTranspose_apply, replicateCol_apply, replicateCol_apply, mul_comm]
  rfl

/-- The vector `v` as an element of `EuclideanSpace ℂ (Fin n)`. -/
noncomputable def toE {n : ℕ} (v : Fin n → ℂ) : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v

/-- The DLMF scalar product is Mathlib's inner product with the arguments exchanged. -/
theorem scalarProduct_eq_inner {n : ℕ} (u v : Fin n → ℂ) :
    scalarProduct u v = inner ℂ (toE v) (toE u) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold toE scalarProduct dotProduct
  simp only [Pi.star_apply, Complex.star_def]

theorem toE_ne_zero {n : ℕ} {v : Fin n → ℂ} (hv : v ≠ 0) : toE v ≠ 0 := fun h =>
  hv (by simpa [toE] using congrArg WithLp.ofLp h)

/-- **DLMF 1.2.41**: `⟨u, v⟩ = ⟨v, u⟩̅`. -/
theorem dlmf_1_2_41 {n : ℕ} (u v : Fin n → ℂ) :
    scalarProduct u v = starRingEnd ℂ (scalarProduct v u) := by
  unfold scalarProduct
  rw [map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

/-- **DLMF 1.2.42**: `⟨αu, βv⟩ = α β̅ ⟨u, v⟩` for `α, β ∈ ℂ`. -/
theorem dlmf_1_2_42 {n : ℕ} (α β : ℂ) (u v : Fin n → ℂ) :
    scalarProduct (α • u) (β • v) = α * starRingEnd ℂ β * scalarProduct u v := by
  unfold scalarProduct
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

/-- **DLMF 1.2.43**: `⟨v, v⟩ = 0` iff `v = 0` (`inner_self_eq_zero`). -/
theorem dlmf_1_2_43 {n : ℕ} (v : Fin n → ℂ) : scalarProduct v v = 0 ↔ v = 0 := by
  rw [scalarProduct_eq_inner, inner_self_eq_zero]
  constructor
  · intro h
    simpa [toE] using congrArg WithLp.ofLp h
  · rintro rfl
    rfl

/-- **DLMF 1.2.44**: two vectors are orthogonal when `⟨u, v⟩ = 0`. -/
def Orthogonal {n : ℕ} (u v : Fin n → ℂ) : Prop := scalarProduct u v = 0

theorem dlmf_1_2_44 {n : ℕ} (u v : Fin n → ℂ) : Orthogonal u v ↔ scalarProduct u v = 0 :=
  Iff.rfl

/-- **DLMF 1.2.45**: the `ℓᵖ` norm `‖v‖ₚ = (∑ᵢ |vᵢ|^p)^(1/p)`, `p ≥ 1`. -/
noncomputable def lpNorm {n : ℕ} (p : ℝ) (v : Fin n → ℂ) : ℝ := (∑ i, ‖v i‖ ^ p) ^ (1 / p)

theorem dlmf_1_2_45 {n : ℕ} (p : ℝ) (v : Fin n → ℂ) :
    lpNorm p v = (∑ i, ‖v i‖ ^ p) ^ (1 / p) :=
  rfl

/-- The `ℓ²` norm is the Euclidean norm of `toE v` (`EuclideanSpace.norm_eq`). -/
theorem lpNorm_two_eq_norm {n : ℕ} (v : Fin n → ℂ) : lpNorm 2 v = ‖toE v‖ := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_rpow]
  unfold lpNorm toE
  simp only [Real.rpow_two]

/-- **DLMF 1.2.46**: the Euclidean length `‖v‖ = ‖v‖₂ = √⟨v, v⟩` (the `ℓ²` norm, implied when no
index is given; `⟨v, v⟩` is a nonnegative real). -/
theorem dlmf_1_2_46 {n : ℕ} (v : Fin n → ℂ) :
    lpNorm 2 v = Real.sqrt (scalarProduct v v).re ∧
      scalarProduct v v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  have h : scalarProduct v v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    unfold scalarProduct
    rw [Complex.ofReal_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  refine ⟨?_, h⟩
  rw [h, Complex.ofReal_re, Real.sqrt_eq_rpow]
  unfold lpNorm
  simp only [Real.rpow_two]

/-- **DLMF 1.2.47**: the `ℓ¹` norm `‖v‖₁ = ∑ᵢ |vᵢ|`. -/
theorem dlmf_1_2_47 {n : ℕ} (v : Fin n → ℂ) : lpNorm 1 v = ∑ i, ‖v i‖ := by
  unfold lpNorm
  simp only [Real.rpow_one, div_one]

/-- **DLMF 1.2.48**: the `ℓ^∞` norm `‖v‖_∞ = max(|v₁|, …, |vₙ|)` (`n ≥ 1`). -/
noncomputable def linfNorm {n : ℕ} [NeZero n] (v : Fin n → ℂ) : ℝ :=
  univ.sup' univ_nonempty fun i => ‖v i‖

theorem dlmf_1_2_48 {n : ℕ} [NeZero n] (v : Fin n → ℂ) :
    linfNorm v = univ.sup' univ_nonempty fun i => ‖v i‖ :=
  rfl

/-- **DLMF 1.2.49**: conjugate exponents, `1/p + 1/q = 1` (for `p > 1`; Mathlib's
`Real.HolderConjugate`, `Real.holderConjugate_iff`). -/
theorem dlmf_1_2_49 {p q : ℝ} (hp : 1 < p) : Real.HolderConjugate p q ↔ 1 / p + 1 / q = 1 := by
  rw [Real.holderConjugate_iff, one_div, one_div]
  exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩

/-- **DLMF 1.2.50**, Hölder's inequality: `|⟨u, v⟩| ≤ ‖u‖ₚ ‖v‖_q` for conjugate exponents
(`Real.inner_le_Lp_mul_Lq_of_nonneg` on the moduli). -/
theorem dlmf_1_2_50 {n : ℕ} {p q : ℝ} (hpq : Real.HolderConjugate p q) (u v : Fin n → ℂ) :
    ‖scalarProduct u v‖ ≤ lpNorm p u * lpNorm q v := by
  unfold scalarProduct lpNorm
  calc ‖∑ i, u i * starRingEnd ℂ (v i)‖ ≤ ∑ i, ‖u i * starRingEnd ℂ (v i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖u i‖ * ‖v i‖ := by
        refine sum_congr rfl fun i _ => ?_
        rw [norm_mul, Complex.norm_conj]
    _ ≤ (∑ i, ‖u i‖ ^ p) ^ (1 / p) * (∑ i, ‖v i‖ ^ q) ^ (1 / q) :=
        Real.inner_le_Lp_mul_Lq_of_nonneg univ hpq (fun i _ => norm_nonneg _)
          (fun i _ => norm_nonneg _)

/-- **DLMF 1.2.51**, the Cauchy–Schwarz inequality `|⟨u, v⟩| ≤ ‖u‖ ‖v‖` (Hölder with
`p = q = 2`). -/
theorem dlmf_1_2_51 {n : ℕ} (u v : Fin n → ℂ) :
    ‖scalarProduct u v‖ ≤ lpNorm 2 u * lpNorm 2 v :=
  dlmf_1_2_50 Real.HolderConjugate.two_two u v

/-- **DLMF 1.2.51**, the equality case: for nonzero `u, v`, `|⟨u, v⟩| = ‖u‖ ‖v‖` iff `v` is a
scalar multiple of `u` (`norm_inner_eq_norm_iff`). -/
theorem dlmf_1_2_51_eq {n : ℕ} {u v : Fin n → ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖scalarProduct u v‖ = lpNorm 2 u * lpNorm 2 v ↔ ∃ c : ℂ, c ≠ 0 ∧ v = c • u := by
  rw [dlmf_1_2_41, Complex.norm_conj, scalarProduct_eq_inner, lpNorm_two_eq_norm,
    lpNorm_two_eq_norm, norm_inner_eq_norm_iff (toE_ne_zero hu) (toE_ne_zero hv)]
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, ?_⟩
    have := congrArg WithLp.ofLp h
    simpa [toE] using this
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, by rw [h]; rfl⟩

/-- **DLMF 1.2.52**, the triangle inequality `‖u + v‖ ≤ ‖u‖ + ‖v‖` (`norm_add_le`). -/
theorem dlmf_1_2_52 {n : ℕ} (u v : Fin n → ℂ) :
    lpNorm 2 (u + v) ≤ lpNorm 2 u + lpNorm 2 v := by
  rw [lpNorm_two_eq_norm, lpNorm_two_eq_norm, lpNorm_two_eq_norm]
  exact norm_add_le (toE u) (toE v)

/-! ### §1.2(vi) Square matrices

A square matrix of order `n` is `Matrix (Fin n) (Fin n) ℂ`.  Mathlib's `1` is the identity
matrix, `A⁻¹` the inverse (the adjugate divided by the determinant, so defined for every `A` and
a two-sided inverse exactly when `det A ≠ 0`), `A.det` the determinant, `A.trace` the trace and
`⁅A, B⁆` the commutator. -/

/-- **DLMF 1.2.53**: the identity matrix `I = [δᵢⱼ]` (`Matrix.one_apply`). -/
theorem dlmf_1_2_53 {n : ℕ} (i j : Fin n) :
    (1 : Matrix (Fin n) (Fin n) ℂ) i j = if i = j then 1 else 0 :=
  Matrix.one_apply

/-- **DLMF 1.2.54**: `A` is a diagonal matrix if `aᵢⱼ = 0` for `i ≠ j` (`Matrix.IsDiag`). -/
theorem dlmf_1_2_54 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A.IsDiag ↔ ∀ i j, i ≠ j → A i j = 0 :=
  ⟨fun h _ _ hij => h hij, fun h _ _ hij => h _ _ hij⟩

/-- **DLMF 1.2.55**: a real matrix is symmetric if `aⱼᵢ = aᵢⱼ` (`Matrix.IsSymm.ext_iff`). -/
theorem dlmf_1_2_55 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.IsSymm ↔ ∀ i j, A j i = A i j :=
  IsSymm.ext_iff

/-- **DLMF 1.2.56**: `A` is Hermitian if `aⱼᵢ = conj aᵢⱼ` (`Matrix.IsHermitian.ext_iff`). -/
theorem dlmf_1_2_56 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A.IsHermitian ↔ ∀ i j, A j i = starRingEnd ℂ (A i j) := by
  rw [IsHermitian.ext_iff]
  simp only [Complex.star_def]
  exact forall₂_congr fun i j =>
    ⟨fun h => by rw [← h, Complex.conj_conj], fun h => by rw [h, Complex.conj_conj]⟩

/-- **DLMF 1.2.57**: `A` is tridiagonal if `aᵢⱼ = 0` for `|i − j| > 1`. -/
def IsTridiagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i j : Fin n, 1 < |(i : ℤ) - j| → A i j = 0

theorem dlmf_1_2_57 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    IsTridiagonal A ↔ ∀ i j : Fin n, 1 < |(i : ℤ) - j| → A i j = 0 :=
  Iff.rfl

/-- **DLMF 1.2.58**: the determinant `|A| = det(A)`, Mathlib's `Matrix.det`, in full index form
for orders `1`, `2` and `3` (`Matrix.det_fin_one_of`, `Matrix.det_fin_two_of`,
`Matrix.det_fin_three`); the general index form is the Leibniz formula 1.2.59. -/
theorem dlmf_1_2_58 (a b c d : ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ) :
    !![a].det = a ∧ !![a, b; c, d].det = a * d - b * c ∧
      B.det = B 0 0 * B 1 1 * B 2 2 - B 0 0 * B 1 2 * B 2 1 - B 0 1 * B 1 0 * B 2 2 +
        B 0 1 * B 1 2 * B 2 0 + B 0 2 * B 1 0 * B 2 1 - B 0 2 * B 1 1 * B 2 0 :=
  ⟨det_fin_one_of a, det_fin_two_of a b c d, det_fin_three B⟩

/-- **DLMF 1.2.59**, the Leibniz formula `det A = ∑_{σ ∈ 𝔖ₙ} sign σ ∏ᵢ a_{i,σ(i)}`
(`Matrix.det_apply'` applied to the transpose, `Matrix.det_transpose`). -/
theorem dlmf_1_2_59 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A.det = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A i (σ i) := by
  rw [← det_transpose, det_apply']
  rfl

/-- **DLMF 1.2.60**: if `det A ≠ 0` then `A A⁻¹ = A⁻¹ A = I` (`Matrix.mul_nonsing_inv`,
`Matrix.nonsing_inv_mul`; Mathlib's `A⁻¹` is the adjugate divided by the determinant). -/
theorem dlmf_1_2_60 {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.det ≠ 0) :
    A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 :=
  ⟨mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA)⟩

/-- **DLMF 1.2.60**, uniqueness of the inverse: `A B = I` or `B A = I` forces `B = A⁻¹`
(`Matrix.inv_eq_right_inv`, `Matrix.inv_eq_left_inv`). -/
theorem dlmf_1_2_60_unique {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} :
    (A * B = 1 → B = A⁻¹) ∧ (B * A = 1 → B = A⁻¹) :=
  ⟨fun h => (inv_eq_right_inv h).symm, fun h => (inv_eq_left_inv h).symm⟩

/-- **DLMF 1.2.60**, the remark on cancellation: if `det A ≠ 0` then `A B = A C` implies
`B = C`, as both sides may be multiplied by `A⁻¹` (`Matrix.nonsing_inv_mul_cancel_left`). -/
theorem dlmf_1_2_60_cancel {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.det ≠ 0)
    {B C : Matrix (Fin n) (Fin n) ℂ} (h : A * B = A * C) : B = C := by
  have hu := isUnit_iff_ne_zero.mpr hA
  rw [← nonsing_inv_mul_cancel_left A B hu, h, nonsing_inv_mul_cancel_left A C hu]

/-- **DLMF 1.2.60**, the remark on singular matrices: if `det A = 0` then `A B = A C` does not
imply `B = C` (`A = 0`, `B = 0`, `C = I`, for `n ≥ 1`). -/
theorem dlmf_1_2_60_singular {n : ℕ} [NeZero n] :
    ∃ A B C : Matrix (Fin n) (Fin n) ℂ, A.det = 0 ∧ A * B = A * C ∧ B ≠ C :=
  ⟨0, 0, 1, by have : Nonempty (Fin n) := ⟨0⟩; exact det_zero, by simp,
    fun h => by simpa using congrFun (congrFun h 0) 0⟩

/-- **DLMF 1.2.61**: if `det A ≠ 0`, the system of `n` linear equations in `n` unknowns
`A b = c` has the unique solution `b = A⁻¹ c` (`Matrix.mulVec_mulVec`, `Matrix.one_mulVec`). -/
theorem dlmf_1_2_61 {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.det ≠ 0) (b c : Fin n → ℂ) :
    A *ᵥ b = c ↔ b = A⁻¹ *ᵥ c := by
  obtain ⟨h₁, h₂⟩ := dlmf_1_2_60 hA
  constructor
  · intro h
    rw [← h, mulVec_mulVec, h₂, one_mulVec]
  · intro h
    rw [h, mulVec_mulVec, h₁, one_mulVec]

theorem dlmf_1_2_61_unique {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.det ≠ 0)
    (c : Fin n → ℂ) : ∃! b, A *ᵥ b = c :=
  ⟨A⁻¹ *ᵥ c, (dlmf_1_2_61 hA _ c).mpr rfl, fun b hb => (dlmf_1_2_61 hA b c).mp hb⟩

/-- **DLMF 1.2.61**, the singular case: if `det A = 0` then, depending on `c`, there is either
no solution or there are infinitely many (`Matrix.exists_mulVec_eq_zero_iff` gives a nonzero
`z` with `A z = 0`, and `b₀ + t z` solves the system for every `t`). -/
theorem dlmf_1_2_61_singular {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.det = 0)
    (c : Fin n → ℂ) :
    (¬ ∃ b, A *ᵥ b = c) ∨ {b | A *ᵥ b = c}.Infinite := by
  by_cases hex : ∃ b, A *ᵥ b = c
  · right
    obtain ⟨b₀, hb₀⟩ := hex
    obtain ⟨z, hz, hAz⟩ := exists_mulVec_eq_zero_iff.mpr hA
    have hinj : Function.Injective fun t : ℂ => b₀ + t • z := by
      intro s t hst
      exact smul_left_injective ℂ hz (add_left_cancel hst)
    refine (Set.infinite_range_of_injective hinj).mono ?_
    rintro _ ⟨t, rfl⟩
    show A *ᵥ (b₀ + t • z) = c
    rw [mulVec_add, mulVec_smul, hAz, hb₀, smul_zero, add_zero]
  · exact Or.inl hex

/-- **DLMF 1.2.61**, the structure of the solutions: every solution is the sum of a particular
solution `b₀` and a solution of `A b = 0`. -/
theorem dlmf_1_2_61_particular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {b₀ c : Fin n → ℂ}
    (hb₀ : A *ᵥ b₀ = c) (b : Fin n → ℂ) :
    A *ᵥ b = c ↔ ∃ z, A *ᵥ z = 0 ∧ b = b₀ + z := by
  constructor
  · intro h
    exact ⟨b - b₀, by rw [mulVec_sub, h, hb₀, sub_self], by abel⟩
  · rintro ⟨z, hz, rfl⟩
    rw [mulVec_add, hb₀, hz, add_zero]

/-- **DLMF 1.2.62**: the trace `tr A = ∑ᵢ aᵢᵢ` (`Matrix.trace`). -/
theorem dlmf_1_2_62 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : A.trace = ∑ i, A i i :=
  rfl

/-- **DLMF 1.2.63**: `tr(αA) = α tr A` (`Matrix.trace_smul`). -/
theorem dlmf_1_2_63 {n : ℕ} (α : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (α • A).trace = α * A.trace := by
  rw [trace_smul, smul_eq_mul]

/-- **DLMF 1.2.64**: `tr(A + B) = tr A + tr B` (`Matrix.trace_add`). -/
theorem dlmf_1_2_64 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A + B).trace = A.trace + B.trace :=
  trace_add A B

/-- **DLMF 1.2.65**: `tr(AB) = tr(BA)` (`Matrix.trace_mul_comm`). -/
theorem dlmf_1_2_65 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A * B).trace = (B * A).trace :=
  trace_mul_comm A B

/-- **DLMF 1.2.66**: the commutator `[A, B] = −[B, A] = AB − BA` (the Lie bracket of the matrix
ring, `Ring.lie_def`). -/
theorem dlmf_1_2_66 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    ⁅A, B⁆ = -⁅B, A⁆ ∧ ⁅A, B⁆ = A * B - B * A :=
  ⟨by rw [Ring.lie_def, Ring.lie_def, neg_sub], Ring.lie_def A B⟩

/-! #### Norms of square matrices

`‖A‖` is the `ℓ²` operator norm (Mathlib's scoped instance `Matrix.Norms.L2Operator`,
`Matrix.l2_opNorm_def`): the norm of the continuous linear map `x ↦ A x` on
`EuclideanSpace ℂ (Fin n)`.  DLMF's two maxima are 1.2.67. -/

section L2OpNorm

open scoped Matrix.Norms.L2Operator

/-- The continuous linear map `x ↦ A x` on `EuclideanSpace ℂ (Fin n)`. -/
noncomputable def toCLM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A

theorem toCLM_toE {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    toCLM A (toE x) = toE (A *ᵥ x) :=
  rfl

theorem norm_eq_norm_toCLM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ = ‖toCLM A‖ :=
  l2_opNorm_def A

/-- `‖A x‖ ≤ ‖A‖ ‖x‖` (`ContinuousLinearMap.le_opNorm`). -/
theorem lpNorm_mulVec_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    lpNorm 2 (A *ᵥ x) ≤ ‖A‖ * lpNorm 2 x := by
  rw [lpNorm_two_eq_norm, lpNorm_two_eq_norm, norm_eq_norm_toCLM, ← toCLM_toE]
  exact (toCLM A).le_opNorm (toE x)

/-- The operator norm is attained on the unit sphere (`n ≥ 1`): the sphere is compact
(`isCompact_sphere`) and `x ↦ ‖A x‖` is continuous. -/
theorem exists_lpNorm_eq_one_norm_mulVec_eq {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ x : Fin n → ℂ, lpNorm 2 x = 1 ∧ lpNorm 2 (A *ᵥ x) = ‖A‖ := by
  have hne : (Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1).Nonempty :=
    ⟨EuclideanSpace.single 0 1, by rw [mem_sphere_zero_iff_norm, PiLp.norm_single, norm_one]⟩
  obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ (Fin n)) 1).exists_isMaxOn
    hne (toCLM A).continuous.norm.continuousOn
  rw [mem_sphere_zero_iff_norm] at hx₀
  have hx : toE x₀.ofLp = x₀ := rfl
  refine ⟨x₀.ofLp, by rw [lpNorm_two_eq_norm, hx, hx₀], ?_⟩
  rw [lpNorm_two_eq_norm, norm_eq_norm_toCLM, ← toCLM_toE, hx]
  apply le_antisymm
  · calc ‖toCLM A x₀‖ ≤ ‖toCLM A‖ * ‖x₀‖ := (toCLM A).le_opNorm x₀
      _ = ‖toCLM A‖ := by rw [hx₀, mul_one]
  · refine (toCLM A).opNorm_le_bound (norm_nonneg _) fun y => ?_
    by_cases hy : y = 0
    · simp [hy]
    · have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have h2 : ‖toCLM A ((‖y‖⁻¹ : ℂ) • y)‖ ≤ ‖toCLM A x₀‖ :=
        hmax (mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℂ) hy))
      rw [map_smul, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (norm_nonneg y)] at h2
      rw [inv_mul_le_iff₀ hypos] at h2
      rw [mul_comm]
      exact h2

/-- **DLMF 1.2.67**: the norm of a square matrix of order `n ≥ 1`,
`‖A‖ = max_{x ≠ 0} ‖A x‖ / ‖x‖ = max_{‖x‖ = 1} ‖A x‖` with the `ℓ²` vector norm: `‖A‖` is the
greatest value of each expression. -/
theorem dlmf_1_2_67 {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) :
    IsGreatest ((fun x : Fin n → ℂ => lpNorm 2 (A *ᵥ x) / lpNorm 2 x) '' {x | x ≠ 0}) ‖A‖ ∧
      IsGreatest ((fun x : Fin n → ℂ => lpNorm 2 (A *ᵥ x)) '' {x | lpNorm 2 x = 1}) ‖A‖ := by
  obtain ⟨x₀, hx₀, hAx₀⟩ := exists_lpNorm_eq_one_norm_mulVec_eq A
  have hx₀ne : x₀ ≠ 0 := by
    rintro rfl
    rw [lpNorm_two_eq_norm, show toE (0 : Fin n → ℂ) = 0 from rfl, norm_zero] at hx₀
    exact zero_ne_one hx₀
  refine ⟨⟨⟨x₀, hx₀ne, by simp only [hAx₀, hx₀, div_one]⟩, ?_⟩, ⟨⟨x₀, hx₀, hAx₀⟩, ?_⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hpos : 0 < lpNorm 2 x := by
      rw [lpNorm_two_eq_norm]
      exact norm_pos_iff.mpr (toE_ne_zero hx)
    exact div_le_of_le_mul₀ hpos.le (norm_nonneg _) (lpNorm_mulVec_le A x)
  · rintro _ ⟨x, hx, rfl⟩
    have := lpNorm_mulVec_le A x
    rwa [hx, mul_one] at this

/-- **DLMF 1.2.68**: `‖AB‖ ≤ ‖A‖ ‖B‖` (`Matrix.l2_opNorm_mul`). -/
theorem dlmf_1_2_68 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  l2_opNorm_mul A B

/-- **DLMF 1.2.69**: `‖A + B‖ ≤ ‖A‖ + ‖B‖` (`norm_add_le`). -/
theorem dlmf_1_2_69 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : ‖A + B‖ ≤ ‖A‖ + ‖B‖ :=
  norm_add_le A B

end L2OpNorm

/-! #### Eigenvectors and eigenvalues of square matrices

An eigenvector `a` of `A` for the eigenvalue `λ` is Mathlib's
`Module.End.HasEigenvector (Matrix.toLin' A) λ a`, and `Module.End.HasEigenvalue (toLin' A) λ`
says that one exists. -/

/-- **DLMF 1.2.70**: `A` has the eigenvalue `λ` with eigenvector `a ≠ 0` if `A a = λ a`
(`Module.End.hasEigenvector_iff`, `Module.End.mem_eigenspace_iff`). -/
theorem dlmf_1_2_70 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) (a : Fin n → ℂ) :
    Module.End.HasEigenvector (toLin' A) μ a ↔ a ≠ 0 ∧ A *ᵥ a = μ • a := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, toLin'_apply, and_comm]

/-- **DLMF 1.2.70**, the remark that `a` and `λ` may be complex even if `A` is real: the
rotation `!![0, −1; 1, 0]` has no real eigenvalue, but over `ℂ` it has the eigenvalue `i` with
eigenvector `(1, −i)` (`Matrix.charpoly_fin_two`). -/
theorem dlmf_1_2_70_real :
    (∀ μ : ℝ, ¬ Module.End.HasEigenvalue (toLin' !![(0 : ℝ), -1; 1, 0]) μ) ∧
      Module.End.HasEigenvector (toLin' !![(0 : ℂ), -1; 1, 0]) Complex.I ![1, -Complex.I] := by
  constructor
  · intro μ h
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, charpoly_toLin', charpoly_fin_two,
      trace_fin_two_of, det_fin_two_of, IsRoot.def] at h
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C] at h
    nlinarith [sq_nonneg μ]
  · rw [dlmf_1_2_70]
    refine ⟨?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp at this
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `A a = λ a` iff `(A − λ I) a = 0` (1.2.72), the form used to solve 1.2.71. -/
theorem mulVec_eq_smul_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) (a : Fin n → ℂ) :
    A *ᵥ a = μ • a ↔ (A - μ • 1) *ᵥ a = 0 := by
  rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]

/-- **DLMF 1.2.71**: the eigenvalues are the roots of the polynomial equation `det(A − λ I) = 0`
(from `Matrix.exists_mulVec_eq_zero_iff`). -/
theorem dlmf_1_2_71 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    Module.End.HasEigenvalue (toLin' A) μ ↔ (A - μ • 1).det = 0 := by
  rw [← exists_mulVec_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := h.exists_hasEigenvector
    rw [dlmf_1_2_70, mulVec_eq_smul_iff] at ha
    exact ⟨a, ha⟩
  · rintro ⟨a, ha, hAa⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ((dlmf_1_2_70 A μ a).mpr ⟨ha, (mulVec_eq_smul_iff A μ a).mpr hAa⟩)

/-- **DLMF 1.2.71**, as a polynomial equation: `λ` is an eigenvalue iff it is a root of the
characteristic polynomial `det(λ I − A)` (`Module.End.hasEigenvalue_iff_isRoot_charpoly`,
`Matrix.charpoly_toLin'`). -/
theorem dlmf_1_2_71_charpoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    Module.End.HasEigenvalue (toLin' A) μ ↔ A.charpoly.IsRoot μ := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, charpoly_toLin']

/-- **DLMF 1.2.72**: the eigenvectors for `λ` are the nonzero solutions of `(A − λ I) a = 0`. -/
theorem dlmf_1_2_72 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) (a : Fin n → ℂ) :
    Module.End.HasEigenvector (toLin' A) μ a ↔ a ≠ 0 ∧ (A - μ • 1) *ᵥ a = 0 := by
  rw [dlmf_1_2_70, mulVec_eq_smul_iff]

/-! #### Non-defective square matrices -/

/-- **DLMF**, the definition of linear independence: `v₁, …, vₘ` are linearly independent if
`∑ cᵢ vᵢ = 0` implies that all coefficients `cᵢ` are zero (`Fintype.linearIndependent_iff`). -/
theorem dlmf_1_2_73_linearIndependent {n m : ℕ} (v : Fin m → Fin n → ℂ) :
    LinearIndependent ℂ v ↔ ∀ c : Fin m → ℂ, ∑ i, c i • v i = 0 → ∀ i, c i = 0 :=
  Fintype.linearIndependent_iff

/-- A matrix of order `n` is non-defective if it has `n` linearly independent eigenvectors. -/
def IsNonDefective {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ v : Fin n → Fin n → ℂ,
    LinearIndependent ℂ v ∧ ∀ i, ∃ μ, Module.End.HasEigenvector (toLin' A) μ (v i)

/-- If `A S = S Λ` with `Λ` diagonal, the `j`-th column of `S` satisfies `A s = Λⱼⱼ s`. -/
theorem mulVec_col_eq_smul {n : ℕ} {A S Λ : Matrix (Fin n) (Fin n) ℂ} (hΛ : Λ.IsDiag)
    (h : A * S = S * Λ) (j : Fin n) : A *ᵥ S.col j = Λ j j • S.col j := by
  ext i
  have := congrFun (congrFun h i) j
  rw [← hΛ.diagonal_diag, mul_diagonal, Matrix.mul_apply] at this
  show ∑ k, A i k * S k j = Λ j j * S i j
  rw [this, mul_comm]
  rfl

/-- **DLMF 1.2.73**: the non-defective matrices are precisely those that can be diagonalized by
a similarity transformation `Λ = S⁻¹ A S` with `S` invertible and `Λ` diagonal
(`Matrix.linearIndependent_cols_iff_isUnit`). -/
theorem dlmf_1_2_73 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    IsNonDefective A ↔
      ∃ S Λ : Matrix (Fin n) (Fin n) ℂ, S.det ≠ 0 ∧ Λ.IsDiag ∧ Λ = S⁻¹ * A * S := by
  constructor
  · rintro ⟨v, hv, hev⟩
    choose μ hμ using hev
    set S : Matrix (Fin n) (Fin n) ℂ := (Matrix.of v)ᵀ with hS
    have hcol : S.col = v := by
      ext j i
      rfl
    have hu : IsUnit S := linearIndependent_cols_iff_isUnit.mp (hcol ▸ hv)
    have hdet : IsUnit S.det := (isUnit_iff_isUnit_det S).mp hu
    refine ⟨S, diagonal μ, isUnit_iff_ne_zero.mp hdet, isDiag_diagonal μ, ?_⟩
    have hAS : A * S = S * diagonal μ := by
      ext i j
      rw [mul_diagonal]
      have := congrFun ((dlmf_1_2_70 A (μ j) (v j)).mp (hμ j)).2 i
      rw [Pi.smul_apply, smul_eq_mul] at this
      show ∑ k, A i k * v j k = v j i * μ j
      rw [mul_comm, ← this]
      rfl
    rw [mul_assoc, hAS, nonsing_inv_mul_cancel_left S _ hdet]
  · rintro ⟨S, Λ, hS, hΛ, h⟩
    have hdet : IsUnit S.det := isUnit_iff_ne_zero.mpr hS
    have hu : IsUnit S := (isUnit_iff_isUnit_det S).mpr hdet
    have hAS : A * S = S * Λ := by
      rw [h, ← mul_assoc, mul_nonsing_inv_cancel_left S _ hdet]
    have hv : LinearIndependent ℂ S.col := linearIndependent_cols_iff_isUnit.mpr hu
    exact ⟨S.col, hv, fun j =>
      ⟨Λ j j, (dlmf_1_2_70 A _ _).mpr ⟨hv.ne_zero j, mulVec_col_eq_smul hΛ hAS j⟩⟩⟩

/-- **DLMF 1.2.73**, the columns of `S` are eigenvectors of `A` with the diagonal entries of
`Λ` as eigenvalues. -/
theorem dlmf_1_2_73_columns {n : ℕ} {A S Λ : Matrix (Fin n) (Fin n) ℂ} (hS : S.det ≠ 0)
    (hΛ : Λ.IsDiag) (h : Λ = S⁻¹ * A * S) (j : Fin n) :
    Module.End.HasEigenvector (toLin' A) (Λ j j) (S.col j) := by
  have hdet : IsUnit S.det := isUnit_iff_ne_zero.mpr hS
  have hAS : A * S = S * Λ := by
    rw [h, ← mul_assoc, mul_nonsing_inv_cancel_left S _ hdet]
  exact (dlmf_1_2_70 A _ _).mpr
    ⟨(linearIndependent_cols_iff_isUnit.mpr ((isUnit_iff_isUnit_det S).mpr hdet)).ne_zero j,
      mulVec_col_eq_smul hΛ hAS j⟩

/-- **DLMF 1.2.73**, multiplicities: the diagonal entries of `Λ` need not be distinct, and the
number of entries equal to `λ` is the multiplicity of the eigenvalue `λ` (as a root of the
characteristic polynomial; `Matrix.charpoly_units_conj'`, `Matrix.charpoly_diagonal`,
`Polynomial.roots_multiset_prod_X_sub_C`). -/
theorem dlmf_1_2_73_multiplicity {n : ℕ} {A S Λ : Matrix (Fin n) (Fin n) ℂ} (hS : S.det ≠ 0)
    (hΛ : Λ.IsDiag) (h : Λ = S⁻¹ * A * S) (μ : ℂ) :
    A.charpoly.rootMultiplicity μ = (univ.filter fun j => Λ j j = μ).card := by
  obtain ⟨U, hU⟩ := (isUnit_iff_isUnit_det S).mpr (isUnit_iff_ne_zero.mpr hS)
  have hA : A.charpoly = Λ.charpoly := by
    rw [h, ← hU, charpoly_units_conj']
  rw [hA, ← hΛ.diagonal_diag, charpoly_diagonal, ← count_roots, prod_eq_multiset_prod,
    show (univ.val.map fun i => X - C (diag Λ i)) = (univ.val.map (diag Λ)).map fun a => X - C a
      by rw [Multiset.map_map]; rfl,
    roots_multiset_prod_X_sub_C, Multiset.count_map, card_def, filter_val]
  congr 1
  exact Multiset.filter_congr fun j _ => by rw [diagonal_apply_eq, eq_comm]

/-- **DLMF 1.2.73**, the sum of all multiplicities is `n` (for every square matrix over `ℂ`:
the characteristic polynomial has degree `n` and splits; `Matrix.charpoly_natDegree_eq_dim`,
`Polynomial.Splits.natDegree_eq_card_roots`). -/
theorem dlmf_1_2_73_sum_multiplicity {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∑ μ ∈ A.charpoly.roots.toFinset, A.charpoly.rootMultiplicity μ = n := by
  simp_rw [← count_roots]
  rw [Multiset.toFinset_sum_count_eq,
    ← Polynomial.Splits.natDegree_eq_card_roots (IsAlgClosed.splits A.charpoly),
    charpoly_natDegree_eq_dim, Fintype.card_fin]

/-! #### Relation of eigenvalues to the determinant and trace -/

/-- **DLMF 1.2.74**: for non-defective `A` with `Λ = S⁻¹ A S`,
`det A = det(S S⁻¹ A) = det(S⁻¹ A S) = ∏ λᵢ` (`Matrix.det_mul`, `Matrix.det_diagonal`). -/
theorem dlmf_1_2_74 {n : ℕ} {A S Λ : Matrix (Fin n) (Fin n) ℂ} (hS : S.det ≠ 0)
    (hΛ : Λ.IsDiag) (h : Λ = S⁻¹ * A * S) :
    A.det = (S * S⁻¹ * A).det ∧ (S * S⁻¹ * A).det = (S⁻¹ * A * S).det ∧
      (S⁻¹ * A * S).det = ∏ i, Λ i i := by
  refine ⟨by rw [mul_nonsing_inv S (isUnit_iff_ne_zero.mpr hS), one_mul], ?_, ?_⟩
  · simp only [det_mul]
    ring
  · rw [← h, ← hΛ.diagonal_diag, det_diagonal]
    exact prod_congr rfl fun i _ => (diagonal_apply_eq _ i).symm

/-- **DLMF 1.2.74**, the remark: `det A` is the product of the `n` eigenvalues counted with
multiplicity, for every square matrix over `ℂ` (`Matrix.det_eq_prod_roots_charpoly`). -/
theorem dlmf_1_2_74_roots {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A.det = A.charpoly.roots.prod :=
  det_eq_prod_roots_charpoly A

/-- **DLMF 1.2.75**: for non-defective `A` with `Λ = S⁻¹ A S`,
`tr A = tr(S S⁻¹ A) = tr(S⁻¹ A S) = ∑ λᵢ` (`Matrix.trace_mul_comm`, `Matrix.trace_diagonal`). -/
theorem dlmf_1_2_75 {n : ℕ} {A S Λ : Matrix (Fin n) (Fin n) ℂ} (hS : S.det ≠ 0)
    (hΛ : Λ.IsDiag) (h : Λ = S⁻¹ * A * S) :
    A.trace = (S * S⁻¹ * A).trace ∧ (S * S⁻¹ * A).trace = (S⁻¹ * A * S).trace ∧
      (S⁻¹ * A * S).trace = ∑ i, Λ i i := by
  refine ⟨by rw [mul_nonsing_inv S (isUnit_iff_ne_zero.mpr hS), one_mul], ?_, ?_⟩
  · rw [mul_assoc, trace_mul_comm]
  · rw [← h, ← hΛ.diagonal_diag, trace_diagonal]
    exact sum_congr rfl fun i _ => (diagonal_apply_eq _ i).symm

/-- **DLMF 1.2.75**, the remark: `tr A` is the sum of the eigenvalues counted with multiplicity,
for every square matrix over `ℂ` (`Matrix.trace_eq_sum_roots_charpoly`). -/
theorem dlmf_1_2_75_roots {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A.trace = A.charpoly.roots.sum :=
  trace_eq_sum_roots_charpoly A

/-! #### The matrix exponential and the exponential of the trace

`NormedSpace.exp A` is Mathlib's exponential of the matrix ring with its product topology; every
matrix norm gives the same series (`Mathlib.Analysis.Normed.Algebra.MatrixExponential`). -/

/-- **DLMF 1.2.76**: `exp A = ∑_{n ≥ 0} Aⁿ / n!`, convergent in norm for every `A`
(`NormedSpace.exp_series_hasSum_exp'` under the `ℓ²` operator norm). -/
theorem dlmf_1_2_76 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    HasSum (fun k : ℕ => (k.factorial⁻¹ : ℂ) • A ^ k) (NormedSpace.exp A) := by
  open scoped Matrix.Norms.L2Operator in
  exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A

/-- **DLMF 1.2.76**, entrywise convergence (`Pi.hasSum`). -/
theorem dlmf_1_2_76_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasSum (fun k : ℕ => (k.factorial⁻¹ : ℂ) * (A ^ k) i j) (NormedSpace.exp A i j) := by
  have := Pi.hasSum.mp (Pi.hasSum.mp (dlmf_1_2_76 A) i) j
  simpa using this

/-- **DLMF 1.2.77**: the exponential of the trace, `etr(A) = exp(tr A)`. -/
noncomputable def etr {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℂ := Complex.exp A.trace

/-- **DLMF 1.2.77**: for a non-defective matrix, `det(exp A) = exp(tr A) = etr(A)`
(from 1.2.73–1.2.75: `Matrix.exp_conj`, `Matrix.exp_diagonal`, `Matrix.det_conj`,
`Complex.exp_sum`).  The DLMF remarks that the formula holds for every square matrix
(Hall 2015, Thm 2.12): that is `dlmf_1_2_77_general` below. -/
theorem dlmf_1_2_77 {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsNonDefective A) :
    (NormedSpace.exp A).det = Complex.exp A.trace ∧ Complex.exp A.trace = etr A := by
  refine ⟨?_, rfl⟩
  obtain ⟨S, Λ, hS, hΛ, h⟩ := (dlmf_1_2_73 A).mp hA
  have hdet : IsUnit S.det := isUnit_iff_ne_zero.mpr hS
  have hu : IsUnit S := (isUnit_iff_isUnit_det S).mpr hdet
  have hA' : A = S * Λ * S⁻¹ := by
    rw [h, ← mul_assoc, mul_nonsing_inv_cancel_left S _ hdet, mul_assoc,
      mul_nonsing_inv S hdet, mul_one]
  rw [hA', Matrix.exp_conj S Λ hu, det_conj hu, trace_mul_cycle, nonsing_inv_mul S hdet, one_mul,
    ← hΛ.diagonal_diag, Matrix.exp_diagonal, det_diagonal, trace_diagonal, Complex.exp_sum]
  refine prod_congr rfl fun i _ => ?_
  rw [Pi.coe_exp, Complex.exp_eq_exp_ℂ]

/-! #### `det(exp A) = exp(tr A)` for every square matrix

Jacobi's formula along the curve `t ↦ exp(tA)`: the determinant is a continuous multilinear
function of the rows, so `d/dt det M(t) = ∑ᵢ det(M with row i replaced by M'ᵢ)`; with
`M' = A M` each term is `aᵢᵢ det M` (`Matrix.det_updateRow_sum`), hence
`f(t) = det(exp(tA))` solves `f' = tr(A) f`, `f(0) = 1`, and `f(t) exp(−t tr A)` is constant. -/

/-- The determinant as a continuous multilinear map of the rows (`Matrix.detRowAlternating`). -/
noncomputable def detCML (n : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin n → ℂ) ℂ :=
  { ((detRowAlternating : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ).toMultilinearMap :
      MultilinearMap ℂ (fun _ : Fin n => Fin n → ℂ) ℂ) with
    cont := Continuous.matrix_det continuous_id }

theorem detCML_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : detCML n M = M.det :=
  rfl

/-- The row `i` of `A * M` is the combination `∑ₖ aᵢₖ Mₖ` of the rows of `M`. -/
theorem mul_row_eq_sum {n : ℕ} (A M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (A * M) i = ∑ k, A i k • M k := by
  funext j
  rw [Matrix.mul_apply, Finset.sum_apply]
  rfl

/-- Jacobi's formula for `M' = A M`: if the rows of `M` move with velocity `A M`, the
determinant moves with velocity `tr(A) det M`. -/
theorem hasDerivAt_det_of_hasDerivAt {n : ℕ} {M : ℂ → Fin n → Fin n → ℂ}
    (A : Matrix (Fin n) (Fin n) ℂ) {t : ℂ}
    (hM : HasDerivAt M (Matrix.of.symm (A * Matrix.of (M t))) t) :
    HasDerivAt (fun u => Matrix.det (Matrix.of (M u)))
      (A.trace * Matrix.det (Matrix.of (M t))) t := by
  have h := ((detCML n).hasFDerivAt (M t)).comp_hasDerivAt t hM
  refine h.congr_deriv ?_
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  change ∑ i, (Matrix.updateRow (Matrix.of (M t)) i ((A * Matrix.of (M t)) i)).det = _
  simp_rw [mul_row_eq_sum, det_updateRow_sum, smul_eq_mul, ← Finset.sum_mul]
  rfl

section L2OpNorm

open scoped Matrix.Norms.L2Operator

/-- `t ↦ exp(tA)` is differentiable entrywise with derivative `A exp(tA)`
(`hasDerivAt_exp_smul_const'` under the `ℓ²` operator norm, projected to each entry). -/
theorem hasDerivAt_exp_smul_pi {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    HasDerivAt (fun u : ℂ => Matrix.of.symm (NormedSpace.exp (u • A)))
      (Matrix.of.symm (A * NormedSpace.exp (t • A))) t := by
  have h : HasDerivAt (fun u : ℂ => NormedSpace.exp (u • A)) (A * NormedSpace.exp (t • A)) t :=
    hasDerivAt_exp_smul_const' A t
  refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
  let p : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap p).hasFDerivAt.comp_hasDerivAt t h

end L2OpNorm

/-- `f(t) = det(exp(tA))` satisfies `f' = tr(A) f`. -/
theorem hasDerivAt_det_exp_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    HasDerivAt (fun u : ℂ => (NormedSpace.exp (u • A)).det)
      (A.trace * (NormedSpace.exp (t • A)).det) t :=
  hasDerivAt_det_of_hasDerivAt A (hasDerivAt_exp_smul_pi A t)

/-- **DLMF 1.2.77**, the remark: `det(exp A) = exp(tr A)` holds for every square matrix, not
only the non-defective ones (Hall 2015, Thm 2.12).  Proof by Jacobi's formula:
`t ↦ det(exp(tA)) exp(−t tr A)` has zero derivative, so it is constant (`is_const_of_deriv_eq_zero`)
and equal to its value `1` at `t = 0`. -/
theorem dlmf_1_2_77_general {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (NormedSpace.exp A).det = Complex.exp A.trace := by
  set g : ℂ → ℂ := fun t => (NormedSpace.exp (t • A)).det * Complex.exp (-(t * A.trace)) with hg
  have hd : ∀ t, HasDerivAt g 0 t := by
    intro t
    have h1 := hasDerivAt_det_exp_smul A t
    have h2 : HasDerivAt (fun u : ℂ => Complex.exp (-(u * A.trace)))
        (Complex.exp (-(t * A.trace)) * -A.trace) t := by
      have := ((hasDerivAt_id t).mul_const A.trace).neg.cexp
      simpa using this
    have := h1.mul h2
    refine this.congr_deriv ?_
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) 1 0
  simp only [hg, one_smul, zero_smul, NormedSpace.exp_zero, det_one, zero_mul, neg_zero,
    Complex.exp_zero, mul_one, one_mul] at hconst
  rw [Complex.exp_neg, mul_inv_eq_one₀ (Complex.exp_ne_zero _)] at hconst
  exact hconst

end Azurite.DLMF
