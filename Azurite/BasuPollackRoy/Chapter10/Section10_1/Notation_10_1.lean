/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field

/-!
# BPR Notation 10.1: the Cauchy bounds

For `P = aₚXᵖ + ⋯ + a_qX^q` over an ordered field (BPR's setting: coefficients
in an ordered field `K`, roots in a real closed `R ⊇ K` — covered here by
stating everything over the one ordered field the roots live in):

* `C(P) = ∑_{q ≤ i ≤ p} |aᵢ/aₚ|` — every root has absolute value smaller than
  `C(P)` (Lemma 10.2);
* `c(P) = (∑_{q ≤ i ≤ p} |aᵢ/a_q|)⁻¹` — every nonzero root has absolute value
  greater than `c(P)`.

The Lean sums run over `0 ≤ i ≤ p`; the extra terms vanish (the coefficients
below the trailing degree are zero), so the values agree with BPR's.
-/

namespace Azurite.BPR

open Polynomial Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **BPR Notation 10.1 (Cauchy bound).** `C(P) = ∑ᵢ |aᵢ/aₚ|`: the upper bound
on the absolute values of the roots of `P` (Lemma 10.2). -/
noncomputable def cauchyBound (P : K[X]) : K :=
  ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i / P.leadingCoeff|

/-- **BPR Notation 10.1 (Cauchy bound), lower version.**
`c(P) = (∑ᵢ |aᵢ/a_q|)⁻¹` where `a_q` is the trailing coefficient: the lower
bound on the absolute values of the nonzero roots of `P`. -/
noncomputable def cauchyLowerBound (P : K[X]) : K :=
  (∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i / P.trailingCoeff|)⁻¹

/-- The normalizing sum of `C(P)` is at least `1` (the `i = p` term is `1`). -/
theorem one_le_cauchyBound {P : K[X]} (hP : P ≠ 0) : 1 ≤ cauchyBound P := by
  have h1 : |P.coeff P.natDegree / P.leadingCoeff| = 1 := by
    rw [show P.coeff P.natDegree = P.leadingCoeff from rfl,
      div_self (Polynomial.leadingCoeff_ne_zero.mpr hP), abs_one]
  calc (1 : K) = |P.coeff P.natDegree / P.leadingCoeff| := h1.symm
    _ ≤ cauchyBound P := Finset.single_le_sum
        (f := fun i => |P.coeff i / P.leadingCoeff|) (fun _ _ => abs_nonneg _)
        (Finset.self_mem_range_succ P.natDegree)

theorem cauchyBound_pos {P : K[X]} (hP : P ≠ 0) : 0 < cauchyBound P :=
  lt_of_lt_of_le one_pos (one_le_cauchyBound hP)

/-- The sum over `0 ≤ i ≤ q` of the `a_q`-normalized absolute coefficients is
exactly `1`: the terms below the trailing degree vanish and the `i = q` term is
`|a_q/a_q| = 1`. -/
theorem sum_abs_div_trailingCoeff_eq_one {P : K[X]} (hP : P ≠ 0) :
    ∑ i ∈ Finset.range (P.natTrailingDegree + 1), |P.coeff i / P.trailingCoeff| = 1 := by
  have htc : P.trailingCoeff ≠ 0 := fun h => hP (Polynomial.trailingCoeff_eq_zero.mp h)
  rw [Finset.sum_range_succ,
    show P.coeff P.natTrailingDegree / P.trailingCoeff = 1 from by
      rw [show P.coeff P.natTrailingDegree = P.trailingCoeff from rfl, div_self htc],
    abs_one, Finset.sum_eq_zero, zero_add]
  intro i hi
  rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (Finset.mem_range.mp hi), zero_div,
    abs_zero]

/-- The normalizing sum of `c(P)` is at least `1` (the `i = q` term is `1`). -/
theorem one_le_sum_abs_div_trailingCoeff {P : K[X]} (hP : P ≠ 0) :
    1 ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i / P.trailingCoeff| := by
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le (P.natTrailingDegree + 1))
      (by have := Polynomial.natTrailingDegree_le_natDegree P; omega),
    ← Finset.range_eq_Ico, sum_abs_div_trailingCoeff_eq_one hP]
  have h0 : (0 : K) ≤ ∑ i ∈ Finset.Ico (P.natTrailingDegree + 1) (P.natDegree + 1),
      |P.coeff i / P.trailingCoeff| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  linarith

theorem cauchyLowerBound_pos {P : K[X]} (hP : P ≠ 0) : 0 < cauchyLowerBound P :=
  inv_pos.mpr (lt_of_lt_of_le one_pos (one_le_sum_abs_div_trailingCoeff hP))

theorem cauchyLowerBound_le_one {P : K[X]} (hP : P ≠ 0) : cauchyLowerBound P ≤ 1 := by
  rw [cauchyLowerBound,
    inv_le_one₀ (lt_of_lt_of_le one_pos (one_le_sum_abs_div_trailingCoeff hP))]
  exact one_le_sum_abs_div_trailingCoeff hP

end Azurite.BPR
