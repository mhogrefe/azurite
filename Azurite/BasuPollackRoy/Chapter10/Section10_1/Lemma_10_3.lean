/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter10.Section10_1.Lemma_10_2
import Azurite.AzPolynomial.Equiv.ComposedOps

/-!
# BPR Lemma 10.3: the lower Cauchy bound

`lemma_10_3`: every *nonzero* root of `P ≠ 0` has absolute value strictly
greater than `c(P)` (Notation 10.1). BPR's proof: apply Lemma 10.2 to the
reciprocal polynomial `x^p P(1/x)`, whose roots are the inverses of the
nonzero roots of `P`.

The reciprocal polynomial is Mathlib's `Polynomial.reverse`, and the root
inversion property is `Polynomial.isRoot_reverse_iff` from the
root-manipulation toolkit (`Azurite.AzPolynomial.Equiv.ComposedOps`, where it
underpins `invertRoots` and the composed product). The bridge
`cauchyBound_reverse` identifies the Cauchy bound of the reversal with
`c(P)⁻¹` (unconditionally): reversal exchanges the leading and trailing coefficients, and
reindexing the coefficient sum shows the two normalizing sums agree.
-/

namespace Azurite.BPR

open Polynomial Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The Cauchy bound of the reciprocal polynomial is the reciprocal of `c(P)`:
`C(x^p P(1/x)) = c(P)⁻¹`. -/
theorem cauchyBound_reverse (P : K[X]) :
    cauchyBound P.reverse = (cauchyLowerBound P)⁻¹ := by
  set p := P.natDegree with hp
  set q := P.natTrailingDegree with hq
  have hqp : q ≤ p := Polynomial.natTrailingDegree_le_natDegree P
  rw [cauchyBound, cauchyLowerBound, inv_inv, Polynomial.reverse_natDegree,
    Polynomial.reverse_leadingCoeff]
  -- each coefficient of the reversal is a mirrored coefficient of `P`
  have hcoeff : ∀ i ∈ Finset.range (p - q + 1),
      |P.reverse.coeff i / P.trailingCoeff| = |P.coeff (p - i) / P.trailingCoeff| := by
    intro i hi
    rw [Polynomial.coeff_reverse, Polynomial.revAt_le (by
      have := Finset.mem_range.mp hi
      omega : i ≤ p)]
  rw [Finset.sum_congr rfl hcoeff]
  -- extend the sum to `range (p + 1)`: the extra terms mirror below the
  -- trailing degree, hence vanish
  have hext : ∑ i ∈ Finset.range (p + 1), |P.coeff (p - i) / P.trailingCoeff|
      = ∑ i ∈ Finset.range (p - q + 1), |P.coeff (p - i) / P.trailingCoeff| := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (p - q + 1)) (by omega : p - q + 1 ≤ p + 1),
      ← Finset.range_eq_Ico, Finset.sum_eq_zero (s := Finset.Ico (p - q + 1) (p + 1)), add_zero]
    intro i hi
    rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by
      have := Finset.mem_Ico.mp hi
      omega : p - i < q), zero_div, abs_zero]
  rw [← hext]
  -- reflect the summation index
  have hreflect := Finset.sum_range_reflect
    (fun j => |P.coeff j / P.trailingCoeff|) (p + 1)
  calc ∑ i ∈ Finset.range (p + 1), |P.coeff (p - i) / P.trailingCoeff|
      = ∑ i ∈ Finset.range (p + 1), |P.coeff (p + 1 - 1 - i) / P.trailingCoeff| := by
        exact Finset.sum_congr rfl (fun i hi => by norm_num)
    _ = ∑ j ∈ Finset.range (p + 1), |P.coeff j / P.trailingCoeff| := hreflect

/-- **BPR Lemma 10.3.** The absolute value of any nonzero root of `P` is
bigger than `c(P)`. Follows from Lemma 10.2 applied to the reciprocal
polynomial `x^p P(1/x)`. -/
theorem lemma_10_3 {P : K[X]} (hP : P ≠ 0) {x : K} (hx : P.IsRoot x) (hx0 : x ≠ 0) :
    cauchyLowerBound P < |x| := by
  have hrev_ne : P.reverse ≠ 0 := by
    rw [Ne, Polynomial.reverse_eq_zero]
    exact hP
  -- `x⁻¹` is a root of the reciprocal polynomial
  have hxinv : P.reverse.IsRoot x⁻¹ := by
    rw [Polynomial.isRoot_reverse_iff (inv_ne_zero hx0), inv_inv]
    exact hx
  -- Lemma 10.2 for the reversal, with its Cauchy bound identified as `c(P)⁻¹`
  have h2 := lemma_10_2 hrev_ne hxinv
  rw [cauchyBound_reverse P, abs_inv] at h2
  exact (inv_lt_inv₀ (abs_pos.mpr hx0) (cauchyLowerBound_pos hP)).mp h2

end Azurite.BPR
