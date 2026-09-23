/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Equiv.CauchyIndexBridges
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Theorem_2_58
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Theorem_2_61
import Azurite.BasuPollackRoy.Chapter2.Section2_3.FiberFormula

/-!
# Equivalence: AzPolynomial Cauchy index ↔ BPR Cauchy index

`AzPolynomial.cauchyIndexOnSRem Q P a b` (computable) equals
`Azurite.BPR.cauchyIndexOn (toPoly Q) (toPoly P) a b` (noncomputable),
under the BPR Theorem 2.58 hypotheses (real closed coefficient field,
`a < b`, `P` not vanishing at `a, b`).

The shared bridges (`evalPolyExt_eq_BPR`, `varAt_eq_BPR`,
`map_sRemSList_toPoly`) live in `Equiv.CauchyIndexBridges` and are
shared with `Equiv.TarskiQuery`.

The whole-line specialization `cauchyIndexOnSRem_negInf_posInf_eq_BPR`
proves, unconditionally over a real closed field,
`cauchyIndexOnSRem Q P (-∞) (+∞) = Ind(Q/P)` — the exact analogue of
`cauchyIndex_eq_BPR` for the signed-remainder algorithm. The
`P = 0` case (both sides `0`) is handled directly, and for `P ≠ 0` the
Theorem 2.58 hypotheses are discharged: the endpoints `±∞` are never roots of
`P` (`h_aP`/`h_bP`), and the signed remainder sequence terminates by index
`Q.coeffs.size + 2` (`SRemS_eq_zero_natDegree_succ_succ` + `SRemS_zero_ge`).
-/

open Polynomial

namespace Azurite.AzPolynomial

open Azurite.BPR (ExtendedPoint)

/-- **Correctness of `cauchyIndexOnSRem` (BPR Theorem 2.58).**

    Given:
    * `K` is a (computable) ordered field with the intermediate value
      property (e.g. real closed);
    * `P ≠ 0`;
    * `a < b` in extended order;
    * `a` and `b` are not roots of any nonzero polynomial in the
      `BPR.SRemS` sequence;
    * `Q.coeffs.size + 2` is past the end of the SRemS sequence (a
      property of the Euclidean degree-decrease that holds whenever the
      sequence is over a field).

    Then the computable `cauchyIndexOnSRem Q P a b` equals BPR's
    (noncomputable) `cauchyIndexOnSRem`. -/
theorem cauchyIndexOnSRem_eq_BPR
    {K : Type _} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [DecidableEq K]
    (hIVP : Azurite.BPR.HasIntermediateValueProperty K)
    (Q P : AzPolynomial K) (hP : AzPolynomial.toPoly P ≠ 0)
    (a b : ExtendedPoint K) (hab : ExtendedPoint.Lt a b)
    (h_aP : ExtendedPoint.evalPoly (AzPolynomial.toPoly P) a ≠ 0)
    (h_bP : ExtendedPoint.evalPoly (AzPolynomial.toPoly P) b ≠ 0)
    (h_n_zero : Azurite.BPR.SRemS (AzPolynomial.toPoly P)
        (AzPolynomial.toPoly Q) (Q.coeffs.size + 2) = 0) :
    (cauchyIndexOnSRem Q P a b : ℤ) =
      Azurite.BPR.cauchyIndexOn (AzPolynomial.toPoly Q)
        (AzPolynomial.toPoly P) a b := by
  show (varAt (sRemSList P Q (Q.coeffs.size + 2)) a : ℤ) -
      (varAt (sRemSList P Q (Q.coeffs.size + 2)) b : ℤ) = _
  rw [varAt_eq_BPR, varAt_eq_BPR, map_sRemSList_toPoly]
  exact Azurite.BPR.theorem_2_58 hIVP (AzPolynomial.toPoly P)
    (AzPolynomial.toPoly Q) hP a b hab h_aP h_bP (Q.coeffs.size + 2) h_n_zero

/-! ### Whole-line specialization (unconditional over a real closed field) -/

section WholeLine

variable {R : Type _} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq R]

omit [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq R] in
/-- Evaluating the zero polynomial at any extended point gives `0`. -/
theorem evalPolyExt_zero (x : ExtendedPoint R) : evalPolyExt (0 : AzPolynomial R) x = 0 := by
  cases x <;> simp [evalPolyExt, AzPolynomial.eval, AzPolynomial.leadingCoeff, AzPolynomial.coeff,
    AzPolynomial.natDegree]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- A signed-remainder step from `0` gives `0` (the remainder of `0` is `0`). -/
theorem sRemSStep_zero_left (Q : AzPolynomial R) : sRemSStep 0 Q = 0 := by
  have hrem : (0 : AzPolynomial R).rem Q = 0 := by
    show (quoRem 0 Q).2 = 0; unfold quoRem
    have h0 : (0 : AzPolynomial R).coeffs.size = 0 := rfl
    split_ifs <;> simp_all
  unfold sRemSStep; split
  · rfl
  · rw [hrem]; exact toPoly_inj.mp (by rw [toPoly_neg, toPoly_zero, neg_zero])

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- A signed-remainder step with second argument `0` gives `0`. -/
theorem sRemSStep_zero_right (P : AzPolynomial R) : sRemSStep P 0 = 0 := by
  unfold sRemSStep; simp

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The remainder sequence from `(0, 0)` is all zeros. -/
theorem sRemSBuild_zero_zero (m : ℕ) : sRemSBuild m (0 : AzPolynomial R) 0 = List.replicate m 0 := by
  induction m with
  | zero => rfl
  | succ k ih => rw [sRemSBuild, sRemSStep_zero_right, ih, List.replicate_succ]

omit [IsStrictOrderedRing R] in
set_option linter.unusedSimpArgs false in
/-- With a zero denominator the sign-variation count vanishes: the remainder
sequence `sRemSList 0 Q n` is `[0, Q, 0, …, 0]`, so at most one entry is
nonzero. -/
theorem varAt_sRemSList_zero_denom (Q : AzPolynomial R) (x : ExtendedPoint R) (m : ℕ) :
    varAt (sRemSList 0 Q (m + 2)) x = 0 := by
  unfold varAt sRemSList
  rw [sRemSBuild, sRemSStep_zero_left, sRemSBuild, sRemSStep_zero_right, sRemSBuild_zero_zero,
    Azurite.BPR.Var_eq_varNonzero_filter]
  have hrep : (List.replicate m (0 : R)).filter (· ≠ 0) = [] := by
    apply List.filter_eq_nil_iff.mpr; intro y hy; simp [List.eq_of_mem_replicate hy]
  simp only [List.map_cons, List.map_replicate, evalPolyExt_zero, List.filter_cons, ne_eq,
    decide_not, hrep]
  by_cases h : evalPolyExt Q x = 0 <;> simp [h, Azurite.BPR.varNonzero_singleton]

variable [IsRealClosed R]

/-- **Whole-line correctness of `cauchyIndexOnSRem`.** Over a real closed coefficient
field, for *any* `Q` and `P`, the computable signed-remainder Cauchy index on
`(-∞, +∞)` equals `Ind(Q/P)`. This is the exact analogue of
`cauchyIndex_eq_BPR` (BPR Algorithm 9.4) for the signed-remainder
algorithm: no degree hypothesis, `P = 0` giving `0` on both sides. -/
theorem cauchyIndexOnSRem_negInf_posInf_eq_BPR (Q P : AzPolynomial R) :
    cauchyIndexOnSRem Q P .negInf .posInf
      = Azurite.BPR.cauchyIndex (AzPolynomial.toPoly Q) (AzPolynomial.toPoly P) := by
  rcases eq_or_ne P 0 with rfl | hP
  · -- `P = 0`: `P` has no poles, and the remainder sequence collapses.
    have hLHS : cauchyIndexOnSRem Q (0 : AzPolynomial R) .negInf .posInf = 0 := by
      show (varAt (sRemSList 0 Q (Q.coeffs.size + 2)) .negInf : ℤ)
        - (varAt (sRemSList 0 Q (Q.coeffs.size + 2)) .posInf : ℤ) = 0
      rw [varAt_sRemSList_zero_denom Q .negInf Q.coeffs.size,
        varAt_sRemSList_zero_denom Q .posInf Q.coeffs.size]; ring
    rw [hLHS, toPoly_zero, Azurite.BPR.cauchyIndex_eq_cauchyIndexOn_negInf_posInf]
    unfold Azurite.BPR.cauchyIndexOn; simp [Polynomial.roots_zero]
  · -- `P ≠ 0`: discharge the Theorem 2.58 hypotheses at the `±∞` endpoints.
    have hPm : AzPolynomial.toPoly P ≠ 0 := fun h => hP (toPoly_inj.mp (h.trans toPoly_zero.symm))
    have h_aP : ExtendedPoint.evalPoly (AzPolynomial.toPoly P) (.negInf : ExtendedPoint R) ≠ 0 := by
      show (-1 : R) ^ (AzPolynomial.toPoly P).natDegree * (AzPolynomial.toPoly P).leadingCoeff ≠ 0
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        (mt Polynomial.leadingCoeff_eq_zero.mp hPm)
    have h_bP : ExtendedPoint.evalPoly (AzPolynomial.toPoly P) (.posInf : ExtendedPoint R) ≠ 0 := by
      show (AzPolynomial.toPoly P).leadingCoeff ≠ 0
      exact mt Polynomial.leadingCoeff_eq_zero.mp hPm
    have hn : Azurite.BPR.SRemS (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
        (Q.coeffs.size + 2) = 0 := by
      have hbase : Azurite.BPR.SRemS (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
          ((AzPolynomial.toPoly Q).natDegree + 1 + 1) = 0 :=
        Azurite.BPR.SRemS_eq_zero_natDegree_succ_succ _ _
      refine Azurite.BPR.SRemS_zero_ge _ _ ((AzPolynomial.toPoly Q).natDegree + 1) hbase
        (Q.coeffs.size + 2) ?_
      rw [AzPolynomial.natDegree_toPoly]; unfold AzPolynomial.natDegree; omega
    rw [cauchyIndexOnSRem_eq_BPR Azurite.BPR.hasIVP_of_isRealClosed Q P hPm .negInf .posInf
        (by trivial) h_aP h_bP hn,
      ← Azurite.BPR.cauchyIndex_eq_cauchyIndexOn_negInf_posInf]

/-- **`ofPoly` form.** For abstract polynomials `q, p : R[X]`, the computable
whole-line Cauchy index of their `ofPoly` images equals `Ind(q/p)`. -/
theorem cauchyIndexOnSRem_ofPoly_negInf_posInf_eq_BPR (q p : R[X]) :
    cauchyIndexOnSRem (AzPolynomial.ofPoly q) (AzPolynomial.ofPoly p) .negInf .posInf
      = Azurite.BPR.cauchyIndex q p := by
  rw [cauchyIndexOnSRem_negInf_posInf_eq_BPR, toPoly_ofPoly, toPoly_ofPoly]

end WholeLine

end Azurite.AzPolynomial
