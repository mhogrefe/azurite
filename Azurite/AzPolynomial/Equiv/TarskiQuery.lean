import Azurite.AzPolynomial.Equiv.CauchyIndex
import Azurite.AzPolynomial.Equiv.CauchyIndexBridges
import Azurite.AzPolynomial.Equiv.Derivative
import Azurite.AzPolynomial.Equiv.Mul
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Theorem_2_58
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Theorem_2_61

/-!
# Equivalence: AzPolynomial Tarski query ↔ BPR Tarski query

`AzPolynomial.tarskiQueryOnSRem Q P a b` (computable) equals
`Azurite.BPR.tarskiQueryOn (toPoly Q) (toPoly P) a b` (noncomputable),
under the BPR Theorem 2.61 hypotheses (real closed coefficient field,
`a < b`, `P` not vanishing at `a, b`).

The shared bridges (`evalPolyExt_eq_BPR`, `varAt_eq_BPR`,
`map_sRemSList_toPoly`) live in `Equiv.CauchyIndexBridges`.
-/

open Polynomial

namespace Azurite.AzPolynomial

open Azurite.BPR (ExtendedPoint)

/-- **Correctness of `tarskiQueryOnSRem` (BPR Theorem 2.61).**

    Given:
    * `K` is a (computable) ordered field with the intermediate value
      property (e.g. real closed);
    * `P ≠ 0`;
    * `a < b` in extended order;
    * `a` and `b` are not roots of `P`.

    Then the computable `tarskiQueryOnSRem Q P a b` equals BPR's
    (noncomputable) `tarskiQueryOnSRem`.

    Unlike `cauchyIndexOnSRem_eq_BPR`, no truncation hypothesis is needed:
    BPR Theorem 2.61 contains the SRemS termination bound internally. -/
theorem tarskiQueryOnSRem_eq_BPR
    {K : Type _} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [DecidableEq K] [PolynomialDerivative K]
    (hIVP : Azurite.BPR.HasIntermediateValueProperty K)
    (Q P : AzPolynomial K) (hP : AzPolynomial.toPoly P ≠ 0)
    (a b : ExtendedPoint K) (hab : ExtendedPoint.Lt a b)
    (h_aP : ExtendedPoint.evalPoly (AzPolynomial.toPoly P) a ≠ 0)
    (h_bP : ExtendedPoint.evalPoly (AzPolynomial.toPoly P) b ≠ 0)
    (h_n_zero : Azurite.BPR.SRemS (AzPolynomial.toPoly P)
        ((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q)
        ((P.derivative * Q).coeffs.size + 2) = 0) :
    (tarskiQueryOnSRem Q P a b : ℤ) =
      Azurite.BPR.tarskiQueryOn (AzPolynomial.toPoly Q)
        (AzPolynomial.toPoly P) a b := by
  show (varAt (sRemSList P (P.derivative * Q)
        ((P.derivative * Q).coeffs.size + 2)) a : ℤ) -
      (varAt (sRemSList P (P.derivative * Q)
        ((P.derivative * Q).coeffs.size + 2)) b : ℤ) = _
  -- Identify the AzPolynomial product with the BPR product.
  have h_prod : AzPolynomial.toPoly (P.derivative * Q) =
      (AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q := by
    rw [toPoly_mul P.derivative Q, toPoly_derivative P]
  -- Rewrite via varAt_eq_BPR + map_sRemSList_toPoly.
  rw [varAt_eq_BPR, varAt_eq_BPR, map_sRemSList_toPoly, h_prod]
  -- Apply Theorem 2.58 specialized to (P, P'·Q) at the chosen truncation.
  rw [Azurite.BPR.theorem_2_58 hIVP (AzPolynomial.toPoly P)
    ((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q) hP a b hab
    h_aP h_bP ((P.derivative * Q).coeffs.size + 2) h_n_zero]
  -- Then Proposition 2.57 closes via TaQ definition.
  exact (Azurite.BPR.proposition_2_57 hIVP (AzPolynomial.toPoly Q)
    (AzPolynomial.toPoly P) hP a b).symm

/-! ### Whole-line specialization (unconditional over a real closed field) -/

section WholeLine

variable {R : Type _} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq R]
    [PolynomialDerivative R] [IsRealClosed R]

/-- **Whole-line correctness of `tarskiQueryOnSRem`.** Over a real closed coefficient
field, for *any* `Q` and `P`, the computable signed-remainder Tarski query on
`(−∞, +∞)` equals `TaQ(Q, P)`. This is the exact analogue of
`cauchyIndexOnSRem_negInf_posInf_eq_BPR` (and of the subresultant
`tarskiQuery_eq_BPR`), with no degree hypothesis: `P = 0` gives `0`
on both sides. For `P ≠ 0` the Theorem 2.61 hypotheses are discharged: `±∞` are
never roots of `P`, and the `SRemS(P, P'·Q)` sequence terminates by index
`(P'·Q).coeffs.size + 2`. -/
theorem tarskiQueryOnSRem_negInf_posInf_eq_BPR (Q P : AzPolynomial R) :
    tarskiQueryOnSRem Q P .negInf .posInf
      = Azurite.BPR.tarskiQuery (AzPolynomial.toPoly Q) (AzPolynomial.toPoly P) := by
  rcases eq_or_ne P 0 with rfl | hP
  · -- `P = 0`: `P` has no poles and the remainder sequence collapses.
    have hLHS : tarskiQueryOnSRem Q (0 : AzPolynomial R) .negInf .posInf = 0 := by
      show (varAt (sRemSList 0 ((0 : AzPolynomial R).derivative * Q)
          (((0 : AzPolynomial R).derivative * Q).coeffs.size + 2)) .negInf : ℤ)
        - (varAt (sRemSList 0 ((0 : AzPolynomial R).derivative * Q)
          (((0 : AzPolynomial R).derivative * Q).coeffs.size + 2)) .posInf : ℤ) = 0
      rw [varAt_sRemSList_zero_denom _ .negInf _, varAt_sRemSList_zero_denom _ .posInf _]; ring
    rw [hLHS, toPoly_zero]
    simp [Azurite.BPR.tarskiQuery, Azurite.BPR.tarskiQueryOn, Polynomial.roots_zero]
  · -- `P ≠ 0`: discharge the Theorem 2.61 hypotheses at the `±∞` endpoints.
    have hPm : AzPolynomial.toPoly P ≠ 0 := fun h => hP (toPoly_inj.mp (h.trans toPoly_zero.symm))
    have h_aP : ExtendedPoint.evalPoly (AzPolynomial.toPoly P) (.negInf : ExtendedPoint R) ≠ 0 := by
      show (-1 : R) ^ (AzPolynomial.toPoly P).natDegree * (AzPolynomial.toPoly P).leadingCoeff ≠ 0
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        (mt Polynomial.leadingCoeff_eq_zero.mp hPm)
    have h_bP : ExtendedPoint.evalPoly (AzPolynomial.toPoly P) (.posInf : ExtendedPoint R) ≠ 0 := by
      show (AzPolynomial.toPoly P).leadingCoeff ≠ 0
      exact mt Polynomial.leadingCoeff_eq_zero.mp hPm
    have hn : Azurite.BPR.SRemS (AzPolynomial.toPoly P)
        ((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q)
        ((P.derivative * Q).coeffs.size + 2) = 0 := by
      have hbase : Azurite.BPR.SRemS (AzPolynomial.toPoly P)
          ((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q)
          (((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q).natDegree + 1 + 1) = 0 :=
        Azurite.BPR.SRemS_eq_zero_natDegree_succ_succ _ _
      refine Azurite.BPR.SRemS_zero_ge _ _
        (((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q).natDegree + 1) hbase
        ((P.derivative * Q).coeffs.size + 2) ?_
      have h_prod : AzPolynomial.toPoly (P.derivative * Q)
          = (AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q := by
        rw [toPoly_mul, toPoly_derivative]
      rw [← h_prod, AzPolynomial.natDegree_toPoly]; unfold AzPolynomial.natDegree; omega
    rw [tarskiQueryOnSRem_eq_BPR Azurite.BPR.hasIVP_of_isRealClosed Q P hPm .negInf .posInf
        (by trivial) h_aP h_bP hn,
      ← Azurite.BPR.tarskiQuery_eq_tarskiQueryOn_negInf_posInf]

/-- **`ofPoly` form.** For abstract polynomials `q, p : R[X]`, the computable
whole-line Tarski query of their `ofPoly` images equals `TaQ(q, p)`. -/
theorem tarskiQueryOnSRem_ofPoly_negInf_posInf_eq_BPR (q p : R[X]) :
    tarskiQueryOnSRem (AzPolynomial.ofPoly q) (AzPolynomial.ofPoly p) .negInf .posInf
      = Azurite.BPR.tarskiQuery q p := by
  rw [tarskiQueryOnSRem_negInf_posInf_eq_BPR, toPoly_ofPoly, toPoly_ofPoly]

end WholeLine

end Azurite.AzPolynomial
