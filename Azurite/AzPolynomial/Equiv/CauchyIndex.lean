import Azurite.AzPolynomial.Equiv.CauchyIndexBridges
import Azurite.BasuPollackRoy.Chapter2.Theorem_2_58

/-!
# Equivalence: AzPolynomial Cauchy index ↔ BPR Cauchy index

`AzPolynomial.cauchyIndexOn Q P a b` (computable) equals
`Azurite.BPR.cauchyIndexOn (toPoly Q) (toPoly P) a b` (noncomputable),
under the BPR Theorem 2.58 hypotheses (real closed coefficient field,
`a < b`, `P` not vanishing at `a, b`).

The shared bridges (`evalPolyExt_eq_BPR`, `varAt_eq_BPR`,
`map_sRemSList_toPoly`) live in `Equiv.CauchyIndexBridges` and are
shared with `Equiv.TarskiQuery`.
-/

open Polynomial

namespace Azurite.AzPolynomial

open Azurite.BPR (ExtendedPoint)

/-- **Correctness of `cauchyIndexOn` (BPR Theorem 2.58).**

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

    Then the computable `cauchyIndexOn Q P a b` equals BPR's
    (noncomputable) `cauchyIndexOn`. -/
theorem cauchyIndexOn_eq_BPR
    {K : Type _} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [DecidableEq K]
    (hIVP : Azurite.BPR.HasIntermediateValueProperty K)
    (Q P : AzPolynomial K) (hP : AzPolynomial.toPoly P ≠ 0)
    (a b : ExtendedPoint K) (hab : ExtendedPoint.Lt a b)
    (h_aP : ExtendedPoint.evalPoly (AzPolynomial.toPoly P) a ≠ 0)
    (h_bP : ExtendedPoint.evalPoly (AzPolynomial.toPoly P) b ≠ 0)
    (h_n_zero : Azurite.BPR.SRemS (AzPolynomial.toPoly P)
        (AzPolynomial.toPoly Q) (Q.coeffs.size + 2) = 0) :
    (cauchyIndexOn Q P a b : ℤ) =
      Azurite.BPR.cauchyIndexOn (AzPolynomial.toPoly Q)
        (AzPolynomial.toPoly P) a b := by
  show (varAt (sRemSList P Q (Q.coeffs.size + 2)) a : ℤ) -
      (varAt (sRemSList P Q (Q.coeffs.size + 2)) b : ℤ) = _
  rw [varAt_eq_BPR, varAt_eq_BPR, map_sRemSList_toPoly]
  exact Azurite.BPR.theorem_2_58 hIVP (AzPolynomial.toPoly P)
    (AzPolynomial.toPoly Q) hP a b hab h_aP h_bP (Q.coeffs.size + 2) h_n_zero

end Azurite.AzPolynomial
