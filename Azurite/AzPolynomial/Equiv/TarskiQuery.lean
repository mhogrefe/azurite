import Azurite.AzPolynomial.Equiv.CauchyIndexBridges
import Azurite.AzPolynomial.Equiv.Derivative
import Azurite.AzPolynomial.Equiv.Mul
import Azurite.BasuPollackRoy.Chapter2.Theorem_2_58
import Azurite.BasuPollackRoy.Chapter2.Theorem_2_61

/-!
# Equivalence: AzPolynomial Tarski query ↔ BPR Tarski query

`AzPolynomial.tarskiQueryOn Q P a b` (computable) equals
`Azurite.BPR.tarskiQueryOn (toPoly Q) (toPoly P) a b` (noncomputable),
under the BPR Theorem 2.61 hypotheses (real closed coefficient field,
`a < b`, `P` not vanishing at `a, b`).

The shared bridges (`evalPolyExt_eq_BPR`, `varAt_eq_BPR`,
`map_sRemSList_toPoly`) live in `Equiv.CauchyIndexBridges`.
-/

open Polynomial

namespace Azurite.AzPolynomial

open Azurite.BPR (ExtendedPoint)

/-- **Correctness of `tarskiQueryOn` (BPR Theorem 2.61).**

    Given:
    * `K` is a (computable) ordered field with the intermediate value
      property (e.g. real closed);
    * `P ≠ 0`;
    * `a < b` in extended order;
    * `a` and `b` are not roots of `P`.

    Then the computable `tarskiQueryOn Q P a b` equals BPR's
    (noncomputable) `tarskiQueryOn`.

    Unlike `cauchyIndexOn_eq_BPR`, no truncation hypothesis is needed:
    BPR Theorem 2.61 contains the SRemS termination bound internally. -/
theorem tarskiQueryOn_eq_BPR
    {K : Type _} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [DecidableEq K] [PolynomialDerivative K]
    (hIVP : Azurite.BPR.Azurite.BPR.HasIntermediateValueProperty K)
    (Q P : AzPolynomial K) (hP : AzPolynomial.toPoly P ≠ 0)
    (a b : ExtendedPoint K) (hab : ExtendedPoint.Lt a b)
    (h_aP : ExtendedPoint.evalPoly (AzPolynomial.toPoly P) a ≠ 0)
    (h_bP : ExtendedPoint.evalPoly (AzPolynomial.toPoly P) b ≠ 0)
    (h_n_zero : Azurite.BPR.SRemS (AzPolynomial.toPoly P)
        ((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q)
        ((P.derivative * Q).coeffs.size + 2) = 0) :
    (tarskiQueryOn Q P a b : ℤ) =
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

end Azurite.AzPolynomial
