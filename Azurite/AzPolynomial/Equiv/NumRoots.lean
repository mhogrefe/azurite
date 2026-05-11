import Azurite.AzPolynomial.NumRoots
import Azurite.AzPolynomial.Equiv.CauchyIndex
import Azurite.AzPolynomial.Equiv.Derivative
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Theorem_2_50
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Theorem_2_61
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Remark_2_51

/-!
# Equivalence: AzPolynomial real-root count ↔ BPR Sturm root count

* `numRootsOn_eq_BPR` — `AzPolynomial.numRootsOn P a b` (computable)
  equals the count of distinct roots of `toPoly P` in the open interval
  `(a, b)`, under the BPR Theorem 2.50 hypotheses.
* `numRoots_eq_BPR` — `AzPolynomial.numRoots P` equals
  `(toPoly P).roots.toFinset.card`, the total number of distinct real
  roots of `toPoly P` (no endpoint hypotheses needed beyond `P ≠ 0`).
* `numRoots_pos_iff_exists_root` — `numRoots P > 0` iff `toPoly P` has a
  real root (a computable decision procedure for "does `P` have a root?",
  derived from BPR Remark 2.51).
-/

open Polynomial

namespace Azurite.AzPolynomial

open Azurite.BPR (ExtendedPoint)

/-- **Correctness of `numRootsOn` (BPR Theorem 2.50, Sturm).**

    Given:
    * `K` is a (computable) ordered field with the intermediate value
      property (e.g. real closed);
    * `P ≠ 0`;
    * `a < b` in extended order;
    * `a` and `b` are not roots of `P`;
    * `P.derivative.coeffs.size + 2` is past the end of the SRemS
      sequence (true whenever the sequence is over a field).

    Then `numRootsOn P a b` equals the number of distinct roots of
    `toPoly P` in the open interval `(a, b)`. -/
theorem numRootsOn_eq_BPR
    {K : Type _} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [DecidableEq K] [PolynomialDerivative K]
    (hIVP : Azurite.BPR.HasIntermediateValueProperty K)
    (P : AzPolynomial K) (hP : AzPolynomial.toPoly P ≠ 0)
    (a b : ExtendedPoint K) (hab : ExtendedPoint.Lt a b)
    (h_aP : ExtendedPoint.evalPoly (AzPolynomial.toPoly P) a ≠ 0)
    (h_bP : ExtendedPoint.evalPoly (AzPolynomial.toPoly P) b ≠ 0)
    (h_n_zero : Azurite.BPR.SRemS (AzPolynomial.toPoly P)
        (AzPolynomial.toPoly P.derivative)
        (P.derivative.coeffs.size + 2) = 0) :
    open Classical in
    (numRootsOn P a b : ℤ) =
      (((AzPolynomial.toPoly P).roots.toFinset.filter
        (· ∈ ExtendedPoint.openInterval a b)).card : ℤ) := by
  classical
  -- numRootsOn P a b = cauchyIndexOn P.derivative P a b (def)
  show (cauchyIndexOn P.derivative P a b : ℤ) = _
  -- Bridge to BPR's Cauchy index.
  rw [cauchyIndexOn_eq_BPR hIVP P.derivative P hP a b hab h_aP h_bP h_n_zero]
  -- toPoly P.derivative = (toPoly P).derivative
  rw [toPoly_derivative]
  -- BPR.cauchyIndexOn (toPoly P).derivative (toPoly P) a b
  -- = Var(SRemS) at any past-termination truncation (theorem_2_58 reverse).
  rw [← Azurite.BPR.theorem_2_58 hIVP (AzPolynomial.toPoly P)
    (AzPolynomial.toPoly P).derivative hP a b hab h_aP h_bP
    ((AzPolynomial.toPoly P).derivative.natDegree + 2)
    (Azurite.BPR.SRemS_eq_zero_natDegree_succ_succ _ _)]
  -- And by Sturm: Var(SRemS(P, P'); a, b) = #{P-roots in (a, b)}.
  have h := Azurite.BPR.theorem_2_50 hIVP (AzPolynomial.toPoly P) hP a b hab
    h_aP h_bP
  convert h using 5

/-- **Correctness of `numRoots` (BPR Theorem 2.50 on the full line).**

    For a nonzero `P`, `numRoots P` equals `(toPoly P).roots.toFinset.card`,
    the total number of distinct real roots of `toPoly P`. No endpoint
    hypotheses are needed: at `±∞`, evaluation reduces to (a sign of) the
    leading coefficient, which is nonzero for `P ≠ 0`. -/
theorem numRoots_eq_BPR
    {K : Type _} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [DecidableEq K] [PolynomialDerivative K]
    (hIVP : Azurite.BPR.HasIntermediateValueProperty K)
    (P : AzPolynomial K) (hP : AzPolynomial.toPoly P ≠ 0)
    (h_n_zero : Azurite.BPR.SRemS (AzPolynomial.toPoly P)
        (AzPolynomial.toPoly P.derivative)
        (P.derivative.coeffs.size + 2) = 0) :
    (numRoots P : ℤ) = ((AzPolynomial.toPoly P).roots.toFinset.card : ℤ) := by
  classical
  -- Endpoint hypotheses at ±∞.
  have h_aP : ExtendedPoint.evalPoly (AzPolynomial.toPoly P)
      (.negInf : ExtendedPoint K) ≠ 0 := by
    show (-1 : K) ^ (AzPolynomial.toPoly P).natDegree *
      (AzPolynomial.toPoly P).leadingCoeff ≠ 0
    apply mul_ne_zero
    · exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    · exact mt Polynomial.leadingCoeff_eq_zero.mp hP
  have h_bP : ExtendedPoint.evalPoly (AzPolynomial.toPoly P)
      (.posInf : ExtendedPoint K) ≠ 0 := by
    show (AzPolynomial.toPoly P).leadingCoeff ≠ 0
    exact mt Polynomial.leadingCoeff_eq_zero.mp hP
  have hab : ExtendedPoint.Lt (.negInf : ExtendedPoint K) .posInf := by trivial
  show (numRootsOn P .negInf .posInf : ℤ) = _
  rw [numRootsOn_eq_BPR hIVP P hP .negInf .posInf hab h_aP h_bP h_n_zero]
  -- openInterval .negInf .posInf = Set.univ, so the filter is the identity.
  rw [show (AzPolynomial.toPoly P).roots.toFinset.filter
        (· ∈ ExtendedPoint.openInterval (R := K) .negInf .posInf) =
      (AzPolynomial.toPoly P).roots.toFinset from
    Finset.filter_eq_self.mpr (fun x _ => Set.mem_univ x)]

/-- **Real-root decision procedure (BPR Remark 2.51).** A nonzero
    polynomial `P` has a real root iff `numRoots P > 0`. -/
theorem numRoots_pos_iff_exists_root
    {K : Type _} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [DecidableEq K] [PolynomialDerivative K]
    (hIVP : Azurite.BPR.HasIntermediateValueProperty K)
    (P : AzPolynomial K) (hP : AzPolynomial.toPoly P ≠ 0)
    (h_n_zero : Azurite.BPR.SRemS (AzPolynomial.toPoly P)
        (AzPolynomial.toPoly P.derivative)
        (P.derivative.coeffs.size + 2) = 0) :
    (∃ x : K, (AzPolynomial.toPoly P).IsRoot x) ↔ 0 < numRoots P := by
  classical
  rw [numRoots_eq_BPR hIVP P hP h_n_zero]
  constructor
  · rintro ⟨x, hx⟩
    have h_in : x ∈ (AzPolynomial.toPoly P).roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
      exact hx
    exact_mod_cast Finset.card_pos.mpr ⟨x, h_in⟩
  · intro h
    have h_pos : 0 < (AzPolynomial.toPoly P).roots.toFinset.card := by
      exact_mod_cast h
    obtain ⟨x, hx⟩ := Finset.card_pos.mp h_pos
    refine ⟨x, ?_⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP] at hx
    exact hx

end Azurite.AzPolynomial
