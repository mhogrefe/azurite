import Azurite.AzPolynomial.CauchyIndex
import Azurite.AzPolynomial.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Eval
import Azurite.AzPolynomial.Equiv.SturmSequence
import Azurite.BasuPollackRoy.Chapter2.Theorem_2_58

/-!
# Equivalence: AzPolynomial Cauchy index ↔ Polynomial Cauchy index

`AzPolynomial.cauchyIndexOn Q P a b` (computable) equals
`Azurite.BPR.cauchyIndexOn (toPoly Q) (toPoly P) a b` (noncomputable),
under the BPR Theorem 2.58 hypotheses (real closed coefficient field,
`a < b`, no SRemS root at endpoints).
-/

open Polynomial

namespace Azurite.AzPolynomial

open Azurite.BPR (ExtendedPoint)

/-! ### Bridges to BPR -/

/-- `evalPolyExt` on `AzPolynomial K` matches `BPR.ExtendedPoint.evalPoly`
    on `toPoly`. -/
theorem evalPolyExt_eq_BPR {K : Type _} [CommRing K]
    (P : AzPolynomial K) (x : ExtendedPoint K) :
    evalPolyExt P x = ExtendedPoint.evalPoly (AzPolynomial.toPoly P) x := by
  cases x with
  | finite a =>
    show P.eval a = (AzPolynomial.toPoly P).eval a
    exact (eval_toPoly P a).symm
  | posInf =>
    show P.leadingCoeff = (AzPolynomial.toPoly P).leadingCoeff
    rw [leadingCoeff_toPoly]
  | negInf =>
    show (if P.coeffs.size % 2 = 1 then P.leadingCoeff else -P.leadingCoeff) =
      (-1) ^ (AzPolynomial.toPoly P).natDegree *
        (AzPolynomial.toPoly P).leadingCoeff
    rw [AzPolynomial.natDegree_toPoly, leadingCoeff_toPoly]
    by_cases hP : P.coeffs.size = 0
    · -- P = 0, leadingCoeff = 0.
      have h_lc : P.leadingCoeff = 0 := by
        unfold AzPolynomial.leadingCoeff AzPolynomial.coeff
        simp [hP]
      simp [hP, h_lc]
    · have h_nd : P.natDegree = P.coeffs.size - 1 := rfl
      rw [h_nd]
      rcases Nat.even_or_odd P.coeffs.size with h_even | h_odd
      · -- size even: condition false, natDegree = size - 1 odd.
        have h_mod : P.coeffs.size % 2 = 0 := Nat.even_iff.mp h_even
        have h_odd_nat : Odd (P.coeffs.size - 1) := by
          rcases h_even with ⟨k, hk⟩
          refine ⟨k - 1, ?_⟩
          omega
        rw [if_neg (by omega), h_odd_nat.neg_one_pow, neg_one_mul]
      · -- size odd: condition true, natDegree = size - 1 even.
        have h_mod : P.coeffs.size % 2 = 1 := Nat.odd_iff.mp h_odd
        have h_even_nat : Even (P.coeffs.size - 1) := by
          rcases h_odd with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          omega
        rw [if_pos h_mod, h_even_nat.neg_one_pow, one_mul]

/-- `varAt` on `AzPolynomial` matches `BPR.varAt` on `toPoly` images. -/
theorem varAt_eq_BPR {K : Type _} [CommRing K] [LinearOrder K] [DecidableEq K]
    (L : List (AzPolynomial K)) (x : ExtendedPoint K) :
    varAt L x = Azurite.BPR.varAt (L.map AzPolynomial.toPoly) x := by
  unfold varAt Azurite.BPR.varAt
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro P _
  exact evalPolyExt_eq_BPR P x

/-- `sRemSList` mapped through `toPoly` matches `BPR.SRemSList`. -/
theorem map_sRemSList_toPoly {K : Type _} [Field K] [DecidableEq K]
    (P Q : AzPolynomial K) (n : ℕ) :
    (sRemSList P Q n).map AzPolynomial.toPoly =
      Azurite.BPR.SRemSList (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) n := by
  unfold sRemSList Azurite.BPR.SRemSList
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  exact toPoly_sRemS P Q i

/-! ### Correctness over a real closed field -/

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
    (hIVP : Azurite.BPR.Azurite.BPR.HasIntermediateValueProperty K)
    (Q P : AzPolynomial K) (hP : AzPolynomial.toPoly P ≠ 0)
    (a b : ExtendedPoint K) (hab : ExtendedPoint.Lt a b)
    (h_a : ∀ i : ℕ,
      Azurite.BPR.SRemS (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) i = 0 ∨
        ExtendedPoint.evalPoly
          (Azurite.BPR.SRemS (AzPolynomial.toPoly P)
            (AzPolynomial.toPoly Q) i) a ≠ 0)
    (h_b : ∀ i : ℕ,
      Azurite.BPR.SRemS (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) i = 0 ∨
        ExtendedPoint.evalPoly
          (Azurite.BPR.SRemS (AzPolynomial.toPoly P)
            (AzPolynomial.toPoly Q) i) b ≠ 0)
    (h_n_zero : Azurite.BPR.SRemS (AzPolynomial.toPoly P)
        (AzPolynomial.toPoly Q) (Q.coeffs.size + 2) = 0) :
    (cauchyIndexOn Q P a b : ℤ) =
      Azurite.BPR.cauchyIndexOn (AzPolynomial.toPoly Q)
        (AzPolynomial.toPoly P) a b := by
  unfold cauchyIndexOn
  rw [varAt_eq_BPR, varAt_eq_BPR, map_sRemSList_toPoly]
  exact Azurite.BPR.theorem_2_58 hIVP (AzPolynomial.toPoly P)
    (AzPolynomial.toPoly Q) hP a b hab h_a h_b (Q.coeffs.size + 2) h_n_zero

end Azurite.AzPolynomial
