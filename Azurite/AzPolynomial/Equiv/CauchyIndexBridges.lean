import Azurite.AzPolynomial.CauchyIndex
import Azurite.AzPolynomial.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Eval
import Azurite.AzPolynomial.Equiv.SturmSequence
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Notation_2_34
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Lemma_2_59

/-!
# Bridges: AzPolynomial Cauchy/Tarski primitives ↔ BPR primitives

Shared bridges used by both `Equiv.CauchyIndex` and `Equiv.TarskiQuery`:
* `evalPolyExt_eq_BPR` — `evalPolyExt` matches `BPR.ExtendedPoint.evalPoly`
  on `toPoly` images.
* `varAt_eq_BPR` — computable `varAt` matches BPR's `varAt` on `toPoly`
  images.
* `map_sRemSList_toPoly` — computable `sRemSList` mapped through `toPoly`
  matches BPR's `SRemSList`.
-/

open Polynomial

namespace Azurite.AzPolynomial

open Azurite.BPR (ExtendedPoint)

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
  rw [sRemSList_eq]
  unfold Azurite.BPR.SRemSList
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  exact toPoly_sRemS P Q i

end Azurite.AzPolynomial
