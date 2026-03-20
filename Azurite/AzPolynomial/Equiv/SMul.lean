import Azurite.AzPolynomial.SMul
import Azurite.AzPolynomial.Equiv.Add
import Batteries.Data.Array.Lemmas

open Polynomial

namespace Azurite.AzPolynomial

variable {R S : Type _} [Semiring R] [SMulZeroClass S R] [DecidableEq R]

omit [DecidableEq R] in
lemma List.getCoeff_map_smul (r : S) (l : List R) (n : ℕ) :
  (l.map (r • ·)).getCoeff n = r • l.getCoeff n := by
  dsimp [List.getCoeff]
  rw [List.getElem?_map]
  cases hs : l[n]? with
  | none =>
    simp
  | some val =>
    simp

@[simp] lemma toPoly_smul (r : S) (p : AzPolynomial R) : AzPolynomial.toPoly (r • p) = r • AzPolynomial.toPoly p := by
  ext n
  rw [Polynomial.coeff_smul]
  rw [coeff_toPoly p]
  have h_smul : r • p = normalize ((p.coeffs.map (r • ·))) := rfl
  have ht : AzPolynomial.toPoly (r • p) = (p.coeffs.map (r • ·)).toList.toPoly := by
    rw [h_smul, toPoly_normalize]
  rw [ht]
  rw [coeff_list_toPoly]
  have hw : (p.coeffs.map (r • ·)).toList = p.coeffs.toList.map (r • ·) := by simp
  rw [hw]
  rw [List.getCoeff_map_smul]
  dsimp [coeff, List.getCoeff]
  rw [Array.getElem?_toList]

@[simp] lemma coeff_smul (r : S) (p : AzPolynomial R) (n : ℕ) :
  coeff (r • p) n = r • coeff p n := by
  have h := toPoly_smul r p
  have hc : (AzPolynomial.toPoly (r • p)).coeff n = (r • AzPolynomial.toPoly p).coeff n := by rw [h]
  rw [Polynomial.coeff_smul, coeff_toPoly p] at hc
  rw [← hc]
  exact (coeff_toPoly (r • p) n).symm

@[simp] lemma ofPoly_smul (r : S) (p : Polynomial R) :
  AzPolynomial.ofPoly (r • p) = r • AzPolynomial.ofPoly p := by
  apply equivPolynomial.injective
  dsimp [equivPolynomial]
  rw [toPoly_smul, toPoly_ofPoly, toPoly_ofPoly]

end Azurite.AzPolynomial
