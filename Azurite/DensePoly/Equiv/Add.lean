import Azurite.DensePoly.Add
import Azurite.DensePoly.Equiv.Basic
import Batteries.Data.Array.Lemmas

open Polynomial

namespace Azurite.DensePoly

variable {R : Type _} [Semiring R] [DecidableEq R]

omit [DecidableEq R] in
lemma List.getCoeff_ofFn_aux {n : ℕ} (f : Fin n → R) (i : ℕ) :
  (List.ofFn f).getCoeff i = if h : i < n then f ⟨i, h⟩ else 0 := by
  dsimp [List.getCoeff]
  rw [List.getElem?_ofFn]
  split <;> simp

omit [DecidableEq R] in
@[simp] lemma coeff_list_toPoly (l : List R) (n : ℕ) :
  (List.toPoly l).coeff n = l.getCoeff n := by
  induction l generalizing n with
  | nil =>
    simp [List.toPoly]
  | cons a as ih =>
    simp [List.toPoly]
    cases n with
    | zero => simp
    | succ n => simp [ih n]

omit [DecidableEq R] in
@[simp] lemma coeff_toPoly (p : DensePoly R) (n : ℕ) :
  (DensePoly.toPoly p).coeff n = p.coeff n := by
  dsimp [DensePoly.toPoly, coeff, List.getCoeff]
  rw [coeff_list_toPoly]
  dsimp [List.getCoeff]
  rw [Array.getElem?_toList]

lemma toPoly_normalize (a : Array R) :
  DensePoly.toPoly (normalize a) = a.toList.toPoly := by
  dsimp [DensePoly.toPoly, normalize]
  have h_len : (a.popWhile (· = 0)).toList = dropTrailingZeros a.toList := toList_popWhile_eq_dropTrailingZeros a
  rw [h_len]
  exact toPoly_dropTrailingZeros a.toList

@[simp] lemma toPoly_add (p q : DensePoly R) :
  DensePoly.toPoly (p + q) = DensePoly.toPoly p + DensePoly.toPoly q := by
  ext n
  rw [Polynomial.coeff_add]
  rw [coeff_toPoly p, coeff_toPoly q]
  have h_add : p + q = normalize (Array.ofFn (fun (i : Fin (max p.coeffs.size q.coeffs.size)) => p.coeff i.val + q.coeff i.val)) := rfl
  have ht : DensePoly.toPoly (p + q) = (Array.ofFn (fun (i : Fin (max p.coeffs.size q.coeffs.size)) => p.coeff i.val + q.coeff i.val)).toList.toPoly := by
    rw [h_add, toPoly_normalize]
  rw [ht]
  rw [coeff_list_toPoly]
  have hof : (Array.ofFn (fun (i : Fin (max p.coeffs.size q.coeffs.size)) => p.coeff i.val + q.coeff i.val)).toList = 
             List.ofFn (fun (i : Fin (max p.coeffs.size q.coeffs.size)) => p.coeff i.val + q.coeff i.val) := by
    simp
  rw [hof, List.getCoeff_ofFn_aux]
  split
  · next h_lt => rfl
  · next h_ge =>
    dsimp [coeff]
    have hp : (p.coeffs[n]?).getD 0 = 0 := by
      rw [← Array.getElem?_toList]
      have hn_p : p.coeffs.toList.length ≤ n := by
        have hs : p.coeffs.size = p.coeffs.toList.length := by simp
        omega
      rw [List.getElem?_eq_none hn_p]
      rfl
    have hq : (q.coeffs[n]?).getD 0 = 0 := by
      rw [← Array.getElem?_toList]
      have hn_q : q.coeffs.toList.length ≤ n := by
        have hs : q.coeffs.size = q.coeffs.toList.length := by simp
        omega
      rw [List.getElem?_eq_none hn_q]
      rfl
    rw [hp, hq]
    simp

@[simp] lemma coeff_add (p q : DensePoly R) (n : ℕ) :
  coeff (p + q) n = coeff p n + coeff q n := by
  have h := toPoly_add p q
  have hc : (DensePoly.toPoly (p + q)).coeff n = (DensePoly.toPoly p + DensePoly.toPoly q).coeff n := by rw [h]
  rw [Polynomial.coeff_add, coeff_toPoly p, coeff_toPoly q] at hc
  rw [← hc]
  exact (coeff_toPoly (p + q) n).symm

@[simp] lemma ofPoly_add (p q : Polynomial R) :
  DensePoly.ofPoly (p + q) = DensePoly.ofPoly p + DensePoly.ofPoly q := by
  apply equivPolynomial.injective
  dsimp [equivPolynomial]
  rw [toPoly_add]
  rw [toPoly_ofPoly, toPoly_ofPoly, toPoly_ofPoly]

end Azurite.DensePoly
