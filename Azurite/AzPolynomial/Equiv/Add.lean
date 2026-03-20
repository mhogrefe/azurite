import Azurite.AzPolynomial.Add
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.Equiv.Basic
import Batteries.Data.Array.Lemmas

open Polynomial

namespace Azurite.AzPolynomial

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
@[simp] lemma coeff_toPoly (p : AzPolynomial R) (n : ℕ) :
  (AzPolynomial.toPoly p).coeff n = p.coeff n := by
  dsimp [AzPolynomial.toPoly, coeff, List.getCoeff]
  rw [coeff_list_toPoly]
  dsimp [List.getCoeff]
  rw [Array.getElem?_toList]

lemma toPoly_normalize (a : Array R) :
  AzPolynomial.toPoly (normalize a) = a.toList.toPoly := by
  dsimp [AzPolynomial.toPoly, normalize]
  have h_len : (a.popWhile (· = 0)).toList = dropTrailingZeros a.toList := toList_popWhile_eq_dropTrailingZeros a
  rw [h_len]
  exact toPoly_dropTrailingZeros a.toList

-- Helper: the Array.ofFn coeff equals p.coeff + q.coeff in all cases
omit [DecidableEq R] in
private lemma ofFn_add_coeff (p q : AzPolynomial R) (n : ℕ) :
    ((Array.ofFn (fun (i : Fin (max p.coeffs.size q.coeffs.size)) =>
      p.coeff i.val + q.coeff i.val))[n]?).getD 0 = p.coeff n + q.coeff n := by
  simp [Array.getElem?_ofFn]
  split
  · rfl
  · next h =>
    push_neg at h
    simp [coeff, Array.getElem?_eq_none (by omega : p.coeffs.size ≤ n),
          Array.getElem?_eq_none (by omega : q.coeffs.size ≤ n)]

@[simp] lemma coeff_add (p q : AzPolynomial R) (n : ℕ) :
    coeff (p + q) n = coeff p n + coeff q n := by
  show coeff (add p q) n = coeff p n + coeff q n
  simp only [add]
  split
  · next hps =>
    simp [coeff, Array.eq_empty_of_size_eq_zero hps]
  · split
    · next _ hqs =>
      simp [coeff, Array.eq_empty_of_size_eq_zero hqs]
    · split
      · next _ _ _ =>
        rw [coeff_normalize]
        exact ofFn_add_coeff p q n
      · next _ _ _ =>
        show ((Array.ofFn (fun (i : Fin (max p.coeffs.size q.coeffs.size)) =>
          p.coeff i.val + q.coeff i.val))[n]?).getD 0 = p.coeff n + q.coeff n
        exact ofFn_add_coeff p q n

@[simp] lemma toPoly_add (p q : AzPolynomial R) :
  AzPolynomial.toPoly (p + q) = AzPolynomial.toPoly p + AzPolynomial.toPoly q := by
  ext n
  rw [Polynomial.coeff_add, coeff_toPoly, coeff_toPoly, coeff_toPoly]
  exact coeff_add p q n

@[simp] lemma ofPoly_add (p q : Polynomial R) :
  AzPolynomial.ofPoly (p + q) = AzPolynomial.ofPoly p + AzPolynomial.ofPoly q := by
  apply equivPolynomial.injective
  dsimp [equivPolynomial]
  rw [toPoly_add]
  rw [toPoly_ofPoly, toPoly_ofPoly, toPoly_ofPoly]

/-! ### Equivalence lemmas for `addNoCancel` -/

-- checkBinderAnnotations is disabled because the LSP incorrectly rejects
-- [NoAddCancellation R] when [Add R] and [Zero R] are inherited from [Semiring R].
-- This compiles cleanly with `lake build`.
set_option checkBinderAnnotations false in
omit [DecidableEq R] in
@[simp] lemma coeff_addNoCancel [NoAddCancellation R] (p q : AzPolynomial R) (n : ℕ) :
    coeff (addNoCancel p q) n = coeff p n + coeff q n := by
  simp only [addNoCancel]
  split
  · next hps =>
    simp [coeff, Array.eq_empty_of_size_eq_zero hps]
  · split
    · next _ hqs =>
      simp [coeff, Array.eq_empty_of_size_eq_zero hqs]
    · next _ _ =>
      show ((Array.ofFn (fun (i : Fin (max p.coeffs.size q.coeffs.size)) =>
        p.coeff i.val + q.coeff i.val))[n]?).getD 0 = p.coeff n + q.coeff n
      exact ofFn_add_coeff p q n

set_option checkBinderAnnotations false in
omit [DecidableEq R] in
@[simp] lemma toPoly_addNoCancel [NoAddCancellation R] (p q : AzPolynomial R) :
    AzPolynomial.toPoly (addNoCancel p q) = AzPolynomial.toPoly p + AzPolynomial.toPoly q := by
  ext n
  rw [Polynomial.coeff_add, coeff_toPoly, coeff_toPoly, coeff_toPoly]
  exact coeff_addNoCancel p q n

end Azurite.AzPolynomial
