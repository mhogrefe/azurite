import Azurite.AzPolynomial.Sub
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.Equiv.Add
import Azurite.AzPolynomial.Equiv.Neg

open Polynomial

namespace Azurite.AzPolynomial

variable {R : Type _} [Ring R] [DecidableEq R]

-- coeff of negation, derived via toPoly bridge
@[simp] lemma coeff_neg' (q : AzPolynomial R) (n : ℕ) :
    coeff (-q) n = -(coeff q n) := by
  have h := toPoly_neg q
  have hc := congr_fun (congr_arg Polynomial.coeff h) n
  rw [Polynomial.coeff_neg, coeff_toPoly, coeff_toPoly] at hc
  exact hc

omit [DecidableEq R] in
private lemma ofFn_sub_coeff (p q : AzPolynomial R) (n : ℕ) :
    ((Array.ofFn (fun (i : Fin (max p.coeffs.size q.coeffs.size)) =>
      p.coeff i.val - q.coeff i.val))[n]?).getD 0 = p.coeff n - q.coeff n := by
  simp [Array.getElem?_ofFn]
  split
  · rfl
  · next h =>
    push Not at h
    simp [coeff, Array.getElem?_eq_none (by omega : p.coeffs.size ≤ n),
          Array.getElem?_eq_none (by omega : q.coeffs.size ≤ n)]

omit [DecidableEq R] in
private lemma coeff_zero (n : ℕ) : coeff (0 : AzPolynomial R) n = 0 := by
  simp [coeff]

@[simp] lemma coeff_sub (p q : AzPolynomial R) (n : ℕ) :
    coeff (p - q) n = coeff p n - coeff q n := by
  show coeff (sub p q) n = coeff p n - coeff q n
  simp only [sub]
  split
  · -- p = 0: sub 0 q = -q
    next hps =>
    have hp : p = 0 := AzPolynomial.ext (Array.eq_empty_of_size_eq_zero hps)
    rw [hp, coeff_zero, zero_sub, coeff_neg']
  · split
    · -- q = 0: sub p 0 = p
      next _ hqs =>
      have hq : q = 0 := AzPolynomial.ext (Array.eq_empty_of_size_eq_zero hqs)
      rw [hq, coeff_zero, sub_zero]
    · split
      · -- Same size: normalize
        rw [coeff_normalize]; exact ofFn_sub_coeff p q n
      · -- Different sizes: direct
        show ((Array.ofFn _)[n]?).getD 0 = _
        exact ofFn_sub_coeff p q n

@[simp] lemma toPoly_sub (p q : AzPolynomial R) :
  AzPolynomial.toPoly (p - q) = AzPolynomial.toPoly p - AzPolynomial.toPoly q := by
  ext n
  rw [Polynomial.coeff_sub, coeff_toPoly, coeff_toPoly, coeff_toPoly]
  exact coeff_sub p q n

@[simp] lemma ofPoly_sub (p q : Polynomial R) :
  AzPolynomial.ofPoly (p - q) = AzPolynomial.ofPoly p - AzPolynomial.ofPoly q := by
  apply equivPolynomial.injective
  dsimp [equivPolynomial]
  rw [toPoly_sub, toPoly_ofPoly, toPoly_ofPoly, toPoly_ofPoly]

/-! ### Algebraic properties of subtraction -/

theorem add_sub_cancel' (a b : AzPolynomial R) : a + b - b = a := by
  apply toPoly_inj.mp
  simp [toPoly_add, toPoly_sub]

end Azurite.AzPolynomial
