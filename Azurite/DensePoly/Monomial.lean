import Azurite.DensePoly.Basic
import Azurite.DensePoly.Polynomial

/-!
# Constant Polynomials and Monomials

This module defines constructors for basic polynomials natively within `DensePoly`,
such as `C` for constant polynomials.
-/

namespace Azurite.DensePoly

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- Constructs a constant polynomial with value `c`. -/
def C (c : R) : DensePoly R :=
  if h : c = 0 then
    0
  else
    ⟨#[c], by simp [h]⟩

@[simp] lemma toPoly_C (c : R) : DensePoly.toPoly (C c) = Polynomial.C c := by
  unfold C
  split
  · next hc =>
    rw [hc, Polynomial.C_0]
    exact toPoly_zero
  · next hc =>
    dsimp [DensePoly.toPoly, List.toPoly]
    simp

@[simp] lemma ofPoly_C (c : R) : DensePoly.ofPoly (Polynomial.C c) = C c := by
  rw [← toPoly_inj]
  rw [toPoly_ofPoly]
  exact (toPoly_C c).symm

/-- Constructs the polynomial `X`. -/
def X : DensePoly R :=
  if h : (1 : R) = 0 then
    0
  else
    ⟨#[0, 1], by simp [h]⟩

@[simp] lemma toPoly_X : DensePoly.toPoly (X : DensePoly R) = Polynomial.X := by
  unfold X
  split
  · next h =>
    ext n
    simp [h, Polynomial.coeff_X]
  · next hc =>
    dsimp [DensePoly.toPoly, List.toPoly]
    simp

@[simp] lemma ofPoly_X : DensePoly.ofPoly (Polynomial.X : Polynomial R) = X := by
  rw [← toPoly_inj]
  rw [toPoly_ofPoly]
  exact toPoly_X.symm

/-- Constructs the monomial `a * X^n`. -/
def monomial (n : ℕ) (a : R) : DensePoly R :=
  if h : a = 0 then
    0
  else
    ⟨(Array.replicate n 0).push a, by simp [h]⟩

@[simp] lemma toPoly_monomial (n : ℕ) (a : R) : DensePoly.toPoly (monomial n a) = Polynomial.monomial n a := by
  unfold monomial
  split
  · next h =>
    rw [h, Polynomial.monomial_zero_right, toPoly_zero]
  · next hc =>
    ext i
    have hw : ((Array.replicate n 0).push a).toList = List.replicate n 0 ++ [a] := by
      simp
    dsimp [DensePoly.toPoly]
    rw [hw, coeff_toPoly]
    by_cases h_i : i = n
    · rw [h_i]
      rw [Polynomial.coeff_monomial]
      simp
      dsimp [List.getCoeff]
      have ht : (List.replicate n (0 : R) ++ [a])[n]? = some a := by
        rw [List.getElem?_append_right (by simp)]
        have h0 : n - (List.replicate n (0 : R)).length = 0 := by simp
        rw [h0]
        simp
      rw [ht]
      rfl
    · rw [Polynomial.coeff_monomial]
      have hn : ¬(n = i) := by intro h; exact h_i h.symm
      simp [hn]
      dsimp [List.getCoeff]
      cases lt_trichotomy i n with
      | inl h_lt =>
        have ht : (List.replicate n (0 : R) ++ [a])[i]? = some 0 := by
          rw [List.getElem?_append]
          simp [h_lt]
        rw [ht]
        rfl
      | inr h_or =>
        cases h_or with
        | inl h_eq =>
          exfalso
          exact h_i h_eq
        | inr h_gt =>
          have h_len : (List.replicate n (0 : R) ++ [a]).length = n + 1 := by simp
          have h_ge : (List.replicate n (0 : R) ++ [a]).length ≤ i := by omega
          have ht : (List.replicate n (0 : R) ++ [a])[i]? = none := List.getElem?_eq_none h_ge
          rw [ht]
          rfl

@[simp] lemma ofPoly_monomial (n : ℕ) (a : R) : DensePoly.ofPoly (Polynomial.monomial n a) = monomial n a := by
  rw [← toPoly_inj]
  rw [toPoly_ofPoly]
  exact (toPoly_monomial n a).symm

lemma coeff_normalize (a : Array R) (i : ℕ) :
  (normalize a).coeff i = (a[i]?).getD 0 := by
  have h_pop : (normalize a).coeffs.toList = dropTrailingZeros a.toList := toList_popWhile_eq_dropTrailingZeros a
  have ht_arr : (normalize a).coeffs[i]? = (normalize a).coeffs.toList[i]? := (Array.getElem?_toList).symm
  dsimp [coeff, List.getCoeff]
  rw [ht_arr]
  rw [h_pop]
  have h_get := dropTrailingZeros_get? a.toList i
  rw [h_get]
  split
  · next h_lt =>
    have ht_arr_list : a.toList[i]? = a[i]? := Array.getElem?_toList
    have h_eq : a[i]? = a.toList[i]? := ht_arr_list.symm
    rw [h_eq]
  · next h_ge =>
    by_cases h_bounds : i < a.toList.length
    · have h_drop : (a.toList)[i]? = some 0 := by
        have ht : dropTrailingZeros a.toList ++ (a.toList.reverse.takeWhile (· = 0)).reverse = a.toList := eq_dropTrailingZeros_append_takeWhile a.toList
        have ht_get : (dropTrailingZeros a.toList ++ (a.toList.reverse.takeWhile (· = 0)).reverse)[i]? = a.toList[i]? := by rw [ht]
        rw [List.getElem?_append] at ht_get
        rw [if_neg (by omega)] at ht_get
        have ht2 : ((a.toList.reverse.takeWhile (· = 0)).reverse)[i - (dropTrailingZeros a.toList).length]? = a.toList[i]? := ht_get
        
        have ht3 : a.toList[i]? = ((a.toList.reverse.takeWhile (· = 0)).reverse)[i - (dropTrailingZeros a.toList).length]? := ht2.symm
        rw [ht3]
        
        have h_len_sum : (dropTrailingZeros a.toList).length + (a.toList.reverse.takeWhile (· = 0)).reverse.length = a.toList.length := by
          have h_len_eq : (dropTrailingZeros a.toList ++ (a.toList.reverse.takeWhile (· = 0)).reverse).length = a.toList.length := by rw [ht]
          rw [List.length_append] at h_len_eq
          exact h_len_eq
        
        have h_len_rev : (a.toList.reverse.takeWhile (· = 0)).reverse.length = (a.toList.reverse.takeWhile (·=0)).length := by
          exact List.length_reverse
        
        have h_idx_lt : i - (dropTrailingZeros a.toList).length < (a.toList.reverse.takeWhile (· = 0)).reverse.length := by
          omega
        
        have h_idx_lt2 : i - (dropTrailingZeros a.toList).length < (a.toList.reverse.takeWhile (· = 0)).length := by
          omega
          
        have h_get_rev : ∃ x, ((a.toList.reverse.takeWhile (· = 0)).reverse)[i - (dropTrailingZeros a.toList).length]? = some x := by
          exact ⟨_, List.getElem?_eq_some_iff.mpr ⟨h_idx_lt, rfl⟩⟩
        
        rcases h_get_rev with ⟨x, hx⟩
        rw [hx]
        
        have hx_rev : (a.toList.reverse.takeWhile (· = 0))[ (a.toList.reverse.takeWhile (· = 0)).length - 1 - (i - (dropTrailingZeros a.toList).length) ]? = some x := by
          have h_rev_idx : i - (dropTrailingZeros a.toList).length < (a.toList.reverse.takeWhile (· = 0)).length := by omega
          have h_rev_get : ((a.toList.reverse.takeWhile (· = 0)).reverse)[i - (dropTrailingZeros a.toList).length]? = (a.toList.reverse.takeWhile (· = 0))[ (a.toList.reverse.takeWhile (· = 0)).length - 1 - (i - (dropTrailingZeros a.toList).length) ]? := by
            exact List.getElem?_reverse h_rev_idx
          rw [h_rev_get] at hx
          exact hx
        
        have h_idx_lt_3 : (a.toList.reverse.takeWhile (· = 0)).length - 1 - (i - (dropTrailingZeros a.toList).length) < (a.toList.reverse.takeWhile (· = 0)).length := by
          omega
          
        have hp : (fun x : R => decide (x = 0)) x = true := takeWhile_getElem?_eq_some (a.toList.reverse) ((a.toList.reverse.takeWhile (· = 0)).length - 1 - (i - (dropTrailingZeros a.toList).length)) h_idx_lt_3 x hx_rev
        have hp2 : x = 0 := by exact of_decide_eq_true hp
        rw [hp2]
      have ht_arr_list : a.toList[i]? = a[i]? := Array.getElem?_toList
      rw [ht_arr_list] at h_drop
      rw [h_drop]
      rfl
    · have ht_arr_list : a.toList[i]? = a[i]? := Array.getElem?_toList
      have h_bounds_le : a.toList.length ≤ i := by omega
      have h_none : a.toList[i]? = none := List.getElem?_eq_none h_bounds_le
      rw [ht_arr_list] at h_none
      rw [h_none]

/-- Erases the `n`-th coefficient of a polynomial. -/
def erase (n : ℕ) (p : DensePoly R) : DensePoly R :=
  if p.coeffs.size ≤ n then
    p
  else
    normalize (p.coeffs.set! n 0)

@[simp] lemma toPoly_erase (n : ℕ) (p : DensePoly R) :
  DensePoly.toPoly (erase n p) = Polynomial.erase n (DensePoly.toPoly p) := by
  ext i
  rw [coeff_toPoly_eq]
  rw [Polynomial.coeff_erase]
  dsimp [erase]
  split
  · next h =>
    by_cases h_eq : i = n
    · rw [if_pos h_eq]
      rw [h_eq]
      dsimp [coeff]
      have ht : p.coeffs[n]? = none := Array.getElem?_eq_none_iff.mpr h
      rw [ht]
      rfl
    · rw [if_neg h_eq]
      rw [coeff_toPoly_eq]
  · next hc =>
    by_cases h_eq : i = n
    · rw [if_pos h_eq]
      rw [h_eq]
      rw [coeff_normalize]
      have h_lt : n < p.coeffs.size := by omega
      have ht : (p.coeffs.setIfInBounds n 0)[n]? = some 0 := by
        exact Array.getElem?_setIfInBounds_self_of_lt h_lt
      rw [ht]
      rfl
    · rw [if_neg h_eq]
      rw [coeff_normalize]
      have h_lt : n < p.coeffs.size := by omega
      have ht : (p.coeffs.setIfInBounds n 0)[i]? = p.coeffs[i]? := by
        exact Array.getElem?_setIfInBounds_ne (Ne.symm h_eq)
      rw [ht]
      rw [← coeff]
      rw [coeff_toPoly_eq]

@[simp] lemma ofPoly_erase (n : ℕ) (p : Polynomial R) :
  DensePoly.ofPoly (Polynomial.erase n p) = erase n (DensePoly.ofPoly p) := by
  rw [← toPoly_inj]
  have h := toPoly_erase n (DensePoly.ofPoly p)
  rw [toPoly_ofPoly p] at h
  rw [toPoly_ofPoly]
  exact h.symm

end Azurite.DensePoly
