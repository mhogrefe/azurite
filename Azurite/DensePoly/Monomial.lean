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

end Azurite.DensePoly
