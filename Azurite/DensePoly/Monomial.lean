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

end Azurite.DensePoly
