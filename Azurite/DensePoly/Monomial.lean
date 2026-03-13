import Azurite.DensePoly.Basic
import Azurite.DensePoly.Polynomial

/-!
# Constant Polynomials and Monomials

This module defines constructors for basic polynomials natively within `DensePoly`,
such as `DenseC` for constant polynomials.
-/

namespace Azurite.DensePoly

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- Constructs a constant polynomial with value `c`. -/
def DenseC (c : R) : DensePoly R :=
  if h : c = 0 then
    0
  else
    ⟨#[c], by simp [h]⟩

@[simp] lemma toPoly_DenseC (c : R) : DensePoly.toPoly (DenseC c) = Polynomial.C c := by
  unfold DenseC
  split
  · next hc =>
    rw [hc, Polynomial.C_0]
    exact toPoly_zero
  · next hc =>
    dsimp [DensePoly.toPoly, List.toPoly]
    simp

@[simp] lemma ofPoly_C (c : R) : DensePoly.ofPoly (Polynomial.C c) = DenseC c := by
  rw [← toPoly_inj]
  rw [toPoly_ofPoly]
  exact (toPoly_DenseC c).symm

end Azurite.DensePoly
