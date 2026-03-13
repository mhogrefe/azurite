import Azurite.DensePoly.Polynomial
import Mathlib.Algebra.Polynomial.Basic

open Mathlib
open Polynomial

variable {R : Type _} [Ring R]

namespace Azurite
namespace DensePoly

/-- Negates a `DensePoly R` by mapping negation over its coefficients. -/
instance instNegDensePoly : Neg (DensePoly R) where
  neg p :=
    if h : p.coeffs = [] then 0 else
    ⟨p.coeffs.map (-·), by
      intro hc
      have h1 : (p.coeffs.map (-·)).getLast? = some 0 := hc
      rw [List.getLast?_map] at h1
      have hc2 : p.coeffs.getLast? ≠ some 0 := p.last_ne_zero
      -- We have `Option.map (-·) p.coeffs.getLast? = some 0`
      -- We need to prove this implies `p.coeffs.getLast? = some 0`, which contradicts `hc2`
      cases h_opt : p.coeffs.getLast?
      · rw [h_opt] at h1
        contradiction
      · next val =>
        rw [h_opt] at h1
        simp at h1
        rw [h1] at h_opt
        exact hc2 h_opt
    ⟩

lemma toPoly_map_neg (l : List R) : (l.map (-·)).toPoly = - l.toPoly := by
  induction l with
  | nil => simp [List.toPoly]
  | cons a as ih =>
    dsimp [List.toPoly]
    rw [ih]
    rw [map_neg, mul_neg]
    exact (neg_add (C a) (X * as.toPoly)).symm

@[simp] lemma toPoly_neg [DecidableEq R] (p : DensePoly R) : DensePoly.toPoly (-p) = - DensePoly.toPoly p := by
  change DensePoly.toPoly (if h : p.coeffs = [] then (0 : DensePoly R) else ⟨p.coeffs.map (-·), _⟩) = - DensePoly.toPoly p
  split
  · next h =>
    have hp0 : p = 0 := by apply Azurite.DensePoly.ext; exact h
    rw [hp0]
    simp
  · next h =>
    dsimp [DensePoly.toPoly]
    exact toPoly_map_neg p.coeffs

@[simp] lemma ofPoly_neg [DecidableEq R] (p : Polynomial R) : DensePoly.ofPoly (-p) = - DensePoly.ofPoly p := by
  apply equivPolynomial.injective
  change DensePoly.toPoly (DensePoly.ofPoly (-p)) = DensePoly.toPoly (- DensePoly.ofPoly p)
  rw [toPoly_ofPoly, toPoly_neg, toPoly_ofPoly]

end DensePoly
end Azurite
