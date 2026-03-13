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
    if h : p.coeffs.size = 0 then 0 else
    ⟨p.coeffs.map (fun x => -x), by
      intro hc
      have h1 : (p.coeffs.map (fun x => -x)).toList.getLast? = some 0 := by
        have ht : (p.coeffs.map (fun x => -x)).toList.getLast? = (p.coeffs.map (fun x => -x)).back? := by simp
        rw [ht]
        exact hc
      have hw : (p.coeffs.map (fun x => -x)).toList = p.coeffs.toList.map (fun x => -x) := by simp
      rw [hw] at h1
      have hc2 : p.coeffs.back? ≠ some 0 := p.last_ne_zero
      have hlast : (p.coeffs.toList.map (fun x => -x)).getLast? = p.coeffs.toList.getLast?.map (fun x => -x) := List.getLast?_map
      rw [hlast] at h1
      cases h_opt : p.coeffs.toList.getLast?
      · rw [h_opt] at h1; contradiction
      · next val =>
        rw [h_opt] at h1
        simp at h1
        have hb : p.coeffs.back? = p.coeffs.toList.getLast? := by simp
        rw [hb] at hc2
        rw [h_opt] at hc2
        simp at hc2
        exact hc2 h1
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
  change DensePoly.toPoly (if h : p.coeffs.size = 0 then (0 : DensePoly R) else ⟨p.coeffs.map (fun x => -x), _⟩) = - DensePoly.toPoly p
  split
  · next h =>
    have hp0 : p = 0 := by
      apply Azurite.DensePoly.ext
      have ht : p.coeffs.size = p.coeffs.toList.length := by simp
      rw [ht] at h
      have hw : p.coeffs.toList = [] := List.length_eq_zero_iff.mp h
      exact eq_empty_of_toList_empty p.coeffs hw
    rw [hp0]
    simp
  · next h =>
    dsimp [DensePoly.toPoly]
    have hw : (p.coeffs.map (fun x => -x)).toList = p.coeffs.toList.map (fun x => -x) := by simp
    rw [hw]
    exact toPoly_map_neg p.coeffs.toList

@[simp] lemma ofPoly_neg [DecidableEq R] (p : Polynomial R) : DensePoly.ofPoly (-p) = - DensePoly.ofPoly p := by
  apply equivPolynomial.injective
  change DensePoly.toPoly (DensePoly.ofPoly (-p)) = DensePoly.toPoly (- DensePoly.ofPoly p)
  rw [toPoly_ofPoly, toPoly_neg, toPoly_ofPoly]

end DensePoly
end Azurite
