/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_7.ComplexPolySemialgebraic
import Azurite.BasuPollackRoy.Chapter4.Section4_7.NonsingularProjectiveZero
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# BPR §4.7, Proposition 4.106: realification of a complex matrix

The implicit function theorem (Theorem 4.104) is stated over `R` (real coordinates), so applying it to
a system of `k` *complex* equations requires the linear-algebra bridge: the `2k × 2k` real Jacobian of
a holomorphic map is the **realification** of the `k × k` complex Jacobian, and it is invertible
exactly when the complex one is.

For `A : Matrix (Fin k) (Fin k) (Ri R)` we define `realifyMatrix A`, the `2k × 2k` real matrix in the
`Re`/`Im`-block layout matching `realEquiv` (`Cᵏ ≅ R^{2k}`), namely
`[[Re A, -Im A], [Im A, Re A]]`. The key identity is the intertwining
`(realifyMatrix A).mulVec (realEquiv w) = realEquiv (A.mulVec w)`, from which invertibility transports:
if `A.det` is a unit then so is `(realifyMatrix A).det`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-- The **realification** of a complex `k × k` matrix `A`, as the `2k × 2k` real matrix in the
`Re`/`Im`-block layout `[[Re A, -Im A], [Im A, Re A]]` (rows/columns split as `castAdd` = real block,
`natAdd` = imaginary block, matching `realEquiv`). -/
noncomputable def realifyMatrix (A : Matrix (Fin k) (Fin k) (Ri R)) :
    Matrix (Fin (k + k)) (Fin (k + k)) R :=
  Matrix.of fun i i' =>
    Fin.addCases
      (fun l => Fin.addCases (fun j => Ri.reL (A l j)) (fun j => -Ri.imL (A l j)) i')
      (fun l => Fin.addCases (fun j => Ri.imL (A l j)) (fun j => Ri.reL (A l j)) i')
      i

set_option linter.unusedSectionVars false in
/-- `realEquiv` sends `0` to `0`. -/
theorem realEquiv_zero : realEquiv (0 : Fin k → Ri R) = 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [realEquiv_apply_castAdd]; simp
  · rw [realEquiv_apply_natAdd]; simp

set_option linter.unusedSectionVars false in
/-- **The intertwining identity.** Multiplying the realified matrix by the realified vector equals the
realification of the complex matrix–vector product. -/
theorem realifyMatrix_mulVec (A : Matrix (Fin k) (Fin k) (Ri R)) (w : Fin k → Ri R) :
    (realifyMatrix A).mulVec (realEquiv w) = realEquiv (A.mulVec w) := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · -- real block
    rw [realEquiv_apply_castAdd, Matrix.mulVec, dotProduct,
      Fin.sum_univ_add, Matrix.mulVec, dotProduct, map_sum]
    refine (Finset.sum_add_distrib.symm.trans ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [realifyMatrix, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right,
      realEquiv_apply_castAdd, realEquiv_apply_natAdd, reL_mul]
    ring
  · -- imaginary block
    rw [realEquiv_apply_natAdd, Matrix.mulVec, dotProduct,
      Fin.sum_univ_add, Matrix.mulVec, dotProduct, map_sum]
    refine (Finset.sum_add_distrib.symm.trans ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [realifyMatrix, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right,
      realEquiv_apply_castAdd, realEquiv_apply_natAdd, imL_mul]
    ring

set_option linter.unusedSectionVars false in
/-- **Invertibility transports.** If the complex matrix `A` has unit determinant, then so does its
realification `realifyMatrix A`. -/
theorem isUnit_det_realifyMatrix (A : Matrix (Fin k) (Fin k) (Ri R)) (hA : IsUnit A.det) :
    IsUnit (realifyMatrix A).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hvker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  -- pull `v` back to a complex vector `w` killed by `A`
  refine (isUnit_iff_ne_zero.mp hA) (Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨realEquiv.symm v, ?_, ?_⟩)
  · intro h
    apply hv0
    rw [← Equiv.apply_symm_apply realEquiv v, h, realEquiv_zero]
  · apply realEquiv.injective
    rw [realEquiv_zero, ← realifyMatrix_mulVec, Equiv.apply_symm_apply]
    exact hvker

set_option linter.unusedSectionVars false in
/-- **The IFT invertibility hypothesis at a non-singular zero (chart `0`).** If `(1 : a₁ : ⋯ : a_k)`
is a non-singular projective zero of homogeneous `P₁, …, P_k`, then the realification of the affine
complex Jacobian of the dehomogenized system `Pᵢ(1, X₁, …, X_k)` at `a` is invertible — exactly the
determinant hypothesis the (realified) implicit function theorem requires. -/
theorem isUnit_det_realifyMatrix_jacobian_dehom
    (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i)) (a : Fin k → Ri R)
    (hns : IsNonsingularProjectiveZero P (mkLine (Fin.cons 1 a) (cons_one_ne_zero a))) :
    IsUnit (realifyMatrix
      (jacobian (fun i => aeval (Fin.cons (1 : MvPolynomial (Fin k) (Ri R)) X) (P i)) a)).det := by
  rw [← isNonsingularZero_dehom_iff_isNonsingularProjectiveZero P d hP a] at hns
  exact isUnit_det_realifyMatrix _ (isUnit_iff_ne_zero.mpr hns.2)
