/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_5.SemialgebraicFunction
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Linear maps are semialgebraic

(Not in BPR.) A linear map `R^n → R^m` is semialgebraic: each output coordinate is a linear
(hence polynomial) function of the input, so the graph
`{(x, y) ∈ R^{n+m} | y = M·x}` is the common zero set of the `m` polynomials
`X_{n+j} - ∑ᵢ Mⱼᵢ Xᵢ`, an algebraic set.
-/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The `j`-th coordinate of `M·x`, as a (linear) polynomial in `X_1, …, X_n`. -/
noncomputable def linPoly {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) (j : Fin m) :
    MvPolynomial (Fin n) R :=
  ∑ i, MvPolynomial.C (M j i) * MvPolynomial.X i

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem eval_linPoly {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) (x : Fin n → R) (j : Fin m) :
    MvPolynomial.eval x (linPoly M j) = (M.mulVec x) j := by
  simp only [linPoly, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Matrix.mulVec, dotProduct]

omit [IsStrictOrderedRing R] in
/-- **A matrix-vector map `R^n → R^m` is semialgebraic.** -/
theorem mulVec_isSemialgebraicFunction {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) :
    IsSemialgebraicFunction (Set.univ : Set (Fin n → R)) (fun x => M.mulVec x) := by
  set Q : Fin m → MvPolynomial (Fin (n + m)) R :=
    fun j => MvPolynomial.X (Fin.natAdd n j) - MvPolynomial.rename (Fin.castAdd m) (linPoly M j)
    with hQ
  have hQeval : ∀ (z : Fin (n + m) → R) (j : Fin m),
      MvPolynomial.eval z (Q j) = z (Fin.natAdd n j) - (M.mulVec (z ∘ Fin.castAdd m)) j := by
    intro z j
    rw [hQ]
    simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_rename, eval_linPoly]
  show IsSemialgebraicSet (funGraph (Set.univ : Set (Fin n → R)) (fun x => M.mulVec x))
  refine IsSemialgebraicSet.algebraic ⟨Finset.univ.image Q, ?_⟩
  ext z
  rw [mem_funGraph]
  simp only [Set.mem_univ, true_and, Zer, Set.mem_ofPred_eq, Finset.mem_image, Finset.mem_univ,
    forall_exists_index, forall_apply_eq_imp_iff, hQeval, sub_eq_zero]
  constructor
  · intro h j; exact congrFun h j
  · intro h; funext j; exact h j

omit [IsStrictOrderedRing R] in
/-- **A linear map `R^n → R^m` is semialgebraic.** -/
theorem linearMap_isSemialgebraicFunction {m n : ℕ}
    (f : (Fin n → R) →ₗ[R] (Fin m → R)) :
    IsSemialgebraicFunction (Set.univ : Set (Fin n → R)) (⇑f) := by
  have hf : (⇑f) = fun x => (LinearMap.toMatrix' f).mulVec x := by
    funext x
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rw [hf]
  exact mulVec_isSemialgebraicFunction _

end Azurite.BPR
