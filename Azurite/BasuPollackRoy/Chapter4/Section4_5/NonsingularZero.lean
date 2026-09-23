/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# BPR §4.5: non-singular zeros

Let `P₁, …, P_k` be polynomials in `C[X₁, …, X_k]` (a square system: `k` polynomials in `k`
variables). A *non-singular zero* of `P₁, …, P_k` is a `k`-tuple `x = (x₁, …, x_k) ∈ Cᵏ` that is a
common zero, `P₁(x) = ⋯ = P_k(x) = 0`, and at which the Jacobian determinant
`det([∂Pᵢ/∂Xⱼ(x)])` is nonzero (`IsNonsingularZero`, with `jacobian` the Jacobian matrix).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {C : Type*} [CommRing C]

/-- The **Jacobian matrix** of `P : Fin k → C[X₁, …, X_k]` at `x ∈ Cᵏ`: the `k × k` matrix whose
`(i, j)` entry is `(∂Pᵢ/∂Xⱼ)(x)`. -/
noncomputable def jacobian (P : Fin k → MvPolynomial (Fin k) C) (x : Fin k → C) :
    Matrix (Fin k) (Fin k) C :=
  Matrix.of fun i j => MvPolynomial.aeval x (MvPolynomial.pderiv j (P i))

/-- **BPR Definition (non-singular zero).** A `k`-tuple `x ∈ Cᵏ` is a *non-singular zero* of
`P₁, …, P_k` if it is a common zero (`Pᵢ(x) = 0` for all `i`) and the Jacobian determinant
`det([∂Pᵢ/∂Xⱼ(x)])` is nonzero. -/
def IsNonsingularZero (P : Fin k → MvPolynomial (Fin k) C) (x : Fin k → C) : Prop :=
  (∀ i, MvPolynomial.aeval x (P i) = 0) ∧ (jacobian P x).det ≠ 0

end Azurite.BPR.Chapter4
