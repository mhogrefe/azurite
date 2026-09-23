/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_3.Orthogonality
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# BPR Proposition 4.42: Cauchy–Schwarz inequality

If the quadratic form `Φ_M` of a symmetric matrix `M` is non-negative, then
`B_M(f, g)² ≤ Φ_M(f) · Φ_M(g)` for all `f, g`.

Following BPR, fix `f` and `g` and consider the degree-2 polynomial
`P(t) = Φ_M(f + t·g) = Φ_M(f) + 2·t·B_M(f, g) + t²·Φ_M(g)`. Since `Φ_M` is
non-negative, `P(t) ≥ 0` for every `t ∈ R`, so its discriminant
`4·B_M(f, g)² − 4·Φ_M(f)·Φ_M(g)` is non-positive (Mathlib's `discrim_le_zero`),
which is exactly the claimed inequality.
-/

namespace Azurite.BPR.Chapter4

open scoped Matrix

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ}

/-- **Proposition 4.42 (Cauchy–Schwarz inequality).** If the quadratic form of a
symmetric matrix `M` is non-negative, then `B_M(f, g)² ≤ Φ_M(f) · Φ_M(g)`. -/
theorem proposition_4_42 (M : Matrix (Fin n) (Fin n) R) (hM : M.IsSymm)
    (hpos : IsNonNeg M) (f g : Fin n → R) :
    bilinFormM M f g ^ 2 ≤ quadraticForm M f * quadraticForm M g := by
  -- Bridge: the quadratic form is `x ↦ x · M · x`.
  have hbridge : ∀ x : Fin n → R, quadraticForm M x = x ⬝ᵥ M *ᵥ x := by
    intro x
    rw [quadraticForm, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply']
  -- Symmetry: `f · M · g = g · M · f = B_M(f, g)`.
  have hsymm : f ⬝ᵥ M *ᵥ g = bilinFormM M f g := by
    rw [bilinFormM, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq,
      dotProduct_comm]
  -- Expansion of `Φ_M(f + t • g)` as a degree-2 polynomial in `t`.
  have hexp : ∀ t : R, quadraticForm M (f + t • g)
      = quadraticForm M g * (t * t) + (2 * bilinFormM M f g) * t + quadraticForm M f := by
    intro t
    rw [hbridge, hbridge, hbridge]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
      dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hsymm]
    simp only [bilinFormM]
    ring
  -- The discriminant of the (non-negative) polynomial is `≤ 0`.
  have hdiscrim : discrim (quadraticForm M g) (2 * bilinFormM M f g) (quadraticForm M f) ≤ 0 := by
    apply discrim_le_zero
    intro t
    rw [← hexp t]
    exact hpos (f + t • g)
  rw [discrim] at hdiscrim
  nlinarith [hdiscrim]

end Azurite.BPR.Chapter4
