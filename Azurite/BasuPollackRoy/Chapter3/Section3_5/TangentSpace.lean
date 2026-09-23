/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_5.Proposition_3_26

/-! # BPR §3.5 — the tangent space `T_x(M)`

**With a chart `ϕ : U → Ω` at a smooth point `x` of an `𝒮^∞` submanifold `M` of dimension
`ℓ`, the tangent space to `M` at `x` is `T_x(M) = x + dϕ(0)(R^ℓ × {0})`.** It contains `x`
and is a translate of a linear subspace of `R^k` (an `ℓ`-flat); more concretely, it is the
translate by `x` of the linear span of the first `ℓ` columns of the Jacobian matrix
`dϕ(0)` (since `dϕ(0)·e_j` is the `j`-th column).

This packages the direction `dϕ(0)(R^ℓ × {0})` (used inline in Propositions 3.26 and 3.27)
as `tangentSpaceDir`, with `tangentSpace x g ℓ = x + tangentSpaceDir g ℓ`. -/

namespace Azurite.BPR

open MvPolynomial

variable {k ℓ : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The coordinate subspace `R^ℓ × {0}` is the span of the standard basis vectors
`e_j = Pi.single j 1` with `j < ℓ`. -/
theorem coordSubmodule_eq_span :
    coordSubmodule (R := R) k ℓ
      = Submodule.span R ((fun j : Fin k => Pi.single j (1 : R)) '' {j | (j : ℕ) < ℓ}) := by
  apply le_antisymm
  · intro z hz
    rw [pi_eq_sum_univ' z]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : (i : ℕ) < ℓ
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · have hz0 : z i = 0 := hz i (by omega)
      rw [hz0, zero_smul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩ i hi
    have hjl : (j : ℕ) < ℓ := hj
    have hij : i ≠ j := Fin.ne_of_val_ne (by omega)
    simp [hij]

/-- The **tangent direction** `dϕ(0)(R^ℓ × {0})` — the linear subspace of which `T_x(M)`
is a translate. -/
noncomputable def tangentSpaceDir (g : Fin k → Fin k → (Fin k → R) → R) (ℓ : ℕ) :
    Submodule R (Fin k → R) :=
  Submodule.map (Matrix.mulVecLin (jacobianMatrix g 0)) (coordSubmodule k ℓ)

/-- **BPR definition (tangent space).** `T_x(M) = x + dϕ(0)(R^ℓ × {0})`. -/
def tangentSpace (x : Fin k → R) (g : Fin k → Fin k → (Fin k → R) → R) (ℓ : ℕ) :
    Set (Fin k → R) :=
  (fun w => x + w) '' (tangentSpaceDir g ℓ : Set (Fin k → R))

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The tangent space **contains `x`**. -/
theorem self_mem_tangentSpace (x : Fin k → R) (g : Fin k → Fin k → (Fin k → R) → R)
    (ℓ : ℕ) : x ∈ tangentSpace x g ℓ :=
  ⟨0, (tangentSpaceDir g ℓ).zero_mem, by simp⟩

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- The tangent space is the **translate by `x`** of the linear subspace `tangentSpaceDir`:
`y ∈ T_x(M) ↔ y − x ∈ dϕ(0)(R^ℓ × {0})`. -/
theorem mem_tangentSpace_iff {x : Fin k → R} {g : Fin k → Fin k → (Fin k → R) → R}
    {ℓ : ℕ} {y : Fin k → R} :
    y ∈ tangentSpace x g ℓ ↔ y - x ∈ tangentSpaceDir g ℓ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [add_sub_cancel_left]
    exact hw
  · intro h
    exact ⟨y - x, h, by simp⟩

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- **The concrete description.** `T_x(M)` is the translate by `x` of the linear span of
the first `ℓ` columns of the Jacobian matrix (`dϕ(0)·e_j` is the `j`-th column). -/
theorem tangentSpaceDir_eq_span_cols (g : Fin k → Fin k → (Fin k → R) → R) (ℓ : ℕ) :
    tangentSpaceDir g ℓ
      = Submodule.span R
          ((fun j : Fin k => (jacobianMatrix g 0).mulVec (Pi.single j 1)) '' {j | (j : ℕ) < ℓ}) := by
  rw [tangentSpaceDir, coordSubmodule_eq_span, Submodule.map_span, Set.image_image]
  simp only [Matrix.mulVecLin_apply]

end Azurite.BPR
