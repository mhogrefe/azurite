/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_7.ComplexPolySemialgebraic

/-!
# BPR §4.7, Proposition 4.106: the Hermitian norm on `Cᵏ`

To establish projective completeness (the substitute for compactness, since closed + bounded ⊄ compact
over a real closed field), we will embed `ℙ_k(C)` into a space of Hermitian projectors. The basic
metric ingredient is the **Hermitian norm** `‖v‖² = ∑ⱼ (Re vⱼ)² + (Im vⱼ)²` of a vector
`v ∈ Cᵏ = (Fin n → Ri R)`. Expressed through the order-free real/imaginary parts `Ri.reL`/`Ri.imL`,
this is exactly the squared Euclidean norm of the realification `realEquiv v ∈ R^{2n}`; it is
non-negative and vanishes only at `0` (anisotropy, as `R` is real closed).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {n : ℕ}

set_option linter.unusedSectionVars false in
/-- Two elements of `Ri R` are equal iff their real and imaginary parts agree. -/
theorem Ri.ext_reL_imL {x y : Ri R} (hre : Ri.reL x = Ri.reL y) (him : Ri.imL x = Ri.imL y) :
    x = y := by
  rw [← Ri.of_reL_add_of_imL_mul_i x, ← Ri.of_reL_add_of_imL_mul_i y, hre, him]

set_option linter.unusedSectionVars false in
/-- The **Hermitian norm squared** `‖v‖² = ∑ⱼ (Re vⱼ)² + (Im vⱼ)²` of a vector in `Cⁿ`. -/
noncomputable def hermNormSq (v : Fin n → Ri R) : R :=
  ∑ j, ((Ri.reL (v j)) ^ 2 + (Ri.imL (v j)) ^ 2)

set_option linter.unusedSectionVars false in
theorem hermNormSq_nonneg (v : Fin n → Ri R) : 0 ≤ hermNormSq v :=
  Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The Hermitian norm is anisotropic: it vanishes only at the zero vector. -/
theorem hermNormSq_eq_zero_iff {v : Fin n → Ri R} : hermNormSq v = 0 ↔ v = 0 := by
  rw [hermNormSq,
    Finset.sum_eq_zero_iff_of_nonneg fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _)]
  constructor
  · intro h
    funext j
    have hj := h j (Finset.mem_univ j)
    rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _), sq_eq_zero_iff, sq_eq_zero_iff] at hj
    refine Ri.ext_reL_imL ?_ ?_ <;> simp [hj.1, hj.2]
  · rintro rfl j _
    simp

/-- The Hermitian norm of a nonzero vector is positive. -/
theorem hermNormSq_pos {v : Fin n → Ri R} (hv : v ≠ 0) : 0 < hermNormSq v :=
  lt_of_le_of_ne (hermNormSq_nonneg v) fun h => hv (hermNormSq_eq_zero_iff.mp h.symm)

end Azurite.BPR.Chapter4
