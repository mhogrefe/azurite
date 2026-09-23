/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_7.ProjectiveTopology

/-!
# BPR §4.7: semialgebraic sets of `ℙ_k(C) × ℙ_ℓ(C)` and semialgebraic maps

The semialgebraic subsets of a product `ℙ_k(C) × ℙ_ℓ(C)` are defined exactly as for a single
projective space, but using the product charts `φᵢ × φⱼ : Cᵏ × Cˡ → ℙ_k(C) × ℙ_ℓ(C)`: a subset `S`
is semialgebraic when, for every pair of charts `(i, j)`, the pullback
`(φᵢ × φⱼ)⁻¹(S ∩ (𝒰ᵢ × 𝒰ⱼ))` is semialgebraic in `Cᵏ × Cˡ = C^{k+ℓ} = R^{2(k+ℓ)}` (the product domain
being recorded as the first `k` and last `ℓ` blocks of `C^{k+ℓ}`).

A **semialgebraic map** `ℙ_k(C) → ℙ_ℓ(C)` is one whose graph is a semialgebraic subset of the
product.
-/

namespace Azurite.BPR.Chapter4

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k ℓ : ℕ}

/-- The product chart `φᵢ × φⱼ`, with domain recorded as `C^{k+ℓ}` (first `k` blocks feed `φᵢ`, last
`ℓ` blocks feed `φⱼ`). -/
noncomputable def prodChart (i : Fin (k + 1)) (j : Fin (ℓ + 1)) :
    (Fin (k + ℓ) → Ri R) → complexProjectiveSpace R k × complexProjectiveSpace R ℓ :=
  fun z => (chartMap i (z ∘ Fin.castAdd ℓ), chartMap j (z ∘ Fin.natAdd k))

/-- **BPR §4.7 (semialgebraic subset of `ℙ_k(C) × ℙ_ℓ(C)`).** `S` is semialgebraic iff, for every pair
of charts `(i, j)`, the pullback `(φᵢ × φⱼ)⁻¹(S ∩ (𝒰ᵢ × 𝒰ⱼ))` is semialgebraic in `C^{k+ℓ}`. -/
def IsSemialgebraicSetPP
    (S : Set (complexProjectiveSpace R k × complexProjectiveSpace R ℓ)) : Prop :=
  ∀ (i : Fin (k + 1)) (j : Fin (ℓ + 1)),
    IsSemialgebraicSetC
      (prodChart i j ⁻¹' (S ∩ chartSet i ×ˢ chartSet j) : Set (Fin (k + ℓ) → Ri R))

/-- **Fidelity.** `S` is semialgebraic in the product exactly when each product-chart pullback is
semialgebraic. -/
theorem isSemialgebraicSetPP_iff
    {S : Set (complexProjectiveSpace R k × complexProjectiveSpace R ℓ)} :
    IsSemialgebraicSetPP S ↔
      ∀ (i : Fin (k + 1)) (j : Fin (ℓ + 1)),
        IsSemialgebraicSetC
          (prodChart i j ⁻¹' (S ∩ chartSet i ×ˢ chartSet j) : Set (Fin (k + ℓ) → Ri R)) :=
  Iff.rfl

/-- **BPR §4.7 (semialgebraic mapping).** A map `ℙ_k(C) → ℙ_ℓ(C)` is *semialgebraic* if its graph is a
semialgebraic subset of `ℙ_k(C) × ℙ_ℓ(C)`. -/
def IsSemialgebraicMapP (f : complexProjectiveSpace R k → complexProjectiveSpace R ℓ) : Prop :=
  IsSemialgebraicSetPP {p : complexProjectiveSpace R k × complexProjectiveSpace R ℓ | p.2 = f p.1}

end Azurite.BPR.Chapter4
