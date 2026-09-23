/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_87
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Multiplicity

/-!
# BPR §4.6, Notation 4.96: the multiplication map `L_f`

We consider a zero-dimensional system `𝒫` and the finite-dimensional vector spaces
`A = K[X₁, …, X_k] / Ideal(𝒫, K)` and `Ā = C[X₁, …, X_k] / Ideal(𝒫, C)`.

For `f ∈ A`, `L_f : A → A` is the `K`-linear map of multiplication by `f`, `L_f(g) = f g`
(`mulMap`). For `f ∈ Ā`, `L_f : Ā → Ā` is the `C`-linear multiplication by `f` (`mulMapExt`).
Since `A ⊂ Ā` (Lemma 4.87), for `f ∈ A` we also write `L_f : Ā → Ā` for multiplication by the image
of `f` in `Ā` (`mulMapBaseExt`). All three are Mathlib's `LinearMap.mulLeft`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K] (C : Type*) [Field C] [Algebra K C]
  (Ps : Finset (MvPolynomial (Fin k) K))

/-- **BPR Notation 4.96 (multiplication map on `A`).** For `f ∈ A`, `L_f : A → A` is the `K`-linear
map `g ↦ f g`. -/
noncomputable def mulMap (f : quotPolys Ps) : quotPolys Ps →ₗ[K] quotPolys Ps :=
  LinearMap.mulLeft K f

@[simp] theorem mulMap_apply (f g : quotPolys Ps) : mulMap Ps f g = f * g := rfl

/-- **BPR Notation 4.96 (multiplication map on `Ā`).** For `f ∈ Ā`, `L_f : Ā → Ā` is the `C`-linear
map `g ↦ f g`. -/
noncomputable def mulMapExt (f : quotPolysExt C Ps) :
    quotPolysExt C Ps →ₗ[C] quotPolysExt C Ps :=
  LinearMap.mulLeft C f

@[simp] theorem mulMapExt_apply (f g : quotPolysExt C Ps) : mulMapExt C Ps f g = f * g := rfl

/-- **BPR Notation 4.96 (multiplication on `Ā` by `f ∈ A`).** Using `A ⊂ Ā` (Lemma 4.87), for
`f ∈ A`, `L_f : Ā → Ā` is the `C`-linear map `g ↦ (image of f) · g`. -/
noncomputable def mulMapBaseExt (f : quotPolys Ps) :
    quotPolysExt C Ps →ₗ[C] quotPolysExt C Ps :=
  LinearMap.mulLeft C (inclExt C Ps f)

@[simp] theorem mulMapBaseExt_apply (f : quotPolys Ps) (g : quotPolysExt C Ps) :
    mulMapBaseExt C Ps f g = inclExt C Ps f * g := rfl

/-- **The multiplication map on the localization `Ā_x`.** For `f ∈ Ā` and `x ∈ Zer(𝒫, Cᵏ)`,
`L_{f,x} : Ā_x → Ā_x` is the `C`-linear map `P/Q ↦ f P/Q`, i.e. multiplication by the image of `f`
in `Ā_x`. (It is the restriction of `L_f` to `Ā_x`, viewing `Ā_x` as a subspace of `Ā` via the
corner.) -/
noncomputable def mulMapLoc (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps)
    (f : quotPolysExt C Ps) :
    localizationAtPoint C Ps x hx →ₗ[C] localizationAtPoint C Ps x hx :=
  LinearMap.mulLeft C (algebraMap (quotPolysExt C Ps) (localizationAtPoint C Ps x hx) f)

@[simp] theorem mulMapLoc_apply (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps)
    (f : quotPolysExt C Ps) (z : localizationAtPoint C Ps x hx) :
    mulMapLoc C Ps x hx f z
      = algebraMap (quotPolysExt C Ps) (localizationAtPoint C Ps x hx) f * z := rfl

end Azurite.BPR.Chapter4
