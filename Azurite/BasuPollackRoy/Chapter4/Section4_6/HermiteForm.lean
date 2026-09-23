/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_6.MultiplicationMap
import Mathlib.RingTheory.Trace.Defs
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.Algebra.Bilinear

/-!
# BPR §4.6: Hermite's bilinear map and quadratic form

For `Q ∈ A`, **Hermite's bilinear map** `her(𝒫, Q) : A × A → K` is `(f, g) ↦ Tr(L_{f g Q})`, and the
associated **Hermite's quadratic form** `Her(𝒫, Q) : A → K` is `f ↦ Tr(L_{f² Q})`. When `Q = 1`
we write `her(𝒫) = her(𝒫, 1)` and `Her(𝒫) = Her(𝒫, 1)`.

Since `Tr(L_z) = Algebra.trace K A z`, Hermite's bilinear map is the trace form of `A`
precomposed (in its second argument) with multiplication by `Q`, which makes its bilinearity and
symmetry automatic.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K]

/-- The trace of the multiplication map `L_z` is the algebra trace of `z`. -/
theorem trace_mulMap (Ps : Finset (MvPolynomial (Fin k) K)) (z : quotPolys Ps) :
    LinearMap.trace K (quotPolys Ps) (mulMap Ps z) = Algebra.trace K (quotPolys Ps) z := by
  rw [Algebra.trace_apply]; rfl

/-- **Hermite's bilinear map** `her(𝒫, Q) : A × A → K`, `(f, g) ↦ Tr(L_{f g Q})`. It is the trace
form of `A` with its second argument multiplied by `Q`. -/
noncomputable def hermiteBilin (Ps : Finset (MvPolynomial (Fin k) K)) (Q : quotPolys Ps) :
    LinearMap.BilinForm K (quotPolys Ps) :=
  (Algebra.traceForm K (quotPolys Ps)).compl₂ (LinearMap.mulRight K Q)

@[simp] theorem hermiteBilin_apply (Ps : Finset (MvPolynomial (Fin k) K))
    (Q f g : quotPolys Ps) :
    hermiteBilin Ps Q f g = LinearMap.trace K (quotPolys Ps) (mulMap Ps (f * g * Q)) := by
  rw [hermiteBilin, LinearMap.compl₂_apply, Algebra.traceForm_apply, LinearMap.mulRight_apply,
    trace_mulMap, mul_assoc]

/-- **Hermite's quadratic form** `Her(𝒫, Q) : A → K`, `f ↦ Tr(L_{f² Q})`, the quadratic form
associated to Hermite's bilinear map `her(𝒫, Q)`. -/
noncomputable def hermiteQuad (Ps : Finset (MvPolynomial (Fin k) K)) (Q : quotPolys Ps) :
    QuadraticForm K (quotPolys Ps) :=
  (hermiteBilin Ps Q).toQuadraticMap

@[simp] theorem hermiteQuad_apply (Ps : Finset (MvPolynomial (Fin k) K)) (Q f : quotPolys Ps) :
    hermiteQuad Ps Q f = LinearMap.trace K (quotPolys Ps) (mulMap Ps (f ^ 2 * Q)) := by
  rw [hermiteQuad, LinearMap.BilinMap.toQuadraticMap_apply, hermiteBilin_apply, sq]

/-- `her(𝒫) = her(𝒫, 1)`. -/
noncomputable def hermiteBilinOne (Ps : Finset (MvPolynomial (Fin k) K)) :
    LinearMap.BilinForm K (quotPolys Ps) :=
  hermiteBilin Ps 1

/-- `Her(𝒫) = Her(𝒫, 1)`. -/
noncomputable def hermiteQuadOne (Ps : Finset (MvPolynomial (Fin k) K)) :
    QuadraticForm K (quotPolys Ps) :=
  hermiteQuad Ps 1

theorem hermiteBilinOne_apply (Ps : Finset (MvPolynomial (Fin k) K)) (f g : quotPolys Ps) :
    hermiteBilinOne Ps f g = LinearMap.trace K (quotPolys Ps) (mulMap Ps (f * g)) := by
  rw [hermiteBilinOne, hermiteBilin_apply, mul_one]

theorem hermiteQuadOne_apply (Ps : Finset (MvPolynomial (Fin k) K)) (f : quotPolys Ps) :
    hermiteQuadOne Ps f = LinearMap.trace K (quotPolys Ps) (mulMap Ps (f ^ 2)) := by
  rw [hermiteQuadOne, hermiteQuad_apply, mul_one]

end Azurite.BPR.Chapter4
