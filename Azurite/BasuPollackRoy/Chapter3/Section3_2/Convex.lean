/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Convex.Basic

/-! # BPR §3.2 — convex sets

A subset `C ⊆ R^k` is *convex* if for all `x, y ∈ C` the segment
`[x, y] = {(1 − λ) x + λ y | λ ∈ [0,1]}` is contained in `C`.

This is exactly Mathlib's `Convex R` for the `R`-module `R^k = Fin k → R`; we record the BPR-phrased
definition and its equivalence with `Convex R` so the Mathlib convexity API is available. -/

namespace Azurite.BPR

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **BPR definition (convex set).** A subset `C ⊆ R^k` is *convex* if for all `x, y ∈ C` the segment
`{(1 − λ) x + λ y | λ ∈ [0,1]}` is contained in `C`. -/
def IsConvex (C : Set (Fin k → R)) : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C → ∀ l : R, l ∈ Set.Icc (0 : R) 1 → (1 - l) • x + l • y ∈ C

/-- `IsConvex` agrees with Mathlib's `Convex R`, giving access to the convexity API. -/
theorem isConvex_iff_convex {C : Set (Fin k → R)} : IsConvex C ↔ Convex R C := by
  rw [convex_iff_segment_subset]
  refine ⟨fun h x hx y hy z hz => ?_, fun h x hx y hy l hl => ?_⟩
  · rw [segment_eq_image] at hz
    obtain ⟨l, hl, rfl⟩ := hz
    exact h hx hy l hl
  · exact h hx hy (by rw [segment_eq_image]; exact ⟨l, hl, rfl⟩)

end Azurite.BPR
