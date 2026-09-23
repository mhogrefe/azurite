/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_1.SemialgebraicHomeomorphism
import Azurite.BasuPollackRoy.Chapter3.Section3_1.Exercise_3_1

/-! # BPR §3.1, Exercise 3.2 — `Ext` preserves semialgebraic homeomorphisms

Let `R'` be a real closed field containing `R`. If `f` is a semialgebraic homeomorphism from `S` to
`T`, then `Ext(f, R')` is a semialgebraic homeomorphism from `Ext(S, R')` to `Ext(T, R')`.

Each ingredient transfers along the extension: semialgebraicity of the extended function comes from
`Ext` of a semialgebraic set being semialgebraic; bijectivity from Exercise 2.17(a); continuity (of
both `f` and its inverse) from Exercise 3.1(b); and the inverse relation from the fact that the graph
of the inverse is the `blockSwap` transpose of the graph of `f`, which `ext_comap` carries to `R'`. -/

namespace Azurite.BPR

variable {k ℓ : ℕ}
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
variable {R' : Type*} [Field R'] [LinearOrder R'] [IsStrictOrderedRing R'] [IsRealClosed R']
variable [Algebra R R']

/-- **The extension of a semialgebraic set is semialgebraic** (realize it by a quantifier-free
formula and reinterpret over `R'`). -/
theorem isSemialgebraicSet_extension {S : Set (Fin k → R)} (hS : IsSemialgebraicSet S) :
    IsSemialgebraicSet (extension (R' := R') S hS) := by
  obtain ⟨Φ, hqf, hSeq⟩ := semialgebraic_isQFRealizable S hS
  rw [ext_eq hS hSeq]
  exact IsSemialgebraicSet.of_definedOver (D := R) (qfRealizable_isSemialgebraicSetOver hqf)

/-- **BPR Exercise 3.2.** If `f` is a semialgebraic homeomorphism from `S` to `T` (with inverse `g`),
and `f'`, `g'` are the extensions of `f`, `g` to `R'` (specified by their graphs being the extended
graphs), then `f'` is a semialgebraic homeomorphism from `Ext(S, R')` to `Ext(T, R')`. -/
theorem exercise_3_2 {S : Set (Fin k → R)} {T : Set (Fin ℓ → R)}
    {f : (Fin k → R) → (Fin ℓ → R)} {g : (Fin ℓ → R) → (Fin k → R)}
    {f' : (Fin k → R') → (Fin ℓ → R')} {g' : (Fin ℓ → R') → (Fin k → R')}
    (hsah : IsSemialgebraicHomeomorphism S T f g)
    (hS : IsSemialgebraicSet S) (hT : IsSemialgebraicSet T)
    (hgraphf : extension (R' := R') (funGraph S f) hsah.isSemialgebraicFunction
        = funGraph (extension (R' := R') S hS) f')
    (hgraphg : extension (R' := R') (funGraph T g)
          (inverse_isSemialgebraicFunction hsah.isSemialgebraicFunction hsah.bijOn hsah.invOn)
        = funGraph (extension (R' := R') T hT) g') :
    IsSemialgebraicHomeomorphism (extension (R' := R') S hS) (extension (R' := R') T hT) f' g' := by
  set hg := inverse_isSemialgebraicFunction hsah.isSemialgebraicFunction hsah.bijOn hsah.invOn
    with hgdef
  -- `f'` is a semialgebraic function: its graph is the (semialgebraic) extension of `funGraph S f`.
  have hf' : IsSemialgebraicFunction (extension (R' := R') S hS) f' := by
    show IsSemialgebraicSet (funGraph (extension (R' := R') S hS) f')
    rw [← hgraphf]; exact isSemialgebraicSet_extension hsah.isSemialgebraicFunction
  -- The graph-transpose relation transfers to `R'`, forcing `g'` to be the inverse of `f'`.
  have hgtR' : funGraph (extension (R' := R') T hT) g'
      = {v' : Fin (ℓ + k) → R' | v' ∘ blockSwap k ℓ ∈ funGraph (extension (R' := R') S hS) f'} := by
    rw [← hgraphg, ← hgraphf,
      ext_congr hg (IsSemialgebraicSet.comap (blockSwap k ℓ) hsah.isSemialgebraicFunction)
        (funGraph_inverse_eq hsah.bijOn hsah.invOn),
      ext_comap (blockSwap k ℓ) (blockSwap_injective k ℓ) hsah.isSemialgebraicFunction]
  exact
    { isSemialgebraicFunction := hf'
      bijOn := (exercise_2_17a_bijOn hS hT hsah.isSemialgebraicFunction hgraphf).mp hsah.bijOn
      continuousOn := (ext_continuousOn hS hsah.isSemialgebraicFunction hgraphf).mp hsah.continuousOn
      invOn := invOn_of_funGraph_transpose hgtR'
      continuousOn_inv := (ext_continuousOn hT hg hgraphg).mp hsah.continuousOn_inv }

/-- **Exercise 3.2, existence form.** Some extension `f'` of `f` (with some extension `g'` of `g`) is
a semialgebraic homeomorphism `Ext(S, R') → Ext(T, R')`; the extensions are produced by
Proposition 2.89. -/
theorem exercise_3_2_exists {S : Set (Fin k → R)} {T : Set (Fin ℓ → R)}
    {f : (Fin k → R) → (Fin ℓ → R)} {g : (Fin ℓ → R) → (Fin k → R)}
    (hsah : IsSemialgebraicHomeomorphism S T f g)
    (hS : IsSemialgebraicSet S) (hT : IsSemialgebraicSet T) :
    ∃ (f' : (Fin k → R') → (Fin ℓ → R')) (g' : (Fin ℓ → R') → (Fin k → R')),
      IsSemialgebraicHomeomorphism (extension (R' := R') S hS) (extension (R' := R') T hT) f' g' := by
  obtain ⟨f', hgraphf, -⟩ :=
    proposition_2_89 (R' := R') hS hT hsah.isSemialgebraicFunction hsah.bijOn.mapsTo
  obtain ⟨g', hgraphg, -⟩ := proposition_2_89 (R' := R') hT hS
    (inverse_isSemialgebraicFunction hsah.isSemialgebraicFunction hsah.bijOn hsah.invOn)
    (Set.BijOn.symm hsah.invOn.symm hsah.bijOn).mapsTo
  exact ⟨f', g', exercise_3_2 hsah hS hT hgraphf hgraphg⟩

end Azurite.BPR
