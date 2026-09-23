/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Map functions for `AzMvPolynomial` (Fin-indexed).
-/
import Azurite.AzMvPolynomial.Basic
import Mathlib.Algebra.Algebra.Basic

namespace Azurite
open AzMvPolynomial

variable {R S : Type _} [Semiring R] [Semiring S] [DecidableEq S]
         {n : ℕ} {ord : MonomialOrder}

/-! ### Helpers -/

/-- Map a monomial's coefficient, producing `none` if the result is zero. -/
def mapMonomialCoeff (f : R →+* S)
    (m : Monomial n R ord) : Option (Monomial n S ord) :=
  if h : f m.coeff.val = 0 then none
  else some ⟨⟨f m.coeff.val, h⟩, m.monic⟩

/-- `mapMonomialCoeff` preserves the monic part. -/
theorem mapMonomialCoeff_some {f : R →+* S}
    {m : Monomial n R ord} {m' : Monomial n S ord}
    (h : mapMonomialCoeff f m = some m') : m'.monic = m.monic := by
  unfold mapMonomialCoeff at h; split at h
  · contradiction
  · injection h with h'; subst h'; rfl

private theorem pairwise_gt_filterMap (f : R →+* S)
    {l : List (Monomial n R ord)}
    (hp : l.Pairwise (fun a b => a.monic > b.monic)) :
    (l.filterMap (mapMonomialCoeff f)).Pairwise
      (fun a b => a.monic > b.monic) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hp
    rw [List.filterMap_cons]
    rcases ha : mapMonomialCoeff f a with _ | a'
    · exact ih hp.2
    · rw [List.pairwise_cons]
      refine ⟨fun b hb => ?_, ih hp.2⟩
      obtain ⟨m', hm', hmap⟩ := List.mem_filterMap.mp hb
      rw [mapMonomialCoeff_some ha, mapMonomialCoeff_some hmap]
      exact hp.1 m' hm'

/-- Map each coefficient, preserving nonzero when `f` is zero-injective. -/
def mapCoeff (f : R → S) (hf : ∀ r, f r = 0 → r = 0)
    (m : Monomial n R ord) : Monomial n S ord :=
  ⟨⟨f m.coeff.val, fun h => m.coeff.property (hf _ h)⟩, m.monic⟩

/-! ### Map functions -/

/-- A general-purpose coefficient map that skips filtering when `f` preserves
    zeros strictly (`f r = 0 ↔ r = 0`). -/
def AzMvPolynomial.mapZeroInjective
    (f : R → S) (hf : ∀ r, f r = 0 ↔ r = 0)
    (p : AzMvPolynomial n R ord) : AzMvPolynomial n S ord :=
  ⟨p.terms.map (mapCoeff f (fun r h => (hf r).mp h)),
   by rw [Array.toList_map]; exact p.sorted.map _ (fun _ _ h => h)⟩

/-- Map coefficients via an injective ring homomorphism. -/
def AzMvPolynomial.mapInjective
    (f : R →+* S) (hf : Function.Injective f)
    (p : AzMvPolynomial n R ord) : AzMvPolynomial n S ord :=
  AzMvPolynomial.mapZeroInjective f
    (fun r => ⟨fun h => hf (by rw [h, f.map_zero]),
              fun h => by rw [h, f.map_zero]⟩) p

/-- Map coefficients via `algebraMap R S` when it is injective. -/
def AzMvPolynomial.mapAlgebraMap {R S : Type _} [CommSemiring R] [Semiring S] [Algebra R S]
    {n : ℕ} {ord : MonomialOrder}
    (hf : Function.Injective (algebraMap R S))
    (p : AzMvPolynomial n R ord) : AzMvPolynomial n S ord :=
  AzMvPolynomial.mapInjective (algebraMap R S) hf p

/-- Map coefficients via a ring homomorphism, filtering out zero results. -/
def AzMvPolynomial.map
    (f : R →+* S) (p : AzMvPolynomial n R ord) : AzMvPolynomial n S ord :=
  ⟨(p.terms.toList.filterMap (mapMonomialCoeff f)).toArray,
   by rw [List.toList_toArray]; exact pairwise_gt_filterMap f p.sorted⟩

end Azurite
