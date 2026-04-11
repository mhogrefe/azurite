/-
  Map functions for `AzMvPolynomialNew` (Fin-indexed).
-/
import Azurite.AzMvPolynomial.New.Basic

namespace Azurite
open AzMvPolynomialNew

variable {R S : Type _} [Semiring R] [Semiring S] [DecidableEq S]
         {n : ℕ} {ord : MonomialOrder}

/-! ### Helpers -/

/-- Map a monomial's coefficient, producing `none` if the result is zero. -/
def mapMonomialCoeffNew (f : R →+* S)
    (m : MonomialNew n R ord) : Option (MonomialNew n S ord) :=
  if h : f m.coeff.val = 0 then none
  else some ⟨⟨f m.coeff.val, h⟩, m.monic⟩

/-- `mapMonomialCoeffNew` preserves the monic part. -/
theorem mapMonomialCoeffNew_some {f : R →+* S}
    {m : MonomialNew n R ord} {m' : MonomialNew n S ord}
    (h : mapMonomialCoeffNew f m = some m') : m'.monic = m.monic := by
  unfold mapMonomialCoeffNew at h; split at h
  · contradiction
  · injection h with h'; subst h'; rfl

private theorem pairwise_gt_filterMap_new (f : R →+* S)
    {l : List (MonomialNew n R ord)}
    (hp : l.Pairwise (fun a b => a.monic > b.monic)) :
    (l.filterMap (mapMonomialCoeffNew f)).Pairwise
      (fun a b => a.monic > b.monic) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hp
    rw [List.filterMap_cons]
    rcases ha : mapMonomialCoeffNew f a with _ | a'
    · exact ih hp.2
    · rw [List.pairwise_cons]
      refine ⟨fun b hb => ?_, ih hp.2⟩
      obtain ⟨m', hm', hmap⟩ := List.mem_filterMap.mp hb
      rw [mapMonomialCoeffNew_some ha, mapMonomialCoeffNew_some hmap]
      exact hp.1 m' hm'

/-- Map each coefficient, preserving nonzero when `f` is zero-injective. -/
def mapCoeffNew (f : R → S) (hf : ∀ r, f r = 0 → r = 0)
    (m : MonomialNew n R ord) : MonomialNew n S ord :=
  ⟨⟨f m.coeff.val, fun h => m.coeff.property (hf _ h)⟩, m.monic⟩

/-! ### Map functions -/

/-- A general-purpose coefficient map that skips filtering when `f` preserves
    zeros strictly (`f r = 0 ↔ r = 0`). -/
def AzMvPolynomialNew.mapZeroInjective
    (f : R → S) (hf : ∀ r, f r = 0 ↔ r = 0)
    (p : AzMvPolynomialNew n R ord) : AzMvPolynomialNew n S ord :=
  ⟨p.terms.map (mapCoeffNew f (fun r h => (hf r).mp h)),
   by rw [Array.toList_map]; exact p.sorted.map _ (fun _ _ h => h)⟩

/-- Map coefficients via an injective ring homomorphism. -/
def AzMvPolynomialNew.mapInjective
    (f : R →+* S) (hf : Function.Injective f)
    (p : AzMvPolynomialNew n R ord) : AzMvPolynomialNew n S ord :=
  AzMvPolynomialNew.mapZeroInjective f
    (fun r => ⟨fun h => hf (by rw [h, f.map_zero]),
              fun h => by rw [h, f.map_zero]⟩) p

/-- Map coefficients via `algebraMap R S` when it is injective. -/
def AzMvPolynomialNew.mapAlgebraMap {R S : Type _} [CommSemiring R] [Semiring S] [Algebra R S]
    {n : ℕ} {ord : MonomialOrder}
    (hf : Function.Injective (algebraMap R S))
    (p : AzMvPolynomialNew n R ord) : AzMvPolynomialNew n S ord :=
  AzMvPolynomialNew.mapInjective (algebraMap R S) hf p

/-- Map coefficients via a ring homomorphism, filtering out zero results. -/
def AzMvPolynomialNew.map
    (f : R →+* S) (p : AzMvPolynomialNew n R ord) : AzMvPolynomialNew n S ord :=
  ⟨(p.terms.toList.filterMap (mapMonomialCoeffNew f)).toArray,
   by rw [List.toList_toArray]; exact pairwise_gt_filterMap_new f p.sorted⟩

end Azurite
