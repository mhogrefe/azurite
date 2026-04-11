/-
  Scalar multiplication for `AzMvPolynomialNew`.
-/
import Azurite.AzMvPolynomial.New.Basic

namespace Azurite
open AzMvPolynomialNew

variable {R : Type _} [CommSemiring R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-- Map a monomial's coefficient by multiplication with `r`, returning `none`
    if the result is zero. -/
def smulMonomialNew (r : R) (m : MonomialNew n R ord) :
    Option (MonomialNew n R ord) :=
  if h : r * m.coeff.val = 0 then none
  else some ⟨⟨r * m.coeff.val, h⟩, m.monic⟩

/-- `smulMonomialNew` preserves the monic part. -/
theorem smulMonomialNew_monic {r : R} {m m' : MonomialNew n R ord}
    (h : smulMonomialNew r m = some m') : m'.monic = m.monic := by
  unfold smulMonomialNew at h
  split at h
  · contradiction
  · injection h with h'; subst h'; rfl

theorem pairwise_gt_filterMap_smul_new (r : R)
    {l : List (MonomialNew n R ord)}
    (hp : l.Pairwise (fun a b => a.monic > b.monic)) :
    (l.filterMap (smulMonomialNew r)).Pairwise (fun a b => a.monic > b.monic) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hp; rw [List.filterMap_cons]
    rcases ha : smulMonomialNew r a with _ | a'
    · exact ih hp.2
    · rw [List.pairwise_cons]; refine ⟨fun b hb => ?_, ih hp.2⟩
      obtain ⟨m', hm', hmap⟩ := List.mem_filterMap.mp hb
      rw [smulMonomialNew_monic ha, smulMonomialNew_monic hmap]
      exact hp.1 m' hm'

/-- Scalar multiplication of an `AzMvPolynomialNew` by a ring element `r`. -/
def AzMvPolynomialNew.smul (r : R) (p : AzMvPolynomialNew n R ord) :
    AzMvPolynomialNew n R ord :=
  ⟨(p.terms.toList.filterMap (smulMonomialNew r)).toArray,
   by rw [List.toList_toArray]; exact pairwise_gt_filterMap_smul_new r p.sorted⟩

instance : SMul R (AzMvPolynomialNew n R ord) := ⟨AzMvPolynomialNew.smul⟩

end Azurite
