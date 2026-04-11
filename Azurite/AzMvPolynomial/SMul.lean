/-
  Scalar multiplication for `AzMvPolynomial`.
-/
import Azurite.AzMvPolynomial.Basic

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-- Map a monomial's coefficient by multiplication with `r`, returning `none`
    if the result is zero. -/
def smulMonomial (r : R) (m : Monomial n R ord) :
    Option (Monomial n R ord) :=
  if h : r * m.coeff.val = 0 then none
  else some ⟨⟨r * m.coeff.val, h⟩, m.monic⟩

/-- `smulMonomial` preserves the monic part. -/
theorem smulMonomial_monic {r : R} {m m' : Monomial n R ord}
    (h : smulMonomial r m = some m') : m'.monic = m.monic := by
  unfold smulMonomial at h
  split at h
  · contradiction
  · injection h with h'; subst h'; rfl

theorem pairwise_gt_filterMap_smul (r : R)
    {l : List (Monomial n R ord)}
    (hp : l.Pairwise (fun a b => a.monic > b.monic)) :
    (l.filterMap (smulMonomial r)).Pairwise (fun a b => a.monic > b.monic) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hp; rw [List.filterMap_cons]
    rcases ha : smulMonomial r a with _ | a'
    · exact ih hp.2
    · rw [List.pairwise_cons]; refine ⟨fun b hb => ?_, ih hp.2⟩
      obtain ⟨m', hm', hmap⟩ := List.mem_filterMap.mp hb
      rw [smulMonomial_monic ha, smulMonomial_monic hmap]
      exact hp.1 m' hm'

/-- Scalar multiplication of an `AzMvPolynomial` by a ring element `r`. -/
def AzMvPolynomial.smul (r : R) (p : AzMvPolynomial n R ord) :
    AzMvPolynomial n R ord :=
  ⟨(p.terms.toList.filterMap (smulMonomial r)).toArray,
   by rw [List.toList_toArray]; exact pairwise_gt_filterMap_smul r p.sorted⟩

instance : SMul R (AzMvPolynomial n R ord) := ⟨AzMvPolynomial.smul⟩

end Azurite
