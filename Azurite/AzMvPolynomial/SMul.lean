/-
  Scalar multiplication for AzMvPolynomial.
  Analogous to AzPolynomial/SMul.lean.
-/
import Azurite.AzMvPolynomial.Basic

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

/-- Map a monomial's coefficient by multiplication with `r`, returning `none`
    if the result is zero. -/
def smulMonomial (r : R) (m : Monomial σ R ord) :
    Option (Monomial σ R ord) :=
  if h : r * m.coeff.val = 0 then none
  else some ⟨⟨r * m.coeff.val, h⟩, m.monic⟩

/-- `smulMonomial` preserves the monic part. -/
theorem smulMonomial_monic {r : R} {m m' : Monomial σ R ord}
    (h : smulMonomial r m = some m') : m'.monic = m.monic := by
  unfold smulMonomial at h
  split at h
  · contradiction
  · injection h with h'; subst h'; rfl

theorem pairwise_gt_filterMap_smul (r : R)
    {l : List (Monomial σ R ord)}
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

/-- Scalar multiplication of an `AzMvPolynomial` by a ring element `r`.
    Each monomial coefficient is multiplied by `r`, and monomials whose
    coefficient becomes zero are dropped. -/
def AzMvPolynomial.smul (r : R) (p : AzMvPolynomial σ R ord) :
    AzMvPolynomial σ R ord :=
  ⟨(p.terms.toList.filterMap (smulMonomial r)).toArray,
   by rw [List.toList_toArray]; exact pairwise_gt_filterMap_smul r p.sorted⟩

instance : SMul R (AzMvPolynomial σ R ord) := ⟨AzMvPolynomial.smul⟩

end Azurite
