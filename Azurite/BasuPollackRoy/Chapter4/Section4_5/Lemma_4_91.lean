import Azurite.BasuPollackRoy.Chapter4.Section4_5.Definition_4_89
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# BPR §4.5, Lemma 4.91: powers of a separating element are independent

If `a` is separating and `Zer(𝒫, Cᵏ)` has `n` elements, then `1, a, …, a^{n-1}` are linearly
independent in `A`.

If `∑_{i<n} cᵢ aⁱ = 0` in `A`, then a polynomial representative `∑_{i<n} cᵢ rⁱ` lies in
`Ideal(𝒫, K)`, so it vanishes at every `x ∈ Zer(𝒫, Cᵏ)`; hence the univariate polynomial
`∑_{i<n} cᵢ Tⁱ` (of degree `< n`) vanishes at the `n` distinct values `a(x)` (distinct because `a`
is separating). A nonzero polynomial of degree `< n` cannot have `n` distinct roots, so the
polynomial is identically zero and all `cᵢ = 0`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical

variable {k : ℕ} {K : Type*} [Field K] (C : Type*) [Field C] [Algebra K C]

/-- **BPR Lemma 4.91.** If `a ∈ A` is separating for `𝒫` and `Zer(𝒫, Cᵏ)` has `n` elements, then
`1, a, …, a^{n-1}` are linearly independent over `K` in `A`. -/
theorem lemma_4_91 (Ps : Finset (MvPolynomial (Fin k) K)) (a : quotPolys Ps)
    (hsep : IsSeparating C Ps a) (hfin : (zerOfFinset C Ps).Finite) :
    LinearIndependent K (fun i : Fin hfin.toFinset.card => a ^ (i : ℕ)) := by
  set n := hfin.toFinset.card with hn
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- a representative `r` of `a`
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective a
  -- the representative of the vanishing combination lies in `Ideal(𝒫, K)`
  have hpoly : (∑ i : Fin n, c i • r ^ (i : ℕ)) ∈ idealOfPolys Ps := by
    have key : Ideal.Quotient.mkₐ K (idealOfPolys Ps) (∑ i : Fin n, c i • r ^ (i : ℕ)) = 0 := by
      rw [map_sum, ← hc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_pow, Ideal.Quotient.mkₐ_eq_mk, hr]
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at key
    exact key
  -- the value `a(x) = aeval x r` is injective on `Zer` (because `a` is separating)
  have hinj : Set.InjOn (fun x => MvPolynomial.aeval x r) (zerOfFinset C Ps) := by
    intro x hx y hy hxy
    refine hsep x hx y hy ?_
    rw [← hr, valueAt_mk, valueAt_mk]
    exact hxy
  -- each value `aeval x r` is a root of `∑ cᵢ Tⁱ`
  have hroot : ∀ x ∈ zerOfFinset C Ps,
      (∑ i : Fin n, Polynomial.C (algebraMap K C (c i)) * Polynomial.X ^ (i : ℕ)).eval
        (MvPolynomial.aeval x r) = 0 := by
    intro x hx
    have hz : MvPolynomial.aeval x (∑ i : Fin n, c i • r ^ (i : ℕ)) = 0 :=
      aeval_eq_zero_of_mem_idealOfPolys hpoly x hx
    rw [map_sum] at hz
    rw [Polynomial.eval_finsetSum, ← hz]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      map_smul, map_pow, Algebra.smul_def]
  intro i
  have hn1 : 0 < n := by have := i.isLt; omega
  -- `∑ cᵢ Tⁱ` has `n` distinct roots but degree `< n`, so it vanishes
  have hq0 : (∑ i : Fin n, Polynomial.C (algebraMap K C (c i)) * Polynomial.X ^ (i : ℕ)) = 0 := by
    by_contra hq
    have hsub : hfin.toFinset.image (fun x => MvPolynomial.aeval x r)
        ⊆ (∑ i : Fin n, Polynomial.C (algebraMap K C (c i)) * Polynomial.X ^ (i : ℕ)).roots.toFinset
        := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨x, hxT, rfl⟩ := hz
      exact Multiset.mem_toFinset.mpr
        (Polynomial.mem_roots'.mpr ⟨hq, hroot x (hfin.mem_toFinset.mp hxT)⟩)
    have hcard1 : (hfin.toFinset.image (fun x => MvPolynomial.aeval x r)).card = n :=
      Finset.card_image_of_injOn (by rw [hfin.coe_toFinset]; exact hinj)
    have hcard2 :
        ((∑ i : Fin n, Polynomial.C (algebraMap K C (c i)) * Polynomial.X ^ (i : ℕ)).roots.toFinset).card
          ≤ n - 1 := by
      refine le_trans (Multiset.toFinset_card_le _) (le_trans (Polynomial.card_roots' _) ?_)
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      rw [Polynomial.natDegree_X_pow]
      exact Nat.le_sub_one_of_lt j.isLt
    have hle := Finset.card_le_card hsub
    rw [hcard1] at hle
    omega
  -- read off the coefficient
  have hcoeff : (∑ i' : Fin n, Polynomial.C (algebraMap K C (c i')) * Polynomial.X ^ (i' : ℕ)).coeff
      (i : ℕ) = algebraMap K C (c i) := by
    rw [Polynomial.finsetSum_coeff,
      Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
        (fun j _ hj => by rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          if_neg (fun heq => hj (Fin.val_injective heq).symm), mul_zero])]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  rw [hq0, Polynomial.coeff_zero] at hcoeff
  exact (algebraMap K C).injective (hcoeff.symm.trans (map_zero (algebraMap K C)).symm)

end Azurite.BPR.Chapter4
