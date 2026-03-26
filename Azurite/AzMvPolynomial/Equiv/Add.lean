/-
  Equivalence proofs for AzMvPolynomial addition.
-/
import Azurite.AzMvPolynomial.Add
import Azurite.AzMvPolynomial.Equiv.Basic

namespace Azurite
open AzMvPolynomial MvPolynomial

variable {R : Type _} [CommSemiring R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

/-! ### Helper: addSorted preserves the MvPolynomial sum -/

/-- The sum of `toMvPoly` over `addSorted ps qs` equals the sum over `ps`
    plus the sum over `qs`. -/
theorem toMvPoly_addSorted (ps qs : List (Monomial σ R ord)) :
    ((addSorted ps qs).map Monomial.toMvPoly).sum =
    (ps.map Monomial.toMvPoly).sum + (qs.map Monomial.toMvPoly).sum := by
  match ps, qs with
  | [], qs => simp [addSorted]
  | p :: ps', [] => simp [addSorted]
  | p :: ps', q :: qs' =>
    simp only [List.map_cons, List.sum_cons]
    unfold addSorted; split_ifs with hpq hqp hc
    · -- p > q: emit p, then recurse
      simp only [List.map_cons, List.sum_cons]
      rw [toMvPoly_addSorted ps' (q :: qs')]
      simp only [List.map_cons, List.sum_cons]; ring
    · -- q > p: emit q, then recurse
      simp only [List.map_cons, List.sum_cons]
      rw [toMvPoly_addSorted (p :: ps') qs']
      simp only [List.map_cons, List.sum_cons]; ring
    · -- equal monics, coefficient sum is zero: both terms cancel
      rw [toMvPoly_addSorted ps' qs']
      have heq : p.monic = q.monic :=
        le_antisymm (not_lt.mp hpq) (not_lt.mp hqp)
      have hcancel : p.toMvPoly + q.toMvPoly = 0 := by
        simp only [Monomial.toMvPoly, heq]
        rw [← map_add (MvPolynomial.monomial q.monic.toFinsupp), hc, map_zero]
      calc (ps'.map Monomial.toMvPoly).sum + (qs'.map Monomial.toMvPoly).sum
          = 0 + ((ps'.map Monomial.toMvPoly).sum + (qs'.map Monomial.toMvPoly).sum) := by ring
        _ = (p.toMvPoly + q.toMvPoly) +
            ((ps'.map Monomial.toMvPoly).sum + (qs'.map Monomial.toMvPoly).sum) := by
          rw [hcancel]
        _ = _ := by ring
    · -- equal monics, nonzero coefficient sum: emit combined monomial
      simp only [List.map_cons, List.sum_cons]
      rw [toMvPoly_addSorted ps' qs']
      have heq : p.monic = q.monic :=
        le_antisymm (not_lt.mp hpq) (not_lt.mp hqp)
      have hcomb :
          (⟨⟨p.coeff.val + q.coeff.val, hc⟩, p.monic⟩ : Monomial σ R ord).toMvPoly =
          p.toMvPoly + q.toMvPoly := by
        simp only [Monomial.toMvPoly, heq]
        exact map_add (MvPolynomial.monomial q.monic.toFinsupp) (p.coeff : R) (q.coeff : R)
      rw [hcomb]; ring
termination_by ps.length + qs.length

/-! ### toMvPoly_add -/

/-- Addition commutes with `toMvPoly`. -/
@[simp] theorem toMvPoly_add (p q : AzMvPolynomial σ R ord) :
    (p + q).toMvPoly = p.toMvPoly + q.toMvPoly := by
  have h1 : (p + q).toMvPoly =
      ((addSorted p.terms.toList q.terms.toList).map Monomial.toMvPoly).sum := by
    show (AzMvPolynomial.add p q).toMvPoly = _
    simp only [AzMvPolynomial.toMvPoly, AzMvPolynomial.add]
    rw [← Array.foldl_toList, foldl_add_map_eq_sum, List.toList_toArray]
  rw [h1, AzMvPolynomial.toMvPoly_eq_list_sum p, AzMvPolynomial.toMvPoly_eq_list_sum q]
  exact toMvPoly_addSorted p.terms.toList q.terms.toList

/-! ### ofMvPoly_add -/

/-- Addition commutes with `ofMvPoly`. -/
@[simp] theorem ofMvPoly_add (p q : MvPolynomial σ R) :
    (AzMvPolynomial.ofMvPoly (p + q) : AzMvPolynomial σ R ord) =
      AzMvPolynomial.ofMvPoly p + AzMvPolynomial.ofMvPoly q := by
  set a := AzMvPolynomial.ofMvPoly (ord := ord) p
  set b := AzMvPolynomial.ofMvPoly (ord := ord) q
  have hp : a.toMvPoly = p := toMvPoly_ofMvPoly p
  have hq : b.toMvPoly = q := toMvPoly_ofMvPoly q
  rw [← hp, ← hq, ← toMvPoly_add a b]
  exact ofMvPoly_toMvPoly (a + b)

end Azurite
