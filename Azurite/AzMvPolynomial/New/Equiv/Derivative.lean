/-
  Equivalence proof: `AzMvPolynomialNew.pderivGeneral` commutes with `toMvPoly`.
-/
import Azurite.AzMvPolynomial.New.Derivative
import Azurite.AzMvPolynomial.New.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv

namespace Azurite

open MvPolynomial MonicMonomialNew MonomialNew AzMvPolynomialNew

variable {R : Type _} [CommSemiring R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-- Sum over filterMap equals sum over map with a default of 0 for `none`. -/
private theorem sum_map_filterMap_new {α β M : Type _} [AddCommMonoid M]
    (l : List α) (f : α → Option β) (g : β → M) :
    (l.filterMap f |>.map g).sum = (l.map (fun x => (f x).elim 0 g)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
    rcases hfa : f a with _ | b
    · simp [ih]
    · simp [ih]

/-- Monomial-level: `toMvPoly` of `pderivAt` result matches `pderiv` of `toMvPoly`. -/
private theorem toMvPoly_pderivAt_eq_new (m : MonomialNew n R ord) (j : Fin n) :
    ((m.pderivAt j).elim 0 MonomialNew.toMvPoly) =
      (MvPolynomial.pderiv j) m.toMvPoly := by
  simp only [MonomialNew.pderivAt]
  have hv : m.monic.toFinsupp j = m.monic.exponents[j] := by
    simp [MonicMonomialNew.toFinsupp]
  split
  · -- exponent = 0: derivative is 0
    rename_i he
    simp only [Option.elim, MonomialNew.toMvPoly, MvPolynomial.pderiv_monomial, hv, he,
      Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero]
  · -- exponent ≠ 0: need to handle possible coeff cancellation
    rename_i hne
    split
    · -- coeff * exponent = 0 (cancellation)
      rename_i hc
      simp only [Option.elim, MonomialNew.toMvPoly, MvPolynomial.pderiv_monomial, hv]
      rw [MvPolynomial.monomial_eq_zero.mpr]; exact_mod_cast hc
    · -- coeff * exponent ≠ 0: both sides match
      rename_i hnc
      simp only [Option.elim, MonomialNew.toMvPoly, MvPolynomial.pderiv_monomial]
      congr 1
      · -- monic parts: decrExp corresponds to finsupp subtraction
        congr 1; ext w
        simp only [MonicMonomialNew.toFinsupp, MonicMonomialNew.decrExp,
          Finsupp.onFinset_apply, Finsupp.tsub_apply, Finsupp.single_apply,
          Fin.getElem_fin, Vector.getElem_ofFn]
        split <;> simp_all [eq_comm]

/-- Partial derivative commutes with `toMvPoly`. -/
theorem toMvPoly_pderivGeneral_new (j : Fin n) (p : AzMvPolynomialNew n R ord) :
    (AzMvPolynomialNew.pderivGeneral j p).toMvPoly =
      MvPolynomial.pderiv j (p.toMvPoly) := by
  simp only [pderivGeneral]
  rw [toMvPoly_ofMonomials_new, List.toList_toArray, sum_map_filterMap_new]
  conv_lhs => rw [show p.terms.toList.map (fun x =>
    (x.pderivAt j).elim 0 MonomialNew.toMvPoly) =
    p.terms.toList.map (fun m => (MvPolynomial.pderiv j) m.toMvPoly)
    from List.map_congr_left fun m _ => toMvPoly_pderivAt_eq_new m j]
  rw [show (fun m : MonomialNew n R ord => (MvPolynomial.pderiv j) m.toMvPoly) =
    (⇑(MvPolynomial.pderiv j)) ∘ MonomialNew.toMvPoly from rfl,
    ← List.map_map, ← map_list_sum (MvPolynomial.pderiv j)]
  exact congr_arg _ (AzMvPolynomialNew.toMvPoly_eq_list_sum p).symm

end Azurite
