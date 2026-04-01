/-
  Equivalence proof: AzMvPolynomial.pderivGeneral commutes with toMvPoly.
-/
import Azurite.AzMvPolynomial.Derivative
import Azurite.AzMvPolynomial.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv

namespace Azurite

open MvPolynomial MonicMonomial Monomial AzMvPolynomial

variable {R : Type _} [CommSemiring R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

/-- Sum over filterMap equals sum over map with a default of 0 for `none`. -/
private theorem sum_map_filterMap {α β M : Type _} [AddCommMonoid M]
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
private theorem toMvPoly_pderivAt_eq (m : Monomial σ R ord) (v : σ) :
    ((m.pderivAt (Var.toFin v)).elim 0 Monomial.toMvPoly) =
      (MvPolynomial.pderiv v) m.toMvPoly := by
  simp only [Monomial.pderivAt]
  have hv : m.monic.toFinsupp v = m.monic.exponents[Var.toFin v] := by
    simp [MonicMonomial.toFinsupp]
  split
  · -- exponent = 0: derivative is 0
    rename_i he
    simp only [Option.elim, Monomial.toMvPoly, MvPolynomial.pderiv_monomial, hv, he,
      Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero]
  · -- exponent ≠ 0: need to handle possible coeff cancellation
    rename_i hne
    split
    · -- coeff * exponent = 0 (cancellation)
      rename_i hc
      simp only [Option.elim, Monomial.toMvPoly, MvPolynomial.pderiv_monomial, hv]
      rw [MvPolynomial.monomial_eq_zero.mpr]; exact_mod_cast hc
    · -- coeff * exponent ≠ 0: both sides match
      rename_i hnc
      simp only [Option.elim, Monomial.toMvPoly, MvPolynomial.pderiv_monomial]
      congr 1
      · -- monic parts: decrExp corresponds to finsupp subtraction
        congr 1; ext w
        simp only [MonicMonomial.toFinsupp, MonicMonomial.decrExp,
          Finsupp.onFinset_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        simp [Vector.getElem_ofFn, Var.toFin_injective.eq_iff]
        split <;> simp_all [eq_comm]

/-- Partial derivative commutes with `toMvPoly`. -/
theorem toMvPoly_pderivGeneral (v : σ) (p : AzMvPolynomial σ R ord) :
    (AzMvPolynomial.pderivGeneral v p).toMvPoly =
      MvPolynomial.pderiv v (p.toMvPoly) := by
  -- LHS: unfold pderivGeneral, apply toMvPoly_ofMonomials
  simp only [pderivGeneral]
  rw [toMvPoly_ofMonomials, List.toList_toArray, sum_map_filterMap]
  -- Goal: (map (pderivAt elim 0 toMvPoly) terms).sum = pderiv v p.toMvPoly
  -- Transform monomial-by-monomial via toMvPoly_pderivAt_eq
  conv_lhs => rw [show p.terms.toList.map (fun x =>
    (x.pderivAt (Var.toFin v)).elim 0 Monomial.toMvPoly) =
    p.terms.toList.map (fun m => (MvPolynomial.pderiv v) m.toMvPoly)
    from List.map_congr_left fun m _ => toMvPoly_pderivAt_eq m v]
  -- Goal: (map (pderiv v ∘ toMvPoly) terms).sum = pderiv v p.toMvPoly
  rw [show (fun m : Monomial σ R ord => (MvPolynomial.pderiv v) m.toMvPoly) =
    (⇑(MvPolynomial.pderiv v)) ∘ Monomial.toMvPoly from rfl,
    ← List.map_map, ← map_list_sum (MvPolynomial.pderiv v)]
  exact congr_arg _ (AzMvPolynomial.toMvPoly_eq_list_sum p).symm

end Azurite
