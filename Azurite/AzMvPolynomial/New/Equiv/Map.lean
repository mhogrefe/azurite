/-
  Equivalence proofs between `AzMvPolynomialNew` map functions and
  `MvPolynomial.map`.
-/
import Azurite.AzMvPolynomial.New.Map
import Azurite.AzMvPolynomial.New.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.Eval

namespace Azurite
open MvPolynomial

variable {R S : Type _} [CommSemiring R] [CommSemiring S] [DecidableEq S]
         {n : ℕ} {ord : MonomialOrder}

/-! ### General map equivalence -/

/-- Zero-coefficient monomials contribute `0` to the `MvPolynomial` sum,
    so `filterMap`-based `map` and the full `MvPolynomial.map` agree. -/
private theorem filterMap_toMvPoly_sum_new (f : R →+* S)
    (l : List (MonomialNew n R ord)) :
    ((l.filterMap (mapMonomialCoeffNew f)).map MonomialNew.toMvPoly).sum =
    MvPolynomial.map f ((l.map MonomialNew.toMvPoly).sum) := by
  induction l with
  | nil => simp
  | cons m t ih =>
    rw [List.map_cons, List.sum_cons, map_add, ← ih, List.filterMap_cons]
    rcases hm : mapMonomialCoeffNew f m with _ | m'
    · simp only [MonomialNew.toMvPoly, MvPolynomial.map_monomial]
      have : f m.coeff.val = 0 := by
        unfold mapMonomialCoeffNew at hm; split at hm <;> [assumption; contradiction]
      rw [this, MvPolynomial.monomial_zero, zero_add]
    · rw [List.map_cons, List.sum_cons]; congr 1
      simp only [MonomialNew.toMvPoly, MvPolynomial.map_monomial]
      unfold mapMonomialCoeffNew at hm; split at hm <;> [contradiction; skip]
      injection hm with hm'; subst hm'; rfl

/-- The general `map` commutes with `toMvPoly`. -/
@[simp] theorem toMvPoly_map_new [DecidableEq R]
    (f : R →+* S) (p : AzMvPolynomialNew n R ord) :
    (p.map f).toMvPoly = MvPolynomial.map f p.toMvPoly := by
  rw [AzMvPolynomialNew.toMvPoly_eq_list_sum, AzMvPolynomialNew.toMvPoly_eq_list_sum]
  simp only [AzMvPolynomialNew.map, List.toList_toArray]
  exact filterMap_toMvPoly_sum_new f p.terms.toList

/-! ### mapInjective equivalence -/

omit [DecidableEq S] in
/-- `mapInjective` commutes with `toMvPoly`. -/
@[simp] theorem toMvPoly_mapInjective_new [DecidableEq R]
    (f : R →+* S) (hf : Function.Injective f)
    (p : AzMvPolynomialNew n R ord) :
    (p.mapInjective f hf).toMvPoly =
      MvPolynomial.map f p.toMvPoly := by
  rw [AzMvPolynomialNew.toMvPoly_eq_list_sum, AzMvPolynomialNew.toMvPoly_eq_list_sum]
  rw [map_list_sum (MvPolynomial.map f)]
  simp only [AzMvPolynomialNew.mapInjective, AzMvPolynomialNew.mapZeroInjective,
             Array.toList_map, List.map_map]
  congr 1; ext m
  simp [mapCoeffNew, Function.comp, MonomialNew.toMvPoly, MvPolynomial.map_monomial]

/-! ### mapAlgebraMap equivalence -/

omit [DecidableEq S] in
/-- `mapAlgebraMap` commutes with `toMvPoly`. -/
@[simp] theorem toMvPoly_mapAlgebraMap_new
    {R S : Type _} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [DecidableEq R]
    (hf : Function.Injective (algebraMap R S))
    (p : AzMvPolynomialNew n R ord) :
    (p.mapAlgebraMap hf).toMvPoly =
      MvPolynomial.map (algebraMap R S) p.toMvPoly :=
  toMvPoly_mapInjective_new (algebraMap R S) hf p

end Azurite
