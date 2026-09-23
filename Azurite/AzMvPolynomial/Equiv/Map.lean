/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs between `AzMvPolynomial` map functions and
  `MvPolynomial.map`.
-/
import Azurite.AzMvPolynomial.Map
import Azurite.AzMvPolynomial.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.Eval

namespace Azurite
open MvPolynomial

variable {R S : Type _} [CommSemiring R] [CommSemiring S] [DecidableEq S]
         {n : ℕ} {ord : MonomialOrder}

/-! ### General map equivalence -/

/-- Zero-coefficient monomials contribute `0` to the `MvPolynomial` sum,
    so `filterMap`-based `map` and the full `MvPolynomial.map` agree. -/
private theorem filterMap_toMvPoly_sum (f : R →+* S)
    (l : List (Monomial n R ord)) :
    ((l.filterMap (mapMonomialCoeff f)).map Monomial.toMvPoly).sum =
    MvPolynomial.map f ((l.map Monomial.toMvPoly).sum) := by
  induction l with
  | nil => simp
  | cons m t ih =>
    rw [List.map_cons, List.sum_cons, map_add, ← ih, List.filterMap_cons]
    rcases hm : mapMonomialCoeff f m with _ | m'
    · simp only [Monomial.toMvPoly, MvPolynomial.map_monomial]
      have : f m.coeff.val = 0 := by
        unfold mapMonomialCoeff at hm; split at hm <;> [assumption; contradiction]
      rw [this, MvPolynomial.monomial_zero, zero_add]
    · rw [List.map_cons, List.sum_cons]; congr 1
      simp only [Monomial.toMvPoly, MvPolynomial.map_monomial]
      unfold mapMonomialCoeff at hm; split at hm <;> [contradiction; skip]
      injection hm with hm'; subst hm'; rfl

/-- The general `map` commutes with `toMvPoly`. -/
@[simp] theorem toMvPoly_map [DecidableEq R]
    (f : R →+* S) (p : AzMvPolynomial n R ord) :
    (p.map f).toMvPoly = MvPolynomial.map f p.toMvPoly := by
  rw [AzMvPolynomial.toMvPoly_eq_list_sum, AzMvPolynomial.toMvPoly_eq_list_sum]
  simp only [AzMvPolynomial.map, List.toList_toArray]
  exact filterMap_toMvPoly_sum f p.terms.toList

/-! ### mapInjective equivalence -/

omit [DecidableEq S] in
/-- `mapInjective` commutes with `toMvPoly`. -/
@[simp] theorem toMvPoly_mapInjective [DecidableEq R]
    (f : R →+* S) (hf : Function.Injective f)
    (p : AzMvPolynomial n R ord) :
    (p.mapInjective f hf).toMvPoly =
      MvPolynomial.map f p.toMvPoly := by
  rw [AzMvPolynomial.toMvPoly_eq_list_sum, AzMvPolynomial.toMvPoly_eq_list_sum]
  rw [map_list_sum (MvPolynomial.map f)]
  simp only [AzMvPolynomial.mapInjective, AzMvPolynomial.mapZeroInjective,
             Array.toList_map, List.map_map]
  congr 1; ext m
  simp [mapCoeff, Function.comp, Monomial.toMvPoly, MvPolynomial.map_monomial]

/-! ### mapAlgebraMap equivalence -/

omit [DecidableEq S] in
/-- `mapAlgebraMap` commutes with `toMvPoly`. -/
@[simp] theorem toMvPoly_mapAlgebraMap
    {R S : Type _} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [DecidableEq R]
    (hf : Function.Injective (algebraMap R S))
    (p : AzMvPolynomial n R ord) :
    (p.mapAlgebraMap hf).toMvPoly =
      MvPolynomial.map (algebraMap R S) p.toMvPoly :=
  toMvPoly_mapInjective (algebraMap R S) hf p

end Azurite
