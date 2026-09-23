/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence between `AzMvPolynomial.rename` and `MvPolynomial.rename`.

  Key theorem:
    (p.rename f ord₂).toMvPoly = MvPolynomial.rename f p.toMvPoly
-/
import Mathlib.Algebra.MvPolynomial.Rename
import Azurite.AzMvPolynomial.Equiv.Basic
import Azurite.AzMvPolynomial.Rename

namespace Azurite

open MvPolynomial MonomialOrder Monomial MonicMonomial

variable {R : Type _} [CommSemiring R]
    {n₁ : ℕ} {n₂ : ℕ} {ord : MonomialOrder}

/-! ### Sum-preservation lemmas for the `rename` pipeline -/

section SumPreservation

variable [DecidableEq R] {n : ℕ}

/-- Convert a (MonicMonomial, coefficient) pair to MvPolynomial. -/
noncomputable def pairToMvPoly (p : MonicMonomial n ord × R) :
    MvPolynomial (Fin n) R :=
  MvPolynomial.monomial p.1.toFinsupp p.2

omit [DecidableEq R] in
theorem pairToMvPoly_eq_toMvPoly (m : Monomial n R ord) :
    pairToMvPoly (m.monic, m.coeff.val) = m.toMvPoly := by
  simp [pairToMvPoly, Monomial.toMvPoly]

omit [DecidableEq R] in
/-- `collapseAux` preserves the MvPolynomial sum. -/
theorem collapseAux_sum
    (curM : MonicMonomial n ord) (curC : R)
    (acc : List (MonicMonomial n ord × R))
    (rest : List (Monomial n R ord)) :
    ((collapseAux (curM, curC) acc rest).map pairToMvPoly).sum =
    (acc.reverse.map pairToMvPoly).sum + pairToMvPoly (curM, curC) +
    (rest.map Monomial.toMvPoly).sum := by
  induction rest generalizing curM curC acc with
  | nil =>
    simp [collapseAux, List.reverse_cons, List.map_append, List.sum_append]
  | cons m rest' ih =>
    simp only [collapseAux, List.map_cons, List.sum_cons]
    split
    · next heq =>
      rw [ih]
      simp only [pairToMvPoly, Monomial.toMvPoly, heq, map_add]
      ring
    · next hne =>
      rw [ih]
      simp only [List.reverse_cons, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        pairToMvPoly_eq_toMvPoly]
      ring

omit [DecidableEq R] in
/-- `collapseMonics` preserves the MvPolynomial sum. -/
theorem collapseMonics_sum (l : List (Monomial n R ord)) :
    ((collapseMonics l).map pairToMvPoly).sum =
    (l.map Monomial.toMvPoly).sum := by
  match l with
  | [] => simp [collapseMonics]
  | m :: rest =>
    simp only [collapseMonics, List.map_cons, List.sum_cons]
    rw [collapseAux_sum]
    simp [pairToMvPoly_eq_toMvPoly]

/-- Filtering out zero-coefficient pairs preserves the MvPolynomial sum. -/
theorem filterMap_sum_eq (l : List (MonicMonomial n ord × R)) :
    ((l.filterMap (fun p =>
      if h : p.2 = 0 then none else some ⟨⟨p.2, h⟩, p.1⟩)).map
      Monomial.toMvPoly).sum =
    (l.map pairToMvPoly).sum := by
  induction l with
  | nil => simp
  | cons p t ih =>
    simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
    by_cases h : p.2 = 0
    · simp [h, pairToMvPoly, MvPolynomial.monomial_zero, ih]
    · simp only [dite_eq_right h, List.map_cons, List.sum_cons, ← ih]
      simp [Monomial.toMvPoly, pairToMvPoly]

end SumPreservation

/-! ### MonicMonomial-level bridge -/

/-- Renaming variables in a `MonicMonomial` and converting to `Finsupp`
    is the same as converting to `Finsupp` first and applying `mapDomain`. -/
theorem MonicMonomial.toFinsupp_rename
    (m : MonicMonomial n₁ ord) (f : Fin n₁ → Fin n₂) (ord₂ : MonomialOrder) :
    (m.rename f ord₂).toFinsupp = Finsupp.mapDomain f m.toFinsupp := by
  apply Finsupp.ext; intro v
  unfold MonicMonomial.toFinsupp MonicMonomial.rename
  simp only [Finsupp.onFinset_apply, Finsupp.mapDomain, Finsupp.sum]
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  symm
  rw [Finset.sum_subset Finsupp.support_onFinset_subset (by
    intro x _ hx
    simp only [Finsupp.mem_support_iff, Finsupp.onFinset_apply, not_not] at hx
    split <;> [exact hx; rfl])]

/-! ### Monomial-level bridge -/

/-- Renaming variables in a `Monomial` and converting to `MvPolynomial`
    is the same as converting first and applying `MvPolynomial.rename`. -/
theorem Monomial.toMvPoly_rename (m : Monomial n₁ R ord) (f : Fin n₁ → Fin n₂)
    (ord₂ : MonomialOrder) :
    (m.rename f ord₂).toMvPoly = MvPolynomial.rename f m.toMvPoly := by
  simp only [Monomial.toMvPoly, Monomial.rename, rename_monomial]
  rw [MonicMonomial.toFinsupp_rename]

/-! ### The `rename_toMvPoly_eq_sum` bridge -/

variable [DecidableEq R]

/-- The rename pipeline preserves the MvPolynomial sum. -/
theorem AzMvPolynomial.rename_toMvPoly_eq_sum
    (p : AzMvPolynomial n₁ R ord) (f : Fin n₁ → Fin n₂) (ord₂ : MonomialOrder) :
    (p.rename f ord₂).toMvPoly =
    (p.terms.toList.map (fun m => (m.rename f ord₂).toMvPoly)).sum := by
  simp only [AzMvPolynomial.toMvPoly]
  rw [← Array.foldl_toList, foldl_add_map_eq_sum]
  unfold AzMvPolynomial.rename
  dsimp only
  rw [filterMap_sum_eq]
  rw [collapseMonics_sum]
  rw [((List.mergeSort_perm _ monicGeq).map
    (Monomial.toMvPoly (R := R) (ord := ord₂))).sum_eq]
  simp only [List.map_map, Function.comp_def]

/-! ### Polynomial-level equivalence -/

/-- Renaming in `AzMvPolynomial` and converting to `MvPolynomial` gives
    the same result as converting first and renaming in `MvPolynomial`. -/
theorem AzMvPolynomial.toMvPoly_rename
    (p : AzMvPolynomial n₁ R ord) (f : Fin n₁ → Fin n₂) (ord₂ : MonomialOrder) :
    (p.rename f ord₂).toMvPoly = MvPolynomial.rename f p.toMvPoly := by
  rw [AzMvPolynomial.rename_toMvPoly_eq_sum]
  rw [AzMvPolynomial.toMvPoly, ← Array.foldl_toList, foldl_add_map_eq_sum,
    map_list_sum (MvPolynomial.rename f)]
  simp only [List.map_map, Function.comp_def]
  simp_rw [Monomial.toMvPoly_rename]

/-- Converting `MvPolynomial.rename f p` to `AzMvPolynomial` gives the same
    result as converting `p` first and then renaming. -/
theorem AzMvPolynomial.ofMvPoly_rename
    (p : MvPolynomial (Fin n₁) R) (f : Fin n₁ → Fin n₂) (ord₁ ord₂ : MonomialOrder) :
    (AzMvPolynomial.ofMvPoly (MvPolynomial.rename f p) : AzMvPolynomial n₂ R ord₂) =
    (AzMvPolynomial.ofMvPoly p : AzMvPolynomial n₁ R ord₁).rename f ord₂ := by
  exact toMvPoly_injective
    (by rw [toMvPoly_ofMvPoly, toMvPoly_rename, toMvPoly_ofMvPoly])

/-! ### renameInjective equivalence -/

omit [DecidableEq R] in
/-- `renameInjective` produces the same `MvPolynomial` as `MvPolynomial.rename`. -/
theorem AzMvPolynomial.toMvPoly_renameInjective
    (p : AzMvPolynomial n₁ R ord) (f : Fin n₁ → Fin n₂) (hf : Function.Injective f)
    (ord₂ : MonomialOrder) :
    (p.renameInjective f hf ord₂).toMvPoly = MvPolynomial.rename f p.toMvPoly := by
  simp only [AzMvPolynomial.renameInjective, AzMvPolynomial.toMvPoly]
  rw [← Array.foldl_toList, List.toList_toArray, foldl_add_map_eq_sum]
  rw [← Array.foldl_toList, foldl_add_map_eq_sum]
  rw [(List.mergeSort_perm _ monicGeq).map Monomial.toMvPoly |>.sum_eq]
  rw [List.map_map, map_list_sum (MvPolynomial.rename f)]
  simp only [List.map_map, Function.comp_def]
  simp_rw [Monomial.toMvPoly_rename]

omit [DecidableEq R] in
/-- Converting `MvPolynomial.rename f p` to `AzMvPolynomial` gives the same
    result as converting `p` first and then applying `renameInjective`. -/
theorem AzMvPolynomial.ofMvPoly_renameInjective
    (p : MvPolynomial (Fin n₁) R) (f : Fin n₁ → Fin n₂) (hf : Function.Injective f)
    (ord₁ ord₂ : MonomialOrder) :
    (AzMvPolynomial.ofMvPoly (MvPolynomial.rename f p) : AzMvPolynomial n₂ R ord₂) =
    (AzMvPolynomial.ofMvPoly p : AzMvPolynomial n₁ R ord₁).renameInjective f hf ord₂ := by
  exact toMvPoly_injective
    (by rw [toMvPoly_ofMvPoly, toMvPoly_renameInjective, toMvPoly_ofMvPoly])

/-! ### renameMonotone equivalence -/

omit [DecidableEq R] in
/-- `renameMonotone` produces the same `MvPolynomial` as `MvPolynomial.rename`. -/
theorem AzMvPolynomial.toMvPoly_renameMonotone
    (p : AzMvPolynomial n₁ R ord) (f : Fin n₁ → Fin n₂) (hg : StrictMono f) :
    (p.renameMonotone f hg).toMvPoly = MvPolynomial.rename f p.toMvPoly := by
  simp only [AzMvPolynomial.renameMonotone, AzMvPolynomial.toMvPoly]
  rw [← Array.foldl_toList, List.toList_toArray, foldl_add_map_eq_sum]
  rw [← Array.foldl_toList, foldl_add_map_eq_sum]
  rw [List.map_map, map_list_sum (MvPolynomial.rename f)]
  simp only [List.map_map, Function.comp_def]
  simp_rw [Monomial.toMvPoly_rename]

omit [DecidableEq R] in
/-- Converting `MvPolynomial.rename f p` to `AzMvPolynomial` gives the same
    result as converting `p` first and then applying `renameMonotone`. -/
theorem AzMvPolynomial.ofMvPoly_renameMonotone
    (p : MvPolynomial (Fin n₁) R) (f : Fin n₁ → Fin n₂) (hg : StrictMono f) :
    (AzMvPolynomial.ofMvPoly (MvPolynomial.rename f p) : AzMvPolynomial n₂ R ord) =
    (AzMvPolynomial.ofMvPoly p : AzMvPolynomial n₁ R ord).renameMonotone f hg := by
  exact toMvPoly_injective
    (by rw [toMvPoly_ofMvPoly, toMvPoly_renameMonotone, toMvPoly_ofMvPoly])

/-! ### embed equivalence -/

omit [DecidableEq R] in
/-- `embed` produces the same `MvPolynomial` as `MvPolynomial.rename (Fin.castLE h)`. -/
theorem AzMvPolynomial.toMvPoly_embed
    (h : n₁ ≤ n₂) (p : AzMvPolynomial n₁ R ord) :
    (p.embed h).toMvPoly =
      MvPolynomial.rename (Fin.castLE h : Fin n₁ → Fin n₂) p.toMvPoly :=
  toMvPoly_renameMonotone p (Fin.castLE h) (fun _ _ hab => hab)

omit [DecidableEq R] in
/-- Converting `MvPolynomial.rename (Fin.castLE h) p` to `AzMvPolynomial` gives
    the same result as converting `p` first and then applying `embed`. -/
theorem AzMvPolynomial.ofMvPoly_embed
    (h : n₁ ≤ n₂) (p : MvPolynomial (Fin n₁) R) :
    (AzMvPolynomial.ofMvPoly (MvPolynomial.rename (Fin.castLE h : Fin n₁ → Fin n₂) p)
      : AzMvPolynomial n₂ R ord) =
    (AzMvPolynomial.ofMvPoly p : AzMvPolynomial n₁ R ord).embed h := by
  unfold AzMvPolynomial.embed
  exact ofMvPoly_renameMonotone p (Fin.castLE h) (fun _ _ hab => hab)

end Azurite
