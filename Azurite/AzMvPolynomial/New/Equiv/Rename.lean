/-
  Equivalence between `AzMvPolynomialNew.rename` and `MvPolynomial.rename`.

  Key theorem:
    (p.rename f ord₂).toMvPoly = MvPolynomial.rename f p.toMvPoly
-/
import Mathlib.Algebra.MvPolynomial.Rename
import Azurite.AzMvPolynomial.New.Equiv.Basic
import Azurite.AzMvPolynomial.New.Rename

namespace Azurite

open MvPolynomial MonomialOrder MonomialNew MonicMonomialNew

variable {R : Type _} [CommSemiring R]
    {n₁ : ℕ} {n₂ : ℕ} {ord : MonomialOrder}

/-! ### Sum-preservation lemmas for the `rename` pipeline -/

section SumPreservation

variable [DecidableEq R] {n : ℕ}

/-- Convert a (MonicMonomialNew, coefficient) pair to MvPolynomial. -/
noncomputable def pairToMvPolyNew (p : MonicMonomialNew n ord × R) :
    MvPolynomial (Fin n) R :=
  MvPolynomial.monomial p.1.toFinsupp p.2

omit [DecidableEq R] in
theorem pairToMvPolyNew_eq_toMvPoly (m : MonomialNew n R ord) :
    pairToMvPolyNew (m.monic, m.coeff.val) = m.toMvPoly := by
  simp [pairToMvPolyNew, MonomialNew.toMvPoly]

omit [DecidableEq R] in
/-- `collapseAuxNew` preserves the MvPolynomial sum. -/
theorem collapseAuxNew_sum
    (curM : MonicMonomialNew n ord) (curC : R)
    (acc : List (MonicMonomialNew n ord × R))
    (rest : List (MonomialNew n R ord)) :
    ((collapseAuxNew (curM, curC) acc rest).map pairToMvPolyNew).sum =
    (acc.reverse.map pairToMvPolyNew).sum + pairToMvPolyNew (curM, curC) +
    (rest.map MonomialNew.toMvPoly).sum := by
  induction rest generalizing curM curC acc with
  | nil =>
    simp [collapseAuxNew, List.reverse_cons, List.map_append, List.sum_append]
  | cons m rest' ih =>
    simp only [collapseAuxNew, List.map_cons, List.sum_cons]
    split
    · next heq =>
      rw [ih]
      simp only [pairToMvPolyNew, MonomialNew.toMvPoly, heq, map_add]
      ring
    · next hne =>
      rw [ih]
      simp only [List.reverse_cons, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        pairToMvPolyNew_eq_toMvPoly]
      ring

omit [DecidableEq R] in
/-- `collapseMonicsNew` preserves the MvPolynomial sum. -/
theorem collapseMonicsNew_sum (l : List (MonomialNew n R ord)) :
    ((collapseMonicsNew l).map pairToMvPolyNew).sum =
    (l.map MonomialNew.toMvPoly).sum := by
  match l with
  | [] => simp [collapseMonicsNew]
  | m :: rest =>
    simp only [collapseMonicsNew, List.map_cons, List.sum_cons]
    rw [collapseAuxNew_sum]
    simp [pairToMvPolyNew_eq_toMvPoly]

/-- Filtering out zero-coefficient pairs preserves the MvPolynomial sum. -/
theorem filterMapNew_sum_eq (l : List (MonicMonomialNew n ord × R)) :
    ((l.filterMap (fun p =>
      if h : p.2 = 0 then none else some ⟨⟨p.2, h⟩, p.1⟩)).map
      MonomialNew.toMvPoly).sum =
    (l.map pairToMvPolyNew).sum := by
  induction l with
  | nil => simp
  | cons p t ih =>
    simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
    by_cases h : p.2 = 0
    · simp [h, pairToMvPolyNew, MvPolynomial.monomial_zero, ih]
    · simp only [dif_neg h, List.map_cons, List.sum_cons, ← ih]
      simp [MonomialNew.toMvPoly, pairToMvPolyNew]

end SumPreservation

/-! ### MonicMonomial-level bridge -/

/-- Renaming variables in a `MonicMonomialNew` and converting to `Finsupp`
    is the same as converting to `Finsupp` first and applying `mapDomain`. -/
theorem MonicMonomialNew.toFinsupp_rename
    (m : MonicMonomialNew n₁ ord) (f : Fin n₁ → Fin n₂) (ord₂ : MonomialOrder) :
    (m.rename f ord₂).toFinsupp = Finsupp.mapDomain f m.toFinsupp := by
  apply Finsupp.ext; intro v
  unfold MonicMonomialNew.toFinsupp MonicMonomialNew.rename
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

/-- Renaming variables in a `MonomialNew` and converting to `MvPolynomial`
    is the same as converting first and applying `MvPolynomial.rename`. -/
theorem MonomialNew.toMvPoly_rename (m : MonomialNew n₁ R ord) (f : Fin n₁ → Fin n₂)
    (ord₂ : MonomialOrder) :
    (m.rename f ord₂).toMvPoly = MvPolynomial.rename f m.toMvPoly := by
  simp only [MonomialNew.toMvPoly, MonomialNew.rename, rename_monomial]
  rw [MonicMonomialNew.toFinsupp_rename]

/-! ### The `rename_toMvPoly_eq_sum` bridge -/

variable [DecidableEq R]

/-- The rename pipeline preserves the MvPolynomial sum. -/
theorem AzMvPolynomialNew.rename_toMvPoly_eq_sum
    (p : AzMvPolynomialNew n₁ R ord) (f : Fin n₁ → Fin n₂) (ord₂ : MonomialOrder) :
    (p.rename f ord₂).toMvPoly =
    (p.terms.toList.map (fun m => (m.rename f ord₂).toMvPoly)).sum := by
  simp only [AzMvPolynomialNew.toMvPoly]
  rw [← Array.foldl_toList, foldl_add_map_eq_sum_new]
  unfold AzMvPolynomialNew.rename
  dsimp only
  rw [filterMapNew_sum_eq]
  rw [collapseMonicsNew_sum]
  rw [((List.mergeSort_perm _ monicGeq).map
    (MonomialNew.toMvPoly (R := R) (ord := ord₂))).sum_eq]
  simp only [List.map_map, Function.comp_def]

/-! ### Polynomial-level equivalence -/

/-- Renaming in `AzMvPolynomialNew` and converting to `MvPolynomial` gives
    the same result as converting first and renaming in `MvPolynomial`. -/
theorem AzMvPolynomialNew.toMvPoly_rename
    (p : AzMvPolynomialNew n₁ R ord) (f : Fin n₁ → Fin n₂) (ord₂ : MonomialOrder) :
    (p.rename f ord₂).toMvPoly = MvPolynomial.rename f p.toMvPoly := by
  rw [AzMvPolynomialNew.rename_toMvPoly_eq_sum]
  rw [AzMvPolynomialNew.toMvPoly, ← Array.foldl_toList, foldl_add_map_eq_sum_new,
    map_list_sum (MvPolynomial.rename f)]
  simp only [List.map_map, Function.comp_def]
  simp_rw [MonomialNew.toMvPoly_rename]

/-- Converting `MvPolynomial.rename f p` to `AzMvPolynomialNew` gives the same
    result as converting `p` first and then renaming. -/
theorem AzMvPolynomialNew.ofMvPoly_rename
    (p : MvPolynomial (Fin n₁) R) (f : Fin n₁ → Fin n₂) (ord₁ ord₂ : MonomialOrder) :
    (AzMvPolynomialNew.ofMvPoly (MvPolynomial.rename f p) : AzMvPolynomialNew n₂ R ord₂) =
    (AzMvPolynomialNew.ofMvPoly p : AzMvPolynomialNew n₁ R ord₁).rename f ord₂ := by
  exact toMvPoly_injective_new
    (by rw [toMvPoly_ofMvPoly_new, toMvPoly_rename, toMvPoly_ofMvPoly_new])

/-! ### renameInjective equivalence -/

omit [DecidableEq R] in
/-- `renameInjective` produces the same `MvPolynomial` as `MvPolynomial.rename`. -/
theorem AzMvPolynomialNew.toMvPoly_renameInjective
    (p : AzMvPolynomialNew n₁ R ord) (f : Fin n₁ → Fin n₂) (hf : Function.Injective f)
    (ord₂ : MonomialOrder) :
    (p.renameInjective f hf ord₂).toMvPoly = MvPolynomial.rename f p.toMvPoly := by
  simp only [AzMvPolynomialNew.renameInjective, AzMvPolynomialNew.toMvPoly]
  rw [← Array.foldl_toList, List.toList_toArray, foldl_add_map_eq_sum_new]
  rw [← Array.foldl_toList, foldl_add_map_eq_sum_new]
  rw [(List.mergeSort_perm _ monicGeq).map MonomialNew.toMvPoly |>.sum_eq]
  rw [List.map_map, map_list_sum (MvPolynomial.rename f)]
  simp only [List.map_map, Function.comp_def]
  simp_rw [MonomialNew.toMvPoly_rename]

omit [DecidableEq R] in
/-- Converting `MvPolynomial.rename f p` to `AzMvPolynomialNew` gives the same
    result as converting `p` first and then applying `renameInjective`. -/
theorem AzMvPolynomialNew.ofMvPoly_renameInjective
    (p : MvPolynomial (Fin n₁) R) (f : Fin n₁ → Fin n₂) (hf : Function.Injective f)
    (ord₁ ord₂ : MonomialOrder) :
    (AzMvPolynomialNew.ofMvPoly (MvPolynomial.rename f p) : AzMvPolynomialNew n₂ R ord₂) =
    (AzMvPolynomialNew.ofMvPoly p : AzMvPolynomialNew n₁ R ord₁).renameInjective f hf ord₂ := by
  exact toMvPoly_injective_new
    (by rw [toMvPoly_ofMvPoly_new, toMvPoly_renameInjective, toMvPoly_ofMvPoly_new])

/-! ### renameMonotone equivalence -/

omit [DecidableEq R] in
/-- `renameMonotone` produces the same `MvPolynomial` as `MvPolynomial.rename`. -/
theorem AzMvPolynomialNew.toMvPoly_renameMonotone
    (p : AzMvPolynomialNew n₁ R ord) (f : Fin n₁ → Fin n₂) (hg : StrictMono f) :
    (p.renameMonotone f hg).toMvPoly = MvPolynomial.rename f p.toMvPoly := by
  simp only [AzMvPolynomialNew.renameMonotone, AzMvPolynomialNew.toMvPoly]
  rw [← Array.foldl_toList, List.toList_toArray, foldl_add_map_eq_sum_new]
  rw [← Array.foldl_toList, foldl_add_map_eq_sum_new]
  rw [List.map_map, map_list_sum (MvPolynomial.rename f)]
  simp only [List.map_map, Function.comp_def]
  simp_rw [MonomialNew.toMvPoly_rename]

omit [DecidableEq R] in
/-- Converting `MvPolynomial.rename f p` to `AzMvPolynomialNew` gives the same
    result as converting `p` first and then applying `renameMonotone`. -/
theorem AzMvPolynomialNew.ofMvPoly_renameMonotone
    (p : MvPolynomial (Fin n₁) R) (f : Fin n₁ → Fin n₂) (hg : StrictMono f) :
    (AzMvPolynomialNew.ofMvPoly (MvPolynomial.rename f p) : AzMvPolynomialNew n₂ R ord) =
    (AzMvPolynomialNew.ofMvPoly p : AzMvPolynomialNew n₁ R ord).renameMonotone f hg := by
  exact toMvPoly_injective_new
    (by rw [toMvPoly_ofMvPoly_new, toMvPoly_renameMonotone, toMvPoly_ofMvPoly_new])

/-! ### embed equivalence -/

omit [DecidableEq R] in
/-- `embed` produces the same `MvPolynomial` as `MvPolynomial.rename (Fin.castLE h)`. -/
theorem AzMvPolynomialNew.toMvPoly_embed
    (h : n₁ ≤ n₂) (p : AzMvPolynomialNew n₁ R ord) :
    (p.embed h).toMvPoly =
      MvPolynomial.rename (Fin.castLE h : Fin n₁ → Fin n₂) p.toMvPoly :=
  toMvPoly_renameMonotone p (Fin.castLE h) (fun _ _ hab => hab)

omit [DecidableEq R] in
/-- Converting `MvPolynomial.rename (Fin.castLE h) p` to `AzMvPolynomialNew` gives
    the same result as converting `p` first and then applying `embed`. -/
theorem AzMvPolynomialNew.ofMvPoly_embed
    (h : n₁ ≤ n₂) (p : MvPolynomial (Fin n₁) R) :
    (AzMvPolynomialNew.ofMvPoly (MvPolynomial.rename (Fin.castLE h : Fin n₁ → Fin n₂) p)
      : AzMvPolynomialNew n₂ R ord) =
    (AzMvPolynomialNew.ofMvPoly p : AzMvPolynomialNew n₁ R ord).embed h := by
  unfold AzMvPolynomialNew.embed
  exact ofMvPoly_renameMonotone p (Fin.castLE h) (fun _ _ hab => hab)

end Azurite
