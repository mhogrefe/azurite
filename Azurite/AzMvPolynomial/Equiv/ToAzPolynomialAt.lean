import Azurite.AzMvPolynomial.ToAzPolynomial
import Azurite.AzMvPolynomial.OfAzPolynomial
import Azurite.AzMvPolynomial.Equiv.Basic
import Azurite.AzMvPolynomial.Equiv.Vars
import Azurite.AzMvPolynomial.Equiv.ToAzPolynomial
import Azurite.AzPolynomial.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Equivalence: AzMvPolynomial.toAzPolynomialAt ↔ Mathlib

For arbitrary `σ` with `p.vars ⊆ {v}`, we prove:

  `AzPolynomial.toPoly (p.toAzPolynomialAt hv) =
     MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) (toMvPoly p)`

This generalizes `toPoly_toAzPolynomial` (which requires `[Unique σ]`).
-/

namespace Azurite

open AzMvPolynomial MonomialOrder MvPolynomial Polynomial

variable {R : Type _} [CommSemiring R] [DecidableEq R]
  {σ : Type _} {n : ℕ} [DecidableEq σ] [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-! ### Monomial membership → vars subset -/

omit [DecidableEq R] in
private theorem mem_foldl_of_mem_init
    (l : List (Monomial σ R ord)) (init : Finset σ) (w : σ) (hw : w ∈ init) :
    w ∈ l.foldl (fun acc m => acc ∪ m.vars) init := by
  induction l generalizing init with
  | nil => exact hw
  | cons _ tl ih => exact ih _ (Finset.mem_union_left _ hw)

omit [DecidableEq R] in
private theorem vars_sub_foldl
    (l : List (Monomial σ R ord)) (init : Finset σ) (m : Monomial σ R ord)
    (hm : m ∈ l) : m.vars ⊆ l.foldl (fun acc m => acc ∪ m.vars) init := by
  induction l generalizing init with
  | nil => simp at hm
  | cons a tl ih =>
    rw [List.mem_cons] at hm
    rcases hm with rfl | hm
    · intro w hw
      exact mem_foldl_of_mem_init tl _ w (Finset.mem_union_right _ hw)
    · exact ih _ hm

omit [DecidableEq σ] [DecidableEq R] in
theorem Monomial.vars_sub_of_mem
    (p : AzMvPolynomial σ R ord) (m : Monomial σ R ord)
    (hm : m ∈ p.terms.toList) : m.vars ⊆ p.vars := by
  unfold AzMvPolynomial.vars; rw [← Array.foldl_toList]
  exact vars_sub_foldl _ _ _ hm

/-! ### Finsupp representation -/

/-- When `m.vars ⊆ {v}`, the finsupp is `single v (exponent v)`. -/
theorem MonicMonomial.toFinsupp_eq_single_exponent
    (m : MonicMonomial σ ord) (v : σ) (hv : m.vars ⊆ {v}) :
    m.toFinsupp = Finsupp.single v (m.exponent v) := by
  ext w
  simp only [MonicMonomial.toFinsupp, Finsupp.onFinset_apply, Finsupp.single_apply]
  by_cases hw : w = v
  · subst hw; simp [MonicMonomial.exponent]
  · have hwv : w ∉ m.vars := fun hmem => hw (Finset.mem_singleton.mp (hv hmem))
    rw [MonicMonomial.vars_eq_toFinsupp_support] at hwv
    rw [Finsupp.notMem_support_iff] at hwv
    simp only [MonicMonomial.toFinsupp, Finsupp.onFinset_apply] at hwv
    rw [hwv, if_neg (Ne.symm hw)]

/-! ### eval₂ of a single monomial at a variable -/

omit [DecidableEq R] in
private theorem eval₂_monomial_at_var
    (m : MonicMonomial σ ord) (c : R) (v : σ) (hv : m.vars ⊆ {v}) :
    MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
      (MvPolynomial.monomial m.toFinsupp c) =
    Polynomial.monomial (m.exponent v) c := by
  rw [MonicMonomial.toFinsupp_eq_single_exponent m v hv, MvPolynomial.eval₂_monomial]
  simp [Finsupp.prod_single_index, Polynomial.C_mul_X_pow_eq_monomial]

/-! ### eval₂ distributes over the term sum, using vars hypothesis -/

omit [DecidableEq R] in
private theorem eval₂_sum_map_toMvPoly_at
    (l : List (Monomial σ R ord)) (v : σ)
    (hv : ∀ m ∈ l, (m : Monomial σ R ord).monic.vars ⊆ {v}) :
    MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) (l.map Monomial.toMvPoly).sum =
    (l.map (fun m => Polynomial.monomial (m.monic.exponent v) m.coeff.val)).sum := by
  induction l with
  | nil => simp
  | cons m ms ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [MvPolynomial.eval₂_add, ih (fun m' hm' => hv m' (List.mem_cons_of_mem _ hm'))]
    congr 1
    exact eval₂_monomial_at_var m.monic m.coeff.val v (hv m (List.mem_cons_self ..))

/-! ### Properties of the coefficient fold (generalized) -/

omit [DecidableEq R] [DecidableEq σ] in
private theorem foldl_set_size_list_at
    (l : List (Monomial σ R ord)) (acc : Array R) (v : σ) :
    (l.foldl (fun (acc : Array R) m =>
      let deg := m.monic.exponent v
      if h : deg < acc.size then acc.set deg m.coeff.val else acc) acc).size = acc.size := by
  induction l generalizing acc with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldl_cons]; rw [ih]; split <;> simp [*]

omit [DecidableEq R] [DecidableEq σ] in
private theorem foldl_set_getElem_at (v : σ)
    (l : List (Monomial σ R ord))
    (hpw : l.Pairwise (fun a b => a.monic.exponent v ≠ b.monic.exponent v))
    (acc : Array R) (i : ℕ) (hi : i < acc.size)
    (hdegs : ∀ m ∈ l, m.monic.exponent v < acc.size) :
    let result := l.foldl (fun (acc : Array R) m =>
      let deg := m.monic.exponent v
      if h : deg < acc.size then acc.set deg m.coeff.val else acc) acc
    result[i]'(by rw [foldl_set_size_list_at]; exact hi) =
      match l.find? (fun m => decide (m.monic.exponent v = i)) with
      | some m => m.coeff.val
      | none => acc[i] := by
  induction l generalizing acc with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons, List.find?]
    have hpw' := (List.pairwise_cons.mp hpw).2
    have hdegs' : ∀ m ∈ ts, m.monic.exponent v < acc.size :=
      fun m hm => hdegs m (List.mem_cons_of_mem _ hm)
    have ht_lt : t.monic.exponent v < acc.size := hdegs t (List.mem_cons_self ..)
    simp only [dif_pos ht_lt]
    have hi' : i < (acc.set (t.monic.exponent v) t.coeff.val).size := by simp; exact hi
    have hdegs'' : ∀ m ∈ ts, m.monic.exponent v <
        (acc.set (t.monic.exponent v) t.coeff.val).size :=
      fun m hm => by simp; exact hdegs' m hm
    by_cases ht : t.monic.exponent v = i
    · subst ht; simp only [decide_true]
      have hne : ∀ m ∈ ts, m.monic.exponent v ≠ t.monic.exponent v :=
        fun m hm => Ne.symm ((List.pairwise_cons.mp hpw).1 m hm)
      rw [ih hpw' _ hi' hdegs'']
      have : ts.find? (fun m => decide (m.monic.exponent v = t.monic.exponent v)) = none :=
        List.find?_eq_none.mpr (fun m hm => by simp; exact hne m hm)
      rw [this]; simp
    · simp only [show decide (t.monic.exponent v = i) = false from decide_eq_false ht]
      rw [ih hpw' _ hi' hdegs'']
      cases ts.find? (fun m => decide (m.monic.exponent v = i)) with
      | some m => rfl
      | none => simp [Array.getElem_set, ht]

/-! ### Pairwise distinct exponents from sorted terms -/

omit [DecidableEq R] in
private theorem pairwise_exponent_ne_of_sorted (v : σ)
    (l : List (Monomial σ R ord))
    (hsorted : l.Pairwise (fun a b => a.monic > b.monic))
    (hvars : ∀ m ∈ l, (m : Monomial σ R ord).monic.vars ⊆ {v}) :
    l.Pairwise (fun a b => a.monic.exponent v ≠ b.monic.exponent v) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a as ih =>
    rw [List.pairwise_cons] at hsorted ⊢
    refine ⟨fun b hb heq => ?_, ih hsorted.2 (fun m hm => hvars m (List.mem_cons_of_mem _ hm))⟩
    exact ne_of_gt (hsorted.1 b hb) (MonicMonomial.toFinsupp_injective
      (by rw [MonicMonomial.toFinsupp_eq_single_exponent _ v (hvars a (List.mem_cons_self ..)),
              MonicMonomial.toFinsupp_eq_single_exponent _ v (hvars b (List.mem_cons_of_mem _ hb)),
              heq]))

/-! ### Monomials with vars ⊆ {v} equal ofVarPow -/

omit [CommSemiring R] [DecidableEq R] [DecidableEq σ] in
theorem MonicMonomial.eq_ofVarPow_of_vars_sub
    (m : MonicMonomial σ ord) (v : σ) (hv : m.vars ⊆ {v}) :
    m = MonicMonomial.ofVarPow v (m.exponent v) := by
  ext1; ext i hi
  simp only [MonicMonomial.ofVarPow, Vector.getElem_ofFn]
  by_cases hiv : Var.toFin v = ⟨i, hi⟩
  · simp [hiv, MonicMonomial.exponent]
  · simp only [hiv, ↓reduceIte]
    have hvi : Var.ofFin (⟨i, hi⟩ : Fin n) ≠ v := fun h => hiv (h ▸ Var.toFin_ofFin _)
    have : Var.ofFin (⟨i, hi⟩ : Fin n) ∉ m.vars :=
      fun hmem => hvi (Finset.mem_singleton.mp (hv hmem))
    rw [MonicMonomial.vars_eq_toFinsupp_support] at this
    rw [Finsupp.notMem_support_iff] at this
    simp [MonicMonomial.toFinsupp, Finsupp.onFinset_apply, Var.toFin_ofFin] at this
    exact this

/-! ### Exponent ordering from monomial ordering -/

omit [CommSemiring R] [DecidableEq R] [DecidableEq σ] in
private theorem exponent_le_of_monic_le (v : σ) (a b : MonicMonomial σ ord)
    (hab : a ≤ b) (hav : a.vars ⊆ {v}) (hbv : b.vars ⊆ {v}) :
    a.exponent v ≤ b.exponent v := by
  rw [MonicMonomial.eq_ofVarPow_of_vars_sub a v hav,
      MonicMonomial.eq_ofVarPow_of_vars_sub b v hbv] at hab
  exact (MonicMonomial.ofVarPow_strictMono v).le_iff_le.mp hab

omit [DecidableEq R] [DecidableEq σ] in
private theorem exponents_le_lead_at (v : σ)
    (l : List (Monomial σ R ord))
    (hsorted : l.Pairwise (fun a b => a.monic > b.monic))
    (hvars : ∀ m ∈ l, (m : Monomial σ R ord).monic.vars ⊆ {v})
    (hne : l ≠ []) :
    ∀ m ∈ l, m.monic.exponent v < (l.head hne).monic.exponent v + 1 := by
  intro m hm
  rcases l with _ | ⟨a, as⟩
  · exact absurd rfl hne
  · simp only [List.head_cons]
    rw [List.mem_cons] at hm; rcases hm with rfl | hm
    · omega
    · exact Nat.lt_succ_of_le (exponent_le_of_monic_le v m.monic a.monic
        (le_of_lt ((List.pairwise_cons.mp hsorted).1 m hm))
        (hvars m (List.mem_cons_of_mem _ hm)) (hvars a (List.mem_cons_self ..)))

/-! ### Main equivalence theorem -/

/-- Converting an `AzMvPolynomial` to an `AzPolynomial` via `toAzPolynomialAt` and then to
    Mathlib's `Polynomial` agrees with applying `eval₂ C X` to the `MvPolynomial` form. -/
theorem toPoly_toAzPolynomialAt
    (p : AzMvPolynomial σ R ord) {v : σ} (hv : p.vars ⊆ {v}) :
    AzPolynomial.toPoly (p.toAzPolynomialAt hv) =
    MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) (toMvPoly p) := by
  have hvars : ∀ m ∈ p.terms.toList, (m : Monomial σ R ord).monic.vars ⊆ {v} :=
    fun m hm => (Monomial.vars_sub_of_mem p m hm).trans hv
  have hmvp : p.toMvPoly = (p.terms.toList.map Monomial.toMvPoly).sum := by
    have : (‹DecidableEq σ› : DecidableEq σ) = (LinearOrder.toDecidableEq : DecidableEq σ) :=
      Subsingleton.elim _ _
    subst this
    exact AzMvPolynomial.toMvPoly_eq_list_sum p
  rw [hmvp, eval₂_sum_map_toMvPoly_at _ v hvars]
  by_cases h : p.terms.size = 0
  · have hterms : p.terms = #[] := Array.eq_empty_of_size_eq_zero h
    simp [AzMvPolynomial.toAzPolynomialAt, AzPolynomial.toPoly, AzPolynomial.zero,
      List.toPoly, hterms]
  · unfold AzMvPolynomial.toAzPolynomialAt; rw [dif_neg h]; simp only; rw [toPoly_normalize]
    ext i; rw [coeff_toPoly]
    have hcoeff_sum :
        (p.terms.toList.map (fun m => Polynomial.monomial (m.monic.exponent v) m.coeff.val)).sum.coeff i =
        (p.terms.toList.map (fun m =>
          (Polynomial.monomial (m.monic.exponent v) m.coeff.val).coeff i)).sum := by
      induction p.terms.toList with | nil => simp | cons h t ih => simp [ih]
    rw [hcoeff_sum, show (p.terms.toList.map (fun m =>
          (Polynomial.monomial (m.monic.exponent v) m.coeff.val).coeff i)) =
        (p.terms.toList.map (fun m =>
          if m.monic.exponent v = i then m.coeff.val else 0)) from
      List.map_congr_left (fun m _ => Polynomial.coeff_monomial)]
    have hpw := pairwise_exponent_ne_of_sorted v p.terms.toList p.sorted hvars
    rw [sum_ite_eq_find p.terms.toList
      (fun m => m.monic.exponent v) (fun m => (m.coeff : R)) hpw i]
    simp only [List.getCoeff]
    rw [show (buildCoeffsFromTermsAt v p.terms
        (p.terms[0].monic.exponent v + 1)).toList[i]? =
        (buildCoeffsFromTermsAt v p.terms
        (p.terms[0].monic.exponent v + 1))[i]? from by simp]
    simp only [buildCoeffsFromTermsAt]
    rw [← Array.foldl_toList]
    have hne : p.terms.toList ≠ [] := by
      intro heq; exact h (by simp [Array.toList_eq_nil_iff.mp heq])
    have hdegs := exponents_le_lead_at v p.terms.toList p.sorted hvars hne
    have hhead : (p.terms.toList.head hne) = p.terms[0] := by
      simp [List.head_eq_getElem]
    rw [hhead] at hdegs
    have hsize : (Array.replicate (p.terms[0].monic.exponent v + 1) (0 : R)).size =
        p.terms[0].monic.exponent v + 1 := by simp
    have hfoldl_size : (p.terms.toList.foldl (fun (acc : Array R) (m : Monomial σ R ord) =>
        let deg := m.monic.exponent v;
        if h : deg < acc.size then acc.set deg m.coeff.val else acc)
        (Array.replicate (p.terms[0].monic.exponent v + 1) (0 : R))).size =
      p.terms[0].monic.exponent v + 1 := by
      rw [foldl_set_size_list_at]; simp
    by_cases hi : i < p.terms[0].monic.exponent v + 1
    · have hi_foldl : i < (p.terms.toList.foldl (fun (acc : Array R) (m : Monomial σ R ord) =>
          let deg := m.monic.exponent v;
          if h : deg < acc.size then acc.set deg m.coeff.val else acc)
          (Array.replicate (p.terms[0].monic.exponent v + 1) (0 : R))).size := by
        rw [hfoldl_size]; exact hi
      rw [show (p.terms.toList.foldl _ _)[i]? = some (p.terms.toList.foldl _ _)[i] from
        Array.getElem?_eq_some_iff.mpr ⟨hi_foldl, rfl⟩]; simp only [Option.getD]
      rw [foldl_set_getElem_at v p.terms.toList hpw
        (Array.replicate (p.terms[0].monic.exponent v + 1) (0 : R))
        i (hsize.symm ▸ hi) (fun m hm => hsize.symm ▸ hdegs m hm)]
      simp only [Array.getElem_replicate]
      cases p.terms.toList.find? (fun m => decide (m.monic.exponent v = i)) <;> rfl
    · have hge : (List.foldl (fun (acc : Array R) (m : Monomial σ R ord) =>
          if h : m.monic.exponent v < acc.size then acc.set (m.monic.exponent v) m.coeff.val else acc)
          (Array.replicate (p.terms[0].monic.exponent v + 1) (0 : R))
          p.terms.toList).size ≤ i := by
        rw [hfoldl_size]; omega
      rw [show (p.terms.toList.foldl _ _)[i]? = none from
        Array.getElem?_eq_none_iff.mpr hge]; simp only [Option.getD]
      have hfind : p.terms.toList.find? (fun a => decide (a.monic.exponent v = i)) = none :=
        List.find?_eq_none.mpr (fun m hm => by
          simp only [decide_eq_true_eq]; intro heq
          have := hdegs m hm; omega)
      rw [hfind]

end Azurite
