import Azurite.AzMvPolynomial.ToAzPolynomial
import Azurite.AzMvPolynomial.OfAzPolynomial
import Azurite.AzMvPolynomial.Equiv.Basic
import Azurite.AzMvPolynomial.Equiv.Vars
import Azurite.AzMvPolynomial.Equiv.ToAzPolynomial
import Azurite.AzPolynomial.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Equivalence: `AzMvPolynomial.toAzPolynomialAt` ↔ Mathlib

For arbitrary `n` with `p.vars ⊆ {i}`, we prove:

  `AzPolynomial.toPoly (p.toAzPolynomialAt hv) =
     MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) (toMvPoly p)`
-/

namespace Azurite

open AzMvPolynomial MonomialOrder MvPolynomial Polynomial

variable {R : Type _} [CommSemiring R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

/-! ### Monomial membership → vars subset -/

omit [DecidableEq R] in
private theorem mem_foldl_of_mem_init
    (l : List (Monomial n R ord)) (init : Finset (Fin n)) (w : Fin n) (hw : w ∈ init) :
    w ∈ l.foldl (fun acc m => acc ∪ m.vars) init := by
  induction l generalizing init with
  | nil => exact hw
  | cons _ tl ih => exact ih _ (Finset.mem_union_left _ hw)

omit [DecidableEq R] in
private theorem vars_sub_foldl
    (l : List (Monomial n R ord)) (init : Finset (Fin n)) (m : Monomial n R ord)
    (hm : m ∈ l) : m.vars ⊆ l.foldl (fun acc m => acc ∪ m.vars) init := by
  induction l generalizing init with
  | nil => simp at hm
  | cons a tl ih =>
    rw [List.mem_cons] at hm
    rcases hm with rfl | hm
    · intro w hw
      exact mem_foldl_of_mem_init tl _ w (Finset.mem_union_right _ hw)
    · exact ih _ hm

omit [DecidableEq R] in
theorem Monomial.vars_sub_of_mem
    (p : AzMvPolynomial n R ord) (m : Monomial n R ord)
    (hm : m ∈ p.terms.toList) : m.vars ⊆ p.vars := by
  unfold AzMvPolynomial.vars; rw [← Array.foldl_toList]
  exact vars_sub_foldl _ _ _ hm

/-! ### Finsupp representation -/

/-- When `m.vars ⊆ {i}`, the finsupp is `single i (exponent i)`. -/
theorem MonicMonomial.toFinsupp_eq_single_exponent
    (m : MonicMonomial n ord) (i : Fin n) (hv : m.vars ⊆ {i}) :
    m.toFinsupp = Finsupp.single i (m.exponent i) := by
  ext w
  simp only [MonicMonomial.toFinsupp, Finsupp.onFinset_apply, Finsupp.single_apply]
  by_cases hw : w = i
  · subst hw; simp [MonicMonomial.exponent]
  · have hwv : w ∉ m.vars := fun hmem => hw (Finset.mem_singleton.mp (hv hmem))
    rw [MonicMonomial.vars_eq_toFinsupp_support] at hwv
    rw [Finsupp.notMem_support_iff] at hwv
    simp only [MonicMonomial.toFinsupp, Finsupp.onFinset_apply] at hwv
    rw [hwv, ite_eq_right (Ne.symm hw)]

/-! ### eval₂ of a single monomial at a variable -/

omit [DecidableEq R] in
private theorem eval₂_monomial_at_var
    (m : MonicMonomial n ord) (c : R) (i : Fin n) (hv : m.vars ⊆ {i}) :
    MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
      (MvPolynomial.monomial m.toFinsupp c) =
    Polynomial.monomial (m.exponent i) c := by
  rw [MonicMonomial.toFinsupp_eq_single_exponent m i hv, MvPolynomial.eval₂_monomial]
  simp [Finsupp.prod_single_index, Polynomial.C_mul_X_pow_eq_monomial]

/-! ### eval₂ distributes over the term sum, using vars hypothesis -/

omit [DecidableEq R] in
private theorem eval₂_sum_map_toMvPoly_at
    (l : List (Monomial n R ord)) (i : Fin n)
    (hv : ∀ m ∈ l, (m : Monomial n R ord).monic.vars ⊆ {i}) :
    MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
      (l.map Monomial.toMvPoly).sum =
    (l.map (fun m => Polynomial.monomial (m.monic.exponent i) m.coeff.val)).sum := by
  induction l with
  | nil => simp
  | cons m ms ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [MvPolynomial.eval₂_add, ih (fun m' hm' => hv m' (List.mem_cons_of_mem _ hm'))]
    congr 1
    exact eval₂_monomial_at_var m.monic m.coeff.val i (hv m (List.mem_cons_self ..))

/-! ### Properties of the coefficient fold (generalized) -/

omit [DecidableEq R] in
private theorem foldl_set_size_list_at
    (l : List (Monomial n R ord)) (acc : Array R) (i : Fin n) :
    (l.foldl (fun (acc : Array R) m =>
      let deg := m.monic.exponent i
      if h : deg < acc.size then acc.set deg m.coeff.val else acc) acc).size = acc.size := by
  induction l generalizing acc with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldl_cons]; rw [ih]; split <;> simp [*]

omit [DecidableEq R] in
private theorem foldl_set_getElem_at (i : Fin n)
    (l : List (Monomial n R ord))
    (hpw : l.Pairwise (fun a b => a.monic.exponent i ≠ b.monic.exponent i))
    (acc : Array R) (k : ℕ) (hk : k < acc.size)
    (hdegs : ∀ m ∈ l, m.monic.exponent i < acc.size) :
    let result := l.foldl (fun (acc : Array R) m =>
      let deg := m.monic.exponent i
      if h : deg < acc.size then acc.set deg m.coeff.val else acc) acc
    result[k]'(by rw [foldl_set_size_list_at]; exact hk) =
      match l.find? (fun m => decide (m.monic.exponent i = k)) with
      | some m => m.coeff.val
      | none => acc[k] := by
  induction l generalizing acc with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons, List.find?]
    have hpw' := (List.pairwise_cons.mp hpw).2
    have hdegs' : ∀ m ∈ ts, m.monic.exponent i < acc.size :=
      fun m hm => hdegs m (List.mem_cons_of_mem _ hm)
    have ht_lt : t.monic.exponent i < acc.size := hdegs t (List.mem_cons_self ..)
    simp only [dite_eq_left ht_lt]
    have hk' : k < (acc.set (t.monic.exponent i) t.coeff.val).size := by simp; exact hk
    have hdegs'' : ∀ m ∈ ts, m.monic.exponent i <
        (acc.set (t.monic.exponent i) t.coeff.val).size :=
      fun m hm => by simp; exact hdegs' m hm
    by_cases ht : t.monic.exponent i = k
    · subst ht; simp only [decide_true]
      have hne : ∀ m ∈ ts, m.monic.exponent i ≠ t.monic.exponent i :=
        fun m hm => Ne.symm ((List.pairwise_cons.mp hpw).1 m hm)
      rw [ih hpw' _ hk' hdegs'']
      have : ts.find? (fun m => decide (m.monic.exponent i = t.monic.exponent i)) = none :=
        List.find?_eq_none.mpr (fun m hm => by simp; exact hne m hm)
      rw [this]; simp
    · simp only [show decide (t.monic.exponent i = k) = false from decide_eq_false ht]
      rw [ih hpw' _ hk' hdegs'']
      cases ts.find? (fun m => decide (m.monic.exponent i = k)) with
      | some m => rfl
      | none => simp [Array.getElem_set, ht]

/-! ### Pairwise distinct exponents from sorted terms -/

omit [DecidableEq R] in
private theorem pairwise_exponent_ne_of_sorted (i : Fin n)
    (l : List (Monomial n R ord))
    (hsorted : l.Pairwise (fun a b => a.monic > b.monic))
    (hvars : ∀ m ∈ l, (m : Monomial n R ord).monic.vars ⊆ {i}) :
    l.Pairwise (fun a b => a.monic.exponent i ≠ b.monic.exponent i) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a as ih =>
    rw [List.pairwise_cons] at hsorted ⊢
    refine ⟨fun b hb heq => ?_,
      ih hsorted.2 (fun m hm => hvars m (List.mem_cons_of_mem _ hm))⟩
    exact ne_of_gt (hsorted.1 b hb) (MonicMonomial.toFinsupp_injective
      (by rw [MonicMonomial.toFinsupp_eq_single_exponent _ i
                (hvars a (List.mem_cons_self ..)),
              MonicMonomial.toFinsupp_eq_single_exponent _ i
                (hvars b (List.mem_cons_of_mem _ hb)),
              heq]))

/-! ### Monomials with vars ⊆ {i} equal ofVarPow -/

omit [CommSemiring R] [DecidableEq R] in
theorem MonicMonomial.eq_ofVarPow_of_vars_sub
    (m : MonicMonomial n ord) (i : Fin n) (hv : m.vars ⊆ {i}) :
    m = MonicMonomial.ofVarPow i (m.exponent i) := by
  ext1; ext j hj
  simp only [MonicMonomial.ofVarPow, Vector.getElem_ofFn]
  by_cases hij : i = ⟨j, hj⟩
  · simp [hij, MonicMonomial.exponent]
  · simp only [hij, ↓reduceIte]
    have hjne : (⟨j, hj⟩ : Fin n) ≠ i := fun h => hij h.symm
    have : (⟨j, hj⟩ : Fin n) ∉ m.vars :=
      fun hmem => hjne (Finset.mem_singleton.mp (hv hmem))
    rw [MonicMonomial.vars_eq_toFinsupp_support] at this
    rw [Finsupp.notMem_support_iff] at this
    simp [MonicMonomial.toFinsupp, Finsupp.onFinset_apply] at this
    exact this

/-! ### Exponent ordering from monomial ordering -/

omit [CommSemiring R] [DecidableEq R] in
private theorem exponent_le_of_monic_le (i : Fin n) (a b : MonicMonomial n ord)
    (hab : a ≤ b) (hav : a.vars ⊆ {i}) (hbv : b.vars ⊆ {i}) :
    a.exponent i ≤ b.exponent i := by
  rw [MonicMonomial.eq_ofVarPow_of_vars_sub a i hav,
      MonicMonomial.eq_ofVarPow_of_vars_sub b i hbv] at hab
  exact (MonicMonomial.ofVarPow_strictMono i).le_iff_le.mp hab

omit [DecidableEq R] in
private theorem exponents_le_lead_at (i : Fin n)
    (l : List (Monomial n R ord))
    (hsorted : l.Pairwise (fun a b => a.monic > b.monic))
    (hvars : ∀ m ∈ l, (m : Monomial n R ord).monic.vars ⊆ {i})
    (hne : l ≠ []) :
    ∀ m ∈ l, m.monic.exponent i < (l.head hne).monic.exponent i + 1 := by
  intro m hm
  rcases l with _ | ⟨a, as⟩
  · exact absurd rfl hne
  · simp only [List.head_cons]
    rw [List.mem_cons] at hm; rcases hm with rfl | hm
    · omega
    · exact Nat.lt_succ_of_le (exponent_le_of_monic_le i m.monic a.monic
        (le_of_lt ((List.pairwise_cons.mp hsorted).1 m hm))
        (hvars m (List.mem_cons_of_mem _ hm)) (hvars a (List.mem_cons_self ..)))

/-! ### Main equivalence theorem -/

/-- Converting an `AzMvPolynomial` to an `AzPolynomial` via `toAzPolynomialAt`
    and then to Mathlib's `Polynomial` agrees with applying `eval₂ C X`. -/
theorem toPoly_toAzPolynomialAt
    (p : AzMvPolynomial n R ord) {i : Fin n} (hv : p.vars ⊆ {i}) :
    AzPolynomial.toPoly (p.toAzPolynomialAt hv) =
    MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) (toMvPoly p) := by
  have hvars : ∀ m ∈ p.terms.toList, (m : Monomial n R ord).monic.vars ⊆ {i} :=
    fun m hm => (Monomial.vars_sub_of_mem p m hm).trans hv
  rw [AzMvPolynomial.toMvPoly_eq_list_sum, eval₂_sum_map_toMvPoly_at _ i hvars]
  by_cases h : p.terms.size = 0
  · have hterms : p.terms = #[] := Array.eq_empty_of_size_eq_zero h
    simp [AzMvPolynomial.toAzPolynomialAt, AzPolynomial.toPoly, AzPolynomial.zero,
      List.toPoly, hterms]
  · unfold AzMvPolynomial.toAzPolynomialAt
    rw [dite_eq_right h]; simp only; rw [toPoly_normalize]
    ext k; rw [coeff_toPoly]
    have hcoeff_sum :
        (p.terms.toList.map
          (fun m => Polynomial.monomial (m.monic.exponent i) m.coeff.val)).sum.coeff k =
        (p.terms.toList.map (fun m =>
          (Polynomial.monomial (m.monic.exponent i) m.coeff.val).coeff k)).sum := by
      induction p.terms.toList with | nil => simp | cons h t ih => simp [ih]
    rw [hcoeff_sum, show (p.terms.toList.map (fun m =>
          (Polynomial.monomial (m.monic.exponent i) m.coeff.val).coeff k)) =
        (p.terms.toList.map (fun m =>
          if m.monic.exponent i = k then m.coeff.val else 0)) from
      List.map_congr_left (fun m _ => Polynomial.coeff_monomial)]
    have hpw := pairwise_exponent_ne_of_sorted i p.terms.toList p.sorted hvars
    rw [sum_ite_eq_find p.terms.toList
      (fun m => m.monic.exponent i) (fun m => (m.coeff : R)) hpw k]
    simp only [List.getCoeff]
    rw [show (buildCoeffsFromTermsAt i p.terms
        (p.terms[0].monic.exponent i + 1)).toList[k]? =
        (buildCoeffsFromTermsAt i p.terms
        (p.terms[0].monic.exponent i + 1))[k]? from by simp]
    simp only [buildCoeffsFromTermsAt]
    rw [← Array.foldl_toList]
    have hne : p.terms.toList ≠ [] := by
      intro heq; exact h (by simp [Array.toList_eq_nil_iff.mp heq])
    have hdegs := exponents_le_lead_at i p.terms.toList p.sorted hvars hne
    have hhead : (p.terms.toList.head hne) = p.terms[0] := by
      simp [List.head_eq_getElem]
    rw [hhead] at hdegs
    have hsize : (Array.replicate (p.terms[0].monic.exponent i + 1) (0 : R)).size =
        p.terms[0].monic.exponent i + 1 := by simp
    have hfoldl_size : (p.terms.toList.foldl
        (fun (acc : Array R) (m : Monomial n R ord) =>
          let deg := m.monic.exponent i;
          if h : deg < acc.size then acc.set deg m.coeff.val else acc)
        (Array.replicate (p.terms[0].monic.exponent i + 1) (0 : R))).size =
      p.terms[0].monic.exponent i + 1 := by
      rw [foldl_set_size_list_at]; simp
    by_cases hk : k < p.terms[0].monic.exponent i + 1
    · have hk_foldl : k < (p.terms.toList.foldl
          (fun (acc : Array R) (m : Monomial n R ord) =>
            let deg := m.monic.exponent i;
            if h : deg < acc.size then acc.set deg m.coeff.val else acc)
          (Array.replicate (p.terms[0].monic.exponent i + 1) (0 : R))).size := by
        rw [hfoldl_size]; exact hk
      rw [show (p.terms.toList.foldl _ _)[k]? = some (p.terms.toList.foldl _ _)[k] from
        Array.getElem?_eq_some_iff.mpr ⟨hk_foldl, rfl⟩]; simp only [Option.getD]
      rw [foldl_set_getElem_at i p.terms.toList hpw
        (Array.replicate (p.terms[0].monic.exponent i + 1) (0 : R))
        k (hsize.symm ▸ hk) (fun m hm => hsize.symm ▸ hdegs m hm)]
      simp only [Array.getElem_replicate]
      cases p.terms.toList.find? (fun m => decide (m.monic.exponent i = k)) <;> rfl
    · have hge : (List.foldl (fun (acc : Array R) (m : Monomial n R ord) =>
          if h : m.monic.exponent i < acc.size then
            acc.set (m.monic.exponent i) m.coeff.val
          else acc)
          (Array.replicate (p.terms[0].monic.exponent i + 1) (0 : R))
          p.terms.toList).size ≤ k := by
        rw [hfoldl_size]; omega
      rw [show (p.terms.toList.foldl _ _)[k]? = none from
        Array.getElem?_eq_none_iff.mpr hge]; simp only [Option.getD]
      have hfind : p.terms.toList.find? (fun a => decide (a.monic.exponent i = k)) = none :=
        List.find?_eq_none.mpr (fun m hm => by
          simp only [decide_eq_true_eq]; intro heq
          have := hdegs m hm; omega)
      rw [hfind]

end Azurite
