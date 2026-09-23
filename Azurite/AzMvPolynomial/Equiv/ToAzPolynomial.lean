/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvPolynomial.ToAzPolynomial
import Azurite.AzMvPolynomial.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Equivalence: `AzMvPolynomial.toAzPolynomial` ↔ Mathlib

For `n = 1` (single-variable multivariate polynomials), we prove:

  `AzPolynomial.toPoly (p.toAzPolynomial) =
   MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) (toMvPoly p)`
-/

namespace Azurite
open AzMvPolynomial MvPolynomial Polynomial MonomialOrder

variable {R : Type _} [CommSemiring R] [DecidableEq R] {ord : MonomialOrder}

/-! ### Finsupp representation for n = 1 -/

omit [CommSemiring R] [DecidableEq R] in
/-- For `n = 1`, a monic monomial's finsupp is `single 0 degree`. -/
theorem MonicMonomial.toFinsupp_eq_single_degree
    (m : MonicMonomial 1 ord) :
    m.toFinsupp = Finsupp.single (⟨0, by omega⟩ : Fin 1) m.degree := by
  apply Finsupp.ext
  intro i
  have hi : i = (⟨0, by omega⟩ : Fin 1) := by
    ext; have := i.isLt; omega
  subst hi
  simp [MonicMonomial.toFinsupp,
    MonicMonomial.degree, MonicMonomial.exponent]

/-! ### eval₂ of a single monomial -/

omit [DecidableEq R] in
/-- `eval₂ C (fun _ => X) (monomial s c) = Polynomial.monomial (degree) c` for n = 1. -/
theorem eval₂_monomial_unique
    (m : MonicMonomial 1 ord) (c : R) :
    MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
      (MvPolynomial.monomial m.toFinsupp c) =
    Polynomial.monomial m.degree c := by
  rw [MonicMonomial.toFinsupp_eq_single_degree, MvPolynomial.eval₂_monomial]
  simp [Finsupp.prod_single_index, Polynomial.C_mul_X_pow_eq_monomial]

/-! ### eval₂ distributes over the term sum -/

omit [DecidableEq R] in
private theorem eval₂_sum_map_toMvPoly
    (l : List (Monomial 1 R ord)) :
    MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
      (l.map Monomial.toMvPoly).sum =
    (l.map (fun m => Polynomial.monomial m.monic.degree m.coeff.val)).sum := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [MvPolynomial.eval₂_add, ih]
    congr 1
    exact eval₂_monomial_unique t.monic t.coeff.val

/-! ### Properties of the coefficient fold -/

omit [DecidableEq R] in
private theorem foldl_set_size_list
    (l : List (Monomial 1 R ord)) (acc : Array R) :
    (l.foldl (fun (acc : Array R) m =>
      let deg := m.monic.degree
      if h : deg < acc.size then acc.set deg m.coeff.val else acc) acc).size = acc.size := by
  induction l generalizing acc with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons]; rw [ih]; split <;> simp [*]

omit [DecidableEq R] in
private theorem foldl_set_getElem
    (l : List (Monomial 1 R ord))
    (hpw : l.Pairwise (fun a b => a.monic.degree ≠ b.monic.degree))
    (acc : Array R) (i : ℕ) (hi : i < acc.size)
    (hdegs : ∀ m ∈ l, m.monic.degree < acc.size) :
    let result := l.foldl (fun (acc : Array R) m =>
      let deg := m.monic.degree
      if h : deg < acc.size then acc.set deg m.coeff.val else acc) acc
    result[i]'(by rw [foldl_set_size_list]; exact hi) =
      match l.find? (fun m => decide (m.monic.degree = i)) with
      | some m => m.coeff.val
      | none => acc[i] := by
  induction l generalizing acc with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons]
    rw [List.pairwise_cons] at hpw
    have hdegs_ts : ∀ m ∈ ts, m.monic.degree < acc.size :=
      fun m hm => hdegs m (List.mem_cons.mpr (Or.inr hm))
    have ht_size : t.monic.degree < acc.size := hdegs t (List.mem_cons.mpr (Or.inl rfl))
    simp only [ht_size, ↓reduceDIte]
    set acc' := acc.set t.monic.degree t.coeff.val
    have hacc'_size : acc'.size = acc.size := by simp [acc']
    have hi' : i < acc'.size := hacc'_size ▸ hi
    have hdegs' : ∀ m ∈ ts, m.monic.degree < acc'.size :=
      fun m hm => hacc'_size ▸ hdegs_ts m hm
    have ih' := ih hpw.2 acc' hi' hdegs'
    rw [ih']
    simp only [List.find?]
    by_cases hti : t.monic.degree = i
    · simp only [hti, decide_true]
      have hno_dup : ∀ m ∈ ts, ¬ (m.monic.degree = i) :=
        fun m hm heq => hpw.1 m hm (heq ▸ hti ▸ rfl)
      rw [List.find?_eq_none.mpr (by intro m hm; simp [hno_dup m hm])]
      show acc'[i]'hi' = ↑t.coeff
      simp only [acc', Array.getElem_set, hti, ↓reduceIte]
    · simp only [hti, decide_false]
      suffices acc'[i]'hi' = acc[i] by
        cases ts.find? (fun m => decide (m.monic.degree = i)) with
        | none => exact this
        | some m => rfl
      simp only [acc', Array.getElem_set, hti, ↓reduceIte]

/-! ### Sum over list with at-most-one match equals find? -/

theorem sum_ite_eq_find {α R : Type _} [AddCommMonoid R]
    (l : List α) (f : α → ℕ) (g : α → R)
    (hpw : l.Pairwise (fun a b => f a ≠ f b)) (i : ℕ) :
    (l.map (fun a => if f a = i then g a else 0)).sum =
    match l.find? (fun a => decide (f a = i)) with
    | some a => g a
    | none => 0 := by
  induction l with
  | nil => simp
  | cons h t ih =>
    rw [List.pairwise_cons] at hpw
    simp only [List.map_cons, List.sum_cons, List.find?]
    by_cases hfi : f h = i
    · simp [hfi]
      have : ∀ a ∈ t, f a ≠ i := fun a ha heq => hpw.1 a ha (heq ▸ hfi ▸ rfl)
      suffices (t.map (fun a => if f a = i then g a else 0)).sum = 0 by
        rw [this, add_zero]
      exact List.sum_eq_zero (fun x hx => by
        simp only [List.mem_map] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        simp [this a ha])
    · simp [hfi]
      exact ih hpw.2

/-! ### Ordering equivalence for n = 1 -/

omit [CommSemiring R] [DecidableEq R] in
/-- For `n = 1`, the linear order on `MonicMonomial` agrees with the ℕ order
    on `degree`. -/
theorem MonicMonomial.lt_iff_degree_lt
    (m₁ m₂ : MonicMonomial 1 ord) : m₁ < m₂ ↔ m₁.degree < m₂.degree := by
  show compareExponents ord m₁.exponents m₂.exponents = .lt ↔ m₁.degree < m₂.degree
  have lex_one : ∀ (a b : Vector ℕ 1), lexCompareAux a b 0 = compare a[0] b[0] := by
    intro a b; unfold lexCompareAux
    simp only [show (0 : ℕ) < 1 from Nat.zero_lt_one, ↓reduceDIte]
    split <;> try rfl
    rename_i heq; show lexCompareAux a b 1 = _
    unfold lexCompareAux; simp only [show ¬ (1 < 1) from lt_irrefl _, ↓reduceDIte]; exact heq.symm
  have revlex_one : ∀ (a b : Vector ℕ 1),
      revlexCompareAux a b 0 = (compare a[0] b[0]).swap := by
    intro a b; unfold revlexCompareAux
    simp only [show (0 : ℕ) < 1 from Nat.zero_lt_one, ↓reduceDIte, show 1 - 1 - 0 = 0 from rfl]
    split
    · rename_i heq; show revlexCompareAux a b 1 = _
      unfold revlexCompareAux
      simp only [show ¬ (1 < 1) from lt_irrefl _, ↓reduceDIte]; rw [heq]; rfl
    · rename_i heq; rw [heq]; rfl
    · rename_i heq; rw [heq]; rfl
  have td_one : ∀ (v : Vector ℕ 1), totalDeg v = v[0] := by
    intro v; unfold totalDeg
    have hvtl : v.toArray = #[v[0]] := by
      apply Array.ext
      · simp
      · intro i hi₁ hi₂
        simp at hi₁
        have hi0 : i = 0 := by omega
        subst hi0
        simp
    rw [hvtl]; simp [Array.foldl]
  have cmp_one : compareExponents ord m₁.exponents m₂.exponents =
      compare m₁.exponents[0] m₂.exponents[0] := by
    unfold compareExponents; cases ord with
    | Lex => exact lex_one _ _
    | Deglex =>
      simp only [td_one]
      split
      · exact lex_one _ _
      · rename_i hne; rfl
    | Degrevlex =>
      simp only [td_one]; split
      · show revlexCompareAux _ _ 0 = _; rw [revlex_one]; rename_i heq; rw [heq]; rfl
      · rfl
  rw [cmp_one]
  simp only [MonicMonomial.degree, MonicMonomial.exponent]
  exact Nat.compare_eq_lt

/-! ### Distinct degrees from sorted invariant -/

omit [DecidableEq R] in
private theorem pairwise_degree_ne_of_sorted
    (terms : Array (Monomial 1 R ord))
    (hsorted : terms.toList.Pairwise (fun a b => a.monic > b.monic)) :
    terms.toList.Pairwise (fun a b => a.monic.degree ≠ b.monic.degree) :=
  hsorted.imp fun {a b} hab => by
    have := (MonicMonomial.lt_iff_degree_lt b.monic a.monic).mp hab; omega

private theorem degrees_le_lead
    (terms : Array (Monomial 1 R ord))
    (hsorted : terms.toList.Pairwise (fun a b => a.monic > b.monic))
    (hne : terms.size ≠ 0) :
    ∀ m ∈ terms.toList, m.monic.degree < (terms[0]'(by omega)).monic.degree + 1 := by
  intro m hm
  have hlen : 0 < terms.toList.length := by
    exact List.length_pos_of_mem hm
  have h0 : terms.toList[0]'hlen = (terms[0]'(by omega)) := by simp
  have hsorted' := hsorted
  rw [List.pairwise_iff_getElem] at hsorted'
  by_cases hi : m = terms.toList[0]'hlen
  · rw [hi, h0]; omega
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
    by_cases hj0 : j = 0
    · subst hj0; exact absurd (h0 ▸ rfl) hi
    · have hlt : 0 < j := Nat.pos_of_ne_zero hj0
      have := hsorted' 0 j hlen hj hlt
      rw [h0] at this
      have := (MonicMonomial.lt_iff_degree_lt _ _).mp this; omega

/-! ### Main equivalence theorem -/

/-- Converting an `AzMvPolynomial 1 R ord` to an `AzPolynomial` and then to
    Mathlib's `Polynomial` agrees with applying `eval₂ C X` to the `MvPolynomial` form. -/
theorem toPoly_toAzPolynomial
    (p : AzMvPolynomial 1 R ord) :
    AzPolynomial.toPoly (p.toAzPolynomial) =
    MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) (toMvPoly p) := by
  rw [AzMvPolynomial.toMvPoly_eq_list_sum, eval₂_sum_map_toMvPoly]
  by_cases h : p.terms.size = 0
  · have hterms : p.terms = #[] := Array.eq_empty_of_size_eq_zero h
    simp [AzMvPolynomial.toAzPolynomial, AzPolynomial.toPoly, AzPolynomial.zero,
      List.toPoly, hterms]
  · unfold AzMvPolynomial.toAzPolynomial; rw [dite_eq_right h]; simp only; rw [toPoly_normalize]
    ext i; rw [coeff_toPoly]
    have hcoeff_sum :
        (p.terms.toList.map
          (fun m => Polynomial.monomial m.monic.degree m.coeff.val)).sum.coeff i =
        (p.terms.toList.map (fun m =>
          (Polynomial.monomial m.monic.degree m.coeff.val).coeff i)).sum := by
      induction p.terms.toList with | nil => simp | cons h t ih => simp [ih]
    rw [hcoeff_sum, show (p.terms.toList.map (fun m =>
          (Polynomial.monomial m.monic.degree m.coeff.val).coeff i)) =
        (p.terms.toList.map (fun m =>
          if m.monic.degree = i then m.coeff.val else 0)) from
      List.map_congr_left (fun m _ => Polynomial.coeff_monomial)]
    rw [sum_ite_eq_find p.terms.toList
      (fun m => m.monic.degree) (fun m => (m.coeff : R))
      (pairwise_degree_ne_of_sorted p.terms p.sorted) i]
    simp only [List.getCoeff]
    rw [show (buildCoeffsFromTerms p.terms
        ((p.terms[0]'(by omega)).monic.degree + 1)).toList[i]? =
        (buildCoeffsFromTerms p.terms
        ((p.terms[0]'(by omega)).monic.degree + 1))[i]? from by simp]
    simp only [buildCoeffsFromTerms]
    rw [← Array.foldl_toList]
    have hpw := pairwise_degree_ne_of_sorted p.terms p.sorted
    have hdegs := degrees_le_lead p.terms p.sorted h
    have hsize :
        (Array.replicate ((p.terms[0]'(by omega)).monic.degree + 1) (0 : R)).size =
        (p.terms[0]'(by omega)).monic.degree + 1 := by simp
    have hfoldl_size : (p.terms.toList.foldl
        (fun (acc : Array R) (m : Monomial 1 R ord) =>
          let deg := m.monic.degree;
          if h : deg < acc.size then acc.set deg m.coeff.val else acc)
        (Array.replicate ((p.terms[0]'(by omega)).monic.degree + 1) (0 : R))).size =
      (p.terms[0]'(by omega)).monic.degree + 1 := by
      rw [foldl_set_size_list]; simp
    by_cases hi : i < (p.terms[0]'(by omega)).monic.degree + 1
    · have hi_foldl : i < (p.terms.toList.foldl
          (fun (acc : Array R) (m : Monomial 1 R ord) =>
            let deg := m.monic.degree;
            if h : deg < acc.size then acc.set deg m.coeff.val else acc)
          (Array.replicate ((p.terms[0]'(by omega)).monic.degree + 1) (0 : R))).size := by
        rw [hfoldl_size]; exact hi
      rw [show (p.terms.toList.foldl _ _)[i]? = some (p.terms.toList.foldl _ _)[i] from
        Array.getElem?_eq_some_iff.mpr ⟨hi_foldl, rfl⟩]; simp only [Option.getD]
      have hi_acc :
          i < (Array.replicate ((p.terms[0]'(by omega)).monic.degree + 1) (0 : R)).size :=
        hsize.symm ▸ hi
      have hdegs_acc : ∀ m ∈ p.terms.toList,
          m.monic.degree <
            (Array.replicate ((p.terms[0]'(by omega)).monic.degree + 1) (0 : R)).size :=
        fun m hm => hsize.symm ▸ hdegs m hm
      rw [foldl_set_getElem p.terms.toList hpw
        (Array.replicate ((p.terms[0]'(by omega)).monic.degree + 1) (0 : R))
        i hi_acc hdegs_acc]
      simp only [Array.getElem_replicate]
      cases p.terms.toList.find? (fun m => decide (m.monic.degree = i)) <;> rfl
    · have hge : (List.foldl (fun (acc : Array R) (m : Monomial 1 R ord) =>
          if h : m.monic.degree < acc.size then acc.set m.monic.degree m.coeff.val else acc)
          (Array.replicate ((p.terms[0]'(by omega)).monic.degree + 1) (0 : R))
          p.terms.toList).size ≤ i := by
        rw [hfoldl_size]; omega
      rw [show (p.terms.toList.foldl _ _)[i]? = none from
        Array.getElem?_eq_none_iff.mpr hge]; simp only [Option.getD]
      have : p.terms.toList.find? (fun a => decide (a.monic.degree = i)) = none :=
        List.find?_eq_none.mpr (fun m hm => by simp; have := hdegs m hm; omega)
      rw [this]

end Azurite
