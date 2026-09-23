/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_7.NonsingularProjectiveZero

/-!
# BPR §4.7, Proposition 4.106: rank of the projective Jacobian and maximal minors

For the `k × (k + 1)` projective Jacobian at a *common* projective zero, the columns satisfy the
Euler relation `∑ⱼ xⱼ · (column j) = 0` (Euler's identity for homogeneous polynomials, in
characteristic zero). Hence each column lies in the span of the others, and full rank `k` is
equivalent to the non-vanishing of the determinant of the `k × k` block obtained by deleting any
single column whose corresponding coordinate is nonzero.

This file proves the matrix-level facts used to express the *singular* locus
(`rank < k` at a common zero) as the vanishing of all maximal minors — an algebraic condition.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-- **Generalized column-drop rank criterion.** For a `k × (k+1)` matrix over a field whose `c`-th
column lies in the span of the remaining columns, full rank `k` is equivalent to non-vanishing of
the determinant of the `k × k` block obtained by deleting column `c`. -/
theorem rank_eq_iff_det_submatrix_succAbove_ne_zero {F : Type*} [Field F]
    (M : Matrix (Fin k) (Fin (k + 1)) F) (c : Fin (k + 1))
    (hcol : M.col c ∈ Submodule.span F (Set.range (M.submatrix id c.succAbove).col)) :
    M.rank = k ↔ (M.submatrix id c.succAbove).det ≠ 0 := by
  set Maff := M.submatrix id c.succAbove with hMaff
  have hcols : Set.range M.col = insert (M.col c) (Set.range Maff.col) := by
    apply Set.eq_of_subset_of_subset
    · rintro _ ⟨j, rfl⟩
      rcases eq_or_ne j c with rfl | hj
      · exact Set.mem_insert _ _
      · obtain ⟨j', rfl⟩ : ∃ j', c.succAbove j' = j :=
          (Fin.exists_succAbove_eq hj)
        exact Set.mem_insert_of_mem _ ⟨j', rfl⟩
    · rw [Set.insert_subset_iff]
      refine ⟨⟨c, rfl⟩, ?_⟩
      rintro _ ⟨j, rfl⟩
      exact ⟨c.succAbove j, rfl⟩
  have hspan : Submodule.span F (Set.range M.col) = Submodule.span F (Set.range Maff.col) := by
    rw [hcols, Submodule.span_insert_eq_span hcol]
  have hrankeq : M.rank = Maff.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols, hspan]
  rw [hrankeq]
  constructor
  · intro hrank hdet
    obtain ⟨v, hv0, hvker⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := Maff)).mpr hdet
    have : Maff.rank < k := by
      rw [Matrix.rank]
      have hle : LinearMap.range Maff.mulVecLin < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro htop
        have hinj : Function.Injective Maff.mulVecLin :=
          LinearMap.injective_iff_surjective.mpr (by rw [← LinearMap.range_eq_top]; exact htop)
        exact hv0 (hinj (by simpa using hvker))
      calc Module.finrank F (LinearMap.range Maff.mulVecLin)
          < Module.finrank F (⊤ : Submodule F (Fin k → F)) :=
            Submodule.finrank_lt_finrank_of_lt hle
        _ = Fintype.card (Fin k) := by
            rw [finrank_top, Module.finrank_fintype_fun_eq_card]
        _ = k := Fintype.card_fin k
    omega
  · intro hdet
    have : IsUnit Maff := (Matrix.isUnit_iff_isUnit_det Maff).mpr (isUnit_iff_ne_zero.mpr hdet)
    rw [Matrix.rank_of_isUnit Maff this, Fintype.card_fin]

set_option linter.unusedSectionVars false in
/-- **Euler relation at a common zero.** If `x` is a common projective zero of the homogeneous
polynomials `P` and `x.rep c ≠ 0`, then column `c` of the projective Jacobian lies in the span of the
remaining columns (the columns of the `c`-dropped block). -/
theorem projJacobian_col_mem_span_of_common_zero
    {P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)} {d : Fin k → ℕ}
    (hP : ∀ i, (P i).IsHomogeneous (d i)) {x : complexProjectiveSpace R k}
    (hx : ∀ i, aeval x.rep (P i) = 0) (c : Fin (k + 1)) (hc : x.rep c ≠ 0) :
    (projJacobian P x).col c ∈
      Submodule.span (Ri R) (Set.range ((projJacobian P x).submatrix id c.succAbove).col) := by
  set M := projJacobian P x with hM
  set S := Set.range ((projJacobian P x).submatrix id c.succAbove).col with hS
  -- Euler's identity gives the vector relation `∑ⱼ (x.rep j) • (column j) = 0`.
  have heuler : ∑ j, (x.rep j) • M.col j = (0 : Fin k → Ri R) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.col_apply, smul_eq_mul, Pi.zero_apply, hM,
      projJacobian, Matrix.of_apply]
    have hkey := congrArg (aeval x.rep) (hP i).sum_X_mul_pderiv
    rw [map_sum, map_nsmul, hx i, nsmul_zero] at hkey
    rw [← hkey]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, aeval_X]
  -- Solve for `(x.rep c) • (column c)` as a combination of the other columns.
  have hsolve : (x.rep c) • M.col c
      = ∑ a, (-(x.rep (c.succAbove a))) • (M.submatrix id c.succAbove).col a := by
    have hsplit := Fin.sum_univ_succAbove (fun j => (x.rep j) • M.col j) c
    rw [heuler] at hsplit
    have : (x.rep c) • M.col c
        = -∑ a, (x.rep (c.succAbove a)) • M.col (c.succAbove a) := by
      rw [eq_neg_iff_add_eq_zero, ← hsplit]
    rw [this, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [neg_smul]; rfl
  -- Hence `(x.rep c) • (column c) ∈ span`, and dividing by the unit `x.rep c` finishes.
  have hmem : (x.rep c) • M.col c ∈ Submodule.span (Ri R) S := by
    rw [hsolve]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have := Submodule.smul_mem _ (x.rep c)⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

set_option linter.unusedSectionVars false in
/-- **The singular condition is "all maximal minors vanish".** For a *common* projective zero `x`,
the projective Jacobian is rank-deficient (`rank < k`) iff every `k × k` maximal minor (obtained by
deleting one column) vanishes. -/
theorem projJacobian_rank_lt_iff_forall_det_eq_zero
    {P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)} {d : Fin k → ℕ}
    (hP : ∀ i, (P i).IsHomogeneous (d i)) {x : complexProjectiveSpace R k}
    (hx : ∀ i, aeval x.rep (P i) = 0) :
    (projJacobian P x).rank < k ↔
      ∀ c : Fin (k + 1), ((projJacobian P x).submatrix id c.succAbove).det = 0 := by
  set M := projJacobian P x with hM
  constructor
  · intro hrank c
    by_contra hdet
    have hsub : (M.submatrix id c.succAbove).rank ≤ M.rank := by
      rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
      apply Submodule.finrank_mono
      apply Submodule.span_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨c.succAbove j, rfl⟩
    have hfull : (M.submatrix id c.succAbove).rank = k := by
      have : IsUnit (M.submatrix id c.succAbove) :=
        (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
      rw [Matrix.rank_of_isUnit _ this, Fintype.card_fin]
    omega
  · intro hall
    -- pick a column `c` with `x.rep c ≠ 0` (exists since the representative is nonzero)
    obtain ⟨c, hc⟩ : ∃ c, x.rep c ≠ 0 := by
      by_contra h
      push Not at h
      exact x.rep_nonzero (funext h)
    have hcol := projJacobian_col_mem_span_of_common_zero hP hx c hc
    rw [← hM] at hcol
    have hiff := rank_eq_iff_det_submatrix_succAbove_ne_zero M c hcol
    have hle : M.rank ≤ k := by
      have := Matrix.rank_le_card_height M
      rwa [Fintype.card_fin] at this
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (hiff.mp h) (by rw [not_not]; exact hall c)
