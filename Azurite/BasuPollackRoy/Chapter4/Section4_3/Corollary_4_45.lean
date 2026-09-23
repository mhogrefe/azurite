/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_3.Theorem_4_43
import Mathlib.Algebra.Polynomial.Roots

/-!
# BPR Corollary 4.45: rank and signature from the eigenvalues

Let `r₊`, `r₋`, `r₀` be the number of positive, negative, and zero eigenvalues of the
symmetric matrix `M` associated to a quadratic form `Φ`, counted with multiplicities
(the multiset `M.charpoly.roots`, all of which lie in `R` by the spectral theorem).
Then `Rank(Φ) = r₊ + r₋` and `Sign(Φ) = r₊ − r₋`.

This follows from the spectral theorem (Theorem 4.43): the orthogonal diagonalization
`Aᵀ M A = diagonal D` makes `M` similar to `diagonal D`, so `M.charpoly.roots` is the
multiset of the `Dⱼ`; and it is a congruence, so by Sylvester's law the sign-counts of
`D` equal the inertia indices `sigPos`/`sigNeg`. The conclusions are then the existing
`quadraticFormRank = sigPos + sigNeg` and `Sign = sigPos − sigNeg`.
-/

namespace Azurite.BPR.Chapter4

open scoped Matrix
open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
  {n : ℕ}

omit [IsRealClosed R] in
set_option linter.unusedSectionVars false in
/-- **Congruence ⇒ isometry with a weighted sum of squares.** If `M = Pᵀ · diagonal D · P`
with `P` invertible, then `quadraticForm M` is isometric to `weightedSumSquares R D`. -/
private theorem equiv_weightedSumSquares_of_congr (M : Matrix (Fin n) (Fin n) R)
    (P : Matrix (Fin n) (Fin n) R) (D : Fin n → R) (hP : IsUnit P.det)
    (hM_eq : M = P.transpose * Matrix.diagonal D * P) :
    QuadraticMap.Equivalent (quadraticForm M) (QuadraticMap.weightedSumSquares R D) := by
  classical
  have h2 : Invertible (2 : R) := invertibleOfNonzero (by norm_num)
  have hinv : Invertible P := P.invertibleOfIsUnitDet hP
  -- the linear automorphism with matrix `P`
  set e : (Fin n → R) ≃ₗ[R] (Fin n → R) := Matrix.toLinearEquiv' P hinv with he
  have hemat : LinearMap.toMatrix' (e : (Fin n → R) →ₗ[R] (Fin n → R)) = P := by
    rw [he, Matrix.toLinearEquiv'_apply, LinearMap.toMatrix'_toLin']
  -- `e f = P *ᵥ f`
  have hef : ∀ f : Fin n → R, (e f) = P *ᵥ f := by
    intro f
    rw [he]
    exact Matrix.toLin'_apply P f
  -- bridge: `Matrix.toQuadraticForm' N v = v ⬝ᵥ N *ᵥ v`
  have hbridge : ∀ (N : Matrix (Fin n) (Fin n) R) (v : Fin n → R),
      Matrix.toQuadraticForm' N v = v ⬝ᵥ N *ᵥ v := by
    intro N v
    rw [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply']
  -- `weightedSumSquares R D = Matrix.toQuadraticForm' (diagonal D)`
  have hwss : (QuadraticMap.weightedSumSquares R D)
      = Matrix.toQuadraticForm' (Matrix.diagonal D) := by
    ext v
    rw [QuadraticMap.weightedSumSquares_apply, hbridge, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mulVec_diagonal]
    ring
  refine ⟨{ toLinearEquiv := e, map_app' := ?_ }⟩
  intro f
  show QuadraticMap.weightedSumSquares R D (e f) = quadraticForm M f
  rw [hwss, hbridge, hef, quadraticForm, hbridge, hM_eq]
  -- `(P*ᵥf) ⬝ᵥ diagonal D *ᵥ P*ᵥf = f ⬝ᵥ (Pᵀ * diagonal D * P) *ᵥ f`
  conv_rhs => rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  rw [Matrix.mulVec_mulVec]

omit [IsRealClosed R] in
/-- **Congruence ⇒ inertia, positive part.** If `M = Pᵀ · diagonal D · P` with `P`
invertible, then the number of positive `Dᵢ` equals the positive inertia index of
`quadraticForm M`. Mirror of `corollary_4_40` with the congruence supplied. -/
private theorem sigPos_eq_card_pos_of_congr (M : Matrix (Fin n) (Fin n) R)
    (P : Matrix (Fin n) (Fin n) R) (D : Fin n → R) (hP : IsUnit P.det)
    (hM_eq : M = P.transpose * Matrix.diagonal D * P) :
    (Finset.univ.filter (fun i => 0 < D i)).card = sigPos (quadraticForm M) := by
  classical
  have h2 : Invertible (2 : R) := invertibleOfNonzero (by norm_num)
  have := QuadraticForm.sigPos_of_equiv_weightedSumSquares
    (Q := quadraticForm M) (w := D) (equiv_weightedSumSquares_of_congr M P D hP hM_eq)
  rw [this, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

omit [IsRealClosed R] in
/-- **Congruence ⇒ inertia, negative part.** -/
private theorem sigNeg_eq_card_neg_of_congr (M : Matrix (Fin n) (Fin n) R)
    (P : Matrix (Fin n) (Fin n) R) (D : Fin n → R) (hP : IsUnit P.det)
    (hM_eq : M = P.transpose * Matrix.diagonal D * P) :
    (Finset.univ.filter (fun i => D i < 0)).card = sigNeg (quadraticForm M) := by
  classical
  have h2 : Invertible (2 : R) := invertibleOfNonzero (by norm_num)
  have := QuadraticForm.sigNeg_of_equiv_weightedSumSquares
    (Q := quadraticForm M) (w := D) (equiv_weightedSumSquares_of_congr M P D hP hM_eq)
  rw [this, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

/-- The roots of the characteristic polynomial of a symmetric matrix over a real closed
field is the multiset of diagonal entries of its spectral diagonalization. We package the
existence statement so the three filter-cardinality facts can be read off uniformly. -/
private theorem exists_diag_roots (M : Matrix (Fin n) (Fin n) R) (hM : M.IsSymm) :
    ∃ D : Fin n → R,
      M.charpoly.roots = Finset.univ.val.map D ∧
      (Finset.univ.filter (fun i => 0 < D i)).card = sigPos (quadraticForm M) ∧
      (Finset.univ.filter (fun i => D i < 0)).card = sigNeg (quadraticForm M) := by
  classical
  obtain ⟨A, hAo, D, hAD⟩ := theorem_4_43 M hM
  have hAAt : A * Aᵀ = 1 := mul_eq_one_comm.mpr hAo
  -- det of `Aᵀ` is a unit
  have hAunit : IsUnit A.det := Matrix.isUnit_det_of_left_inverse hAo
  have hAtunit : IsUnit (Aᵀ).det := by rw [Matrix.det_transpose]; exact hAunit
  -- congruence `M = (Aᵀ)ᵀ * diagonal D * Aᵀ`
  have hMeq : M = (Aᵀ).transpose * Matrix.diagonal D * Aᵀ := by
    rw [Matrix.transpose_transpose, ← hAD]
    -- `M = A * (Aᵀ * M * A) * Aᵀ`
    calc M = (A * Aᵀ) * M * (A * Aᵀ) := by rw [hAAt, Matrix.one_mul, Matrix.mul_one]
      _ = A * (Aᵀ * M * A) * Aᵀ := by simp only [Matrix.mul_assoc]
  refine ⟨D, ?_, ?_, ?_⟩
  · -- roots = univ.val.map D
    -- charpoly M = charpoly (diagonal D)
    set U : (Matrix (Fin n) (Fin n) R)ˣ := ⟨Aᵀ, A, hAo, hAAt⟩ with hU
    have hUval : (↑U : Matrix (Fin n) (Fin n) R) = Aᵀ := rfl
    have hUinv : ((↑U : Matrix (Fin n) (Fin n) R))⁻¹ = A := by
      rw [hUval]; exact Matrix.inv_eq_left_inv hAAt
    have hcp : M.charpoly = (Matrix.diagonal D).charpoly := by
      have hconj := Matrix.charpoly_units_conj U M
      rw [hUval, hUinv] at hconj
      rw [← hconj, hAD]
    rw [hcp, Matrix.charpoly_diagonal]
    -- ∏ i, (X - C (D i)) = (map (X - C ·) (univ.val.map D)).prod
    have hprod : (∏ i, (X - C (D i)))
        = (Multiset.map (fun a => X - C a) (Finset.univ.val.map D)).prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
      rfl
    rw [hprod, Polynomial.roots_multiset_prod_X_sub_C]
  · exact sigPos_eq_card_pos_of_congr M Aᵀ D hAtunit hMeq
  · exact sigNeg_eq_card_neg_of_congr M Aᵀ D hAtunit hMeq

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- For a predicate `p`, the cardinality of the filtered multiset `(univ.val.map D).filter p`
equals the cardinality of `univ.filter (p ∘ D)`. -/
private theorem card_filter_map_val {p : R → Prop} [DecidablePred p] (D : Fin n → R) :
    ((Finset.univ.val.map D).filter p).card
      = (Finset.univ.filter (fun i => p (D i))).card := by
  classical
  rw [← Multiset.countP_eq_card_filter, Multiset.countP_map]
  rw [Finset.filter, Finset.card_def, ← Multiset.countP_eq_card_filter]

/-- **Corollary 4.45.** With `r₊`, `r₋`, `r₀` the numbers of positive, negative, and
zero eigenvalues of the symmetric matrix `M` (counted with multiplicities, i.e. the
roots of its characteristic polynomial), the rank of `Φ` is `r₊ + r₋` and the signature
is `r₊ − r₋`. -/
theorem corollary_4_45 (M : Matrix (Fin n) (Fin n) R) (hM : M.IsSymm) :
    quadraticFormRank M
        = (M.charpoly.roots.filter (0 < ·)).card + (M.charpoly.roots.filter (· < 0)).card ∧
    Sign (quadraticForm M)
        = ((M.charpoly.roots.filter (0 < ·)).card : ℤ)
          - (M.charpoly.roots.filter (· < 0)).card ∧
    (M.charpoly.roots.filter (0 < ·)).card + (M.charpoly.roots.filter (· < 0)).card
        + (M.charpoly.roots.filter (· = 0)).card = n := by
  classical
  obtain ⟨D, hroots, hpos, hneg⟩ := exists_diag_roots M hM
  -- rewrite root-filter cards as univ-filter cards
  have hcardpos : (M.charpoly.roots.filter (0 < ·)).card
      = (Finset.univ.filter (fun i => 0 < D i)).card := by
    rw [hroots, card_filter_map_val]
  have hcardneg : (M.charpoly.roots.filter (· < 0)).card
      = (Finset.univ.filter (fun i => D i < 0)).card := by
    rw [hroots, card_filter_map_val]
  have hcardzero : (M.charpoly.roots.filter (· = 0)).card
      = (Finset.univ.filter (fun i => D i = 0)).card := by
    rw [hroots, card_filter_map_val]
  refine ⟨?_, ?_, ?_⟩
  · -- rank = r₊ + r₋
    rw [quadraticFormRank_eq_sigPos_add_sigNeg M hM, hcardpos, hcardneg, hpos, hneg]
  · -- signature = r₊ - r₋
    rw [Sign, hcardpos, hcardneg, hpos, hneg]
  · -- r₊ + r₋ + r₀ = n
    rw [hcardpos, hcardneg, hcardzero]
    -- partition Fin n by sign of D
    have hsplit : (Finset.univ.filter (fun i => 0 < D i)).card
        + (Finset.univ.filter (fun i => D i < 0)).card
        + (Finset.univ.filter (fun i => D i = 0)).card = n := by
      have key1 := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (p := fun i => D i = 0)
      rw [Finset.card_univ, Fintype.card_fin] at key1
      have hsub : (Finset.univ.filter (fun i => ¬ D i = 0))
          = Finset.univ.filter (fun i => 0 < D i) ∪ Finset.univ.filter (fun i => D i < 0) := by
        rw [← Finset.filter_or]
        refine Finset.filter_congr fun i _ => ?_
        constructor
        · intro h; rcases lt_or_gt_of_ne h with h' | h'
          · exact Or.inr h'
          · exact Or.inl h'
        · rintro (h | h)
          · exact ne_of_gt h
          · exact ne_of_lt h
      have hdisj : Disjoint (Finset.univ.filter (fun i => 0 < D i))
          (Finset.univ.filter (fun i => D i < 0)) := by
        rw [Finset.disjoint_filter]
        exact fun i _ h => lt_asymm h
      rw [hsub, Finset.card_union_of_disjoint hdisj] at key1
      omega
    exact hsplit

end Azurite.BPR.Chapter4
