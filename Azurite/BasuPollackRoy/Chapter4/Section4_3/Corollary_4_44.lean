/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_3.Theorem_4_43

/-!
# BPR Corollary 4.44: signed sum of squares over a real closed field

A quadratic form `Φ` with coefficients in a real closed field `R` can be written as
`Φ = ∑_{i=1}^{rp} Lᵢ² − ∑_{i=rp+1}^{rp+rm} Lᵢ²`, where the `Lᵢ` are linearly
independent, pairwise orthogonal linear forms with coefficients in `R`, and
`r = rp + rm` is the rank of `Φ`.

This follows from the spectral theorem (Theorem 4.43): diagonalize `Φ` orthogonally,
obtaining `Φ(f) = ∑ⱼ Dⱼ (aⱼ · f)²` with the `aⱼ` orthonormal (eigenvectors) and `Dⱼ`
the eigenvalues. Rescaling the nonzero eigen-coordinates by `√|Dⱼ|` (a square root
that exists because `R` is real closed) turns the coefficients into `±1` and drops the
zero eigenvalues, leaving exactly `rank Φ` orthogonal independent forms.
-/

namespace Azurite.BPR.Chapter4

open scoped Matrix

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
  {n : ℕ}

/-- The linear form `f ↦ v ⬝ᵥ f` with coefficient vector `v`, as a *linear* map in `v`. -/
private def dotLM : (Fin n → R) →ₗ[R] ((Fin n → R) →ₗ[R] R) where
  toFun := fun v =>
    { toFun := fun f => v ⬝ᵥ f
      map_add' := dotProduct_add v
      map_smul' := fun c f => by simp [dotProduct_smul] }
  map_add' := fun v w => by ext f; simp [add_dotProduct]
  map_smul' := fun c v => by ext f; simp [smul_dotProduct]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
private theorem dotLM_apply (v f : Fin n → R) : dotLM v f = v ⬝ᵥ f := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
private theorem linearFormCoeffs_dotLM (v : Fin n → R) : linearFormCoeffs (dotLM v) = v := by
  funext i
  rw [linearFormCoeffs, dotLM_apply, dotProduct_single, mul_one]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
private theorem dotLM_injective : Function.Injective ⇑(dotLM (R := R) (n := n)) := by
  intro v w h
  have := congrArg linearFormCoeffs h
  rwa [linearFormCoeffs_dotLM, linearFormCoeffs_dotLM] at this

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- A pairwise-orthogonal family of nonzero vectors is linearly independent. -/
private theorem linearIndependent_of_pairwise_orthogonal {m : ℕ}
    (c : Fin m → (Fin n → R))
    (hne : ∀ i, c i ⬝ᵥ c i ≠ 0)
    (horth : ∀ i j, i ≠ j → c i ⬝ᵥ c j = 0) :
    LinearIndependent R c := by
  rw [Fintype.linearIndependent_iff]
  intro t ht i
  have hdot : (∑ j, t j • c j) ⬝ᵥ c i = 0 := by rw [ht]; simp
  rw [sum_dotProduct] at hdot
  have hstep : (∑ j, (t j • c j) ⬝ᵥ c i) = ∑ j, (if j = i then t j * (c i ⬝ᵥ c i) else 0) :=
    Finset.sum_congr rfl fun j _ => by
      rw [smul_dotProduct, smul_eq_mul]
      by_cases hji : j = i
      · subst hji; rw [ite_eq_left rfl]
      · rw [ite_eq_right hji, horth j i hji, mul_zero]
  rw [hstep, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ i)] at hdot
  exact (mul_eq_zero.mp hdot).resolve_right (hne i)

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- A family of linear forms that are dot-products of a pairwise-orthogonal family of
nonzero vectors is linearly independent. -/
private theorem linearIndependent_dotLM_of_pairwise_orthogonal {m : ℕ}
    (L : Fin m → ((Fin n → R) →ₗ[R] R)) (v : Fin m → (Fin n → R))
    (hLv : ∀ i, L i = dotLM (v i))
    (hne : ∀ i, v i ⬝ᵥ v i ≠ 0)
    (horth : ∀ i j, i ≠ j → v i ⬝ᵥ v j = 0) :
    LinearIndependent R L := by
  have hLI : LinearIndependent R v := linearIndependent_of_pairwise_orthogonal v hne horth
  have hcomp : L = ⇑dotLM ∘ v := funext hLv
  rw [hcomp]
  exact hLI.map' dotLM (LinearMap.ker_eq_bot.mpr dotLM_injective)

/-- **Corollary 4.44.** A quadratic form over a real closed field is a signed sum of
squares of `rank`-many independent, pairwise orthogonal linear forms: with `rp`
positive and `rm` negative squares,
`Φ(f) = ∑_{i<rp} Lᵢ(f)² − ∑_{i<rm} L_{rp+i}(f)²` and `rp + rm = rank Φ`. -/
theorem corollary_4_44 (M : Matrix (Fin n) (Fin n) R) (hM : M.IsSymm) :
    ∃ (rp rm : ℕ) (L : Fin (rp + rm) → ((Fin n → R) →ₗ[R] R)),
      rp + rm = quadraticFormRank M ∧
      LinearIndependent R L ∧
      (∀ i j, i ≠ j → IsOrthogonalForms (L i) (L j)) ∧
      ∀ f, quadraticForm M f =
        (∑ i : Fin rp, (L (Fin.castAdd rm i) f) ^ 2) -
        (∑ i : Fin rm, (L (Fin.natAdd rp i) f) ^ 2) := by
  classical
  -- (0) bridge
  have hqf : ∀ x : Fin n → R, quadraticForm M x = x ⬝ᵥ M *ᵥ x := fun x => by
    rw [quadraticForm, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply']
  -- (1) orthogonal diagonalization
  obtain ⟨A, hAo, D, hAD⟩ := theorem_4_43 M hM
  set a : Fin n → (Fin n → R) := fun j i => A i j with ha
  have hAAt : A * Aᵀ = 1 := mul_eq_one_comm.mpr hAo
  -- orthonormal columns
  have hortho : ∀ i j, a i ⬝ᵥ a j = if i = j then 1 else 0 := by
    intro i j
    have h1 : a i ⬝ᵥ a j = (Aᵀ * A) i j := by
      rw [Matrix.mul_apply]; simp only [ha, dotProduct, Matrix.transpose_apply]
    rw [h1, hAo, Matrix.one_apply]
  -- M = A * diagonal D * Aᵀ
  have hM_eq : M = A * Matrix.diagonal D * Aᵀ := by
    have h := hAD
    calc M = (A * Aᵀ) * M * (A * Aᵀ) := by rw [hAAt, Matrix.one_mul, Matrix.mul_one]
      _ = A * (Aᵀ * M * A) * Aᵀ := by simp only [mul_assoc]
      _ = A * Matrix.diagonal D * Aᵀ := by rw [mul_assoc, h, mul_assoc]
  -- (2) eigen-expansion
  have heigen : ∀ f, quadraticForm M f = ∑ j, D j * (a j ⬝ᵥ f) ^ 2 := by
    intro f
    rw [hqf, hM_eq]
    -- (A * diagonal D * Aᵀ) *ᵥ f
    rw [show (A * Matrix.diagonal D * Aᵀ) *ᵥ f
        = A *ᵥ (Matrix.diagonal D *ᵥ (Aᵀ *ᵥ f)) by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]]
    -- f ⬝ᵥ A *ᵥ y = (Aᵀ *ᵥ f) ⬝ᵥ y
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    set g : Fin n → R := Aᵀ *ᵥ f with hg
    -- g ⬝ᵥ (diagonal D *ᵥ g) = ∑ j, g j * (D j * g j)
    rw [dotProduct]
    have hgj : ∀ j, g j = a j ⬝ᵥ f := by
      intro j
      rw [hg, Matrix.mulVec, dotProduct, dotProduct]
      apply Finset.sum_congr rfl; intro i _
      rw [Matrix.transpose_apply]
    apply Finset.sum_congr rfl; intro j _
    rw [Matrix.mulVec_diagonal, hgj]; ring
  -- (3) partition by sign
  set P : Finset (Fin n) := Finset.univ.filter (fun j => 0 < D j) with hP
  set N : Finset (Fin n) := Finset.univ.filter (fun j => D j < 0) with hN
  set rp := P.card with hrp
  set rm := N.card with hrm
  set s : Fin n → R := fun j => Azurite.BPR.sqrt |D j| with hs
  have hs_sq : ∀ j, (s j) ^ 2 = |D j| := fun j => Azurite.BPR.sq_sqrt (abs_nonneg _)
  set c : Fin n → (Fin n → R) := fun j => s j • a j with hc
  set Lf : Fin n → ((Fin n → R) →ₗ[R] R) := fun j => dotLM (c j) with hLf
  have hLf_apply : ∀ j f, Lf j f = s j * (a j ⬝ᵥ f) := by
    intro j f
    rw [hLf, dotLM_apply, hc, smul_dotProduct, smul_eq_mul]
  -- term equalities
  have hterm_P : ∀ f, ∀ j ∈ P, D j * (a j ⬝ᵥ f) ^ 2 = (Lf j f) ^ 2 := by
    intro f j hj
    have hjpos : 0 < D j := (Finset.mem_filter.mp hj).2
    rw [hLf_apply, mul_pow, hs_sq, abs_of_pos hjpos]
  have hterm_N : ∀ f, ∀ j ∈ N, D j * (a j ⬝ᵥ f) ^ 2 = -(Lf j f) ^ 2 := by
    intro f j hj
    have hjneg : D j < 0 := (Finset.mem_filter.mp hj).2
    rw [hLf_apply, mul_pow, hs_sq, abs_of_neg hjneg]; ring
  have hterm_zero : ∀ f, ∀ j, j ∉ P → j ∉ N → D j * (a j ⬝ᵥ f) ^ 2 = 0 := by
    intro f j hjP hjN
    have hDj : D j = 0 := by
      by_contra h
      rcases lt_or_gt_of_ne h with hlt | hgt
      · exact hjN (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
      · exact hjP (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩)
    rw [hDj, zero_mul]
  -- P and N disjoint
  have hPN_disj : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro j hjP hjN
    exact absurd ((Finset.mem_filter.mp hjP).2.trans (Finset.mem_filter.mp hjN).2) (lt_irrefl _)
  -- (4) reindex
  have hPe : P.card = rp := rfl
  have hNe : N.card = rm := rfl
  set pe : Fin rp ↪o Fin n := P.orderEmbOfFin hPe with hpe
  set ne' : Fin rm ↪o Fin n := N.orderEmbOfFin hNe with hne'
  set L : Fin (rp + rm) → ((Fin n → R) →ₗ[R] R) :=
    Fin.append (fun i => Lf (pe i)) (fun i => Lf (ne' i)) with hL
  have hL_left : ∀ i, L (Fin.castAdd rm i) = Lf (pe i) := fun i => by
    rw [hL, Fin.append_left]
  have hL_right : ∀ i, L (Fin.natAdd rp i) = Lf (ne' i) := fun i => by
    rw [hL, Fin.append_right]
  -- pe-image is P, ne'-image is N
  have hpe_mem : ∀ i, pe i ∈ P := fun i => P.orderEmbOfFin_mem hPe i
  have hne_mem : ∀ i, ne' i ∈ N := fun i => N.orderEmbOfFin_mem hNe i
  -- sum reindexing
  have hsum_P : ∀ (G : Fin n → R), ∑ j ∈ P, G j = ∑ i : Fin rp, G (pe i) := by
    intro G
    have := Finset.sum_image (s := (Finset.univ : Finset (Fin rp))) (g := pe) (f := G)
      (Set.injOn_of_injective pe.injective)
    rw [Finset.image_orderEmbOfFin_univ (h := hPe)] at this
    rw [this]
  have hsum_N : ∀ (G : Fin n → R), ∑ j ∈ N, G j = ∑ i : Fin rm, G (ne' i) := by
    intro G
    have := Finset.sum_image (s := (Finset.univ : Finset (Fin rm))) (g := ne') (f := G)
      (Set.injOn_of_injective ne'.injective)
    rw [Finset.image_orderEmbOfFin_univ (h := hNe)] at this
    rw [this]
  refine ⟨rp, rm, L, ?_, ?_, ?_, ?_⟩
  · -- (6) rank
    -- IsUnit (det A)
    have hdetA : IsUnit A.det := Matrix.isUnit_det_of_left_inverse hAo
    have hdetAt : IsUnit Aᵀ.det := by rw [Matrix.det_transpose]; exact hdetA
    have hrank : quadraticFormRank M = (Matrix.diagonal D).rank := by
      rw [quadraticFormRank, hM_eq]
      rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdetAt,
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdetA]
    rw [hrank, Matrix.rank_diagonal, Fintype.card_subtype]
    -- card {j // D j ≠ 0} = rp + rm
    have hsplit : (Finset.univ.filter (fun j => D j ≠ 0)) = P ∪ N := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hP, hN]
      rw [ne_iff_lt_or_gt, or_comm]
    rw [hsplit, Finset.card_union_of_disjoint hPN_disj]
  · -- (8) linear independence
    -- coefficient vectors L i ↦ c (idx i)
    have hcoeff_left : ∀ i, linearFormCoeffs (L (Fin.castAdd rm i)) = c (pe i) := by
      intro i; rw [hL_left, hLf, linearFormCoeffs_dotLM]
    have hcoeff_right : ∀ i, linearFormCoeffs (L (Fin.natAdd rp i)) = c (ne' i) := by
      intro i; rw [hL_right, hLf, linearFormCoeffs_dotLM]
    -- s nonzero on P ∪ N
    have hs_ne : ∀ j ∈ P ∪ N, s j ≠ 0 := by
      intro j hj hsj
      have hDj : |D j| = 0 := by rw [← hs_sq, hsj, pow_two, mul_zero]
      have hDj0 : D j = 0 := abs_eq_zero.mp hDj
      rcases Finset.mem_union.mp hj with h | h
      · exact absurd hDj0 (ne_of_gt (Finset.mem_filter.mp h).2)
      · exact absurd hDj0 (ne_of_lt (Finset.mem_filter.mp h).2)
    -- c j ⬝ᵥ c j' = s j * s j' * (a j ⬝ᵥ a j')
    have hcc : ∀ j j', c j ⬝ᵥ c j' = (s j * s j') * (a j ⬝ᵥ a j') := by
      intro j j'
      rw [hc]; simp only
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
    -- the coefficient family on Fin (rp + rm)
    set coeff : Fin (rp + rm) → (Fin n → R) := fun i => linearFormCoeffs (L i) with hcoeff_def
    -- index function: castAdd → pe, natAdd → ne'
    have horth_coeff : ∀ i j, i ≠ j → coeff i ⬝ᵥ coeff j = 0 := by
      intro i j hij
      induction i using Fin.addCases with
      | left i' =>
        induction j using Fin.addCases with
        | left j' =>
          show linearFormCoeffs (L _) ⬝ᵥ linearFormCoeffs (L _) = 0
          rw [hcoeff_left, hcoeff_left, hcc, hortho, ite_eq_right, mul_zero]
          intro h; exact hij (by rw [pe.injective h])
        | right j' =>
          show linearFormCoeffs (L _) ⬝ᵥ linearFormCoeffs (L _) = 0
          rw [hcoeff_left, hcoeff_right, hcc, hortho, ite_eq_right, mul_zero]
          intro h
          exact (Finset.disjoint_left.mp hPN_disj (hpe_mem i')) (h ▸ hne_mem j')
      | right i' =>
        induction j using Fin.addCases with
        | left j' =>
          show linearFormCoeffs (L _) ⬝ᵥ linearFormCoeffs (L _) = 0
          rw [hcoeff_right, hcoeff_left, hcc, hortho, ite_eq_right, mul_zero]
          intro h
          exact (Finset.disjoint_left.mp hPN_disj (hpe_mem j')) (h.symm ▸ hne_mem i')
        | right j' =>
          show linearFormCoeffs (L _) ⬝ᵥ linearFormCoeffs (L _) = 0
          rw [hcoeff_right, hcoeff_right, hcc, hortho, ite_eq_right, mul_zero]
          intro h; exact hij (by rw [ne'.injective h])
    have hne_coeff : ∀ i, coeff i ⬝ᵥ coeff i ≠ 0 := by
      intro i
      induction i using Fin.addCases with
      | left i' =>
        show linearFormCoeffs (L _) ⬝ᵥ linearFormCoeffs (L _) ≠ 0
        rw [hcoeff_left, hcc, hortho, ite_eq_left rfl, mul_one]
        have hsi : s (pe i') ≠ 0 := hs_ne _ (Finset.mem_union_left _ (hpe_mem i'))
        exact mul_ne_zero hsi hsi
      | right i' =>
        show linearFormCoeffs (L _) ⬝ᵥ linearFormCoeffs (L _) ≠ 0
        rw [hcoeff_right, hcc, hortho, ite_eq_left rfl, mul_one]
        have hsi : s (ne' i') ≠ 0 := hs_ne _ (Finset.mem_union_right _ (hne_mem i'))
        exact mul_ne_zero hsi hsi
    -- transfer to L via dotLM ∘ linearFormCoeffs
    have hL_eq : ∀ i, L i = dotLM (coeff i) := by
      intro i
      show L i = dotLM (coeff i)
      induction i using Fin.addCases with
      | left i' =>
        show L (Fin.castAdd rm i') = dotLM (linearFormCoeffs (L (Fin.castAdd rm i')))
        rw [hcoeff_left, hL_left, hLf]
      | right i' =>
        show L (Fin.natAdd rp i') = dotLM (linearFormCoeffs (L (Fin.natAdd rp i')))
        rw [hcoeff_right, hL_right, hLf]
    exact linearIndependent_dotLM_of_pairwise_orthogonal L coeff hL_eq hne_coeff horth_coeff
  · -- (7) orthogonality
    intro i j hij
    rw [IsOrthogonalForms, IsOrthogonal]
    -- reduce to coeff orthogonality, reuse the structure inline
    have hcoeff_left : ∀ i, linearFormCoeffs (L (Fin.castAdd rm i)) = c (pe i) := by
      intro i; rw [hL_left, hLf, linearFormCoeffs_dotLM]
    have hcoeff_right : ∀ i, linearFormCoeffs (L (Fin.natAdd rp i)) = c (ne' i) := by
      intro i; rw [hL_right, hLf, linearFormCoeffs_dotLM]
    have hcc : ∀ j j', c j ⬝ᵥ c j' = (s j * s j') * (a j ⬝ᵥ a j') := by
      intro j j'
      rw [hc]; simp only
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
    induction i using Fin.addCases with
    | left i' =>
      induction j using Fin.addCases with
      | left j' =>
        rw [hcoeff_left, hcoeff_left, hcc, hortho, ite_eq_right, mul_zero]
        intro h; exact hij (by rw [pe.injective h])
      | right j' =>
        rw [hcoeff_left, hcoeff_right, hcc, hortho, ite_eq_right, mul_zero]
        intro h
        exact (Finset.disjoint_left.mp hPN_disj (hpe_mem i')) (h ▸ hne_mem j')
    | right i' =>
      induction j using Fin.addCases with
      | left j' =>
        rw [hcoeff_right, hcoeff_left, hcc, hortho, ite_eq_right, mul_zero]
        intro h
        exact (Finset.disjoint_left.mp hPN_disj (hpe_mem j')) (h.symm ▸ hne_mem i')
      | right j' =>
        rw [hcoeff_right, hcoeff_right, hcc, hortho, ite_eq_right, mul_zero]
        intro h; exact hij (by rw [ne'.injective h])
  · -- (5) sum identity
    intro f
    rw [heigen f]
    -- split univ sum over P, N, rest
    have hsplit_sum : (∑ j, D j * (a j ⬝ᵥ f) ^ 2)
        = ∑ j ∈ P, D j * (a j ⬝ᵥ f) ^ 2 + ∑ j ∈ N, D j * (a j ⬝ᵥ f) ^ 2 := by
      rw [← Finset.sum_union hPN_disj]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      rw [Finset.mem_union] at hj
      push Not at hj
      exact hterm_zero f j hj.1 hj.2
    rw [hsplit_sum]
    have hP_eq : ∑ j ∈ P, D j * (a j ⬝ᵥ f) ^ 2 = ∑ j ∈ P, (Lf j f) ^ 2 :=
      Finset.sum_congr rfl (hterm_P f)
    have hN_eq : ∑ j ∈ N, D j * (a j ⬝ᵥ f) ^ 2 = ∑ j ∈ N, -(Lf j f) ^ 2 :=
      Finset.sum_congr rfl (hterm_N f)
    rw [hP_eq, hN_eq, Finset.sum_neg_distrib]
    rw [hsum_P (fun j => (Lf j f) ^ 2), hsum_N (fun j => (Lf j f) ^ 2)]
    simp only [hL_left, hL_right]
    ring

end Azurite.BPR.Chapter4
