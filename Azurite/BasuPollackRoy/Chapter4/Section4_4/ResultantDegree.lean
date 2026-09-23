/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_4.Proposition_4_76
import Azurite.BasuPollackRoy.Chapter4.Section4_4.CoeffTotalDegree
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# BPR §4.4.2: degree bound on the resultant projection

For the quantitative Nullstellensatz (Theorem 4.83): if `P₁` and all members of `rest` have total
degree `≤ d`, then every coefficient (in the auxiliary `U`) of `Res_{X_k}(P₁, R)` has total degree
`≤ 2 d²` in the variables `X₁, …, X_{k-1}`. Equivalently, each generator of `Proj_{X_k}(𝒫)` has
degree `≤ 2 d²`.

This follows from the Sylvester-determinant description of `Res` (`CoeffTotalDegreeLE.det`): the
matrix has size `≤ 2d`, and each entry is an `X₀`-coefficient of `embedX0 P₁` / `Rbar`, which is a
constant `Polynomial.C q` (resp. a `U`-monomial) with `q` of total degree `≤ d`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

open scoped Classical

variable {n : ℕ} {K : Type*} [Field K]

/-- A `monomial i q` has all coefficients of total degree `≤ q.totalDegree`. -/
private theorem coeffTotalDegreeLE_monomial (i : ℕ) (q : MvPolynomial (Fin n) K) :
    CoeffTotalDegreeLE (Polynomial.monomial i q) q.totalDegree := by
  intro j
  rw [Polynomial.coeff_monomial]
  split
  · exact le_refl _
  · simp

/-- A `Polynomial.C q` has all coefficients of total degree `≤ q.totalDegree`. -/
private theorem coeffTotalDegreeLE_C (q : MvPolynomial (Fin n) K) :
    CoeffTotalDegreeLE
      (Polynomial.C q : Polynomial (MvPolynomial (Fin n) K)) q.totalDegree := by
  rw [← Polynomial.monomial_zero_left]
  exact coeffTotalDegreeLE_monomial 0 q

/-- Multiplying by a power of `X` does not increase the coefficient total degree. -/
private theorem coeffTotalDegreeLE_X_pow_mul {d : ℕ}
    (g : Polynomial (Polynomial (MvPolynomial (Fin n) K))) (a b : ℕ)
    (hg : ∀ c, CoeffTotalDegreeLE (g.coeff c) d) :
    CoeffTotalDegreeLE ((Polynomial.X ^ a * g).coeff b) d := by
  rw [Polynomial.coeff_X_pow_mul']
  split
  · exact hg _
  · exact coeffTotalDegreeLE_zero d

/-- `embedX0 P` has the same `X₀`-degree as `finSuccEquiv K n P`. -/
private theorem natDegree_embedX0 (P : MvPolynomial (Fin (n + 1)) K) :
    (embedX0 P).natDegree = (finSuccEquiv K n P).natDegree :=
  Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective (finSuccEquiv K n P)

/-- **Stage 2b (degree of the resultant projection).** Every `U`-coefficient of `Res_{X_k}(P₁, R)`
has total degree `≤ 2 d²` in `X₁, …, X_{k-1}`, when `P₁` and all of `rest` have total degree
`≤ d`. -/
theorem coeffTotalDegreeLE_resXk (d : ℕ) (P₁ : MvPolynomial (Fin (n + 1)) K)
    (rest : List (MvPolynomial (Fin (n + 1)) K)) (hP₁ : P₁.totalDegree ≤ d)
    (hrest : ∀ Q ∈ rest, Q.totalDegree ≤ d) :
    CoeffTotalDegreeLE (resXk P₁ rest) (2 * d ^ 2) := by
  -- Coefficient-total-degree bound for `finSuccEquiv` coefficients of any total-degree-`≤ d` poly.
  have hfse : ∀ (P : MvPolynomial (Fin (n + 1)) K), P.totalDegree ≤ d →
      ∀ c, ((finSuccEquiv K n P).coeff c).totalDegree ≤ d := by
    intro P hP c
    by_cases hz : (finSuccEquiv K n P).coeff c = 0
    · rw [hz]; simp
    · have := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P c hz
      omega
  -- For all `i`, `rest.getD i 0` has total degree `≤ d`.
  have hrestD : ∀ i, (rest.getD i 0).totalDegree ≤ d := by
    intro i
    by_cases hi : i < rest.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact hrest _ (List.getElem_mem hi)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr (by omega), Option.getD_none]
      simp
  -- `embedX0` coefficients are constants of total degree `≤ d`.
  have hembed : ∀ (P : MvPolynomial (Fin (n + 1)) K), P.totalDegree ≤ d →
      ∀ c, CoeffTotalDegreeLE ((embedX0 P).coeff c) d := by
    intro P hP c
    unfold embedX0
    rw [Polynomial.coeff_map]
    exact (coeffTotalDegreeLE_C _).mono (hfse P hP c)
  -- `Rbar` coefficients have total degree `≤ d`.
  have hRbar : ∀ c, CoeffTotalDegreeLE ((Rbar rest).coeff c) d := by
    intro c
    unfold Rbar
    rw [Polynomial.finsetSum_coeff]
    apply CoeffTotalDegreeLE.finsetSum
    intro i _
    -- `uVar ^ i = C (X ^ i)`.
    have huVar : (uVar : Polynomial (Polynomial (MvPolynomial (Fin n) K))) ^ i
        = Polynomial.C ((Polynomial.X : Polynomial (MvPolynomial (Fin n) K)) ^ i) := by
      rw [uVar, ← map_pow]
    rw [huVar, Polynomial.coeff_mul_C]
    unfold embedX0
    rw [Polynomial.coeff_map]
    rw [Polynomial.C_mul_X_pow_eq_monomial]
    exact (coeffTotalDegreeLE_monomial i _).mono (hfse _ (hrestD i) c)
  -- Each Sylvester entry has coefficient total degree `≤ d`.
  have hentry : ∀ i j, CoeffTotalDegreeLE (Syl (embedX0 P₁) (Rbar rest) i j) d := by
    intro i j
    rw [Syl, Matrix.of_apply]
    split
    · exact coeffTotalDegreeLE_X_pow_mul _ _ _ (hembed P₁ hP₁)
    · exact coeffTotalDegreeLE_X_pow_mul _ _ _ hRbar
  -- Assemble via the determinant bound.
  have hdet := CoeffTotalDegreeLE.det hentry
  rw [show resXk P₁ rest = (Syl (embedX0 P₁) (Rbar rest)).det from rfl]
  refine hdet.mono ?_
  -- Bound the matrix dimension by `2 * d`.
  have hN₁ : (embedX0 P₁).natDegree ≤ d := by
    rw [natDegree_embedX0, MvPolynomial.natDegree_finSuccEquiv]
    exact le_trans (MvPolynomial.degreeOf_le_totalDegree P₁ 0) hP₁
  have hN₂ : (Rbar rest).natDegree ≤ d := by
    unfold Rbar
    refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, ?_⟩
    intro i _
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    have hterm : (embedX0 (rest.getD i 0)).natDegree ≤ d := by
      rw [natDegree_embedX0, MvPolynomial.natDegree_finSuccEquiv]
      exact le_trans (MvPolynomial.degreeOf_le_totalDegree _ 0) (hrestD i)
    have huVardeg : ((uVar : Polynomial (Polynomial (MvPolynomial (Fin n) K))) ^ i).natDegree = 0 := by
      rw [uVar, ← map_pow, Polynomial.natDegree_C]
    rw [huVardeg]
    simpa using hterm
  calc ((embedX0 P₁).natDegree + (Rbar rest).natDegree) * d
      ≤ (2 * d) * d := by
        apply Nat.mul_le_mul_right
        omega
    _ = 2 * d ^ 2 := by ring

/-- Every entry of the Sylvester matrix `Polynomial.sylvester P Q m m'` has all coefficients of
total degree `≤ D`, given that `P` and `Q` do. -/
private theorem coeffTotalDegreeLE_sylvester {D : ℕ}
    (P Q : Polynomial (Polynomial (MvPolynomial (Fin n) K))) (m m' : ℕ)
    (hP : ∀ c, CoeffTotalDegreeLE (P.coeff c) D) (hQ : ∀ c, CoeffTotalDegreeLE (Q.coeff c) D)
    (i j : Fin (m + m')) :
    CoeffTotalDegreeLE (Polynomial.sylvester P Q m m' i j) D := by
  rw [Polynomial.sylvester, Matrix.of_apply]
  refine Fin.addCases (fun j₁ => ?_) (fun j₁ => ?_) j
  · rw [Fin.addCases_left]
    split
    · exact hQ _
    · exact coeffTotalDegreeLE_zero D
  · rw [Fin.addCases_right]
    split
    · exact hP _
    · exact coeffTotalDegreeLE_zero D

/-- **Stage 2c part 2 (quantitative Bézout for the resultant).** If every coefficient of
`P, Q ∈ (MvPolynomial (Fin n) K)[U][X₀]` has total degree `≤ D` (in `X₁, …, X_{k-1}`), then the
resultant Bézout cofactors `p, q` in `C(Res P Q) = p·P + q·Q` can be chosen with every coefficient
of total degree `≤ (deg P + deg Q)·D`. (The cofactors are entries of the adjugate of the Sylvester
matrix, so `CoeffTotalDegreeLE.adjugate` bounds them.) -/
theorem coeffTotalDegreeLE_bezout {D : ℕ}
    (P Q : Polynomial (Polynomial (MvPolynomial (Fin n) K)))
    (hP : ∀ c, CoeffTotalDegreeLE (P.coeff c) D) (hQ : ∀ c, CoeffTotalDegreeLE (Q.coeff c) D)
    (H : P.natDegree ≠ 0 ∨ Q.natDegree ≠ 0) :
    ∃ p q : Polynomial (Polynomial (MvPolynomial (Fin n) K)),
      Polynomial.C (Res P Q) = p * P + q * Q ∧
        (∀ c, CoeffTotalDegreeLE (p.coeff c) ((P.natDegree + Q.natDegree) * D)) ∧
        (∀ c, CoeffTotalDegreeLE (q.coeff c) ((P.natDegree + Q.natDegree) * D)) ∧
        p.degree < Q.natDegree ∧ q.degree < P.natDegree := by
  classical
  set m := P.natDegree with hm
  set m' := Q.natDegree with hm'
  -- `m + m' > 0`, so `0 : Fin (m + m')` exists.
  have hmm' : 0 < m + m' := by
    rcases H with h | h <;> omega
  -- The basis vector `b₂ 0` of `degreeLT E (m + m')` is the constant polynomial `1`.
  set b₂ := Polynomial.degreeLT.basis (Polynomial (MvPolynomial (Fin n) K)) (m + m')
  set i0 : Fin (m + m') := ⟨0, hmm'⟩
  -- The image of `1` under `adjSylvester`.
  set X := Polynomial.adjSylvester P Q (m := m) (n := m') (b₂ i0) with hX
  -- The repr of `X` in the product basis equals column `i0` of the adjugate.
  have hrepr : (((Polynomial.degreeLT.basis (Polynomial (MvPolynomial (Fin n) K)) m).prod
      (Polynomial.degreeLT.basis (Polynomial (MvPolynomial (Fin n) K)) m')).reindex
        finSumFinEquiv).repr X = fun j => (Polynomial.sylvester P Q m m').adjugate j i0 := by
    rw [hX, Polynomial.adjSylvester, Matrix.toLin_self]
    exact Module.Basis.repr_sum_self _ _
  -- Every adjugate entry has coefficient total degree `≤ (m + m') * D`.
  have hadj : ∀ i j, CoeffTotalDegreeLE ((Polynomial.sylvester P Q m m').adjugate i j)
      ((m + m') * D) :=
    CoeffTotalDegreeLE.adjugate (coeffTotalDegreeLE_sylvester P Q m m' hP hQ)
  -- The cofactors.
  refine ⟨X.2.1, X.1.1, ?_, ?_, ?_, ?_, ?_⟩
  · -- Bézout identity: `f * X.2 + g * X.1 = C (resultant)`.
    have key := congr(($(Polynomial.sylveserMap_comp_adjSylvester P Q (m := m) (n := m')
      le_rfl le_rfl) (b₂ i0)).1)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Polynomial.sylvesterMap_apply_coe, ← hX] at key
    -- `key : P * X.2 + Q * X.1 = ↑(resultant P Q m m' • b₂ i0)`.
    have hcoe : (↑(P.resultant Q m m' • b₂ i0) :
        Polynomial (Polynomial (MvPolynomial (Fin n) K))) = Polynomial.C (P.resultant Q m m') := by
      rw [Submodule.coe_smul, Polynomial.degreeLT.basis_val]
      simp only [i0]
      rw [pow_zero, Polynomial.smul_eq_C_mul, mul_one]
    rw [hcoe] at key
    rw [Res_eq_resultant, ← hm, ← hm', ← key]
    ring
  · -- Bound on `X.2.coeff c`: it is `adjugate (natAdd m c) i0` for `c < m'`, else `0`.
    intro c
    by_cases hc : c < m'
    · have hco : (↑X.2 : Polynomial (Polynomial (MvPolynomial (Fin n) K))).coeff c
          = (Polynomial.sylvester P Q m m').adjugate (finSumFinEquiv (Sum.inr ⟨c, hc⟩)) i0 := by
        have h := congrFun hrepr (finSumFinEquiv (Sum.inr ⟨c, hc⟩))
        rwa [Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_repr_inr,
          Polynomial.degreeLT.basis_repr] at h
      rw [hco]; exact hadj _ _
    · have : (↑X.2 : Polynomial (Polynomial (MvPolynomial (Fin n) K))).coeff c = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        refine lt_of_lt_of_le (Polynomial.mem_degreeLT.mp X.2.2) ?_
        exact_mod_cast Nat.le_of_not_lt hc
      rw [this]; exact coeffTotalDegreeLE_zero _
  · -- Bound on `X.1.coeff c`: it is `adjugate (castAdd m' c) i0` for `c < m`, else `0`.
    intro c
    by_cases hc : c < m
    · have hco : (↑X.1 : Polynomial (Polynomial (MvPolynomial (Fin n) K))).coeff c
          = (Polynomial.sylvester P Q m m').adjugate (finSumFinEquiv (Sum.inl ⟨c, hc⟩)) i0 := by
        have h := congrFun hrepr (finSumFinEquiv (Sum.inl ⟨c, hc⟩))
        rwa [Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply, Module.Basis.prod_repr_inl,
          Polynomial.degreeLT.basis_repr] at h
      rw [hco]; exact hadj _ _
    · have : (↑X.1 : Polynomial (Polynomial (MvPolynomial (Fin n) K))).coeff c = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        refine lt_of_lt_of_le (Polynomial.mem_degreeLT.mp X.1.2) ?_
        exact_mod_cast Nat.le_of_not_lt hc
      rw [this]; exact coeffTotalDegreeLE_zero _
  · -- `p = X.2.1` has degree `< m' = Q.natDegree`.
    exact Polynomial.mem_degreeLT.mp X.2.2
  · -- `q = X.1.1` has degree `< m = P.natDegree`.
    exact Polynomial.mem_degreeLT.mp X.1.2

/-- The `j`-th `U`-coefficient of `gHom r` has total degree `≤ r.natDegree + B`, when every
coefficient of `r` has total degree `≤ B`. -/
private theorem gHom_coeff_totalDegree_le {B : ℕ}
    (r : Polynomial (Polynomial (MvPolynomial (Fin n) K)))
    (hr : ∀ c, CoeffTotalDegreeLE (r.coeff c) B) (j : ℕ) :
    ((gHom r).coeff j).totalDegree ≤ r.natDegree + B := by
  -- Expand `gHom r` as a finite sum over `X₀`-coefficients.
  have hexp : gHom r =
      ∑ c ∈ Finset.range (r.natDegree + 1),
        betaHom (r.coeff c) * (Polynomial.C (MvPolynomial.X 0))^c := by
    rw [gHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range]
  rw [hexp, Polynomial.finsetSum_coeff]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro c hc
  rw [Finset.mem_range] at hc
  -- `(C (X 0))^c = C ((X 0)^c)`.
  rw [← Polynomial.C_pow, Polynomial.coeff_mul_C]
  -- `(betaHom (r.coeff c)).coeff j = rename Fin.succ ((r.coeff c).coeff j)`.
  have hbc : (betaHom (r.coeff c)).coeff j
      = MvPolynomial.rename Fin.succ ((r.coeff c).coeff j) := by
    rw [betaHom, Polynomial.coe_mapRingHom, Polynomial.coeff_map]; rfl
  rw [hbc]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h1 : (MvPolynomial.rename Fin.succ ((r.coeff c).coeff j)).totalDegree ≤ B :=
    (MvPolynomial.totalDegree_rename_le _ _).trans (hr c j)
  have h2 : ((MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K) ^ c).totalDegree
      ≤ c := by
    rw [MvPolynomial.totalDegree_X_pow]
  have hcle : c ≤ r.natDegree := by omega
  omega

/-- **Stage 3b (quantitative ideal membership of the projection).** Each generator `Q` of
`Proj_{X_k}(𝒫)` lies in `Ideal(𝒫_v)` with a degree-`≤ 3d²` certificate: there is a coefficient
assignment `A` with every `A P` of total degree `≤ 3d²` and `∑ A P · P = rename Fin.succ Q`.
This is the quantitative form of Proposition 4.76's clause (1), supplying the per-step lift in the
quantitative weak Nullstellensatz. -/
theorem quant_proj_mem (d : ℕ) {P₁ : MvPolynomial (Fin (n + 1)) K}
    {rest : List (MvPolynomial (Fin (n + 1)) K)} (hP₁ : P₁.totalDegree ≤ d)
    (hrest : ∀ Q ∈ rest, Q.totalDegree ≤ d)
    (hdeg : (embedX0 P₁).natDegree ≠ 0 ∨ (Rbar rest).natDegree ≠ 0)
    {Q : MvPolynomial (Fin n) K} (hQ : Q ∈ projPolys P₁ rest) :
    ∃ A : MvPolynomial (Fin (n + 1)) K → MvPolynomial (Fin (n + 1)) K,
      (∀ P ∈ insert P₁ rest.toFinset, (A P).totalDegree ≤ 3 * d ^ 2) ∧
        ∑ P ∈ insert P₁ rest.toFinset, A P * P = MvPolynomial.rename Fin.succ Q := by
  classical
  -- Unfold `projPolys` membership.
  unfold projPolys at hQ
  rw [Finset.mem_insert] at hQ
  rcases hQ with hQ0 | hQimg
  · -- `Q = 0`: the trivial certificate.
    refine ⟨fun _ => 0, fun P _ => by simp, ?_⟩
    rw [hQ0, map_zero]
    simp
  · -- `Q = (resXk P₁ rest).coeff j` for some `j`.
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hQimg
    -- Coefficient-total-degree bounds for `embedX0 P₁` and `Rbar rest` (copied from `_resXk`).
    have hfse : ∀ (P : MvPolynomial (Fin (n + 1)) K), P.totalDegree ≤ d →
        ∀ c, ((finSuccEquiv K n P).coeff c).totalDegree ≤ d := by
      intro P hP c
      by_cases hz : (finSuccEquiv K n P).coeff c = 0
      · rw [hz]; simp
      · have := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P c hz
        omega
    have hrestD : ∀ i, (rest.getD i 0).totalDegree ≤ d := by
      intro i
      by_cases hi : i < rest.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
        exact hrest _ (List.getElem_mem hi)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr (by omega), Option.getD_none]
        simp
    have hP : ∀ c, CoeffTotalDegreeLE ((embedX0 P₁).coeff c) d := by
      intro c
      unfold embedX0
      rw [Polynomial.coeff_map]
      exact (coeffTotalDegreeLE_C _).mono (hfse P₁ hP₁ c)
    have hR : ∀ c, CoeffTotalDegreeLE ((Rbar rest).coeff c) d := by
      intro c
      unfold Rbar
      rw [Polynomial.finsetSum_coeff]
      apply CoeffTotalDegreeLE.finsetSum
      intro i _
      have huVar : (uVar : Polynomial (Polynomial (MvPolynomial (Fin n) K))) ^ i
          = Polynomial.C ((Polynomial.X : Polynomial (MvPolynomial (Fin n) K)) ^ i) := by
        rw [uVar, ← map_pow]
      rw [huVar, Polynomial.coeff_mul_C]
      unfold embedX0
      rw [Polynomial.coeff_map, Polynomial.C_mul_X_pow_eq_monomial]
      exact (coeffTotalDegreeLE_monomial i _).mono (hfse _ (hrestD i) c)
    -- natDegree bounds `≤ d`.
    have hN₁ : (embedX0 P₁).natDegree ≤ d := by
      rw [natDegree_embedX0, MvPolynomial.natDegree_finSuccEquiv]
      exact le_trans (MvPolynomial.degreeOf_le_totalDegree P₁ 0) hP₁
    have hN₂ : (Rbar rest).natDegree ≤ d := by
      unfold Rbar
      refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
      rw [Finset.fold_max_le]
      refine ⟨Nat.zero_le _, ?_⟩
      intro i _
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      have hterm : (embedX0 (rest.getD i 0)).natDegree ≤ d := by
        rw [natDegree_embedX0, MvPolynomial.natDegree_finSuccEquiv]
        exact le_trans (MvPolynomial.degreeOf_le_totalDegree _ 0) (hrestD i)
      have huVardeg : ((uVar : Polynomial (Polynomial (MvPolynomial (Fin n) K))) ^ i).natDegree
          = 0 := by rw [uVar, ← map_pow, Polynomial.natDegree_C]
      rw [huVardeg]; simpa using hterm
    -- `d ≥ 1`: otherwise both natDegrees are 0, contradicting `hdeg`.
    have hd1 : 1 ≤ d := by
      rcases hdeg with h | h <;> omega
    -- The quantitative Bézout cofactors.
    obtain ⟨p, q, hbez, hp_bnd, hq_bnd, hp_deg, hq_deg⟩ :=
      coeffTotalDegreeLE_bezout (embedX0 P₁) (Rbar rest) hP hR hdeg
    -- Coefficient total-degree bound `≤ 2 d²`.
    have hpq2 : (embedX0 P₁).natDegree + (Rbar rest).natDegree ≤ 2 * d := by omega
    have hbnd2d2 : ((embedX0 P₁).natDegree + (Rbar rest).natDegree) * d ≤ 2 * d ^ 2 := by
      calc ((embedX0 P₁).natDegree + (Rbar rest).natDegree) * d
          ≤ (2 * d) * d := Nat.mul_le_mul_right _ hpq2
        _ = 2 * d ^ 2 := by ring
    have hp2 : ∀ c, CoeffTotalDegreeLE (p.coeff c) (2 * d ^ 2) :=
      fun c => (hp_bnd c).mono hbnd2d2
    have hq2 : ∀ c, CoeffTotalDegreeLE (q.coeff c) (2 * d ^ 2) :=
      fun c => (hq_bnd c).mono hbnd2d2
    -- natDegree bounds on the cofactors.
    have hp_nd : p.natDegree ≤ d := by
      rw [Polynomial.natDegree_le_iff_degree_le]
      exact le_trans (le_of_lt hp_deg) (by exact_mod_cast hN₂)
    have hq_nd : q.natDegree ≤ d := by
      rw [Polynomial.natDegree_le_iff_degree_le]
      exact le_trans (le_of_lt hq_deg) (by exact_mod_cast hN₁)
    -- Apply `gHom` to the Bézout identity.
    have hgbez := congrArg gHom hbez
    rw [map_add, map_mul, map_mul, gHom_embedX0 P₁, gHom_Rbar] at hgbez
    -- Take the `j`-th `U`-coefficient.
    have hstar := congrArg (fun t => Polynomial.coeff t j) hgbez
    rw [show Res (embedX0 P₁) (Rbar rest) = resXk P₁ rest from rfl,
      gHom_C_resXk_coeff] at hstar
    -- Simplify the RHS coefficient.
    rw [Polynomial.coeff_add, Polynomial.coeff_mul_C] at hstar
    have hRHS2 : (gHom q *
          ∑ l ∈ Finset.range rest.length, Polynomial.C (rest.getD l 0) * Polynomial.X ^ l).coeff j
        = ∑ l ∈ Finset.range rest.length,
            (if l ≤ j then (gHom q).coeff (j - l) else 0) * (rest.getD l 0) := by
      rw [Finset.mul_sum, Polynomial.finsetSum_coeff]
      apply Finset.sum_congr rfl
      intro l _
      rw [show gHom q * (Polynomial.C (rest.getD l 0) * Polynomial.X ^ l)
            = (gHom q * Polynomial.X ^ l) * Polynomial.C (rest.getD l 0) by ring,
        Polynomial.coeff_mul_C, Polynomial.coeff_mul_X_pow']
    rw [hRHS2] at hstar
    -- (★) : `rename Fin.succ ((resXk).coeff j) = (gHom p).coeff j * P₁ + ∑ …`.
    -- Define the certificate.
    set A : MvPolynomial (Fin (n + 1)) K → MvPolynomial (Fin (n + 1)) K :=
      fun P => (if P = P₁ then (gHom p).coeff j else 0) +
        ∑ l ∈ (Finset.range rest.length).filter (fun l => rest.getD l 0 = P ∧ l ≤ j),
          (gHom q).coeff (j - l) with hA
    refine ⟨A, ?_, ?_⟩
    · -- Degree bound `≤ 3 d²` on each `A P`.
      intro P _
      refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
      · -- the `if … then (gHom p).coeff j else 0` part.
        split
        · -- `(gHom p).coeff j` has total degree `≤ d + 2 d² ≤ 3 d²`.
          refine le_trans (gHom_coeff_totalDegree_le p hp2 j) ?_
          nlinarith [hp_nd, hd1]
        · simp
      · -- the fibered sum of `(gHom q).coeff (j - l)` parts.
        refine MvPolynomial.totalDegree_finsetSum_le (fun l _ => ?_)
        refine le_trans (gHom_coeff_totalDegree_le q hq2 (j - l)) ?_
        nlinarith [hq_nd, hd1]
    · -- The summation identity equals (★).
      rw [hstar]
      -- Split `∑ A P * P` into the two pieces.
      have hsplit : ∀ P, A P * P =
          (if P = P₁ then (gHom p).coeff j else 0) * P +
          (∑ l ∈ (Finset.range rest.length).filter (fun l => rest.getD l 0 = P ∧ l ≤ j),
            (gHom q).coeff (j - l)) * P := by
        intro P; rw [hA]; ring
      rw [Finset.sum_congr rfl (fun P _ => hsplit P), Finset.sum_add_distrib]
      congr 1
      · -- First piece: only `P = P₁` contributes.
        rw [Finset.sum_eq_single P₁]
        · simp
        · intro P _ hP'; rw [ite_eq_right hP', zero_mul]
        · intro h; exact absurd (Finset.mem_insert_self _ _) h
      · -- Second piece: fiberwise regrouping.
        rw [show (∑ P ∈ insert P₁ rest.toFinset,
              (∑ l ∈ (Finset.range rest.length).filter (fun l => rest.getD l 0 = P ∧ l ≤ j),
                (gHom q).coeff (j - l)) * P)
            = ∑ P ∈ insert P₁ rest.toFinset,
                ∑ l ∈ (Finset.range rest.length).filter (fun l => rest.getD l 0 = P ∧ l ≤ j),
                  (if l ≤ j then (gHom q).coeff (j - l) else 0) * (rest.getD l 0) from ?_]
        · -- Now regroup over `l`.
          rw [show (∑ l ∈ Finset.range rest.length,
                (if l ≤ j then (gHom q).coeff (j - l) else 0) * (rest.getD l 0))
              = ∑ l ∈ (Finset.range rest.length).filter (fun l => l ≤ j),
                  (if l ≤ j then (gHom q).coeff (j - l) else 0) * (rest.getD l 0) from ?_]
          · -- Fiberwise: the inner filter has the extra `rest_l = P` condition.
            rw [← Finset.sum_fiberwise_of_maps_to
              (t := insert P₁ rest.toFinset) (g := fun l => rest.getD l 0)
              (s := (Finset.range rest.length).filter (fun l => l ≤ j))
              (f := fun l => (if l ≤ j then (gHom q).coeff (j - l) else 0) * (rest.getD l 0))
              (fun l hl => ?_)]
            · apply Finset.sum_congr rfl
              intro P _
              apply Finset.sum_congr ?_ (fun _ _ => rfl)
              rw [Finset.filter_filter]
              apply Finset.filter_congr
              intro l _
              exact and_comm
            · rw [Finset.mem_filter, Finset.mem_range] at hl
              exact Finset.mem_insert_of_mem
                (List.mem_toFinset.mpr (by
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl.1, Option.getD_some]
                  exact List.getElem_mem hl.1))
          · -- Drop the `l > j` terms (they are `0`).
            refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
            intro l hl hlf
            rw [Finset.mem_filter, Finset.mem_range] at hlf
            rw [Finset.mem_range] at hl
            rw [ite_eq_right (fun h => hlf ⟨hl, h⟩), zero_mul]
        · -- Inside each fiber, `rest_l = P` so we may replace `P` by `rest_l`.
          apply Finset.sum_congr rfl
          intro P _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro l hl
          rw [Finset.mem_filter] at hl
          obtain ⟨_, hlP, hlj⟩ := hl
          rw [ite_eq_left hlj, hlP]

end Azurite.BPR.Chapter4
