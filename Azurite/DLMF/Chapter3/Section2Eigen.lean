/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter3.Section2Cond
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# DLMF §3.2(iv)–(v): eigenvalues, eigenvectors, and their condition

Matrices are `n × n` over `ℝ` or `ℂ` (`RCLike 𝕜`). The transpose in `yᵀ` is bilinear, as in the
DLMF.

* **3.2.18**: right eigenvectors `Ax = λx` (`IsRightEigen`) and left eigenvectors `yᵀA = λyᵀ`
  (`IsLeftEigen`), "equivalently `Aᵀy = λy`" (`isLeftEigen_iff`).
  * Normalization to Euclidean norm 1 (`IsRightEigen.normalize`).
* **3.2.19**: `p_n(λ) = det[λI − A]` (`dlmf_3_2_19`). Its zeros are the eigenvalues
  (`charpoly_isRoot_iff`), and `A` and `Aᵀ` have the same eigenvalues (`isEigenvalue_transpose`).
* **Multiplicity**: for nondefective `A` (`IsNondefective`, `n` linearly independent eigenvectors
  `v_k` with eigenvalues `μ_k`), `p_n(λ) = ∏(λ − μ_k)` (`charpoly_eq_prod_of_nondefective`).
  * The multiplicity of `λ` is the number of `k` with `μ_k = λ`, and those `v_k` are `m` linearly
    independent eigenvectors for `λ` (`dlmf_3_2_iv_multiplicity`).
* **3.2.20**: `κ(λ) = 1/|yᵀx|` (`eigCond`).
  * For nondefective `A` and a simple zero `λ`, every eigenvector is a multiple of the basis vector
    for `λ` (`eigvec_eq_smul_of_simple`). The left eigenvector annihilates the other basis vectors,
    so `yᵀx ≠ 0` (`dotProduct_ne_zero_of_simple`).
  * Hence `κ(λ) ≥ 1` (`one_le_eigCond`, via `|yᵀx| ≤ ‖y‖₂‖x‖₂`, `norm_dotProduct_le`).
  * `|yᵀx| = |cos θ|` for real vectors (`abs_dotProduct_eq_abs_cos`).
  * For real symmetric `A`, the left and right eigenvectors coincide up to sign, so `κ(λ) = 1`
    (`eigCond_eq_one_of_symm`).

The statement that symmetric eigenvalue problems are well-conditioned is the interpretation of
`κ(λ) = 1` and is not formalized further.
-/

namespace Azurite.DLMF

open scoped Matrix
open Matrix Polynomial WithLp

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-! ### §3.2(iv) Eigenvalues and eigenvectors -/

/-- **DLMF 3.2.18**: `x` is a (right) eigenvector of `A` for `λ`: `x ≠ 0`, `Ax = λx`. -/
def IsRightEigen (A : Matrix (Fin n) (Fin n) 𝕜) (lam : 𝕜) (x : Fin n → 𝕜) : Prop :=
  x ≠ 0 ∧ A *ᵥ x = lam • x

/-- A left eigenvector: `y ≠ 0`, `yᵀA = λyᵀ`. -/
def IsLeftEigen (A : Matrix (Fin n) (Fin n) 𝕜) (lam : 𝕜) (y : Fin n → 𝕜) : Prop :=
  y ≠ 0 ∧ y ᵥ* A = lam • y

/-- "or, equivalently, `Aᵀy = λy`". -/
theorem isLeftEigen_iff (A : Matrix (Fin n) (Fin n) 𝕜) (lam : 𝕜) (y : Fin n → 𝕜) :
    IsLeftEigen A lam y ↔ IsRightEigen Aᵀ lam y := by
  rw [IsLeftEigen, IsRightEigen, mulVec_transpose]

/-- `λ` is an eigenvalue of `A`. -/
def IsEigenvalue (A : Matrix (Fin n) (Fin n) 𝕜) (lam : 𝕜) : Prop := ∃ x, IsRightEigen A lam x

/-- "A normalized eigenvector has Euclidean norm 1": every eigenvector can be normalized. -/
theorem IsRightEigen.normalize {A : Matrix (Fin n) (Fin n) 𝕜} {lam : 𝕜} {x : Fin n → 𝕜}
    (hx : IsRightEigen A lam x) :
    IsRightEigen A lam (((‖toLp 2 x‖⁻¹ : ℝ) : 𝕜) • x) ∧
      ‖toLp 2 (((‖toLp 2 x‖⁻¹ : ℝ) : 𝕜) • x)‖ = 1 := by
  have hpos : 0 < ‖toLp 2 x‖ := norm_pos_iff.mpr fun h => hx.1 (by simpa using h)
  refine ⟨⟨smul_ne_zero (by simpa using hpos.ne') hx.1, ?_⟩, ?_⟩
  · rw [mulVec_smul, hx.2, smul_comm]
  · rw [toLp_smul, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hpos.ne']

/-- **DLMF 3.2.19**: the characteristic polynomial `p_n(λ) = det[λI − A]`. -/
theorem dlmf_3_2_19 (A : Matrix (Fin n) (Fin n) 𝕜) (lam : 𝕜) :
    A.charpoly.eval lam = (lam • (1 : Matrix (Fin n) (Fin n) 𝕜) - A).det := by
  rw [eval_charpoly, Matrix.smul_one_eq_diagonal]
  rfl

/-- "Its zeros are the eigenvalues of `A`". -/
theorem charpoly_isRoot_iff (A : Matrix (Fin n) (Fin n) 𝕜) (lam : 𝕜) :
    A.charpoly.IsRoot lam ↔ IsEigenvalue A lam := by
  rw [IsRoot, dlmf_3_2_19, ← Matrix.exists_mulVec_eq_zero_iff]
  simp only [IsEigenvalue, IsRightEigen, sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]
  exact ⟨fun ⟨v, h1, h2⟩ => ⟨v, h1, h2.symm⟩, fun ⟨v, h1, h2⟩ => ⟨v, h1, h2.symm⟩⟩

/-- The left eigenvalues are the eigenvalues (`det[λI − Aᵀ] = det[λI − A]`). -/
theorem isEigenvalue_transpose (A : Matrix (Fin n) (Fin n) 𝕜) (lam : 𝕜) :
    IsEigenvalue Aᵀ lam ↔ IsEigenvalue A lam := by
  rw [← charpoly_isRoot_iff, ← charpoly_isRoot_iff, charpoly_transpose]

/-- `A` is nondefective: it has a complete set of `n` linearly independent eigenvectors `v_k`
(eigenvalues `μ_k`). -/
def IsNondefective (A : Matrix (Fin n) (Fin n) 𝕜) (v : Fin n → Fin n → 𝕜) (μ : Fin n → 𝕜) :
    Prop :=
  LinearIndependent 𝕜 v ∧ ∀ k, A *ᵥ v k = μ k • v k

/-- For nondefective `A`, `p_n(λ) = ∏ (λ − μ_k)` (`A` is similar to `diag(μ)`). -/
theorem charpoly_eq_prod_of_nondefective {A : Matrix (Fin n) (Fin n) 𝕜}
    {v : Fin n → Fin n → 𝕜} {μ : Fin n → 𝕜} (hA : IsNondefective A v μ) :
    A.charpoly = ∏ k, (X - C (μ k)) := by
  set P : Matrix (Fin n) (Fin n) 𝕜 := Matrix.of fun i k => v k i
  have hcol : P.col = v := by funext k i; rfl
  have hP : IsUnit P := Matrix.linearIndependent_col_iff_isUnit.mp (hcol ▸ hA.1)
  have hAP : A * P = P * diagonal μ := by
    ext i k
    rw [mul_diagonal, Matrix.mul_apply]
    have := congrFun (hA.2 k) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [P, Matrix.of_apply]
    rw [this, mul_comm]
  set u := hP.unit
  have hu : (u : Matrix (Fin n) (Fin n) 𝕜) = P := rfl
  have hA' : A = (u : Matrix (Fin n) (Fin n) 𝕜) * diagonal μ *
      (u : Matrix (Fin n) (Fin n) 𝕜)⁻¹ := by
    rw [hu, ← hAP, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det P).mp hP), Matrix.mul_one]
  rw [hA', charpoly_units_conj, charpoly_diagonal]

/-- **"To an eigenvalue of multiplicity `m`, there correspond `m` linearly independent
eigenvectors provided that `A` is nondefective"**: the multiplicity of `λ` as a zero of `p_n` is
the number of `k` with `μ_k = λ`, and those `v_k` are linearly independent eigenvectors for `λ`. -/
theorem dlmf_3_2_iv_multiplicity {A : Matrix (Fin n) (Fin n) 𝕜}
    {v : Fin n → Fin n → 𝕜} {μ : Fin n → 𝕜} (hA : IsNondefective A v μ) (lam : 𝕜) :
    A.charpoly.rootMultiplicity lam = (Finset.univ.filter fun k => μ k = lam).card ∧
      LinearIndependent 𝕜 (fun k : {k // μ k = lam} => v k) ∧
      ∀ k, μ k = lam → IsRightEigen A lam (v k) := by
  refine ⟨?_, hA.1.comp Subtype.val Subtype.val_injective, fun k hk =>
    ⟨hA.1.ne_zero k, by rw [hA.2 k, hk]⟩⟩
  classical
  rw [charpoly_eq_prod_of_nondefective hA, ← count_roots,
    show (∏ k, (X - C (μ k)) : 𝕜[X]) = ((Finset.univ.val.map μ).map fun a => X - C a).prod by
      rw [Multiset.map_map]; rfl,
    roots_multiset_prod_X_sub_C, Multiset.count_map, Finset.card_def, Finset.filter_val]
  congr 1
  refine Multiset.filter_congr fun k _ => eq_comm

/-! ### §3.2(v) Condition of eigenvalues -/

/-- **DLMF 3.2.20**: `κ(λ) = 1/|yᵀx|`. -/
noncomputable def eigCond (x y : Fin n → 𝕜) : ℝ := 1 / ‖y ⬝ᵥ x‖

/-- The eigenvectors of a simple eigenvalue of a nondefective matrix are multiples of the one
basis eigenvector `v_i` with `μ_i = λ`. -/
theorem eigvec_eq_smul_of_simple {A : Matrix (Fin n) (Fin n) 𝕜} {v : Fin n → Fin n → 𝕜}
    {μ : Fin n → 𝕜} (hA : IsNondefective A v μ) {lam : 𝕜}
    (hsimple : A.charpoly.rootMultiplicity lam = 1) :
    ∃ i, μ i = lam ∧ (∀ k, μ k = lam → k = i) ∧
      ∀ x, IsRightEigen A lam x → ∃ c : 𝕜, c ≠ 0 ∧ x = c • v i := by
  classical
  obtain ⟨hm, -, -⟩ := dlmf_3_2_iv_multiplicity hA lam
  rw [hsimple] at hm
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hm.symm
  have hi' : μ i = lam := by
    have : i ∈ Finset.univ.filter fun k => μ k = lam := hi ▸ Finset.mem_singleton_self i
    simpa using this
  have huniq : ∀ k, μ k = lam → k = i := fun k hk => by
    have : k ∈ Finset.univ.filter fun k => μ k = lam := by simpa using hk
    rw [hi] at this; simpa using this
  refine ⟨i, hi', huniq, fun x hx => ?_⟩
  have : Nonempty (Fin n) := by
    by_contra h; rw [not_nonempty_iff] at h; exact hx.1 (Subsingleton.elim _ _)
  have hcard : Fintype.card (Fin n) = Module.finrank 𝕜 (Fin n → 𝕜) := by simp
  set b := basisOfLinearIndependentOfCardEqFinrank hA.1 hcard
  have hb : ∀ k, b k = v k := fun k => by simp [b]
  -- the coefficients of `x` in the eigenbasis
  set c := b.repr x
  have hx_sum : x = ∑ k, c k • v k := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [hb]
    rfl
  have hzero : ∀ k, c k * (μ k - lam) = 0 := by
    have h : ∑ k, (c k * (μ k - lam)) • v k = 0 := by
      have e1 : A *ᵥ x = ∑ k, (c k * μ k) • v k := by
        rw [hx_sum, mulVec_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mulVec_smul, hA.2 k, smul_smul]
      have e2 : lam • x = ∑ k, (c k * lam) • v k := by
        rw [hx_sum, Finset.smul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, mul_comm]
      simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, ← e1, ← e2, hx.2, sub_self]
    exact Fintype.linearIndependent_iff.mp hA.1 _ h
  have hck : ∀ k, k ≠ i → c k = 0 := fun k hk => by
    have := hzero k
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (huniq k (sub_eq_zero.mp h)) hk
  have hx_i : x = c i • v i := by
    rw [hx_sum, Finset.sum_eq_single i (fun k _ hk => by rw [hck k hk, zero_smul])
      (by simp)]
  refine ⟨c i, fun h0 => hx.1 ?_, hx_i⟩
  rw [hx_i, h0, zero_smul]

/-- **For a nondefective `A` and a simple zero `λ` of `p_n`, `yᵀx ≠ 0`** for right and left
eigenvectors `x`, `y`: `y` annihilates every other eigenvector of the basis. -/
theorem dotProduct_ne_zero_of_simple {A : Matrix (Fin n) (Fin n) 𝕜} {v : Fin n → Fin n → 𝕜}
    {μ : Fin n → 𝕜} (hA : IsNondefective A v μ) {lam : 𝕜}
    (hsimple : A.charpoly.rootMultiplicity lam = 1) {x y : Fin n → 𝕜}
    (hx : IsRightEigen A lam x) (hy : IsLeftEigen A lam y) : y ⬝ᵥ x ≠ 0 := by
  obtain ⟨i, hi, huniq, hall⟩ := eigvec_eq_smul_of_simple hA hsimple
  obtain ⟨c, hc, rfl⟩ := hall x hx
  have hyv : ∀ k, (μ k - lam) * (y ⬝ᵥ v k) = 0 := fun k => by
    have h1 : y ⬝ᵥ (A *ᵥ v k) = μ k * (y ⬝ᵥ v k) := by rw [hA.2 k, dotProduct_smul, smul_eq_mul]
    have h2 : y ⬝ᵥ (A *ᵥ v k) = lam * (y ⬝ᵥ v k) := by
      rw [dotProduct_mulVec, hy.2, smul_dotProduct, smul_eq_mul]
    rw [sub_mul, ← h1, ← h2, sub_self]
  rw [dotProduct_smul, smul_eq_mul]
  refine mul_ne_zero hc fun h0 => hy.1 ?_
  -- `y` is orthogonal (bilinearly) to the whole eigenbasis, hence `y = 0`
  have hall0 : ∀ k, y ⬝ᵥ v k = 0 := fun k => by
    by_cases hk : k = i
    · rw [hk]; exact h0
    · rcases mul_eq_zero.mp (hyv k) with h | h
      · exact absurd (huniq k (sub_eq_zero.mp h)) hk
      · exact h
  have : Nonempty (Fin n) := by
    by_contra h; rw [not_nonempty_iff] at h; exact hy.1 (Subsingleton.elim _ _)
  have hcard : Fintype.card (Fin n) = Module.finrank 𝕜 (Fin n → 𝕜) := by simp
  set b := basisOfLinearIndependentOfCardEqFinrank hA.1 hcard
  have hb : ∀ k, b k = v k := fun k => by simp [b]
  funext j
  have hw := b.sum_repr (Pi.single j 1)
  have : y ⬝ᵥ (Pi.single j 1 : Fin n → 𝕜) = 0 := by
    rw [← hw, dotProduct_sum]
    exact Finset.sum_eq_zero fun k _ => by rw [dotProduct_smul, hb, hall0, smul_zero]
  simpa using this

/-- `|yᵀx| ≤ ‖y‖₂ ‖x‖₂`. -/
theorem norm_dotProduct_le (x y : Fin n → 𝕜) :
    ‖y ⬝ᵥ x‖ ≤ ‖toLp 2 y‖ * ‖toLp 2 x‖ := by
  rw [dlmf_3_2_13_euclidean, dlmf_3_2_13_euclidean]
  calc ‖y ⬝ᵥ x‖ ≤ ∑ i, ‖y i‖ * ‖x i‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_mul _ _).le)
    _ ≤ Real.sqrt (∑ i, ‖y i‖ ^ 2) * Real.sqrt (∑ i, ‖x i‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- **"We always have `κ(λ) ≥ 1`"**, for a simple zero `λ` of `p_n` of a nondefective `A` and
normalized right and left eigenvectors. -/
theorem one_le_eigCond {A : Matrix (Fin n) (Fin n) 𝕜} {v : Fin n → Fin n → 𝕜}
    {μ : Fin n → 𝕜} (hA : IsNondefective A v μ) {lam : 𝕜}
    (hsimple : A.charpoly.rootMultiplicity lam = 1) {x y : Fin n → 𝕜}
    (hx : IsRightEigen A lam x) (hy : IsLeftEigen A lam y) (hxn : ‖toLp 2 x‖ = 1)
    (hyn : ‖toLp 2 y‖ = 1) : 1 ≤ eigCond x y := by
  have hne := dotProduct_ne_zero_of_simple hA hsimple hx hy
  have hle := norm_dotProduct_le x y
  rw [hxn, hyn, mul_one] at hle
  rw [eigCond, le_div_iff₀ (norm_pos_iff.mpr hne), one_mul]
  exact hle

/-- **"`|yᵀx| = |cos θ|`, where `θ` is the angle between `yᵀ` and `x`"** (real normalized
vectors). -/
theorem abs_dotProduct_eq_abs_cos (x y : Fin n → ℝ) (hxn : ‖toLp 2 x‖ = 1)
    (hyn : ‖toLp 2 y‖ = 1) :
    |y ⬝ᵥ x| = |Real.cos (InnerProductGeometry.angle (toLp 2 y) (toLp 2 x))| := by
  have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (toLp 2 y) (toLp 2 x)
  rw [hxn, hyn, mul_one, mul_one] at h
  rw [h, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- **"When `A` is a symmetric matrix, the left and right eigenvectors coincide, yielding
`κ(λ) = 1`"** (real symmetric nondefective `A`, simple `λ`, normalized eigenvectors). -/
theorem eigCond_eq_one_of_symm {A : Matrix (Fin n) (Fin n) ℝ} (hsymm : Aᵀ = A)
    {v : Fin n → Fin n → ℝ} {μ : Fin n → ℝ} (hA : IsNondefective A v μ) {lam : ℝ}
    (hsimple : A.charpoly.rootMultiplicity lam = 1) {x y : Fin n → ℝ}
    (hx : IsRightEigen A lam x) (hy : IsLeftEigen A lam y) (hxn : ‖toLp 2 x‖ = 1)
    (hyn : ‖toLp 2 y‖ = 1) : eigCond x y = 1 := by
  -- `y` is also a right eigenvector, hence a multiple of `x`
  have hy' : IsRightEigen A lam y := by rw [← hsymm]; exact (isLeftEigen_iff A lam y).mp hy
  obtain ⟨i, -, -, hall⟩ := eigvec_eq_smul_of_simple hA hsimple
  obtain ⟨c, hc, hxc⟩ := hall x hx
  obtain ⟨d, -, hyd⟩ := hall y hy'
  have hyx : y = (d / c) • x := by rw [hyd, hxc, smul_smul, div_mul_cancel₀ _ hc]
  have hxx : x ⬝ᵥ x = 1 := by
    have := dlmf_3_2_13_euclidean x
    rw [hxn] at this
    have h2 : ∑ j, ‖x j‖ ^ 2 = 1 := by
      have h0 : 0 ≤ ∑ j, ‖x j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
      nlinarith [Real.sq_sqrt h0]
    simpa [dotProduct, sq] using h2
  have hdc : |d / c| = 1 := by
    have := hyn
    rw [hyx, toLp_smul, norm_smul, hxn, mul_one, Real.norm_eq_abs] at this
    exact this
  rw [eigCond, hyx, smul_dotProduct, hxx, smul_eq_mul, mul_one, Real.norm_eq_abs, hdc, div_one]

end Azurite.DLMF
