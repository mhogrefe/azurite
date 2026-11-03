/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# DLMF §3.2(iii): condition of linear systems

Matrices are `n × n` over `ℝ` or `ℂ` (`RCLike 𝕜`). The vector `p`-norms are Mathlib's `ℓ^p` norms
on `WithLp p (Fin n → 𝕜)`.

* **3.2.13** (`dlmf_3_2_13`, `dlmf_3_2_13_inf`, `dlmf_3_2_13_euclidean`): `(∑ |x_j|^p)^{1/p}`,
  `max_j |x_j|`, and the Euclidean case `p = 2`.
* **3.2.14** (`matNorm`): `‖A‖_p = sup_{x≠0} ‖Ax‖_p/‖x‖_p`, defined literally as that supremum.
  * It is the operator norm of `A` on `ℓ^p` (`matNorm_eq`, `lpCLM`), hence `‖Ax‖ ≤ ‖A‖‖x‖`
    (`matNorm_mulVec_le`).
  * `‖AB‖ ≤ ‖A‖‖B‖` (`matNorm_mul_le`) and `‖I‖ = 1` (`matNorm_one`).
* **3.2.15**:
  * `‖A‖₁` is the largest column sum (`dlmf_3_2_15_one`, attained at a unit vector).
  * `‖A‖_∞` is the largest row sum (`dlmf_3_2_15_inf`, attained at the sign vector of the row).
  * `‖A‖₂ = √ρ(AAᴴ)` (`dlmf_3_2_15_two`; `dlmf_3_2_15_two_real` for `AAᵀ`), with `ρ` the largest
    absolute value of an eigenvalue (`eigRadius`, `mem_spectrum_iff_eigen`). The proof uses the
    C*-identity `‖AAᴴ‖ = ‖A‖₂²` and the spectral radius of a self-adjoint operator (Mathlib).
* **3.2.16** (`condNum`): `κ(A) = ‖A‖_p ‖A⁻¹‖_p`, and "`κ(A) ≥ 1` for any norm (3.2.14)"
  (`one_le_condNum`, nonsingular `A`, `n ≥ 1`).
* **3.2.17** (`dlmf_3_2_17`): the a posteriori bound `‖x* − x‖/‖x‖ ≤ κ(A)‖r‖/‖b‖`,
  `r = b − Ax*`.

"The larger the value `κ(A)`, the more ill-conditioned the system" is the interpretation of 3.2.17
and is not formalized separately.
-/

namespace Azurite.DLMF

open scoped ENNReal Matrix NNReal
open WithLp Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-! ### Vector norms 3.2.13 -/

/-- **DLMF 3.2.13**: the `p`-norm `(∑ |x_j|^p)^{1/p}`, `p = 1, 2, …` (Mathlib's `PiLp` norm). -/
theorem dlmf_3_2_13 (p : ℕ) (hp : 1 ≤ p) (x : Fin n → 𝕜) :
    ‖toLp (p : ℝ≥0∞) x‖ = (∑ j, ‖x j‖ ^ p) ^ (1 / (p : ℝ)) := by
  rw [PiLp.norm_eq_sum (by simp; omega)]
  simp [Real.rpow_natCast]

/-- **DLMF 3.2.13**: `‖x‖_∞ = max_j |x_j|`. -/
theorem dlmf_3_2_13_inf (x : Fin n → 𝕜) : ‖toLp ∞ x‖ = ⨆ j, ‖x j‖ :=
  PiLp.norm_eq_ciSup _

/-- "The Euclidean norm is the case `p = 2`": `‖x‖₂ = (∑ |x_j|²)^{1/2}`. -/
theorem dlmf_3_2_13_euclidean (x : Fin n → 𝕜) : ‖toLp 2 x‖ = Real.sqrt (∑ j, ‖x j‖ ^ 2) :=
  EuclideanSpace.norm_eq _

/-! ### Matrix norms 3.2.14 -/

/-- **DLMF 3.2.14**: `‖A‖_p = max_{x ≠ 0} ‖Ax‖_p/‖x‖_p` (as a supremum). -/
noncomputable def matNorm (p : ℝ≥0∞) (A : Matrix (Fin n) (Fin n) 𝕜) : ℝ :=
  ⨆ x : {x : Fin n → 𝕜 // x ≠ 0}, ‖toLp p (A *ᵥ x.1)‖ / ‖toLp p x.1‖

/-- The operator of `A` on `ℓ^p`. -/
noncomputable def lpCLM (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin n) (Fin n) 𝕜) :
    WithLp p (Fin n → 𝕜) →L[𝕜] WithLp p (Fin n → 𝕜) :=
  LinearMap.toContinuousLinearMap (toLpLin p p A)

theorem lpCLM_toLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin n) (Fin n) 𝕜) (x : Fin n → 𝕜) :
    lpCLM p A (toLp p x) = toLp p (A *ᵥ x) := by
  simp [lpCLM, toLpLin_toLp, Matrix.toLin'_apply]

/-- The supremum 3.2.14 is the operator norm on `ℓ^p`. -/
theorem matNorm_eq (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin n) (Fin n) 𝕜) :
    matNorm p A = ‖lpCLM p A‖ := by
  set T := lpCLM p A
  have hratio : ∀ x : {x : Fin n → 𝕜 // x ≠ 0},
      ‖toLp p (A *ᵥ x.1)‖ / ‖toLp p x.1‖ ≤ ‖T‖ := by
    intro x
    have hx : 0 < ‖toLp p x.1‖ := norm_pos_iff.mpr fun h => x.2 (by simpa using h)
    rw [div_le_iff₀ hx, ← lpCLM_toLp]
    exact T.le_opNorm _
  have hbdd : BddAbove (Set.range fun x : {x : Fin n → 𝕜 // x ≠ 0} =>
      ‖toLp p (A *ᵥ x.1)‖ / ‖toLp p x.1‖) := ⟨‖T‖, by rintro _ ⟨x, rfl⟩; exact hratio x⟩
  have hnn : 0 ≤ matNorm p A := Real.iSup_nonneg fun x => by positivity
  apply le_antisymm
  · rcases isEmpty_or_nonempty {x : Fin n → 𝕜 // x ≠ 0} with h | h
    · rw [matNorm, Real.iSup_of_isEmpty]; exact norm_nonneg _
    · exact ciSup_le hratio
  · refine T.opNorm_le_bound hnn fun y => ?_
    by_cases hy : y = 0
    · simp [hy]
    · have hy' : ofLp y ≠ 0 := fun h => hy (by simpa using congrArg (toLp p) h)
      have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have := le_ciSup hbdd ⟨ofLp y, hy'⟩
      simp only [toLp_ofLp] at this
      rw [← div_le_iff₀ hpos]
      calc ‖T y‖ / ‖y‖ = ‖toLp p (A *ᵥ ofLp y)‖ / ‖y‖ := by
            rw [← lpCLM_toLp, toLp_ofLp]
        _ ≤ _ := this

theorem matNorm_mulVec_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin n) (Fin n) 𝕜)
    (x : Fin n → 𝕜) : ‖toLp p (A *ᵥ x)‖ ≤ matNorm p A * ‖toLp p x‖ := by
  rw [matNorm_eq, ← lpCLM_toLp]; exact (lpCLM p A).le_opNorm _

theorem lpCLM_mul (p : ℝ≥0∞) [Fact (1 ≤ p)] (A B : Matrix (Fin n) (Fin n) 𝕜) :
    lpCLM p (A * B) = (lpCLM p A).comp (lpCLM p B) := by
  ext x : 1
  simp [lpCLM, toLpLin_mul_same]

theorem matNorm_mul_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (A B : Matrix (Fin n) (Fin n) 𝕜) :
    matNorm p (A * B) ≤ matNorm p A * matNorm p B := by
  simp only [matNorm_eq, lpCLM_mul]
  exact (lpCLM p A).opNorm_comp_le _

theorem matNorm_one (p : ℝ≥0∞) [Fact (1 ≤ p)] (hn : 0 < n) :
    matNorm p (1 : Matrix (Fin n) (Fin n) 𝕜) = 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [matNorm_eq]
  have h : lpCLM p (1 : Matrix (Fin n) (Fin n) 𝕜) = ContinuousLinearMap.id 𝕜 _ := by
    ext x : 1; simp [lpCLM, toLpLin_one]
  rw [h]
  exact ContinuousLinearMap.norm_id

/-! ### The condition number 3.2.16 and the a posteriori bound 3.2.17 -/

/-- **DLMF 3.2.16**: `κ(A) = ‖A‖_p ‖A^{−1}‖_p`. -/
noncomputable def condNum (p : ℝ≥0∞) (A : Matrix (Fin n) (Fin n) 𝕜) : ℝ :=
  matNorm p A * matNorm p A⁻¹

/-- **"For any norm (3.2.14) we have `κ(A) ≥ 1`"** (nonsingular `A`, `n ≥ 1`). -/
theorem one_le_condNum (p : ℝ≥0∞) [Fact (1 ≤ p)] (hn : 0 < n) {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : IsUnit A.det) : 1 ≤ condNum p A := by
  rw [condNum, ← matNorm_one p (𝕜 := 𝕜) hn, ← Matrix.mul_nonsing_inv A hA]
  exact matNorm_mul_le p A A⁻¹

/-- **DLMF 3.2.17**: the a posteriori bound `‖x* − x‖/‖x‖ ≤ κ(A) ‖r‖/‖b‖` for the solution
`x` of `Ax = b ≠ 0`, a computed `x*`, and the residual `r = b − Ax*`. -/
theorem dlmf_3_2_17 (p : ℝ≥0∞) [Fact (1 ≤ p)] {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : IsUnit A.det) {x xs b : Fin n → 𝕜} (hx : A *ᵥ x = b) (hb : b ≠ 0) :
    ‖toLp p (xs - x)‖ / ‖toLp p x‖ ≤
      condNum p A * (‖toLp p (b - A *ᵥ xs)‖ / ‖toLp p b‖) := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx; exact hb hx.symm
  have hxpos : 0 < ‖toLp p x‖ := norm_pos_iff.mpr fun h => hx0 (by simpa using h)
  have hbpos : 0 < ‖toLp p b‖ := norm_pos_iff.mpr fun h => hb (by simpa using h)
  -- `x* − x = −A⁻¹ r`
  have he : xs - x = -(A⁻¹ *ᵥ (b - A *ᵥ xs)) := by
    rw [Matrix.mulVec_sub, ← hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA,
      Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]
    abel
  have h1 : ‖toLp p (xs - x)‖ ≤ matNorm p A⁻¹ * ‖toLp p (b - A *ᵥ xs)‖ := by
    rw [he, toLp_neg, norm_neg]; exact matNorm_mulVec_le p A⁻¹ _
  have h2 : ‖toLp p b‖ ≤ matNorm p A * ‖toLp p x‖ := hx ▸ matNorm_mulVec_le p A x
  have hA0 : 0 ≤ matNorm p A := by rw [matNorm_eq]; exact norm_nonneg _
  have hAi0 : 0 ≤ matNorm p A⁻¹ := by rw [matNorm_eq]; exact norm_nonneg _
  rw [div_le_iff₀ hxpos, condNum]
  calc ‖toLp p (xs - x)‖ ≤ matNorm p A⁻¹ * ‖toLp p (b - A *ᵥ xs)‖ := h1
    _ = matNorm p A⁻¹ * ‖toLp p (b - A *ᵥ xs)‖ / ‖toLp p b‖ * ‖toLp p b‖ := by
        field_simp
    _ ≤ matNorm p A⁻¹ * ‖toLp p (b - A *ᵥ xs)‖ / ‖toLp p b‖ * (matNorm p A * ‖toLp p x‖) := by
        gcongr
    _ = _ := by ring

/-! ### The norms 3.2.15 -/

theorem norm_toLp_one (x : Fin n → 𝕜) : ‖toLp 1 x‖ = ∑ j, ‖x j‖ := by
  rw [PiLp.norm_eq_sum (by simp)]
  simp

/-- **DLMF 3.2.15**: `‖A‖₁ = max_k ∑_j |a_{jk}|` (the largest column sum). -/
theorem dlmf_3_2_15_one (A : Matrix (Fin n) (Fin n) 𝕜) :
    matNorm 1 A = ⨆ k, ∑ j, ‖A j k‖ := by
  rw [matNorm_eq]
  set T := lpCLM 1 A
  set M := ⨆ k, ∑ j, ‖A j k‖
  have hbdd : BddAbove (Set.range fun k => ∑ j, ‖A j k‖) := Set.finite_range _ |>.bddAbove
  have hM : ∀ k, ∑ j, ‖A j k‖ ≤ M := fun k => le_ciSup hbdd k
  have hM0 : 0 ≤ M := Real.iSup_nonneg fun k => Finset.sum_nonneg fun j _ => norm_nonneg _
  apply le_antisymm
  · refine T.opNorm_le_bound hM0 fun y => ?_
    rw [show y = toLp 1 (ofLp y) from (toLp_ofLp _ y).symm, lpCLM_toLp, norm_toLp_one,
      norm_toLp_one]
    calc ∑ j, ‖(A *ᵥ ofLp y) j‖ ≤ ∑ j, ∑ k, ‖A j k‖ * ‖ofLp y k‖ :=
          Finset.sum_le_sum fun j _ => by
            rw [show (A *ᵥ ofLp y) j = ∑ k, A j k * ofLp y k from rfl]
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_mul _ _).le)
      _ = ∑ k, (∑ j, ‖A j k‖) * ‖ofLp y k‖ := by
          rw [Finset.sum_comm]; simp [Finset.sum_mul]
      _ ≤ ∑ k, M * ‖ofLp y k‖ := Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (hM k) (norm_nonneg _)
      _ = M * ∑ k, ‖ofLp y k‖ := by rw [Finset.mul_sum]
  · rcases isEmpty_or_nonempty (Fin n) with h | h
    · rw [show M = 0 from Real.iSup_of_isEmpty _]; exact norm_nonneg _
    · refine ciSup_le fun k => ?_
      have h1 := T.le_opNorm (toLp 1 (Pi.single k 1))
      rw [lpCLM_toLp, norm_toLp_one, norm_toLp_one, Matrix.mulVec_single_one] at h1
      have h2 : ∑ j, ‖(Pi.single k (1 : 𝕜) : Fin n → 𝕜) j‖ = 1 := by
        rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]; simp
      rw [h2, mul_one] at h1
      simpa [Matrix.col] using h1

/-- **DLMF 3.2.15**: `‖A‖_∞ = max_j ∑_k |a_{jk}|` (the largest row sum). -/
theorem dlmf_3_2_15_inf (A : Matrix (Fin n) (Fin n) 𝕜) :
    matNorm ∞ A = ⨆ j, ∑ k, ‖A j k‖ := by
  rw [matNorm_eq]
  set T := lpCLM ∞ A
  set M := ⨆ j, ∑ k, ‖A j k‖
  have hbdd : BddAbove (Set.range fun j => ∑ k, ‖A j k‖) := Set.finite_range _ |>.bddAbove
  have hM : ∀ j, ∑ k, ‖A j k‖ ≤ M := fun j => le_ciSup hbdd j
  have hM0 : 0 ≤ M := Real.iSup_nonneg fun j => Finset.sum_nonneg fun k _ => norm_nonneg _
  apply le_antisymm
  · refine T.opNorm_le_bound hM0 fun y => ?_
    rw [show y = toLp ∞ (ofLp y) from (toLp_ofLp _ y).symm, lpCLM_toLp, dlmf_3_2_13_inf]
    rcases isEmpty_or_nonempty (Fin n) with h | h
    · rw [Real.iSup_of_isEmpty]; positivity
    refine ciSup_le fun j => ?_
    calc ‖(A *ᵥ ofLp y) j‖ ≤ ∑ k, ‖A j k‖ * ‖ofLp y k‖ := by
          rw [show (A *ᵥ ofLp y) j = ∑ k, A j k * ofLp y k from rfl]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_mul _ _).le)
      _ ≤ ∑ k, ‖A j k‖ * ‖toLp ∞ (ofLp y)‖ := Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (by simpa using PiLp.norm_apply_le (toLp ∞ (ofLp y)) k)
            (norm_nonneg _)
      _ = (∑ k, ‖A j k‖) * ‖toLp ∞ (ofLp y)‖ := by rw [Finset.sum_mul]
      _ ≤ M * ‖toLp ∞ (ofLp y)‖ := mul_le_mul_of_nonneg_right (hM j) (norm_nonneg _)
  · rcases isEmpty_or_nonempty (Fin n) with h | h
    · rw [show M = 0 from Real.iSup_of_isEmpty _]; exact norm_nonneg _
    refine ciSup_le fun j => ?_
    -- the sign vector of row `j`
    set s : Fin n → 𝕜 := fun k => if A j k = 0 then 0 else starRingEnd 𝕜 (A j k) / ‖A j k‖
    have hs : ‖toLp ∞ s‖ ≤ 1 := by
      rw [dlmf_3_2_13_inf]
      refine ciSup_le fun k => ?_
      simp only [s]
      split_ifs with h0
      · simp
      · rw [norm_div, RCLike.norm_conj, RCLike.norm_ofReal, abs_norm,
          div_self (norm_ne_zero_iff.mpr h0)]
    have hrow : (A *ᵥ s) j = ((∑ k, ‖A j k‖ : ℝ) : 𝕜) := by
      simp only [Matrix.mulVec, dotProduct, s]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs with h0
      · simp [h0]
      · have hn : (‖A j k‖ : 𝕜) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
        rw [mul_div_assoc', RCLike.mul_conj]
        field_simp
    have h1 := T.le_opNorm (toLp ∞ s)
    rw [lpCLM_toLp] at h1
    calc ∑ k, ‖A j k‖ = ‖(A *ᵥ s) j‖ := by
          rw [hrow, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)]
      _ ≤ ‖toLp ∞ (A *ᵥ s)‖ := by simpa using PiLp.norm_apply_le (toLp ∞ (A *ᵥ s)) j
      _ ≤ ‖T‖ * ‖toLp ∞ s‖ := h1
      _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left hs (norm_nonneg _)
      _ = ‖T‖ := mul_one _

/-- `ρ(M)`: the largest of the absolute values of the eigenvalues of `M`. -/
noncomputable def eigRadius (M : Matrix (Fin n) (Fin n) 𝕜) : ℝ :=
  sSup ((fun μ : 𝕜 => ‖μ‖) '' {μ | ∃ v : Fin n → 𝕜, v ≠ 0 ∧ M *ᵥ v = μ • v})

theorem mem_spectrum_iff_eigen (M : Matrix (Fin n) (Fin n) 𝕜) (μ : 𝕜) :
    μ ∈ spectrum 𝕜 M ↔ ∃ v : Fin n → 𝕜, v ≠ 0 ∧ M *ᵥ v = μ • v := by
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum,
    Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff]
  simp only [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  exact ⟨fun ⟨v, h1, h2⟩ => ⟨v, h2, h1⟩, fun ⟨v, h1, h2⟩ => ⟨v, h2, h1⟩⟩

open scoped Matrix.Norms.L2Operator in
/-- **DLMF 3.2.15**: `‖A‖₂ = √ρ(AAᴴ)` (`Aᴴ = Aᵀ` for real `A`). -/
theorem dlmf_3_2_15_two (A : Matrix (Fin n) (Fin n) 𝕜) :
    matNorm 2 A = Real.sqrt (eigRadius (A * Aᴴ)) := by
  have h2 : matNorm 2 A = ‖A‖ := by rw [matNorm_eq]; rfl
  set H := A * Aᴴ
  set T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕜) H
  have hsa : IsSelfAdjoint T := by
    have : IsSelfAdjoint H := by
      simpa [H, Matrix.star_eq_conjTranspose] using IsSelfAdjoint.star_mul_self Aᴴ
    exact this.map _
  have hrad := T.spectralRadius_eq_nnnorm hsa
  have hspec : spectrum 𝕜 T = spectrum 𝕜 H := AlgEquiv.spectrum_eq
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕜)) H
  have hT : ‖T‖ = ‖A‖ * ‖A‖ := by
    rw [Matrix.l2_opNorm_toEuclideanCLM, show H = (Aᴴ)ᴴ * Aᴴ by simp [H],
      Matrix.l2_opNorm_conjTranspose_mul_self, Matrix.l2_opNorm_conjTranspose]
  -- `ρ(H) = ‖T‖`
  set S := (fun μ : 𝕜 => ‖μ‖) '' {μ | ∃ v : Fin n → 𝕜, v ≠ 0 ∧ H *ᵥ v = μ • v}
  have hmem : ∀ μ : 𝕜, μ ∈ spectrum 𝕜 T ↔ ∃ v : Fin n → 𝕜, v ≠ 0 ∧ H *ᵥ v = μ • v := fun μ => by
    rw [hspec, mem_spectrum_iff_eigen]
  have hle : ∀ μ ∈ spectrum 𝕜 T, ‖μ‖ ≤ ‖T‖ := by
    intro μ hμ
    have : (‖μ‖₊ : ℝ≥0∞) ≤ spectralRadius 𝕜 T :=
      le_iSup₂ (f := fun k (_ : k ∈ quasispectrum 𝕜 T) => (‖k‖₊ : ℝ≥0∞)) μ
        (spectrum_subset_quasispectrum 𝕜 T hμ)
    rw [hrad] at this
    exact_mod_cast this
  have hS : sSup S = ‖T‖ := by
    have hS0 : 0 ≤ sSup S := Real.sSup_nonneg fun y ⟨μ, _, hy⟩ => hy ▸ norm_nonneg _
    have hbdd : BddAbove S := ⟨‖T‖, by rintro _ ⟨μ, hμ, rfl⟩; exact hle μ ((hmem μ).mpr hμ)⟩
    apply le_antisymm
    · exact Real.sSup_le (by rintro _ ⟨μ, hμ, rfl⟩; exact hle μ ((hmem μ).mpr hμ))
        (norm_nonneg _)
    · have : (‖T‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (sSup S) := by
        rw [← hrad]
        refine iSup₂_le fun k hk => ?_
        rw [← enorm_eq_nnnorm, ← ofReal_norm]
        rcases (quasispectrum_eq_spectrum_union_zero 𝕜 T ▸ hk) with hk | hk
        · exact ENNReal.ofReal_le_ofReal (le_csSup hbdd ⟨k, (hmem k).mp hk, rfl⟩)
        · rw [Set.mem_singleton_iff.mp hk, norm_zero]; exact ENNReal.ofReal_le_ofReal hS0
      rw [ENNReal.le_ofReal_iff_toReal_le ENNReal.coe_ne_top hS0] at this
      simpa using this
  rw [h2, eigRadius, show (fun μ : 𝕜 => ‖μ‖) '' {μ | ∃ v : Fin n → 𝕜, v ≠ 0 ∧ H *ᵥ v = μ • v}
    = S from rfl, hS, hT, Real.sqrt_mul_self (norm_nonneg _)]

/-- **DLMF 3.2.15** for real matrices, in the DLMF's form `‖A‖₂ = √ρ(AAᵀ)`. -/
theorem dlmf_3_2_15_two_real (A : Matrix (Fin n) (Fin n) ℝ) :
    matNorm 2 A = Real.sqrt (eigRadius (A * Aᵀ)) := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact dlmf_3_2_15_two A

end Azurite.DLMF
