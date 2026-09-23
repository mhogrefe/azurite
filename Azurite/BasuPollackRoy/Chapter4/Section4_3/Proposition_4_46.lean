/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_1.EuclideanBall
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# BPR §4.3.2: subdiscriminants of symmetric matrices; the trace scalar product

We set up Hermite's quadratic form. For a symmetric `p × p` matrix `M`, the `k`-th
subdiscriminant `sDisc_k(M)` is the determinant of the trace–Hankel matrix `Newt_k(M)`
with `(i,j)`-entry `Tr(M^{i+j-2})` (the Newton sums of `CharPol(M)` are the traces
`Tr(M^i)`).

On the space `Sym(p)` of symmetric matrices, the map `(A,B) ↦ Tr(A·B)` is a scalar
product (Proposition 4.46), with orthonormal basis `E`: `E_{j,j} = F_{j,j}` and
`E_{j,ℓ} = (1/√2)(F_{j,ℓ} + F_{ℓ,j})` for `ℓ > j`, where `F_{j,ℓ}` is the matrix with a
single `1` at `(j,ℓ)`.
-/

namespace Azurite.BPR.Chapter4

open scoped Matrix
open Matrix

/-! ### Matrix subdiscriminant via Newton sums (traces) -/

section Ring

variable {p : ℕ} {D : Type*} [CommRing D]

/-- The `(p−k) × (p−k)` trace–Hankel matrix `Newt_k(M)`: its `(i,j)`-entry is
`Tr(M^{i+j})` (0-indexed), i.e. `Tr(M^{i+j-2})` for `i,j = 1,…,p−k`. -/
def traceNewtMatrix (k : ℕ) (M : Matrix (Fin p) (Fin p) D) :
    Matrix (Fin (p - k)) (Fin (p - k)) D :=
  Matrix.of fun i j => Matrix.trace (M ^ ((i : ℕ) + (j : ℕ)))

/-- `sDisc_k(M)` for a symmetric matrix `M`: the determinant of the trace–Hankel matrix
`Newt_k(M)`. -/
def sDiscOfMatrix (k : ℕ) (M : Matrix (Fin p) (Fin p) D) : D :=
  (traceNewtMatrix k M).det

end Ring

/-! ### The trace scalar product on `Sym(p)` -/

section ScalarProduct

variable {p : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- The trace bilinear form `⟨A, B⟩ = Tr(A · B)` on `p × p` matrices over `R`. -/
noncomputable def traceBilin : LinearMap.BilinForm R (Matrix (Fin p) (Fin p) R) :=
  LinearMap.mk₂ R (fun A B => Matrix.trace (A * B))
    (fun A A' B => by rw [add_mul, Matrix.trace_add])
    (fun c A B => by rw [Matrix.smul_mul, Matrix.trace_smul])
    (fun A B B' => by rw [mul_add, Matrix.trace_add])
    (fun c A B => by rw [Matrix.mul_smul, Matrix.trace_smul])

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
@[simp] theorem traceBilin_apply (A B : Matrix (Fin p) (Fin p) R) :
    traceBilin A B = Matrix.trace (A * B) := rfl

/-- The submodule `Sym(p)` of symmetric `p × p` matrices. -/
def symmMatrices : Submodule R (Matrix (Fin p) (Fin p) R) where
  carrier := {M | M.IsSymm}
  add_mem' {a b} ha hb := show (a + b)ᵀ = a + b by rw [transpose_add, ha, hb]
  zero_mem' := Matrix.isSymm_zero
  smul_mem' c a ha := show (c • a)ᵀ = c • a by rw [transpose_smul, ha]

/-- `F_{j,ℓ}`: the matrix with a single `1` at `(j,ℓ)`. -/
def Fsm (j ℓ : Fin p) : Matrix (Fin p) (Fin p) R := Matrix.single j ℓ 1

/-- The basis matrix `E_{j,ℓ}` of `Sym(p)`: `E_{j,j} = F_{j,j}`, and
`E_{j,ℓ} = (1/√2)(F_{j,ℓ} + F_{ℓ,j})` for `ℓ ≠ j`. -/
noncomputable def Esm (j ℓ : Fin p) : Matrix (Fin p) (Fin p) R :=
  if j = ℓ then Fsm j j else (Azurite.BPR.sqrt (2 : R))⁻¹ • (Fsm j ℓ + Fsm ℓ j)

/-- Index set for `E`: the upper-triangular pairs `(j,ℓ)` with `j ≤ ℓ`. -/
abbrev STri (p : ℕ) := { q : Fin p × Fin p // q.1 ≤ q.2 }

/-- The orthonormal family `E`, indexed by upper-triangular pairs. -/
noncomputable def E (q : STri p) : Matrix (Fin p) (Fin p) R := Esm (R := R) q.val.1 q.val.2

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- `Tr(A·A) = ∑ᵢⱼ (Aᵢⱼ)²` for a symmetric matrix `A`. -/
private lemma traceBilin_self (A : Matrix (Fin p) (Fin p) R) (hA : A.IsSymm) :
    traceBilin A A = ∑ i, ∑ j, (A i j) ^ 2 := by
  rw [traceBilin_apply, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hA.apply i j, sq]

/-- `√2 ≠ 0` in `R`. -/
private lemma sqrt_two_ne_zero : (Azurite.BPR.sqrt (2 : R)) ≠ 0 := by
  intro h
  have : (Azurite.BPR.sqrt (2 : R)) ^ 2 = 2 := Azurite.BPR.sq_sqrt (by norm_num)
  rw [h] at this
  norm_num at this

/-- `((√2)⁻¹)² = 1/2` in `R`. -/
private lemma inv_sqrt_two_sq : ((Azurite.BPR.sqrt (2 : R))⁻¹) ^ 2 = (2 : R)⁻¹ := by
  rw [inv_pow, Azurite.BPR.sq_sqrt (by norm_num : (0:R) ≤ 2)]

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Trace of a product of two single matrices. -/
private lemma trace_Fsm_mul (a b c d : Fin p) :
    traceBilin (Fsm a b : Matrix (Fin p) (Fin p) R) (Fsm c d)
      = if b = c ∧ a = d then 1 else 0 := by
  rw [traceBilin_apply, Fsm, Fsm]
  by_cases hbc : b = c
  · subst hbc
    rw [Matrix.single_mul_single_same, mul_one]
    by_cases had : a = d
    · subst had
      rw [Matrix.trace_single_eq_same, ite_eq_left ⟨rfl, rfl⟩]
    · rw [Matrix.trace_single_eq_of_ne a d 1 had, ite_eq_right (by simp [had])]
  · rw [Matrix.single_mul_single_of_ne 1 a b c hbc 1, Matrix.trace_zero, ite_eq_right (by simp [hbc])]

/-- `Esm j ℓ` is a symmetric matrix. -/
private lemma Esm_isSymm (j ℓ : Fin p) : (Esm (R := R) j ℓ).IsSymm := by
  rw [Matrix.IsSymm, Esm]
  by_cases h : j = ℓ
  · subst h; rw [ite_eq_left rfl, Fsm, Matrix.transpose_single]
  · rw [ite_eq_right h, transpose_smul, transpose_add, Fsm, Fsm, Matrix.transpose_single,
      Matrix.transpose_single, add_comm]

/-- Bilinear expansion: `traceBilin` of `Esm` matrices. -/
private lemma trace_Esm (j ℓ j' ℓ' : Fin p) (hjl : j ≤ ℓ) (hj'l' : j' ≤ ℓ') :
    traceBilin (Esm (R := R) j ℓ) (Esm (R := R) j' ℓ')
      = if j = j' ∧ ℓ = ℓ' then 1 else 0 := by
  have hsmulL : ∀ (c : R) (A B : Matrix (Fin p) (Fin p) R),
      traceBilin (c • A) B = c * traceBilin A B := fun c A B => by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hsmulR : ∀ (c : R) (A B : Matrix (Fin p) (Fin p) R),
      traceBilin A (c • B) = c * traceBilin A B := fun c A B => by
    rw [map_smul, smul_eq_mul]
  have haddL : ∀ (A A' B : Matrix (Fin p) (Fin p) R),
      traceBilin (A + A') B = traceBilin A B + traceBilin A' B := fun A A' B => by
    rw [map_add, LinearMap.add_apply]
  have haddR : ∀ (A B B' : Matrix (Fin p) (Fin p) R),
      traceBilin A (B + B') = traceBilin A B + traceBilin A B' := fun A B B' => by
    rw [map_add]
  by_cases hd : j = ℓ <;> by_cases hd' : j' = ℓ'
  · -- diag, diag
    subst hd; subst hd'
    rw [Esm, ite_eq_left rfl, Esm, ite_eq_left rfl, trace_Fsm_mul]
  · -- diag, off-diag
    subst hd
    rw [Esm, ite_eq_left rfl, Esm, ite_eq_right hd', hsmulR, haddR, trace_Fsm_mul, trace_Fsm_mul]
    split_ifs <;> first | (exfalso; omega) | ring
  · -- off-diag, diag
    subst hd'
    rw [Esm, ite_eq_right hd, Esm, ite_eq_left rfl, hsmulL, haddL, trace_Fsm_mul, trace_Fsm_mul]
    split_ifs <;> first | (exfalso; omega) | ring
  · -- off-diag, off-diag
    rw [Esm, ite_eq_right hd, Esm, ite_eq_right hd', hsmulL, hsmulR, haddL, haddR, haddR,
      trace_Fsm_mul, trace_Fsm_mul, trace_Fsm_mul, trace_Fsm_mul]
    -- terms: (ℓ=j'∧j=ℓ'), (ℓ=ℓ'∧j=j'), (j=j'∧ℓ=ℓ'), (j=ℓ'∧ℓ=j')
    have hlt : j < ℓ := lt_of_le_of_ne hjl hd
    have hlt' : j' < ℓ' := lt_of_le_of_ne hj'l' hd'
    have h2 : ((Azurite.BPR.sqrt (2:R))⁻¹) * ((Azurite.BPR.sqrt (2:R))⁻¹) = (2:R)⁻¹ := by
      rw [← sq, inv_sqrt_two_sq]
    split_ifs <;> (
      first
      | (exfalso; omega)
      | (rw [show (0:R) + 1 + (1 + 0) = 2 by ring, ← mul_assoc, h2, mul_comm]; norm_num)
      | ring)

/-- The coefficient of `E q` when expanding a symmetric matrix `X` in the basis `E`. -/
private noncomputable def Ecoeff (X : Matrix (Fin p) (Fin p) R) (q : STri p) : R :=
  if q.val.1 = q.val.2 then X q.val.1 q.val.1 else (Azurite.BPR.sqrt (2 : R)) * X q.val.1 q.val.2

/-- Entry `(r,s)` of `Esm j ℓ` for `j ≤ ℓ`. -/
private lemma Esm_apply (j ℓ r s : Fin p) :
    (Esm (R := R) j ℓ) r s
      = if j = ℓ then (if j = r ∧ j = s then (1 : R) else 0)
        else (Azurite.BPR.sqrt (2 : R))⁻¹
          * ((if j = r ∧ ℓ = s then (1 : R) else 0) + (if ℓ = r ∧ j = s then 1 else 0)) := by
  rw [Esm]
  by_cases h : j = ℓ
  · subst h; rw [ite_eq_left rfl, ite_eq_left rfl, Fsm, Matrix.single_apply]
  · rw [ite_eq_right h, ite_eq_right h, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
      Fsm, Fsm, Matrix.single_apply, Matrix.single_apply]

/-- A symmetric matrix expands as `∑ q, Ecoeff X q • E q`. -/
private lemma symm_eq_sum_Ecoeff (X : Matrix (Fin p) (Fin p) R) (hX : X.IsSymm) :
    X = ∑ q : STri p, Ecoeff X q • E q := by
  have hs2 : (Azurite.BPR.sqrt (2:R)) * (Azurite.BPR.sqrt (2:R))⁻¹ = 1 :=
    mul_inv_cancel₀ sqrt_two_ne_zero
  ext r s
  rw [Matrix.sum_apply]
  -- only the pair (min r s, max r s) contributes
  set q₀ : STri p := ⟨(min r s, max r s), min_le_max⟩ with hq₀
  rw [Finset.sum_eq_single q₀]
  · -- the q₀ term equals X r s
    have hsne : (Azurite.BPR.sqrt (2:R)) ≠ 0 := sqrt_two_ne_zero
    rw [Matrix.smul_apply, smul_eq_mul, E, hq₀, Ecoeff, Esm_apply]
    rcases le_total r s with hrs | hrs
    · -- r ≤ s : min = r, max = s
      simp only [min_eq_left hrs, max_eq_right hrs]
      by_cases h : r = s
      · subst h; simp
      · simp only [h, ite_false, and_false, ite_true, and_true, mul_one, add_zero]
        field_simp
    · -- s ≤ r : min = s, max = r
      simp only [min_eq_right hrs, max_eq_left hrs]
      by_cases h : s = r
      · subst h; simp
      · simp only [h, ite_false, false_and, ite_true, and_true, mul_one, zero_add, hX.apply s r]
        field_simp
  · -- other terms vanish
    intro q _ hq
    rw [Matrix.smul_apply, smul_eq_mul, E, Esm_apply]
    obtain ⟨⟨j, ℓ⟩, hjl⟩ := q
    simp only at hq ⊢
    by_cases hd : j = ℓ
    · subst hd
      rw [ite_eq_left rfl, ite_eq_right ?_, mul_zero]
      rintro ⟨rfl, rfl⟩
      exact hq (by rw [hq₀, Subtype.ext_iff]; simp [min_self, max_self])
    · rw [ite_eq_right hd]
      have e1 : (if j = r ∧ ℓ = s then (1:R) else 0) = 0 := by
        rw [ite_eq_right]; rintro ⟨rfl, rfl⟩
        exact hq (by rw [hq₀, Subtype.ext_iff]; simp [min_eq_left hjl, max_eq_right hjl])
      have e2 : (if ℓ = r ∧ j = s then (1:R) else 0) = 0 := by
        rw [ite_eq_right]; rintro ⟨rfl, rfl⟩
        exact hq (by rw [hq₀, Subtype.ext_iff]; simp [min_eq_right hjl, max_eq_left hjl])
      rw [e1, e2, add_zero, mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ q₀) h

/-- Orthonormality of the family `E`. -/
private lemma traceBilin_E (a b : STri p) :
    traceBilin (E a : Matrix (Fin p) (Fin p) R) (E b) = if a = b then 1 else 0 := by
  obtain ⟨⟨j, ℓ⟩, hjl⟩ := a
  obtain ⟨⟨j', ℓ'⟩, hj'l'⟩ := b
  rw [E, E, trace_Esm j ℓ j' ℓ' hjl hj'l']
  congr 1
  rw [eq_iff_iff, Subtype.ext_iff, Prod.ext_iff]

/-- **Proposition 4.46.** The map `(A,B) ↦ Tr(A·B)` is a scalar product on `Sym(p)`
(a symmetric, positive-definite bilinear form) with orthonormal basis `E`. -/
theorem proposition_4_46 :
    (traceBilin : LinearMap.BilinForm R (Matrix (Fin p) (Fin p) R)).IsSymm ∧
    (∀ A : Matrix (Fin p) (Fin p) R, A.IsSymm → A ≠ 0 → 0 < traceBilin A A) ∧
    (∀ a b : STri p, traceBilin (E a : Matrix (Fin p) (Fin p) R) (E b : Matrix (Fin p) (Fin p) R)
        = if a = b then 1 else 0) ∧
    ∃ B : Module.Basis (STri p) R (symmMatrices (p := p) (R := R)),
      ∀ a, ((B a : Matrix (Fin p) (Fin p) R)) = (E a : Matrix (Fin p) (Fin p) R) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Conjunct 1: symmetry
    refine ⟨fun x y => ?_⟩
    simp only [traceBilin_apply]
    exact Matrix.trace_mul_comm x y
  · -- Conjunct 2: positive-definiteness on symmetric matrices
    intro A hA hne
    rw [traceBilin_self A hA]
    -- some entry is nonzero
    obtain ⟨i, hi⟩ : ∃ i, ∑ j, (A i j) ^ 2 ≠ 0 := by
      by_contra h
      push Not at h
      apply hne
      ext i j
      have hsum := h i
      have : (A i j) ^ 2 = 0 := by
        refine (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg _)).mp hsum j (Finset.mem_univ j)
      simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
    refine (Finset.sum_nonneg fun j _ => sq_nonneg _).lt_of_ne (Ne.symm hi)
  · -- Conjunct 3: orthonormality
    exact traceBilin_E
  · -- Conjunct 4: basis
    -- the candidate family inside the submodule of symmetric matrices
    set v : STri p → symmMatrices (p := p) (R := R) :=
      fun q => ⟨E q, Esm_isSymm _ _⟩ with hv
    have hv_coe : ∀ q, ((v q : symmMatrices) : Matrix (Fin p) (Fin p) R) = E q := fun q => rfl
    -- linear independence via orthonormality
    have hli : LinearIndependent R v := by
      rw [Fintype.linearIndependent_iff]
      intro c hc b
      -- pass to ambient matrices
      have hc' : (∑ a, c a • E a : Matrix (Fin p) (Fin p) R) = 0 := by
        have := congrArg (Submodule.subtype _) hc
        simpa [map_sum, map_smul, hv_coe] using this
      -- apply the bilinear form against E b
      have key : traceBilin (∑ a, c a • E a : Matrix (Fin p) (Fin p) R) (E b) = 0 := by
        rw [hc']; simp
      rw [map_sum, LinearMap.sum_apply] at key
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, traceBilin_E, mul_ite, mul_one,
        mul_zero] at key
      rwa [Finset.sum_ite_eq' Finset.univ b c, ite_eq_left (Finset.mem_univ b)] at key
    -- spanning
    have hsp : ⊤ ≤ Submodule.span R (Set.range v) := by
      rintro ⟨X, hX⟩ -
      have hXsum : (⟨X, hX⟩ : symmMatrices (p := p) (R := R))
          = ∑ q : STri p, Ecoeff X q • v q := by
        apply Subtype.ext
        rw [hv]
        push_cast [Submodule.coe_sum, SetLike.val_smul]
        exact symm_eq_sum_Ecoeff X hX
      rw [hXsum]
      exact Submodule.sum_mem _ fun q _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self q))
    -- assemble the basis
    refine ⟨Module.Basis.mk hli hsp, fun a => ?_⟩
    rw [Module.Basis.mk_apply, hv_coe]

end ScalarProduct

end Azurite.BPR.Chapter4
