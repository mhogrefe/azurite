/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Feldman.ExpPoly
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Transfer of a transcendence measure to an algebraic extension

Let `ϖ, e ∈ ℂ` satisfy a relation `R(ϖ, e) = 0`, `R ∈ ℤ[X][Y]` of degree `d ≥ 1` in `Y`, with
`δ = r_d(ϖ) ≠ 0`, and of minimal `Y`-degree: no nonzero polynomial of degree `< d` in `Y`
vanishes at `(ϖ, e)`.  For `M ∈ ℤ[X][Y]` of degree `≤ D` in `Y` with `M(ϖ, e) ≠ 0` there is
`𝒟 ∈ ℤ[X]`, `𝒟 ≠ 0`, whose value at `ϖ` is `δ^D M(ϖ, e)` times an explicitly bounded factor
(`transfer_det`), so a lower bound for `|𝒟(ϖ)|` (a transcendence measure of `ϖ`) is a lower
bound for `|M(ϖ, e)|`.

Construction: the matrix `compMat R d` over `ℤ[X]` (the companion matrix of `R` in `Y`,
multiplied by `r_d`) has `b = (1, e, …, e^{d−1})` as an eigenvector at `ϖ` with eigenvalue
`δ e` (`compMat_mulVec`); so `transM = ∑_k m_k r_d^{D−k} (compMat)^k` has `b` as an eigenvector
with eigenvalue `δ^D M(ϖ, e)` (`transM_mulVec`), and `𝒟 = det transM`.  `𝒟 ≠ 0`: a left kernel
vector over `ℤ[X]` would give a relation of degree `< d`.  `det A · b = λ · adj(A) b` for an
eigenvector gives the value.
-/

namespace Azurite.Chudnovsky

open Polynomial Matrix Finset

/-- Evaluation of an integer polynomial at `ϖ`, as a ring homomorphism. -/
noncomputable def evX (ϖ : ℂ) : ℤ[X] →+* ℂ := (aeval ϖ : ℤ[X] →ₐ[ℤ] ℂ).toRingHom

theorem evX_apply (ϖ : ℂ) (q : ℤ[X]) : evX ϖ q = aeval ϖ q := rfl

/-- Evaluation of `M ∈ ℤ[X][Y]` at `(ϖ, e)`. -/
noncomputable def ev2 (ϖ e : ℂ) : ℤ[X][X] →+* ℂ := eval₂RingHom (evX ϖ) e

theorem ev2_eq_sum (ϖ e : ℂ) {M : ℤ[X][X]} {D : ℕ} (hD : M.natDegree ≤ D) :
    ev2 ϖ e M = ∑ k ∈ range (D + 1), evX ϖ (M.coeff k) * e ^ k := by
  unfold ev2
  rw [coe_eval₂RingHom, eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hD)]

/-- The companion matrix of `R` in `Y`, multiplied by the leading coefficient `r_d`. -/
noncomputable def compMat (R : ℤ[X][X]) (d : ℕ) : Matrix (Fin d) (Fin d) ℤ[X] :=
  fun i j => if (i : ℕ) + 1 < d then (if (j : ℕ) = i + 1 then R.coeff d else 0)
    else -R.coeff j

variable {ϖ e : ℂ} {R : ℤ[X][X]} {d : ℕ}

/-- The powers of `e`. -/
noncomputable def powVec (e : ℂ) (d : ℕ) : Fin d → ℂ := fun j => e ^ (j : ℕ)

/-- `b = (1, e, …, e^{d−1})` is an eigenvector of the companion matrix at `ϖ`. -/
theorem compMat_mulVec (hd : R.natDegree = d) (hR : ev2 ϖ e R = 0) :
    ((compMat R d).map (evX ϖ)) *ᵥ powVec e d = (evX ϖ (R.coeff d) * e) • powVec e d := by
  refine _root_.funext fun i => ?_
  simp only [mulVec, dotProduct, Matrix.map_apply, powVec, Pi.smul_apply, smul_eq_mul]
  by_cases hi : (i : ℕ) + 1 < d
  · rw [Finset.sum_eq_single (⟨(i : ℕ) + 1, hi⟩ : Fin d)]
    · simp only [compMat, hi, ↓reduceIte]
      rw [pow_succ]
      ring
    · intro j _ hj
      have hne : (j : ℕ) ≠ (i : ℕ) + 1 := fun h => hj (Fin.ext h)
      simp only [compMat, hi, hne, ↓reduceIte, map_zero, zero_mul]
    · intro h
      exact absurd (mem_univ _) h
  · have hid : (i : ℕ) + 1 = d := by have := i.isLt; omega
    have hsum := ev2_eq_sum ϖ e (M := R) (D := d) hd.le
    rw [hR, Finset.sum_range_succ] at hsum
    have hfin : ∑ j : Fin d, evX ϖ (compMat R d i j) * e ^ (j : ℕ)
        = -∑ k ∈ range d, evX ϖ (R.coeff k) * e ^ k := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => evX ϖ (R.coeff k) * e ^ k) d,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [compMat, hi, ↓reduceIte, map_neg, neg_mul]
    rw [hfin]
    have hpow : e * e ^ (i : ℕ) = e ^ d := by rw [← pow_succ', hid]
    rw [mul_assoc, hpow]
    linear_combination hsum

theorem pow_mulVec_of_eigen {A : Matrix (Fin d) (Fin d) ℂ} {b : Fin d → ℂ} {c : ℂ}
    (h : A *ᵥ b = c • b) (k : ℕ) : (A ^ k) *ᵥ b = c ^ k • b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]

/-- The matrix `∑_k m_k r_d^{D−k} (compMat)^k` over `ℤ[X]`. -/
noncomputable def transM (R M : ℤ[X][X]) (d D : ℕ) : Matrix (Fin d) (Fin d) ℤ[X] :=
  ∑ k ∈ range (D + 1), (M.coeff k * R.coeff d ^ (D - k)) • (compMat R d) ^ k

theorem map_transM (ϖ : ℂ) (R M : ℤ[X][X]) (d D : ℕ) :
    (transM R M d D).map (evX ϖ)
      = ∑ k ∈ range (D + 1), (evX ϖ (M.coeff k) * evX ϖ (R.coeff d) ^ (D - k))
          • ((compMat R d).map (evX ϖ)) ^ k := by
  have h := map_sum (RingHom.mapMatrix (evX ϖ) : Matrix (Fin d) (Fin d) ℤ[X] →+* _)
    (fun k => (M.coeff k * R.coeff d ^ (D - k)) • (compMat R d) ^ k) (range (D + 1))
  simp only [RingHom.mapMatrix_apply] at h
  rw [transM, h]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h2 := map_pow (RingHom.mapMatrix (evX ϖ) : Matrix (Fin d) (Fin d) ℤ[X] →+* _)
    (compMat R d) k
  simp only [RingHom.mapMatrix_apply] at h2
  rw [← h2]
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply]

/-- `b` is an eigenvector of `transM` at `ϖ`, with eigenvalue `δ^D M(ϖ, e)`. -/
theorem transM_mulVec (hd : R.natDegree = d) (hR : ev2 ϖ e R = 0) {M : ℤ[X][X]} {D : ℕ}
    (hD : M.natDegree ≤ D) :
    ((transM R M d D).map (evX ϖ)) *ᵥ powVec e d
      = (evX ϖ (R.coeff d) ^ D * ev2 ϖ e M) • powVec e d := by
  rw [map_transM, Matrix.sum_mulVec, ev2_eq_sum ϖ e hD, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ D := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [Matrix.smul_mulVec, pow_mulVec_of_eigen (compMat_mulVec hd hR) k, smul_smul]
  congr 1
  rw [mul_pow, show evX ϖ (R.coeff d) ^ D = evX ϖ (R.coeff d) ^ (D - k) * evX ϖ (R.coeff d) ^ k by
    rw [← pow_add, Nat.sub_add_cancel hk']]
  ring

/-- **The determinant `𝒟 = det transM` is not zero** when `M(ϖ, e) ≠ 0` and `R` has minimal
`Y`-degree. -/
theorem det_transM_ne_zero (hd : R.natDegree = d) (hR : ev2 ϖ e R = 0)
    (hδ : evX ϖ (R.coeff d) ≠ 0)
    (hmin : ∀ c : ℤ[X][X], c ≠ 0 → c.natDegree < d → ev2 ϖ e c ≠ 0) {M : ℤ[X][X]} {D : ℕ}
    (hD : M.natDegree ≤ D) (hM : ev2 ϖ e M ≠ 0) : (transM R M d D).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := (exists_vecMul_eq_zero_iff (M := transM R M d D)).mpr hdet
  -- evaluate at `ϖ` and pair with `b`
  have h1 : (fun j => evX ϖ (c j)) ᵥ* ((transM R M d D).map (evX ϖ)) = 0 := by
    refine _root_.funext fun j => ?_
    have := congrArg (evX ϖ) (congrFun hc j)
    simp only [vecMul, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at this
    simpa [vecMul, dotProduct, Matrix.map_apply] using this
  have h2 := dotProduct_mulVec (fun j => evX ϖ (c j)) ((transM R M d D).map (evX ϖ)) (powVec e d)
  rw [h1, zero_dotProduct, transM_mulVec hd hR hD, dotProduct_smul, smul_eq_mul] at h2
  have h3 : (fun j => evX ϖ (c j)) ⬝ᵥ powVec e d = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (mul_ne_zero (pow_ne_zero _ hδ) hM)
    · exact h
  -- the relation `∑ c_j Y^j` of degree `< d`
  set P : ℤ[X][X] := ∑ j : Fin d, C (c j) * X ^ (j : ℕ) with hP
  have hPdeg : P.natDegree < d := by
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0
        exact absurd (_root_.funext fun j : Fin 0 => Fin.elim0 j) hc0
      · exact h0
    have : P.natDegree ≤ d - 1 :=
      natDegree_sum_le_of_forall_le _ _ fun j _ =>
        (natDegree_C_mul_X_pow_le _ _).trans (by have := j.isLt; omega)
    omega
  have hPcoeff : ∀ j : Fin d, P.coeff j = c j := by
    intro j
    rw [hP, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [ite_eq_right]
      exact fun h => hij (Fin.ext h.symm)
    · intro h
      exact absurd (mem_univ _) h
  have hP0 : P ≠ 0 := by
    intro h0
    apply hc0
    refine _root_.funext fun j => ?_
    rw [← hPcoeff j, h0, coeff_zero]
    rfl
  have hPev : ev2 ϖ e P = 0 := by
    rw [hP, map_sum]
    simp only [map_mul, map_pow]
    have : ∀ j : Fin d, ev2 ϖ e (C (c j)) * ev2 ϖ e X ^ (j : ℕ) = evX ϖ (c j) * e ^ (j : ℕ) := by
      intro j
      simp [ev2]
    simp only [this]
    exact h3
  exact hmin P hP0 hPdeg hPev

/-- **The value of `𝒟` at `ϖ`**: `𝒟(ϖ) = δ^D M(ϖ, e) · (adj(transM(ϖ)) b)₀`. -/
theorem evX_det_transM (hd : R.natDegree = d) (hd1 : 0 < d) (hR : ev2 ϖ e R = 0) {M : ℤ[X][X]}
    {D : ℕ} (hD : M.natDegree ≤ D) :
    evX ϖ (transM R M d D).det
      = evX ϖ (R.coeff d) ^ D * ev2 ϖ e M
        * (adjugate ((transM R M d D).map (evX ϖ)) *ᵥ powVec e d) ⟨0, hd1⟩ := by
  have h1 : evX ϖ (transM R M d D).det = ((transM R M d D).map (evX ϖ)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have h2 := congrArg (fun A => A *ᵥ powVec e d) (adjugate_mul ((transM R M d D).map (evX ϖ)))
  simp only [← mulVec_mulVec, transM_mulVec hd hR hD, mulVec_smul, smul_mulVec, one_mulVec] at h2
  have h3 := congrFun h2 ⟨0, hd1⟩
  simp only [Pi.smul_apply, smul_eq_mul, powVec, pow_zero, mul_one] at h3
  rw [h1, ← h3]

/-! ### Sizes -/

open Azurite.Feldman

/-- `q ∈ ℤ[X]` has degree `≤ g` and `ℓ¹`-norm `≤ B`. -/
def Sz (g : ℕ) (B : ℝ) (q : ℤ[X]) : Prop := q.natDegree ≤ g ∧ l1 (toC q) ≤ B

theorem Sz.nonneg {g : ℕ} {B : ℝ} {q : ℤ[X]} (h : Sz g B q) : 0 ≤ B := (l1_nonneg _).trans h.2

theorem Sz.mono {g g' : ℕ} {B B' : ℝ} {q : ℤ[X]} (h : Sz g B q) (hg : g ≤ g') (hB : B ≤ B') :
    Sz g' B' q := ⟨h.1.trans hg, h.2.trans hB⟩

theorem Sz.mul {g₁ g₂ : ℕ} {B₁ B₂ : ℝ} {p q : ℤ[X]} (hp : Sz g₁ B₁ p) (hq : Sz g₂ B₂ q) :
    Sz (g₁ + g₂) (B₁ * B₂) (p * q) := by
  refine ⟨natDegree_mul_le.trans (add_le_add hp.1 hq.1), ?_⟩
  rw [toC, Polynomial.map_mul]
  exact (l1_mul_le _ _).trans (mul_le_mul hp.2 hq.2 (l1_nonneg _) hp.nonneg)

theorem Sz.neg {g : ℕ} {B : ℝ} {q : ℤ[X]} (h : Sz g B q) : Sz g B (-q) := by
  refine ⟨by rw [natDegree_neg]; exact h.1, ?_⟩
  rw [toC, Polynomial.map_neg, l1_neg]
  exact h.2

theorem Sz.zero (g : ℕ) {B : ℝ} (hB : 0 ≤ B) : Sz g B 0 := by
  refine ⟨by simp, ?_⟩
  rw [toC, Polynomial.map_zero, l1_zero]
  exact hB

theorem Sz.one : Sz 0 1 (1 : ℤ[X]) := by
  refine ⟨by simp, ?_⟩
  rw [toC, Polynomial.map_one, l1_one]

theorem Sz.sum {ι : Type*} (s : Finset ι) {f : ι → ℤ[X]} {g : ℕ} {B : ℝ}
    (h : ∀ i ∈ s, Sz g B (f i)) : Sz g (s.card * B) (∑ i ∈ s, f i) := by
  refine ⟨natDegree_sum_le_of_forall_le _ _ fun i hi => (h i hi).1, ?_⟩
  rw [toC, Polynomial.map_sum]
  refine (l1_sum_le _ _).trans ?_
  calc ∑ i ∈ s, l1 (map (Int.castRingHom ℂ) (f i)) ≤ ∑ _i ∈ s, B :=
        Finset.sum_le_sum fun i hi => (h i hi).2
    _ = s.card * B := by rw [Finset.sum_const, nsmul_eq_mul]

theorem Sz.pow {g : ℕ} {B : ℝ} {q : ℤ[X]} (h : Sz g B q) (k : ℕ) : Sz (k * g) (B ^ k) (q ^ k) := by
  induction k with
  | zero => simpa using Sz.one
  | succ k ih =>
    have := ih.mul h
    rw [pow_succ, pow_succ]
    exact this.mono (by ring_nf; exact le_rfl) le_rfl

theorem Sz.prod {ι : Type*} (s : Finset ι) {f : ι → ℤ[X]} {g : ℕ} {B : ℝ}
    (h : ∀ i ∈ s, Sz g B (f i)) : Sz (s.card * g) (B ^ s.card) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Sz.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact (h1.mul h2).mono (by ring_nf; exact le_rfl) (by rw [pow_succ]; ring_nf; exact le_rfl)

/-- The value at `ϖ`: `|q(ϖ)| ≤ B max(1, |ϖ|)^g`. -/
theorem Sz.norm_evX_le {g : ℕ} {B : ℝ} {q : ℤ[X]} (h : Sz g B q) (ϖ : ℂ) :
    ‖evX ϖ q‖ ≤ B * max 1 ‖ϖ‖ ^ g := by
  rw [evX_apply, aeval_eq_eval_toC]
  have hd : (toC q).natDegree ≤ g := by rw [natDegree_toC]; exact h.1
  refine (norm_eval_le_l1 hd (le_max_left _ _) (le_max_right _ _)).trans ?_
  exact mul_le_mul_of_nonneg_right h.2 (by positivity)

/-- All entries of a matrix over `ℤ[X]` have size `(g, B)`. -/
def MSz {d : ℕ} (g : ℕ) (B : ℝ) (A : Matrix (Fin d) (Fin d) ℤ[X]) : Prop :=
  ∀ i j, Sz g B (A i j)

theorem MSz.mul {d : ℕ} {g₁ g₂ : ℕ} {B₁ B₂ : ℝ} {A₁ A₂ : Matrix (Fin d) (Fin d) ℤ[X]}
    (h₁ : MSz g₁ B₁ A₁) (h₂ : MSz g₂ B₂ A₂) : MSz (g₁ + g₂) (d * (B₁ * B₂)) (A₁ * A₂) := by
  intro i j
  rw [Matrix.mul_apply]
  have := Sz.sum (Finset.univ : Finset (Fin d)) (f := fun l => A₁ i l * A₂ l j)
    (fun l _ => (h₁ i l).mul (h₂ l j))
  simpa using this

theorem MSz.one (d : ℕ) : MSz 0 1 (1 : Matrix (Fin d) (Fin d) ℤ[X]) := by
  intro i j
  by_cases hij : i = j
  · rw [hij, Matrix.one_apply_eq]
    exact Sz.one
  · rw [Matrix.one_apply_ne hij]
    exact Sz.zero 0 zero_le_one

theorem MSz.pow {d : ℕ} (hd : 0 < d) {g : ℕ} {B : ℝ} {A : Matrix (Fin d) (Fin d) ℤ[X]}
    (h : MSz g B A) (k : ℕ) : MSz (k * g) ((d * B) ^ k) (A ^ k) := by
  have hB : 0 ≤ B := (h ⟨0, hd⟩ ⟨0, hd⟩).nonneg
  induction k with
  | zero => simpa using MSz.one d
  | succ k ih =>
    have := ih.mul h
    rw [pow_succ]
    intro i j
    exact (this i j).mono (by ring_nf; exact le_rfl) (le_of_eq (by ring))

theorem MSz_compMat {R : ℤ[X][X]} {d ρ : ℕ} {lam : ℝ} (hρ : ∀ j, (R.coeff j).natDegree ≤ ρ)
    (hlam : ∀ j, l1 (toC (R.coeff j)) ≤ lam) : MSz ρ lam (compMat R d) := by
  have hl0 : 0 ≤ lam := (l1_nonneg _).trans (hlam 0)
  intro i j
  unfold compMat
  split_ifs
  · exact ⟨hρ d, hlam d⟩
  · exact Sz.zero ρ hl0
  · exact Sz.neg ⟨hρ j, hlam j⟩

/-- The sizes of the entries of `transM`. -/
theorem MSz_transM {R M : ℤ[X][X]} {d D ρ gM : ℕ} {lam LM : ℝ} (hd : 0 < d)
    (hρ : ∀ j, (R.coeff j).natDegree ≤ ρ) (hlam : ∀ j, l1 (toC (R.coeff j)) ≤ lam)
    (hlam1 : 1 ≤ lam) (hgM : ∀ k, (M.coeff k).natDegree ≤ gM)
    (hLM : ∀ k, l1 (toC (M.coeff k)) ≤ LM) :
    MSz (gM + D * ρ) ((D + 1 : ℕ) * (LM * (d * lam) ^ D)) (transM R M d D) := by
  have hLM0 : 0 ≤ LM := (l1_nonneg _).trans (hLM 0)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdl : (1 : ℝ) ≤ d * lam := by nlinarith
  intro i j
  unfold transM
  rw [Matrix.sum_apply]
  have hterm : ∀ k ∈ range (D + 1), Sz (gM + D * ρ) (LM * (d * lam) ^ D)
      (((M.coeff k * R.coeff d ^ (D - k)) • (compMat R d) ^ k) i j) := by
    intro k hk
    have hk' : k ≤ D := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [Matrix.smul_apply, smul_eq_mul]
    have h1 : Sz gM LM (M.coeff k) := ⟨hgM k, hLM k⟩
    have h2 : Sz ((D - k) * ρ) (lam ^ (D - k)) (R.coeff d ^ (D - k)) :=
      Sz.pow ⟨hρ d, hlam d⟩ _
    have h3 := (MSz_compMat (d := d) hρ hlam).pow hd k i j
    refine ((h1.mul h2).mul h3).mono ?_ ?_
    · have : (D - k) * ρ + k * ρ = D * ρ := by rw [← Nat.add_mul, Nat.sub_add_cancel hk']
      omega
    · have hl : lam ^ (D - k) ≤ (d * lam) ^ (D - k) :=
        pow_le_pow_left₀ (by linarith) (by nlinarith) _
      calc LM * lam ^ (D - k) * (d * lam) ^ k ≤ LM * (d * lam) ^ (D - k) * (d * lam) ^ k := by
            gcongr
        _ = LM * (d * lam) ^ D := by
            rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hk']
  have := Sz.sum (range (D + 1)) hterm
  rwa [card_range] at this

/-- The size of a determinant. -/
theorem Sz_det {d : ℕ} {g : ℕ} {B : ℝ} {A : Matrix (Fin d) (Fin d) ℤ[X]}
    (h : MSz g B A) : Sz (d * g) (d.factorial * B ^ d) A.det := by
  rw [Matrix.det_apply]
  have hterm : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin d))),
      Sz (d * g) (B ^ d) (Equiv.Perm.sign σ • ∏ i, A (σ i) i) := by
    intro σ _
    have hp := Sz.prod (Finset.univ : Finset (Fin d)) (f := fun i => A (σ i) i)
      (fun i _ => h (σ i) i)
    rw [Finset.card_univ, Fintype.card_fin] at hp
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul]
      exact hp
    · rw [hs, Units.neg_smul, one_smul]
      exact hp.neg
  have := Sz.sum _ hterm
  rwa [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at this

/-! ### Complex matrices -/

theorem norm_det_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) {B : ℝ}
    (h : ∀ i j, ‖A i j‖ ≤ B) : ‖A.det‖ ≤ d.factorial * B ^ d := by
  rw [Matrix.det_apply]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin d))),
      ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ ≤ B ^ d := by
    intro σ _
    have hp : ‖∏ i, A (σ i) i‖ ≤ B ^ d := by
      rw [norm_prod]
      calc ∏ i, ‖A (σ i) i‖ ≤ ∏ _i : Fin d, B :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => h (σ i) i
        _ = B ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul]
      exact hp
    · rw [hs, Units.neg_smul, one_smul, norm_neg]
      exact hp
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem norm_adjugate_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) {B : ℝ}
    (h : ∀ i j, ‖A i j‖ ≤ B) (i j : Fin d) :
    ‖adjugate A i j‖ ≤ d.factorial * (max 1 B) ^ d := by
  rw [adjugate_apply]
  refine norm_det_le _ fun i' j' => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs
    · rw [norm_one]
      exact le_max_left _ _
    · rw [norm_zero]
      exact le_trans zero_le_one (le_max_left _ _)
  · exact (h i' j').trans (le_max_right _ _)

/-! ### The transfer -/

/-- **Transfer of the measure.**  Under the hypotheses of the file header, with the sizes
`deg r_j ≤ ρ`, `‖r_j‖₁ ≤ lam` (`lam ≥ 1`) of `R` and `deg m_k ≤ gM`, `‖m_k‖₁ ≤ LM` of `M`
(`deg_Y M ≤ D`): there is `𝒟 ∈ ℤ[X]`, `𝒟 ≠ 0`, of degree `≤ d (gM + Dρ)` and `ℓ¹`-norm
`≤ d! ((D + 1) LM (d·lam)^D)^d`, with
`|𝒟(ϖ)| ≤ |δ|^D |M(ϖ, e)| · d · d! B₁^d · max(1, |e|)^d`, where `B₁` bounds the entries of
`transM` at `ϖ`. -/
theorem transfer {ϖ e : ℂ} {R : ℤ[X][X]} {d : ℕ} (hd : R.natDegree = d) (hd1 : 0 < d)
    (hR : ev2 ϖ e R = 0) (hδ : evX ϖ (R.coeff d) ≠ 0)
    (hmin : ∀ c : ℤ[X][X], c ≠ 0 → c.natDegree < d → ev2 ϖ e c ≠ 0) {ρ : ℕ} {lam : ℝ}
    (hρ : ∀ j, (R.coeff j).natDegree ≤ ρ) (hlam : ∀ j, l1 (toC (R.coeff j)) ≤ lam)
    (hlam1 : 1 ≤ lam) {M : ℤ[X][X]} {D gM : ℕ} {LM : ℝ} (hD : M.natDegree ≤ D)
    (hM : ev2 ϖ e M ≠ 0) (hgM : ∀ k, (M.coeff k).natDegree ≤ gM)
    (hLM : ∀ k, l1 (toC (M.coeff k)) ≤ LM) :
    ∃ 𝒟 : ℤ[X], 𝒟 ≠ 0 ∧ 𝒟.natDegree ≤ d * (gM + D * ρ)
      ∧ l1 (toC 𝒟) ≤ d.factorial * ((D + 1 : ℕ) * (LM * (d * lam) ^ D)) ^ d
      ∧ ‖evX ϖ 𝒟‖ ≤ ‖evX ϖ (R.coeff d)‖ ^ D * ‖ev2 ϖ e M‖
          * (d * (d.factorial
            * (max 1 ((D + 1 : ℕ) * (LM * (d * lam) ^ D) * max 1 ‖ϖ‖ ^ (gM + D * ρ))) ^ d)
            * max 1 ‖e‖ ^ d) := by
  have hsz := MSz_transM (R := R) (M := M) (D := D) hd1 hρ hlam hlam1 hgM hLM
  have hdet := Sz_det hsz
  refine ⟨(transM R M d D).det, det_transM_ne_zero hd hR hδ hmin hD hM, hdet.1, hdet.2, ?_⟩
  rw [evX_det_transM hd hd1 hR hD, norm_mul, norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- the cofactor factor
  set B : ℝ := (D + 1 : ℕ) * (LM * (d * lam) ^ D) * max 1 ‖ϖ‖ ^ (gM + D * ρ) with hB
  have hentry : ∀ i j, ‖((transM R M d D).map (evX ϖ)) i j‖ ≤ B := fun i j => by
    rw [Matrix.map_apply]
    exact (hsz i j).norm_evX_le ϖ
  have hadj := norm_adjugate_le _ hentry
  simp only [mulVec, dotProduct]
  refine (norm_sum_le _ _).trans ?_
  have hE1 : (1 : ℝ) ≤ max 1 ‖e‖ := le_max_left _ _
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      ‖adjugate ((transM R M d D).map (evX ϖ)) ⟨0, hd1⟩ j * powVec e d j‖
        ≤ d.factorial * (max 1 B) ^ d * max 1 ‖e‖ ^ d := by
    intro j _
    rw [norm_mul, powVec, norm_pow]
    refine mul_le_mul (hadj _ j) ?_ (by positivity) (by positivity)
    exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ hE1 j.isLt.le)
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Azurite.Chudnovsky
