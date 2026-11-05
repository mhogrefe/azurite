/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section7
import Azurite.DLMF.Chapter3.Section2Tridiag
import Azurite.DLMF.Chapter2.Section7NumSat

/-!
# DLMF §3.7(iii): Taylor-series method, boundary-value problems

* "This can happen only for inhomogeneous equations": no solution of the homogeneous equation
  grows at a rate strictly intermediate to two other solutions (`dlmf_3_7_iii_hom_not_intermediate`,
  via `exists_dep_three`), whereas for `w″ − w = −1` the solution `1` is intermediate to `eᶻ` and
  `e⁻ᶻ` (`dlmf_3_7_iii_inhom_intermediate`).
* 3.7.10–3.7.12: the band matrix `𝐀_P` (`bandAP`, block-indexed; `finProdFinEquiv` gives the
  flat order), `𝐰` (`bandW`), `𝐛` (`bandB`). 3.7.13 `𝐀_P 𝐰 = 𝐛` (`dlmf_3_7_13`,
  `dlmf_3_7_13_flat`); `𝐀_P 𝐲 = 𝐛` says exactly that consecutive blocks satisfy 3.7.5
  (`bandAP_mulVec_eq_iff`).
* 3.7.14 (`IsBC`): together with 3.7.13 the two boundary conditions characterize the values at
  `z₀, …, z_P` of the solutions of the boundary-value problem (`dlmf_3_7_13_14`).
* `β₀ = β₁ = 0`: moving `w(z₀)`, `w(z_P)` to the right-hand side and annihilating the elements below
  the subdiagonal (pivots `A₁₁(τⱼ, zⱼ) ≠ 0`, multipliers `triMult`) gives a tridiagonal system in
  the form 3.2.7 (`bvpA`, `bvpB`, `bvpC`, `bvpF`, `bvp_tridiagonal`), equivalent to 3.7.13
  (`triRows_iff`), satisfied by every solution of the boundary-value problem
  (`dlmf_3_7_iii_tridiag_of_sol`), and each of its solutions comes from one
  (`dlmf_3_7_iii_sol_of_tridiag`). The method of §3.2(ii) (`triX`) solves it when the pivots
  `d_j` do not vanish (`dlmf_3_7_iii_solve`, via `three_term_of_tridiag`).

Not formalized: Olver's algorithm for the case `b = ∞` (see §3.6(v)), the remark on parallelism,
and the references (Olde Daalhuis–Olver 1998, Lozier–Olver 1993, Ascher et al. 1995).
-/

open Filter Topology Set Metric Complex
open scoped Nat Matrix

namespace Azurite.DLMF

section Band

variable {D : Set ℂ} {f g h : ℂ → ℂ}

/-- The step matrix `𝐀(τⱼ, zⱼ)`, `τⱼ = z_{j+1} − zⱼ`. -/
noncomputable def stepA (f g : ℂ → ℂ) (zs : ℕ → ℂ) (j : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  taylorA f g (zs (j + 1) - zs j) (zs j)

/-- The step vector `𝐛(τⱼ, zⱼ)`. -/
noncomputable def stepB (f g h : ℂ → ℂ) (zs : ℕ → ℂ) (j : ℕ) : Fin 2 → ℂ :=
  taylorB f g h (zs (j + 1) - zs j) (zs j)

/-- **DLMF 3.7.10**: the `(2P) × (2P + 2)` band matrix `𝐀_P`. Rows are indexed by `(j, i)`,
`j < P`, and columns by `(k, l)`, `k ≤ P` (`i, l < 2`), in the order of 3.7.11–3.7.12; block
row `j` is `−𝐀(τⱼ, zⱼ)` in block column `j` and `𝐈` in block column `j + 1`. `finProdFinEquiv`
flattens the indices to `Fin (2P)` and `Fin (2P + 2)` (`dlmf_3_7_13_flat`). -/
noncomputable def bandAP (f g : ℂ → ℂ) (zs : ℕ → ℂ) (P : ℕ) :
    Matrix (Fin P × Fin 2) (Fin (P + 1) × Fin 2) ℂ := fun r c =>
  (if c.1 = r.1.castSucc then -stepA f g zs r.1 r.2 c.2 else 0) +
    (if c.1 = r.1.succ then (1 : Matrix (Fin 2) (Fin 2) ℂ) r.2 c.2 else 0)

/-- **DLMF 3.7.11**: `𝐰 = [w(z₀), w′(z₀), …, w(z_P), w′(z_P)]ᵀ`. -/
noncomputable def bandW (w : ℂ → ℂ) (zs : ℕ → ℂ) (P : ℕ) : Fin (P + 1) × Fin 2 → ℂ :=
  fun c => odeState w (zs c.1) c.2

/-- **DLMF 3.7.12**:
`𝐛 = [b₁(τ₀, z₀), b₂(τ₀, z₀), …, b₁(τ_{P−1}, z_{P−1}), b₂(τ_{P−1}, z_{P−1})]ᵀ`. -/
noncomputable def bandB (f g h : ℂ → ℂ) (zs : ℕ → ℂ) (P : ℕ) : Fin P × Fin 2 → ℂ :=
  fun r => stepB f g h zs r.1 r.2

theorem bandAP_mulVec (f g : ℂ → ℂ) (zs : ℕ → ℂ) (P : ℕ) (y : Fin (P + 1) × Fin 2 → ℂ)
    (r : Fin P × Fin 2) :
    (bandAP f g zs P *ᵥ y) r =
      y (r.1.succ, r.2) - (stepA f g zs r.1 *ᵥ fun l => y (r.1.castSucc, l)) r.2 := by
  simp only [Matrix.mulVec, dotProduct, bandAP, add_mul, Finset.sum_add_distrib, ite_mul,
    zero_mul, Fintype.sum_prod_type, Matrix.one_apply, neg_mul, one_mul]
  simp [Fin.sum_univ_two]
  ring

/-- `𝐀_P 𝐲 = 𝐛` says exactly that consecutive blocks of `𝐲` are related by 3.7.5. -/
theorem bandAP_mulVec_eq_iff (f g h : ℂ → ℂ) (zs : ℕ → ℂ) (P : ℕ)
    (y : Fin (P + 1) × Fin 2 → ℂ) :
    bandAP f g zs P *ᵥ y = bandB f g h zs P ↔ ∀ j : Fin P,
      (fun l => y (j.succ, l)) = stepA f g zs j *ᵥ (fun l => y (j.castSucc, l)) +
        stepB f g h zs j := by
  constructor
  · intro H j
    funext l
    have := congrFun H (j, l)
    rw [bandAP_mulVec] at this
    simp only [bandB] at this
    simp only [Pi.add_apply]
    linear_combination this
  · intro H
    funext r
    rw [bandAP_mulVec]
    have := congrFun (H r.1) r.2
    simp only [Pi.add_apply] at this
    simp only [bandB]
    linear_combination this

/-- **DLMF 3.7.13**: `𝐀_P 𝐰 = 𝐛` for every solution of 3.7.1 in `D`. -/
theorem dlmf_3_7_13 (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
    (hh : DifferentiableOn ℂ h D) {w : ℂ → ℂ} (hw : IsInhomSolution D f g h w) {zs : ℕ → ℂ}
    {P : ℕ} (hP : IsTaylorPath D zs P) :
    bandAP f g zs P *ᵥ bandW w zs P = bandB f g h zs P := by
  rw [bandAP_mulVec_eq_iff]
  intro j
  simp only [bandW, Fin.val_succ, Fin.val_castSucc]
  exact odeState_succ hf hg hh hw hP j.isLt

/-- **DLMF 3.7.13** with the indices flattened as in 3.7.10–3.7.12: a `(2P) × (2P + 2)` system. -/
theorem dlmf_3_7_13_flat (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
    (hh : DifferentiableOn ℂ h D) {w : ℂ → ℂ} (hw : IsInhomSolution D f g h w) {zs : ℕ → ℂ}
    {P : ℕ} (hP : IsTaylorPath D zs P) :
    (bandAP f g zs P).submatrix finProdFinEquiv.symm finProdFinEquiv.symm *ᵥ
        (bandW w zs P ∘ finProdFinEquiv.symm) = bandB f g h zs P ∘ finProdFinEquiv.symm := by
  rw [Matrix.submatrix_mulVec_equiv, Function.comp_assoc, Equiv.symm_symm, Equiv.symm_comp_self,
    Function.comp_id, dlmf_3_7_13 hf hg hh hw hP]

/-- `finProdFinEquiv` lists `(k, l)` as `2k + l`: the order of 3.7.11. -/
theorem finProdFinEquiv_two {m : ℕ} (k : Fin m) (l : Fin 2) :
    (finProdFinEquiv (k, l) : ℕ) = 2 * k + l := by
  simp [finProdFinEquiv]; ring

/-- **DLMF 3.7.14**: the boundary condition `α w(z) + β w′(z) = γ` on a state `[w(z), w′(z)]`. -/
def IsBC (α β γ : ℂ) (Y : Fin 2 → ℂ) : Prop := α * Y 0 + β * Y 1 = γ

/-- **DLMF §3.7(iii)**: the `2P` equations 3.7.13 together with the two boundary conditions 3.7.14
characterize the values `w(zⱼ)`, `w′(zⱼ)` of the solutions of the boundary-value problem: a
vector `𝐲` satisfies them iff `𝐲 = 𝐰` for a solution `w` of 3.7.1 in `D` satisfying 3.7.14. -/
theorem dlmf_3_7_13_14 (hD : IsSCDomain D) (hf : DifferentiableOn ℂ f D)
    (hg : DifferentiableOn ℂ g D) (hh : DifferentiableOn ℂ h D) {zs : ℕ → ℂ} {P : ℕ}
    (hP : IsTaylorPath D zs P) (α₀ β₀ γ₀ α₁ β₁ γ₁ : ℂ) (y : Fin (P + 1) × Fin 2 → ℂ) :
    (bandAP f g zs P *ᵥ y = bandB f g h zs P ∧ IsBC α₀ β₀ γ₀ (fun l => y (0, l)) ∧
        IsBC α₁ β₁ γ₁ (fun l => y (Fin.last P, l))) ↔
      ∃ w, IsInhomSolution D f g h w ∧ IsBC α₀ β₀ γ₀ (odeState w (zs 0)) ∧
        IsBC α₁ β₁ γ₁ (odeState w (zs P)) ∧ y = bandW w zs P := by
  constructor
  · rintro ⟨hA, hb0, hb1⟩
    obtain ⟨w, hw, hw0, hw1⟩ :=
      dlmf_1_13_iii_exists hD hf hg hh hP.1 (y (0, 0)) (y (0, 1))
    rw [bandAP_mulVec_eq_iff] at hA
    have hk : ∀ k (hk : k ≤ P), odeState w (zs k) = fun l => y (⟨k, by omega⟩, l) := by
      intro k hk
      induction k with
      | zero =>
        funext l
        fin_cases l <;> simp [odeState, hw0, hw1]
      | succ k ih =>
        rw [odeState_succ hf hg hh hw hP (by omega), ih (by omega)]
        have := hA ⟨k, by omega⟩
        simp only [Fin.succ_mk, Fin.castSucc_mk] at this
        rw [this]
        rfl
    have hy : y = bandW w zs P := by
      funext ⟨k, l⟩
      simp only [bandW]
      rw [hk k (by omega)]
    refine ⟨w, hw, ?_, ?_, hy⟩
    · rw [hk 0 (Nat.zero_le _)]; exact hb0
    · rw [hk P le_rfl]; exact hb1
  · rintro ⟨w, hw, hb0, hb1, rfl⟩
    exact ⟨dlmf_3_7_13 hf hg hh hw hP, hb0, hb1⟩

end Band

/-! ### `β₀ = β₁ = 0`: reduction to a tridiagonal system -/

section Tridiag

variable (M : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (c : ℕ → Fin 2 → ℂ) (P : ℕ) (u₀ uP : ℂ)

/-- The states rebuilt from the `2P` unknowns `x₁ = w′(z₀)`, `x₂ = w(z₁)`, `x₃ = w′(z₁)`, …,
`x_{2P−2} = w(z_{P−1})`, `x_{2P−1} = w′(z_{P−1})`, `x_{2P} = w′(z_P)` (the order of 3.7.11 with
the known `w(z₀) = u₀` and `w(z_P) = u_P` moved to the right-hand side). -/
def triState (x : ℕ → ℂ) (j : ℕ) : Fin 2 → ℂ :=
  ![if j = 0 then u₀ else if j = P then uP else x (2 * j),
    if j = P then x (2 * P) else x (2 * j + 1)]

/-- The multiplier `A₂₁/A₁₁` of the row operation that annihilates the element below the
subdiagonal. -/
noncomputable def triMult (j : ℕ) : ℂ := M j 1 0 / M j 0 0

/-- Subdiagonal of the reduced system (rows `r = 1, …, 2P`, as in 3.2.7): odd rows `2j + 1` are
the first rows of 3.7.5, even rows `2j + 2` the second rows minus `A₂₁/A₁₁` times the first. -/
noncomputable def bvpA (r : ℕ) : ℂ :=
  if r % 2 = 1 then (if r = 1 then 0 else -M ((r - 1) / 2) 0 0)
  else -M ((r - 1) / 2) 1 1 + triMult M ((r - 1) / 2) * M ((r - 1) / 2) 0 1

/-- Diagonal of the reduced system. -/
noncomputable def bvpB (r : ℕ) : ℂ :=
  if r % 2 = 1 then -M ((r - 1) / 2) 0 1 else if r = 2 * P then 1 else -triMult M ((r - 1) / 2)

/-- Superdiagonal of the reduced system. -/
def bvpC (r : ℕ) : ℂ :=
  if r % 2 = 1 then (if r = 2 * P - 1 then 0 else 1) else (if r = 2 * P then 0 else 1)

/-- Right-hand side of the reduced system. -/
noncomputable def bvpF (r : ℕ) : ℂ :=
  if r % 2 = 1 then
    c ((r - 1) / 2) 0 + (if r = 1 then M 0 0 0 * u₀ else 0) - (if r = 2 * P - 1 then uP else 0)
  else c ((r - 1) / 2) 1 - triMult M ((r - 1) / 2) * c ((r - 1) / 2) 0 +
    (if r = 2 * P then triMult M ((r - 1) / 2) * uP else 0)

/-- Row `r` of the reduced tridiagonal system. -/
def TriRow (x : ℕ → ℂ) (r : ℕ) : Prop :=
  bvpA M r * x (r - 1) + bvpB M P r * x r + bvpC P r * x (r + 1) = bvpF M c P u₀ uP r

variable {M c P u₀ uP}

theorem block_iff {Y Y' : Fin 2 → ℂ} {A : Matrix (Fin 2) (Fin 2) ℂ} {v : Fin 2 → ℂ} :
    Y' = A *ᵥ Y + v ↔ (Y' 0 = A 0 0 * Y 0 + A 0 1 * Y 1 + v 0 ∧
      Y' 1 = A 1 0 * Y 0 + A 1 1 * Y 1 + v 1) := by
  simp [funext_iff, Fin.forall_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

section Values

variable (M c u₀ uP)

theorem bvpA_odd (j : ℕ) : bvpA M (2 * j + 1) = if j = 0 then 0 else -M j 0 0 := by
  have e1 : (2 * j + 1) % 2 = 1 := by omega
  have e2 : (2 * j + 1 - 1) / 2 = j := by omega
  unfold bvpA
  simp only [e1, e2, ↓reduceIte]
  by_cases h : j = 0 <;> simp [h]

theorem bvpB_odd (j : ℕ) : bvpB M P (2 * j + 1) = -M j 0 1 := by
  have e1 : (2 * j + 1) % 2 = 1 := by omega
  have e2 : (2 * j + 1 - 1) / 2 = j := by omega
  unfold bvpB
  simp only [e1, e2, ↓reduceIte]

theorem bvpC_odd {j : ℕ} (hj : j < P) : bvpC P (2 * j + 1) = if j + 1 = P then 0 else 1 := by
  have e1 : (2 * j + 1) % 2 = 1 := by omega
  have e3 : (2 * j + 1 = 2 * P - 1) = (j + 1 = P) := propext (by omega)
  unfold bvpC
  simp only [e1, e3, ↓reduceIte]

theorem bvpF_odd {j : ℕ} (hj : j < P) : bvpF M c P u₀ uP (2 * j + 1) =
    c j 0 + (if j = 0 then M 0 0 0 * u₀ else 0) - (if j + 1 = P then uP else 0) := by
  have e1 : (2 * j + 1) % 2 = 1 := by omega
  have e2 : (2 * j + 1 - 1) / 2 = j := by omega
  have e3 : (2 * j + 1 = 2 * P - 1) = (j + 1 = P) := propext (by omega)
  have e4 : (2 * j + 1 = 1) = (j = 0) := propext (by omega)
  unfold bvpF
  simp only [e1, e2, e3, e4, ↓reduceIte]

theorem bvpA_even (j : ℕ) :
    bvpA M (2 * j + 2) = -M j 1 1 + triMult M j * M j 0 1 := by
  have e1 : (2 * j + 2) % 2 = 0 := by omega
  have e2 : (2 * j + 2 - 1) / 2 = j := by omega
  unfold bvpA
  simp only [e1, e2, zero_ne_one, ↓reduceIte]

theorem bvpB_even (j : ℕ) :
    bvpB M P (2 * j + 2) = if j + 1 = P then 1 else -triMult M j := by
  have e1 : (2 * j + 2) % 2 = 0 := by omega
  have e2 : (2 * j + 2 - 1) / 2 = j := by omega
  have e3 : (2 * j + 2 = 2 * P) = (j + 1 = P) := propext (by omega)
  unfold bvpB
  simp only [e1, e2, e3, zero_ne_one, ↓reduceIte]

theorem bvpC_even (j : ℕ) : bvpC P (2 * j + 2) = if j + 1 = P then 0 else 1 := by
  have e1 : (2 * j + 2) % 2 = 0 := by omega
  have e3 : (2 * j + 2 = 2 * P) = (j + 1 = P) := propext (by omega)
  unfold bvpC
  simp only [e1, e3, zero_ne_one, ↓reduceIte]

theorem bvpF_even (j : ℕ) : bvpF M c P u₀ uP (2 * j + 2) =
    c j 1 - triMult M j * c j 0 + (if j + 1 = P then triMult M j * uP else 0) := by
  have e1 : (2 * j + 2) % 2 = 0 := by omega
  have e2 : (2 * j + 2 - 1) / 2 = j := by omega
  have e3 : (2 * j + 2 = 2 * P) = (j + 1 = P) := propext (by omega)
  unfold bvpF
  simp only [e1, e2, e3, zero_ne_one, ↓reduceIte]

theorem triState_zero {j : ℕ} (x : ℕ → ℂ) (hj : j < P) :
    triState P u₀ uP x j 0 = if j = 0 then u₀ else x (2 * j) := by
  have : (j = P) = False := eq_false (by omega)
  simp [triState, this]

theorem triState_one {j : ℕ} (x : ℕ → ℂ) (hj : j < P) :
    triState P u₀ uP x j 1 = x (2 * j + 1) := by
  have : (j = P) = False := eq_false (by omega)
  simp [triState, this]

theorem triState_succ_zero (j : ℕ) (x : ℕ → ℂ) :
    triState P u₀ uP x (j + 1) 0 = if j + 1 = P then uP else x (2 * j + 2) := by
  simp only [triState, Matrix.cons_val_zero, Nat.add_one_ne_zero, ↓reduceIte]
  by_cases h : j + 1 = P <;> simp only [h, ↓reduceIte]
  ring_nf

theorem triState_succ_one {j : ℕ} (x : ℕ → ℂ) (hj : j < P) :
    triState P u₀ uP x (j + 1) 1 = if j + 1 = P then x (2 * j + 2) else x (2 * j + 2 + 1) := by
  simp only [triState, Matrix.cons_val_one, Matrix.cons_val_zero]
  by_cases h : j + 1 = P
  · subst h; simp only [↓reduceIte]; ring_nf
  · simp only [h, ↓reduceIte]; ring_nf

end Values

theorem triRow_odd (x : ℕ → ℂ) {j : ℕ} (hj : j < P) :
    TriRow M c P u₀ uP x (2 * j + 1) ↔ triState P u₀ uP x (j + 1) 0 =
      M j 0 0 * triState P u₀ uP x j 0 + M j 0 1 * triState P u₀ uP x j 1 + c j 0 := by
  unfold TriRow
  rw [bvpA_odd, bvpB_odd, bvpC_odd hj, bvpF_odd M c u₀ uP hj, triState_succ_zero u₀ uP j x,
    triState_zero u₀ uP x hj, triState_one u₀ uP x hj, show 2 * j + 1 - 1 = 2 * j by omega,
    show 2 * j + 1 + 1 = 2 * j + 2 by omega]
  by_cases hjP : j + 1 = P <;> simp only [hjP, ↓reduceIte] <;>
    by_cases hj0 : j = 0 <;> simp only [hj0, ↓reduceIte] <;>
    constructor <;> intro H <;> linear_combination H

theorem triRow_even (x : ℕ → ℂ) {j : ℕ} (hj : j < P) (hpiv : M j 0 0 ≠ 0)
    (hE : triState P u₀ uP x (j + 1) 0 =
      M j 0 0 * triState P u₀ uP x j 0 + M j 0 1 * triState P u₀ uP x j 1 + c j 0) :
    TriRow M c P u₀ uP x (2 * j + 2) ↔ triState P u₀ uP x (j + 1) 1 =
      M j 1 0 * triState P u₀ uP x j 0 + M j 1 1 * triState P u₀ uP x j 1 + c j 1 := by
  have hm : triMult M j * M j 0 0 = M j 1 0 := div_mul_cancel₀ _ hpiv
  rw [triState_succ_zero u₀ uP j x, triState_zero u₀ uP x hj, triState_one u₀ uP x hj] at hE
  unfold TriRow
  rw [bvpA_even, bvpB_even M j, bvpC_even j, bvpF_even M c u₀ uP j,
    triState_succ_one u₀ uP x hj, triState_zero u₀ uP x hj, triState_one u₀ uP x hj,
    show 2 * j + 2 - 1 = 2 * j + 1 by omega]
  set Y := (if j = 0 then u₀ else x (2 * j))
  by_cases hjP : j + 1 = P <;> simp only [hjP, ↓reduceIte] at hE ⊢ <;>
    constructor <;> intro H
  · linear_combination H + triMult M j * hE + Y * hm
  · linear_combination H - triMult M j * hE - Y * hm
  · linear_combination H + triMult M j * hE + Y * hm
  · linear_combination H - triMult M j * hE - Y * hm

/-- The `2P` rows of the reduced system are equivalent to the `P` block equations 3.7.5 for the
rebuilt states (`A₁₁(τⱼ, zⱼ) ≠ 0`, the pivots of the row operations). -/
theorem triRows_iff (hpiv : ∀ j < P, M j 0 0 ≠ 0) (x : ℕ → ℂ) :
    (∀ r, 1 ≤ r → r ≤ 2 * P → TriRow M c P u₀ uP x r) ↔
      ∀ j < P, triState P u₀ uP x (j + 1) = M j *ᵥ triState P u₀ uP x j + c j := by
  simp only [block_iff]
  constructor
  · intro H j hj
    have h1 := (triRow_odd x hj).mp (H (2 * j + 1) (by omega) (by omega))
    exact ⟨h1, (triRow_even x hj (hpiv j hj) h1).mp (H (2 * j + 2) (by omega) (by omega))⟩
  · intro H r hr1 hr2
    obtain ⟨j, rfl | rfl⟩ : ∃ j, r = 2 * j + 1 ∨ r = 2 * j + 2 := ⟨(r - 1) / 2, by omega⟩
    · exact (triRow_odd x (by omega)).mpr (H j (by omega)).1
    · have hj : j < P := by omega
      exact (triRow_even x hj (hpiv j hj) (H j hj).1).mpr (H j hj).2

/-- The reduced system is tridiagonal in the sense of 3.2.7: row `r` involves only
`x_{r−1}, x_r, x_{r+1}`, with no `x₀` in the first row and no `x_{2P+1}` in the last. -/
theorem bvp_tridiagonal : bvpA M 1 = 0 ∧ bvpC P (2 * P) = 0 := by
  refine ⟨by simp [bvpA], ?_⟩
  have : (2 * P) % 2 = 0 := by omega
  simp [bvpC, this]

end Tridiag

/-! ### Solution by the method of §3.2(ii) -/

theorem triEntry_mul_split (a b c x : ℕ → ℂ) (k j : ℕ) :
    triEntry a b c k j * x (j + 1) = (if j = k then b (k + 1) * x (j + 1) else 0) +
      (if j = k + 1 then c (k + 1) * x (j + 1) else 0) +
      (if j + 1 = k then a (k + 1) * x (j + 1) else 0) := by
  unfold triEntry
  split_ifs <;> first | omega | ring

/-- A solution of the matrix equation of §3.2(ii) (3.2.7, `a₁ = c_n = 0`) satisfies the
three-term equations `a_r x_{r−1} + b_r x_r + c_r x_{r+1} = f_r`, `r = 1, …, n`. -/
theorem three_term_of_tridiag {n : ℕ} (a b c f x : ℕ → ℂ)
    (H : (tridiag a b c : AzMatrix ℂ n n).mulVec (AzVector.ofFn fun i => x (i.val + 1)) =
      AzVector.ofFn fun i => f (i.val + 1)) (ha : a 1 = 0) (hc : c n = 0) {r : ℕ} (h1 : 1 ≤ r)
    (h2 : r ≤ n) : a r * x (r - 1) + b r * x r + c r * x (r + 1) = f r := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  have := congrArg (fun v => AzVector.toFn v ⟨k, by omega⟩) H
  simp only [AzMatrix.toFn_mulVec, AzVector.toFn_ofFn, tridiag, AzMatrix.toFn_ofFn,
    dotProduct] at this
  rw [← this, Fin.sum_univ_eq_sum_range (fun j => triEntry a b c k j * x (j + 1)) n]
  simp only [triEntry_mul_split, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range,
    show k < n by omega, ↓reduceIte, Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : ∀ j : ℕ, (j + 1 = 0) = False := fun j => eq_false (by omega)
    by_cases hn : 0 + 1 < n <;> simp [h0, ha, hn]
    have : n = 1 := by omega
    subst this; simp [hc]
  · have h0 : ∀ j : ℕ, (j + 1 = k) = (j = k - 1) := fun j => propext (by omega)
    simp only [h0, Finset.sum_ite_eq', Finset.mem_range, show k - 1 < n by omega, ↓reduceIte,
      show k - 1 + 1 = k by omega]
    by_cases hn : k + 1 < n
    · simp only [hn, ↓reduceIte]; ring
    · have : n = k + 1 := by omega
      subst this; simp [hc]; ring

/-! ### The boundary-value problem with `β₀ = β₁ = 0` -/

section BVP

variable {D : Set ℂ} {f g h : ℂ → ℂ}

/-- The `2P` unknowns `w′(z₀), w(z₁), w′(z₁), …, w(z_{P−1}), w′(z_{P−1}), w′(z_P)` of a function
`w` (indexed from `1`). -/
noncomputable def bvpX (w : ℂ → ℂ) (zs : ℕ → ℂ) (P : ℕ) (r : ℕ) : ℂ :=
  if r = 2 * P then deriv w (zs P) else if r % 2 = 0 then w (zs (r / 2)) else deriv w (zs (r / 2))

theorem triState_bvpX {w : ℂ → ℂ} {zs : ℕ → ℂ} {P : ℕ} (hP1 : 1 ≤ P) {u₀ uP : ℂ}
    (h0 : w (zs 0) = u₀) (hP : w (zs P) = uP) {j : ℕ} (hj : j ≤ P) :
    triState P u₀ uP (bvpX w zs P) j = odeState w (zs j) := by
  have e1 : (2 * j) % 2 = 0 := by omega
  have e2 : 2 * j / 2 = j := by omega
  have e3 : (2 * j + 1) % 2 = 1 := by omega
  have e4 : (2 * j + 1) / 2 = j := by omega
  have e5 : (2 * j + 1 = 2 * P) = False := eq_false (by omega)
  funext l
  fin_cases l
  · by_cases hj0 : j = 0
    · subst hj0; simp [triState, odeState, h0]
    · by_cases hjP : j = P
      · subst hjP; simp [triState, odeState, hj0, hP]
      · have e6 : (2 * j = 2 * P) = False := eq_false (by omega)
        simp [triState, odeState, bvpX, hj0, hjP, e1, e2, e6]
  · by_cases hjP : j = P
    · subst hjP; simp [triState, odeState, bvpX]
    · simp [triState, odeState, bvpX, hjP, e3, e4, e5]

/-- **DLMF §3.7(iii)**, `β₀ = β₁ = 0`: on moving `w(z₀) = γ₀/α₀` and `w(z_P) = γ₁/α₁` to the
right-hand side of 3.7.13 and annihilating the elements below the subdiagonal (pivots
`A₁₁(τⱼ, zⱼ) ≠ 0`), the values `w′(z₀), w(z₁), …, w′(z_P)` of every solution of the
boundary-value problem satisfy the tridiagonal system (`bvpA`, `bvpB`, `bvpC`, `bvpF`;
`bvp_tridiagonal`). -/
theorem dlmf_3_7_iii_tridiag_of_sol (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
    (hh : DifferentiableOn ℂ h D) {zs : ℕ → ℂ} {P : ℕ} (hP1 : 1 ≤ P)
    (hP : IsTaylorPath D zs P) {α₀ γ₀ α₁ γ₁ : ℂ} (hα₀ : α₀ ≠ 0) (hα₁ : α₁ ≠ 0)
    (hpiv : ∀ j < P, stepA f g zs j 0 0 ≠ 0) {w : ℂ → ℂ} (hw : IsInhomSolution D f g h w)
    (hb₀ : IsBC α₀ 0 γ₀ (odeState w (zs 0))) (hb₁ : IsBC α₁ 0 γ₁ (odeState w (zs P))) :
    ∀ r, 1 ≤ r → r ≤ 2 * P →
      TriRow (stepA f g zs) (stepB f g h zs) P (γ₀ / α₀) (γ₁ / α₁) (bvpX w zs P) r := by
  have h0 : w (zs 0) = γ₀ / α₀ := by
    rw [eq_div_iff hα₀]; simp only [IsBC, odeState] at hb₀; simpa [mul_comm] using hb₀
  have h1 : w (zs P) = γ₁ / α₁ := by
    rw [eq_div_iff hα₁]; simp only [IsBC, odeState] at hb₁; simpa [mul_comm] using hb₁
  rw [triRows_iff hpiv]
  intro j hj
  rw [triState_bvpX hP1 h0 h1 (by omega), triState_bvpX hP1 h0 h1 hj.le]
  exact odeState_succ hf hg hh hw hP hj

/-- **DLMF §3.7(iii)**, `β₀ = β₁ = 0`, conversely: every solution `x` of the tridiagonal system
gives the values `w′(z₀), w(z₁), …, w′(z_P)` of a solution `w` of the boundary-value problem. -/
theorem dlmf_3_7_iii_sol_of_tridiag (hD : IsSCDomain D) (hf : DifferentiableOn ℂ f D)
    (hg : DifferentiableOn ℂ g D) (hh : DifferentiableOn ℂ h D) {zs : ℕ → ℂ} {P : ℕ}
    (hP1 : 1 ≤ P) (hP : IsTaylorPath D zs P) {α₀ γ₀ α₁ γ₁ : ℂ} (hα₀ : α₀ ≠ 0) (hα₁ : α₁ ≠ 0)
    (hpiv : ∀ j < P, stepA f g zs j 0 0 ≠ 0) {x : ℕ → ℂ}
    (hx : ∀ r, 1 ≤ r → r ≤ 2 * P →
      TriRow (stepA f g zs) (stepB f g h zs) P (γ₀ / α₀) (γ₁ / α₁) x r) :
    ∃ w, IsInhomSolution D f g h w ∧ IsBC α₀ 0 γ₀ (odeState w (zs 0)) ∧
      IsBC α₁ 0 γ₁ (odeState w (zs P)) ∧
      ∀ j ≤ P, odeState w (zs j) = triState P (γ₀ / α₀) (γ₁ / α₁) x j := by
  rw [triRows_iff hpiv] at hx
  set y : Fin (P + 1) × Fin 2 → ℂ := fun c => triState P (γ₀ / α₀) (γ₁ / α₁) x c.1 c.2
  have hA : bandAP f g zs P *ᵥ y = bandB f g h zs P := by
    rw [bandAP_mulVec_eq_iff]
    intro j
    simpa [y, Fin.val_succ, Fin.val_castSucc] using hx j j.isLt
  have hb₀ : IsBC α₀ 0 γ₀ (fun l => y (0, l)) := by
    simp only [IsBC, y, triState, Fin.val_zero]
    simp [mul_div_cancel₀ _ hα₀]
  have hb₁ : IsBC α₁ 0 γ₁ (fun l => y (Fin.last P, l)) := by
    simp only [IsBC, y, triState, Fin.val_last]
    simp [show P ≠ 0 by omega, mul_div_cancel₀ _ hα₁]
  obtain ⟨w, hw, hw₀, hw₁, hy⟩ :=
    (dlmf_3_7_13_14 hD hf hg hh hP α₀ 0 γ₀ α₁ 0 γ₁ y).mp ⟨hA, hb₀, hb₁⟩
  refine ⟨w, hw, hw₀, hw₁, fun j hj => ?_⟩
  funext l
  have := congrFun hy (⟨j, by omega⟩, l)
  simpa [y, bandW] using this.symm

/-- **DLMF §3.7(iii)**: "The equations can then be solved by the method of §3.2(ii)": when the
pivots `d₁, …, d_{2P}` of 3.2.10 for the reduced system do not vanish, forward elimination and
back substitution (`triX`, 3.2.11–3.2.12) give the values `w′(z₀), w(z₁), …, w′(z_P)` of a
solution `w` of the boundary-value problem. -/
theorem dlmf_3_7_iii_solve (hD : IsSCDomain D) (hf : DifferentiableOn ℂ f D)
    (hg : DifferentiableOn ℂ g D) (hh : DifferentiableOn ℂ h D) {zs : ℕ → ℂ} {P : ℕ}
    (hP1 : 1 ≤ P) (hP : IsTaylorPath D zs P) {α₀ γ₀ α₁ γ₁ : ℂ} (hα₀ : α₀ ≠ 0) (hα₁ : α₁ ≠ 0)
    (hpiv : ∀ j < P, stepA f g zs j 0 0 ≠ 0)
    (hd : ∀ j, 1 ≤ j → j ≤ 2 * P →
      triD (bvpA (stepA f g zs)) (bvpB (stepA f g zs) P) (bvpC P) j ≠ 0) :
    ∃ w, IsInhomSolution D f g h w ∧ IsBC α₀ 0 γ₀ (odeState w (zs 0)) ∧
      IsBC α₁ 0 γ₁ (odeState w (zs P)) ∧
      ∀ j ≤ P, odeState w (zs j) = triState P (γ₀ / α₀) (γ₁ / α₁)
        (triX (bvpA (stepA f g zs)) (bvpB (stepA f g zs) P) (bvpC P)
          (bvpF (stepA f g zs) (stepB f g h zs) P (γ₀ / α₀) (γ₁ / α₁)) (2 * P)) j := by
  refine dlmf_3_7_iii_sol_of_tridiag hD hf hg hh hP1 hP hα₀ hα₁ hpiv fun r h1 h2 => ?_
  exact three_term_of_tridiag _ _ _ _ _ (tridiag_solve (n := 2 * P) _ _ _ _ hd)
    (bvp_tridiagonal (M := stepA f g zs) (P := P)).1
    (bvp_tridiagonal (M := stepA f g zs) (P := P)).2 h1 h2

end BVP

/-! ### "This can happen only for inhomogeneous equations" -/

section Growth

variable {D : Set ℂ} {f g : ℂ → ℂ}

/-- Any three solutions of the homogeneous equation (1.13.1) are linearly dependent. -/
theorem exists_dep_three (hD : IsSCDomain D) (hf : DifferentiableOn ℂ f D)
    (hg : DifferentiableOn ℂ g D) {u v w : ℂ → ℂ} (hu : IsODESolution D f g u)
    (hv : IsODESolution D f g v) (hw : IsODESolution D f g w) :
    ∃ a b c : ℂ, (a, b, c) ≠ 0 ∧ ∀ z ∈ D, a * u z + b * v z + c * w z = 0 := by
  obtain ⟨z₀, hz₀⟩ := hD.isConnected.nonempty
  set Mx : Matrix (Fin 3) (Fin 3) ℂ :=
    !![u z₀, v z₀, w z₀; deriv u z₀, deriv v z₀, deriv w z₀; 0, 0, 0]
  have hdet : Mx.det = 0 := Matrix.det_eq_zero_of_row_eq_zero 2 fun j => by
    fin_cases j <;> rfl
  obtain ⟨k, hk0, hk⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have e0 := congrFun hk 0
  have e1 := congrFun hk 1
  simp [Mx, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e0 e1
  refine ⟨k 0, k 1, k 2, fun h => hk0 ?_, fun z hz => ?_⟩
  · simp only [Prod.mk_eq_zero] at h
    funext i
    fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  · have hS := (hu.linearCombo hD.isOpen hv (k 0) (k 1)).linearCombo hD.isOpen hw 1 (k 2)
    have hd := (hu.linearCombo hD.isOpen hv (k 0) (k 1)).hasDerivAt_linearCombo hD.isOpen hw 1
      (k 2) hz₀
    have hd' := hu.hasDerivAt_linearCombo hD.isOpen hv (k 0) (k 1) hz₀
    have := dlmf_1_13_i_eq_zero hD hf hg hz₀ hS (by linear_combination e0)
      (by rw [hd.deriv, hd'.deriv]; linear_combination e1) z hz
    simpa using this

/-- **DLMF §3.7(iii)**: "This can happen only for inhomogeneous equations." No solution `w` of the
homogeneous equation has a rate of growth along `l` intermediate to those of two other solutions
`u` (faster: `w/u → 0`) and `v` (slower: `v/w → 0`). -/
theorem dlmf_3_7_iii_hom_not_intermediate (hD : IsSCDomain D) (hf : DifferentiableOn ℂ f D)
    (hg : DifferentiableOn ℂ g D) {u v w : ℂ → ℂ} (hu : IsODESolution D f g u)
    (hv : IsODESolution D f g v) (hw : IsODESolution D f g w) {l : Filter ℂ} [l.NeBot]
    (hl : ∀ᶠ z in l, z ∈ D) (hne : ∀ᶠ z in l, u z ≠ 0 ∧ v z ≠ 0 ∧ w z ≠ 0)
    (hwu : Tendsto (fun z => w z / u z) l (𝓝 0)) (hvw : Tendsto (fun z => v z / w z) l (𝓝 0)) :
    False := by
  obtain ⟨a, b, c, habc, hrel⟩ := exists_dep_three hD hf hg hu hv hw
  have hvu : Tendsto (fun z => v z / u z) l (𝓝 0) := by
    have := hvw.mul hwu
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [hne] with z hz
    field_simp [hz.2.2]
  have ha : a = 0 := by
    have h1 : Tendsto (fun z => a + b * (v z / u z) + c * (w z / u z)) l
        (𝓝 (a + b * 0 + c * 0)) :=
      (tendsto_const_nhds.add (hvu.const_mul b)).add (hwu.const_mul c)
    have h2 : (fun z => a + b * (v z / u z) + c * (w z / u z)) =ᶠ[l] fun _ => 0 := by
      filter_upwards [hl, hne] with z hz hz'
      have := hrel z hz
      field_simp [hz'.1]
      linear_combination this
    simpa using tendsto_nhds_unique (h1.congr' h2) tendsto_const_nhds
  have hc : c = 0 := by
    have h1 : Tendsto (fun z => b * (v z / w z) + c) l (𝓝 (b * 0 + c)) :=
      (hvw.const_mul b).add tendsto_const_nhds
    have h2 : (fun z => b * (v z / w z) + c) =ᶠ[l] fun _ => 0 := by
      filter_upwards [hl, hne] with z hz hz'
      have := hrel z hz
      rw [ha] at this
      field_simp [hz'.2.2]
      linear_combination this
    simpa using tendsto_nhds_unique (h1.congr' h2) tendsto_const_nhds
  obtain ⟨z, hz, hz'⟩ := (hl.and hne).exists
  have := hrel z hz
  rw [ha, hc] at this
  have hb : b = 0 := by
    simpa [hz'.2.1] using this
  exact habc (by simp [ha, hb, hc])

/-- The ray `z → +∞` along the positive real axis. -/
def posRealRay : Filter ℂ := Filter.map ((↑) : ℝ → ℂ) atTop

instance : posRealRay.NeBot := by unfold posRealRay; infer_instance

theorem tendsto_exp_neg_posRealRay (k : ℕ) :
    Tendsto (fun z => Complex.exp (-z) ^ (k + 1)) posRealRay (𝓝 0) := by
  unfold posRealRay
  rw [tendsto_map'_iff]
  have h := ((Complex.continuous_ofReal.tendsto 0).comp
    Real.tendsto_exp_neg_atTop_nhds_zero).pow (k + 1)
  rw [Complex.ofReal_zero, zero_pow (Nat.succ_ne_zero k)] at h
  refine h.congr fun x => ?_
  simp [Complex.ofReal_exp]

/-- **DLMF §3.7(iii)**: for an inhomogeneous equation the situation does occur. For
`w″ − w = −1` along the positive real axis the solution `w = 1` is intermediate to the solutions
`eᶻ` (dominant) and `e⁻ᶻ` (recessive) of `w″ − w = 0`. -/
theorem dlmf_3_7_iii_inhom_intermediate :
    IsODESolution univ (fun _ => 0) (fun _ => -1) Complex.exp ∧
      IsODESolution univ (fun _ => 0) (fun _ => -1) (fun z => Complex.exp (-z)) ∧
      IsInhomSolution univ (fun _ => 0) (fun _ => -1) (fun _ => -1) (fun _ => 1) ∧
      Tendsto (fun z => Complex.exp (-z) / Complex.exp z) posRealRay (𝓝 0) ∧
      Tendsto (fun z => (1 : ℂ) / Complex.exp z) posRealRay (𝓝 0) ∧
      Tendsto (fun z => Complex.exp (-z) / 1) posRealRay (𝓝 0) := by
  refine ⟨isODESolution_exp, isODESolution_exp_neg,
    ⟨differentiableOn_const _, fun z _ => by simp⟩, ?_, ?_, ?_⟩
  · refine (tendsto_exp_neg_posRealRay 1).congr fun z => ?_
    rw [div_eq_mul_inv, ← Complex.exp_neg, pow_two]
  · refine (tendsto_exp_neg_posRealRay 0).congr fun z => ?_
    rw [pow_one, one_div, Complex.exp_neg]
  · refine (tendsto_exp_neg_posRealRay 0).congr fun z => ?_
    rw [pow_one, div_one]

end Growth

end Azurite.DLMF
