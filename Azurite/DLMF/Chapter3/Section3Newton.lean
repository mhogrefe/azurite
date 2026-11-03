/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section3Divided

/-!
# DLMF §3.3(iv): Newton's interpolation formula

Nodes are a sequence `z : ℕ → F`, distinct on `{0, …, n}` (`Set.InjOn z (Set.Iic n)`).

* Updating: `newton_update`, `P_{n+1}(z) = P_n(z) + (z − z₀)⋯(z − z_n) [z₀, …, z_{n+1}] f`.
  Proof: `P_{n+1} − [z₀, …, z_{n+1}] f · ω_{n+1}` has degree `≤ n` (its `z^{n+1}` coefficient
  cancels by `divDiff_eq_coeff`) and interpolates `f` at `z₀, …, z_n`, so it is `P_n`.
* 3.3.38: `newton_interpolate` (the polynomial identity, by induction with `newton_update`),
  `dlmf_3_3_38` (with the remainder `R_n` of §3.3(i)).
* Confluence: `divDiff_confluent`, the limiting form `[z₀, …, z₀] f = f^{(k)}(z₀)/k!` for real
  nodes (`k + 1` distinct points tending to `z₀`), from 3.3.36 and continuity of `f^{(k)}` at
  `z₀`.
-/

open Polynomial Finset Lagrange

namespace Azurite.DLMF

theorem injective_of_injOn_Iic {α : Type*} {z : ℕ → α} {n : ℕ} (hz : Set.InjOn z (Set.Iic n)) :
    Function.Injective fun i : Fin (n + 1) => z i := fun i j h =>
  Fin.ext (hz (Set.mem_Iic.mpr (Nat.lt_succ_iff.mp i.2)) (Set.mem_Iic.mpr (Nat.lt_succ_iff.mp j.2))
    h)

section Field

variable {F : Type*} [Field F]

/-- **Updating** (§3.3(iv)): adding the node `z_{n+1}` adds the single term
`(z − z₀)⋯(z − z_n) [z₀, …, z_{n+1}] f`. -/
theorem newton_update (z : ℕ → F) (n : ℕ) (hz : Set.InjOn z (Set.Iic (n + 1))) (f : F → F)
    (w : F) :
    (interpolate univ (fun i : Fin (n + 2) => z i) (fun k => f (z k))).eval w =
      (interpolate univ (fun i : Fin (n + 1) => z i) (fun k => f (z k))).eval w +
        (∏ j ∈ range (n + 1), (w - z j)) * divDiff (n + 1) (fun i : Fin (n + 2) => z i) f := by
  have hinj1 := injective_of_injOn_Iic hz
  have hinj0 := injective_of_injOn_Iic (hz.mono (Set.Iic_subset_Iic.mpr (Nat.le_succ n)))
  obtain ⟨hd1, hev1, -⟩ := lagrange_unique _ hinj1 (fun k => f (z k))
  obtain ⟨-, -, huniq0⟩ := lagrange_unique _ hinj0 (fun k => f (z k))
  have hdd := divDiff_eq_coeff _ hinj1 f
  set P1 := interpolate univ (fun i : Fin (n + 2) => z i) (fun k => f (z k))
  set P0 := interpolate univ (fun i : Fin (n + 1) => z i) (fun k => f (z k))
  set ω := nodal univ (fun i : Fin (n + 1) => z i)
  set d := divDiff (n + 1) (fun i : Fin (n + 2) => z i) f
  have hωdeg : ω.natDegree = n + 1 := by rw [natDegree_nodal, card_univ, Fintype.card_fin]
  have hlead := (nodal_monic (s := univ) (v := fun i : Fin (n + 1) => z i)).coeff_natDegree
  rw [hωdeg] at hlead
  have key : P1 - C d * ω = P0 := by
    refine huniq0 _ (natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_) fun k => ?_
    · rcases (show N = n + 1 ∨ n + 1 < N by omega) with rfl | hN'
      · rw [coeff_sub, coeff_C_mul, hlead, hdd]; ring
      · rw [coeff_sub, coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by omega : P1.natDegree < N),
          coeff_eq_zero_of_natDegree_lt (by omega : ω.natDegree < N)]
        ring
    · have h1 := hev1 k.castSucc
      simp only [Fin.val_castSucc] at h1
      have hω0 : ω.eval (z k) = 0 :=
        eval_nodal_at_node (v := fun i : Fin (n + 1) => z i) (mem_univ k)
      rw [eval_sub, eval_mul, eval_C, h1, hω0, mul_zero, sub_zero]
  rw [← key, eval_sub, eval_mul, eval_C, eval_nodal,
    Fin.prod_univ_eq_prod_range (fun j => w - z j) (n + 1)]
  ring

/-- **DLMF 3.3.38**, the polynomial part: `P_n(z) = ∑_{k=0}^{n} (z − z₀)⋯(z − z_{k−1})
[z₀, …, z_k] f`. -/
theorem newton_interpolate (z : ℕ → F) (f : F → F) (w : F) :
    ∀ n : ℕ, Set.InjOn z (Set.Iic n) →
      (interpolate univ (fun i : Fin (n + 1) => z i) (fun k => f (z k))).eval w =
        ∑ k ∈ range (n + 1), (∏ j ∈ range k, (w - z j)) *
          divDiff k (fun i : Fin (k + 1) => z i) f
  | 0, hz => by
    obtain ⟨-, -, huniq⟩ := lagrange_unique _ (injective_of_injOn_Iic hz) (fun k => f (z k))
    rw [← huniq (C (f (z 0))) (by simp) fun k => by
      rw [Subsingleton.elim (α := Fin 1) k 0, eval_C]; rfl]
    simp [divDiff]
  | n + 1, hz => by
    rw [newton_update z n hz f w,
      newton_interpolate z f w n (hz.mono (Set.Iic_subset_Iic.mpr (Nat.le_succ n))),
      sum_range_succ _ (n + 1)]

/-- **DLMF 3.3.38**: `f(z) = [z₀] f + (z − z₀)[z₀, z₁] f + ⋯ + (z − z₀)⋯(z − z_{n−1})
[z₀, …, z_n] f + R_n(z)`, with `R_n` the remainder of §3.3(i). -/
theorem dlmf_3_3_38 (z : ℕ → F) (n : ℕ) (hz : Set.InjOn z (Set.Iic n)) (f : F → F) (w : F) :
    f w = ∑ k ∈ range (n + 1), (∏ j ∈ range k, (w - z j)) *
        divDiff k (fun i : Fin (k + 1) => z i) f +
      lagrangeRem (fun i : Fin (n + 1) => z i) f w := by
  rw [lagrangeRem, ← newton_interpolate z f w n hz]
  ring

end Field

/-! ### Confluence -/

/-- **Confluence** (§3.3(iv)): `[z₀, z₀, …, z₀] f = f^{(k)}(z₀)/k!` (`k + 1` coincident points)
as the limiting form: the divided difference at `k + 1` distinct real points within `δ` of
`z₀` tends to `f^{(k)}(z₀)/k!`, for `f` that is `k` times differentiable on an open set around
`z₀` with `f^{(k)}` continuous at `z₀`. -/
theorem divDiff_confluent {k : ℕ} (f : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U) {z₀ : ℝ}
    (hz₀ : z₀ ∈ U) (hd : ∀ j < k, DifferentiableOn ℝ (iteratedDeriv j f) U)
    (hc : ContinuousAt (iteratedDeriv k f) z₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ x : Fin (k + 1) → ℝ, Function.Injective x → (∀ i, |x i - z₀| < δ) →
      |divDiff k x f - iteratedDeriv k f z₀ / k.factorial| < ε := by
  intro ε hε
  have hk : (0 : ℝ) < k.factorial := by positivity
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  obtain ⟨δ₂, hδ₂, hcont⟩ := Metric.continuousAt_iff.mp hc (ε * k.factorial) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx hxδ => ?_⟩
  have hmem : ∀ y ∈ univ.image x, |y - z₀| < min δ₁ δ₂ := fun y hy => by
    obtain ⟨i, -, rfl⟩ := mem_image.mp hy
    exact hxδ i
  have hIcc : ∀ y ∈ Set.Icc ((univ.image x).min' (univ_nonempty.image x))
      ((univ.image x).max' (univ_nonempty.image x)), |y - z₀| < min δ₁ δ₂ := fun y hy => by
    have h1 := abs_lt.mp (hmem _ (min'_mem _ (univ_nonempty.image x)))
    have h2 := abs_lt.mp (hmem _ (max'_mem _ (univ_nonempty.image x)))
    exact abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨ξ, hξ, hdd⟩ := dlmf_3_3_36 x hx f hU hd fun y hy =>
    hball (by rw [Metric.mem_ball, Real.dist_eq]; exact (hIcc y hy).trans_le (min_le_left _ _))
  have hξc : |iteratedDeriv k f ξ - iteratedDeriv k f z₀| < ε * k.factorial := by
    have := hcont (x := ξ) (by rw [Real.dist_eq]; exact (hIcc ξ hξ).trans_le (min_le_right _ _))
    rwa [Real.dist_eq] at this
  rw [hdd, ← sub_div, abs_div, abs_of_pos hk, div_lt_iff₀ hk]
  exact hξc

end Azurite.DLMF
