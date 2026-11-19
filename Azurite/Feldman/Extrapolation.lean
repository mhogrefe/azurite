/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Feldman.Hermite
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Extrapolation at the points `πix` (Fel'dman's Lemma B, analytic part)

Lemma 7 (`norm_le_of_small_jets`) at the nodes `a_x = πix`, `0 ≤ x ≤ X`, with multiplicity `T`:
`ρ = π/2`, `D = 1` (every factor of `Q_x` is at least `π/2 > 1` on the disc of radius `π/2`
round `a_x`), outer radius `r = 9πX`, `L = 10πX`, `d = 8πX`, and `L_z = 4πX` for
`|z| ≤ 2πX + 1`, so that `L_z/d = 1/2`:

  `|φ⁽ⁱ⁾(πix)| ≤ δ` (`i < T`, `x ≤ X`),  `|φ| ≤ M` on `|w| = 9πX`
    ⟹  `|φ(z)| ≤ E + 2^(−T(X+1)) (M + E)` for `|z| ≤ 2πX + 1` (`extrapolate`),

`E = (X + 1) (10πX)^(TX) T δ e^{π/2} (20X)^T`; and by Cauchy's estimate on circles of radius `1`
the derivatives `φ⁽σ⁾(πix')`, `x' ≤ 2X`, are at most `σ!` times that (`extrapolate_deriv`).
-/

namespace Azurite.Feldman

open Complex Metric Finset

/-- The bound `E` for the Hermite interpolant at the nodes `πix`, `x ≤ X`. -/
noncomputable def extE (X T : ℕ) (δ : ℝ) : ℝ :=
  ((X + 1 : ℕ) : ℝ) * ((10 * Real.pi * X) ^ (T * (X + 1 - 1))
    * (T * (δ * Real.exp (Real.pi / 2) / 1) * (10 * Real.pi * X / (Real.pi / 2)) ^ T))

theorem norm_node_sub (x x' : ℕ) :
    ‖Complex.I * (x : ℂ) * Real.pi - Complex.I * (x' : ℂ) * Real.pi‖
      = Real.pi * |(x : ℝ) - x'| := by
  have : Complex.I * (x : ℂ) * Real.pi - Complex.I * (x' : ℂ) * Real.pi
      = Complex.I * (((Real.pi * ((x : ℝ) - x') : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [this, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos Real.pi_pos]

theorem norm_node (x : ℕ) : ‖Complex.I * (x : ℂ) * Real.pi‖ = Real.pi * x := by
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_comm]

/-- **Lemma 7 at the nodes `πix`.** -/
theorem extrapolate {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) {X T : ℕ} (hX : 1 ≤ X) {δ M : ℝ}
    (hδ0 : 0 ≤ δ)
    (hδ : ∀ x ≤ X, ∀ i < T, ‖iteratedDeriv i φ (Complex.I * x * Real.pi)‖ ≤ δ)
    (hM : ∀ w : ℂ, ‖w‖ = 9 * Real.pi * X → ‖φ w‖ ≤ M) {z : ℂ}
    (hz : ‖z‖ ≤ 2 * Real.pi * X + 1) :
    ‖φ z‖ ≤ extE X T δ + (1 / 2) ^ (T * (X + 1)) * (M + extE X T δ) := by
  have hπ := Real.pi_pos
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hπX : (3 : ℝ) < Real.pi * X := by nlinarith
  set a : ℕ → ℂ := fun x => Complex.I * (x : ℂ) * Real.pi with ha
  have hmemI : ∀ x, x ∈ range (X + 1) ↔ x ≤ X := fun x => by
    rw [mem_range]
    omega
  have hxr : ∀ x ∈ range (X + 1), (x : ℝ) ≤ X := fun x hx => by
    exact_mod_cast (hmemI x).mp hx
  have hinj : Set.InjOn a (range (X + 1) : Set ℕ) := by
    intro x _ x' _ h
    have h0 : ‖a x - a x'‖ = 0 := by rw [h, sub_self, norm_zero]
    rw [ha, norm_node_sub] at h0
    have : |(x : ℝ) - x'| = 0 := by
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 hπ.ne'
      · exact h1
    have : (x : ℝ) = x' := by linarith [abs_eq_zero.mp this]
    exact_mod_cast this
  have hD : ∀ x ∈ range (X + 1), ∀ ξ ∈ closedBall (a x) (Real.pi / 2),
      (1 : ℝ) ≤ ‖hermQ (range (X + 1)) a T x ξ‖ := by
    intro x _ ξ hξ
    unfold hermQ
    rw [norm_prod]
    have h1 : (1 : ℝ) = ∏ _x' ∈ (range (X + 1)).erase x, (1 : ℝ) := by simp
    rw [h1]
    refine Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun x' hx' => ?_
    rw [norm_pow]
    refine one_le_pow₀ ?_
    have hne : x' ≠ x := Finset.ne_of_mem_erase hx'
    have hd : (1 : ℝ) ≤ |(x : ℝ) - x'| := by
      have : (x : ℤ) ≠ x' := by exact_mod_cast hne.symm
      have h2 : (1 : ℤ) ≤ |(x : ℤ) - x'| := Int.one_le_abs (sub_ne_zero.mpr this)
      exact_mod_cast h2
    have h3 : ‖a x - a x'‖ ≤ ‖a x - ξ‖ + ‖ξ - a x'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h4 : ‖a x - ξ‖ ≤ Real.pi / 2 := by
      rw [← dist_eq_norm, dist_comm]
      exact mem_closedBall.mp hξ
    rw [ha, norm_node_sub] at h3
    nlinarith
  have hnode : ∀ x ∈ range (X + 1), ‖a x‖ ≤ Real.pi * X := fun x hx => by
    rw [ha, norm_node]
    exact mul_le_mul_of_nonneg_left (hxr x hx) hπ.le
  have hmain := norm_le_of_small_jets (I := range (X + 1)) (a := a) (T := T) hφ hinj
    (ρ := Real.pi / 2) (D := 1) (δ := δ) (L := 10 * Real.pi * X) (r := 9 * Real.pi * X)
    (d := 8 * Real.pi * X) (M := M) (Lz := 4 * Real.pi * X) (by positivity) one_pos hD hδ0
    (fun x hx i hi => hδ x ((hmemI x).mp hx) i hi) (by nlinarith)
    (fun w hw x hx => (norm_sub_le _ _).trans (by linarith [hnode x hx]))
    (by positivity)
    (fun w hw x hx => by
      have h1 : ‖w‖ = 9 * Real.pi * X := mem_sphere_zero_iff_norm.mp hw
      have h2 := norm_sub_norm_le w (a x)
      linarith [hnode x hx])
    (fun w hw => hM w (mem_sphere_zero_iff_norm.mp hw)) (z := z) (by nlinarith)
    (fun x hx => (norm_sub_le _ _).trans (by nlinarith [hnode x hx]))
  have hratio : 4 * Real.pi * X / (8 * Real.pi * X) = 1 / 2 := by
    field_simp
    ring
  rw [hratio, card_range] at hmain
  exact hmain

/-- **The derivatives at the points `πix'`, `x' ≤ 2X`.** -/
theorem extrapolate_deriv {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) {X T : ℕ} (hX : 1 ≤ X)
    {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ x ≤ X, ∀ i < T, ‖iteratedDeriv i φ (Complex.I * x * Real.pi)‖ ≤ δ)
    (hM : ∀ w : ℂ, ‖w‖ = 9 * Real.pi * X → ‖φ w‖ ≤ M) {x' : ℕ} (hx' : x' ≤ 2 * X) (σ : ℕ) :
    ‖iteratedDeriv σ φ (Complex.I * x' * Real.pi)‖
      ≤ σ.factorial * (extE X T δ + (1 / 2) ^ (T * (X + 1)) * (M + extE X T δ)) := by
  have h := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le σ one_pos
    (c := Complex.I * x' * Real.pi) hφ.diffContOnCl
    (C := extE X T δ + (1 / 2) ^ (T * (X + 1)) * (M + extE X T δ))
    (fun z hz => extrapolate hφ hX hδ0 hδ hM (by
      have h1 : ‖z - Complex.I * x' * Real.pi‖ = 1 := mem_sphere_iff_norm.mp hz
      have h2 : ‖z‖ ≤ ‖z - Complex.I * x' * Real.pi‖ + ‖Complex.I * (x' : ℂ) * Real.pi‖ := by
        have := norm_add_le (z - Complex.I * x' * Real.pi) (Complex.I * (x' : ℂ) * Real.pi)
        rwa [sub_add_cancel] at this
      rw [h1, norm_node] at h2
      have h3 : (x' : ℝ) ≤ 2 * X := by exact_mod_cast hx'
      nlinarith [Real.pi_pos]))
  rwa [one_pow, div_one] at h

end Azurite.Feldman
