/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section5
import Azurite.DLMF.Chapter2.Section5Rectangle

/-!
# DLMF §2.5(i): the shift of the contour (2.5.6–2.5.7)

If `x^{−z} 𝓜f(1 − z) 𝓜h(z)` continues to a function `F` analytic on a neighbourhood of the strip
`d ≤ ℜz ≤ c` except for finitely many poles `S` in `d < ℜz < c`, and the contour `ℜz = c` "can
be translated to `ℜz = d`" — the integrals over the horizontal segments `[d, c] ± iT` tend to
`0` and the symmetric truncations of the integral over `ℜz = d` converge — then
`I(x) = ∑_{d<ℜz<c} res[x^{−z} 𝓜f(1 − z) 𝓜h(z)] + E(x)` (2.5.6) with
`E(x) = (2πi)⁻¹ ∫_{d−i∞}^{d+i∞} x^{−z} 𝓜f(1 − z) 𝓜h(z) dz` (2.5.7). The proof applies the residue
theorem on the rectangle `[d, c] × [−T, T]` (`rectBoundary_eq_sum_residues`) and lets `T → ∞`.
The line integrals are written with the real parameter `y`, `z = c + iy`, so `E(x)` appears as
`(2π)⁻¹ lim_T ∫_{−T}^{T} F(d + iy) dy`.
-/

open MeasureTheory Filter Topology Set Complex Metric
open scoped Real

namespace Azurite.DLMF

/-- The boundary integral over the rectangle `[d, c] × [−T, T]`. -/
theorem rectBoundary_strip (F : ℂ → ℂ) (d c T : ℝ) :
    rectBoundary F ⟨d, -T⟩ ⟨c, T⟩ =
      (∫ σ in d..c, F (σ - T * I)) - (∫ σ in d..c, F (σ + T * I)) +
        I * (∫ y in (-T)..T, F (c + y * I)) - I * ∫ y in (-T)..T, F (d + y * I) := by
  simp only [rectBoundary, smul_eq_mul]
  have : (∫ x in d..c, F (↑x + ↑(-T) * I)) = ∫ σ in d..c, F (↑σ - ↑T * I) :=
    intervalIntegral.integral_congr fun σ _ => by
      congr 1
      push_cast
      ring
  rw [this]

/-- **DLMF 2.5.6–2.5.7**: with `F` the meromorphic continuation of
`x^{−z} 𝓜f(1 − z) 𝓜h(z)` to a neighbourhood `U` of the strip `d ≤ ℜz ≤ c`, poles `S` in the
open strip, horizontal integrals tending to `0` and the symmetric line integrals on `ℜz = d`
converging to `E`, `I(x) = ∑_{s ∈ S} res_s F + (2π)⁻¹ E`. -/
theorem dlmf_2_5_6 {f h : ℝ → ℂ} {c d : ℝ} (hdc : d < c) (hf : MellinConvergent f (1 - c))
    (hh : MellinConvergent h c)
    (hint : VerticalIntegrable (mellin h) c ∨ Integrable fun y : ℝ => mellin f (1 - c - y * I))
    {x : ℝ} (hx : 0 < x) {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hstrip : {z : ℂ | z.re ∈ Icc d c} ⊆ U) {S : Finset ℂ}
    (hS : ∀ s ∈ S, d < s.re ∧ s.re < c) (hFd : DifferentiableOn ℂ F (U \ ↑S))
    (hFeq : ∀ y : ℝ, F (c + y * I) =
      (x : ℂ) ^ (-((c : ℂ) + y * I)) * mellin f (1 - (c + y * I)) * mellin h (c + y * I))
    (hFint : Integrable fun y : ℝ => F (c + y * I)) (R : ℂ → ℝ)
    (hR : ∀ s ∈ S, 0 < R s ∧ ball s (R s) ⊆ U ∧ ∀ t ∈ S, t ≠ s → R s ≤ dist t s)
    (htop : Tendsto (fun T : ℝ => ∫ σ in d..c, F (σ + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ σ in d..c, F (σ - T * I)) atTop (𝓝 0)) {E : ℂ}
    (hE : Tendsto (fun T : ℝ => ∫ y in (-T)..T, F (d + y * I)) atTop (𝓝 E)) :
    mellinConvInt f h x = ∑ s ∈ S, residue F s (R s) + (2 * π : ℂ)⁻¹ * E := by
  -- the poles lie below height `M`
  obtain ⟨M, hM⟩ := (S.finite_toSet.image fun s : ℂ => |s.im|).bddAbove
  have hM' : ∀ s ∈ S, |s.im| ≤ M := fun s hs => hM ⟨s, hs, rfl⟩
  -- the rectangle identity for `T > max M 0`
  have hrect : ∀ T : ℝ, max M 0 < T →
      rectBoundary F ⟨d, -T⟩ ⟨c, T⟩ = 2 * π * I * ∑ s ∈ S, residue F s (R s) := by
    intro T hT
    have hT0 : 0 < T := lt_of_le_of_lt (le_max_right _ _) hT
    have hTM : M < T := lt_of_le_of_lt (le_max_left _ _) hT
    refine rectBoundary_eq_sum_residues (p := ⟨d, -T⟩) (q := ⟨c, T⟩) hdc (by simp; linarith) hU
      (fun z hz => hstrip hz.1) (fun s hs => ⟨(hS s hs).1, (hS s hs).2, ?_, ?_⟩) hFd R hR
    · have := (abs_le.mp (hM' s hs)).1
      show -T < s.im
      linarith
    · have := (abs_le.mp (hM' s hs)).2
      show s.im < T
      linarith
  set Φ : ℝ → ℂ := fun T => rectBoundary F ⟨d, -T⟩ ⟨c, T⟩ with hΦ
  have h1 : Tendsto Φ atTop (𝓝 (2 * π * I * ∑ s ∈ S, residue F s (R s))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (max M 0)] with T hT
    exact (hrect T hT).symm
  set L : ℂ := ∫ y : ℝ, F ((c : ℂ) + y * I) with hLdef
  have hC : Tendsto (fun T : ℝ => ∫ y in (-T)..T, F (c + y * I)) atTop (𝓝 L) :=
    intervalIntegral_tendsto_integral hFint tendsto_neg_atTop_atBot tendsto_id
  have h2 : Tendsto Φ atTop (𝓝 (0 - 0 + I * L - I * E)) := by
    have := ((hbot.sub htop).add (hC.const_mul I)).sub (hE.const_mul I)
    refine this.congr' (Eventually.of_forall fun T => ?_)
    show _ = rectBoundary F ⟨d, -T⟩ ⟨c, T⟩
    rw [rectBoundary_strip]
  have hkey := tendsto_nhds_unique h1 h2
  have hL : L = 2 * π * ∑ s ∈ S, residue F s (R s) + E := by
    have : I * L = I * (2 * π * ∑ s ∈ S, residue F s (R s) + E) := by
      linear_combination -hkey
    exact mul_left_cancel₀ I_ne_zero this
  rw [dlmf_2_5_5 hf hh hint hx]
  have hF' : (∫ y : ℝ, (x : ℂ) ^ (-((c : ℂ) + y * I)) * mellin f (1 - (c + y * I)) *
      mellin h (c + y * I)) = L :=
    integral_congr_ae (Eventually.of_forall fun y => (hFeq y).symm)
  have hπ : (2 * π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [hF', hL, mul_add, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]

end Azurite.DLMF
