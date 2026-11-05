/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section8
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue

/-!
# DLMF §3.8(ii): Newton's rule

* 3.8.4 (`newtonStep`), for real or complex `f` (`RCLike`).
* Simple zeros: with `f′` Lipschitz near `ζ` the error satisfies `|e_{n+1}| ≤ K |eₙ|²` on a ball
  mapped into itself (`newton_sq_estimate`, `newton_simple_zero_ball`). Hence local, quadratic
  convergence (`dlmf_3_8_ii_simple`), in particular for `f ∈ C²` near `ζ`, real or complex
  analytic (`dlmf_3_8_ii_simple_of_contDiffAt`, `newton_eventually_quadratic`).
* Multiple zeros `f = (z − ζ)ᵐ g`, `m ≥ 2`: the error is
  `(z − ζ)((m − 1)g + (z − ζ)g′)/(mg + (z − ζ)g′)` (`newton_error_of_factor`). So convergence is
  local and linear with ratio `→ (m − 1)/m`, and of no order `p > 1`. The rule with `f/f′`
  multiplied by `m` (`newtonStepMul`) converges quadratically (`dlmf_3_8_ii_multiple`). Complex
  analytic `f` satisfy the hypotheses (`exists_factor_of_multiplicity`).
* Real `f`, conditions (a) and (b) (`dlmf_3_8_ii_a`, `dlmf_3_8_ii_b`): monotonic convergence, and
  quadratic convergence eventually. The core is `newton_real_step`: by the mean value theorem
  `N(x) − ξ = (x − ξ)(1 − f′(c)/f′(x))`, and `|f′|` increases away from `ξ`
  (`(x₀ − ξ) f′ f″ ≥ 0`), so `N(x) − ξ = (x − ξ)(1 − t)` with
  `|f′(ξ)|/|f′(x₀)| ≤ t ≤ 1`. Then `newton_real_monotone`. In (b) the sign conditions are
  assumed on the closed interval `[x₀, x₁]`.

The Example is in `Section8NewtonExample` and `Section8NewtonTable`.
-/

open Filter Topology Metric

namespace Azurite.DLMF

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **DLMF 3.8.4**: `z_{n+1} = zₙ − f(zₙ)/f′(zₙ)`. -/
noncomputable def newtonStep (f : 𝕜 → 𝕜) (z : 𝕜) : 𝕜 := z - f z / deriv f z

/-! ### Simple zeros: local quadratic convergence -/

section Simple

/-- The Newton estimate `|N(z) − ζ| ≤ L |z − ζ|²/|f′(z)|` for `f′` `L`-Lipschitz on `B(ζ, r)`. -/
theorem newton_sq_estimate {f : 𝕜 → 𝕜} {ζ : 𝕜} {r L : ℝ} (hL0 : 0 ≤ L)
    (hf : ∀ z ∈ ball ζ r, DifferentiableAt 𝕜 f z)
    (hL : ∀ w ∈ ball ζ r, ∀ z ∈ ball ζ r, ‖deriv f w - deriv f z‖ ≤ L * ‖w - z‖)
    (hζ : f ζ = 0) {z : 𝕜} (hz : ‖z - ζ‖ < r / 2) :
    ‖newtonStep f z - ζ‖ * ‖deriv f z‖ ≤ L * ‖z - ζ‖ ^ 2 := by
  set s := closedBall z ‖ζ - z‖
  have hzs : z ∈ s := mem_closedBall_self (norm_nonneg _)
  have hζs : ζ ∈ s := by rw [mem_closedBall, dist_eq_norm]
  have hsub : s ⊆ ball ζ r := fun w hw => by
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball, dist_eq_norm]
    calc ‖w - ζ‖ = ‖(w - z) + (z - ζ)‖ := by abel_nf
      _ ≤ ‖w - z‖ + ‖z - ζ‖ := norm_add_le _ _
      _ ≤ ‖ζ - z‖ + ‖z - ζ‖ := by gcongr
      _ < r := by rw [norm_sub_rev ζ z]; linarith
  have hzr : z ∈ ball ζ r := hsub hzs
  set g : 𝕜 → 𝕜 := fun w => f w - deriv f z * w
  have hg : ∀ w ∈ s, HasDerivWithinAt g (deriv f w - deriv f z) s w := fun w hw =>
    (((hf w (hsub hw)).hasDerivAt.sub ((hasDerivAt_id w).const_mul (deriv f z))).congr_deriv
      (by simp)).hasDerivWithinAt
  have hmvt := (convex_closedBall z ‖ζ - z‖).norm_image_sub_le_of_norm_hasDerivWithin_le hg
    (C := L * ‖ζ - z‖) (fun w hw => by
      have := hL w (hsub hw) z hzr
      rw [mem_closedBall, dist_eq_norm] at hw
      exact this.trans (mul_le_mul_of_nonneg_left hw hL0)) hzs hζs
  rcases eq_or_ne (deriv f z) 0 with h0 | h0
  · rw [h0, norm_zero, mul_zero]; positivity
  have heq : newtonStep f z - ζ = (g ζ - g z) / deriv f z := by
    simp only [newtonStep, g, hζ]
    field_simp
    ring
  rw [heq, norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr h0), norm_sub_rev ζ z] at *
  calc ‖g ζ - g z‖ ≤ L * ‖z - ζ‖ * ‖z - ζ‖ := hmvt
    _ = L * ‖z - ζ‖ ^ 2 := by ring

/-- Near a simple zero, Newton's map maps a ball into itself, contracts by `1/2` and squares
the error: `|N(z) − ζ| ≤ K |z − ζ|²`. -/
theorem newton_simple_zero_ball {f : 𝕜 → 𝕜} {ζ : 𝕜} {r L : ℝ} (hr : 0 < r) (hL0 : 0 ≤ L)
    (hf : ∀ z ∈ ball ζ r, DifferentiableAt 𝕜 f z)
    (hL : ∀ w ∈ ball ζ r, ∀ z ∈ ball ζ r, ‖deriv f w - deriv f z‖ ≤ L * ‖w - z‖)
    (hζ : f ζ = 0) (hd : deriv f ζ ≠ 0) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ z ∈ ball ζ δ, newtonStep f z ∈ ball ζ δ ∧
      ‖newtonStep f z - ζ‖ ≤ K * ‖z - ζ‖ ^ 2 ∧ ‖newtonStep f z - ζ‖ ≤ ‖z - ζ‖ / 2 := by
  set d := ‖deriv f ζ‖
  have hd0 : 0 < d := norm_pos_iff.mpr hd
  set K := 2 * L / d
  have hK0 : 0 ≤ K := by positivity
  set δ := min (r / 2) (min (d / (2 * (L + 1))) (1 / (2 * (K + 1))))
  have hδ0 : 0 < δ := lt_min (by linarith) (lt_min (by positivity) (by positivity))
  have hδ1 : δ ≤ r / 2 := min_le_left _ _
  have hδ2 : δ ≤ d / (2 * (L + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ 1 / (2 * (K + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ0, K, hK0, fun z hz => ?_⟩
  rw [mem_ball, dist_eq_norm] at hz
  have hzr : z ∈ ball ζ r := by rw [mem_ball, dist_eq_norm]; linarith
  have hζr : ζ ∈ ball ζ r := mem_ball_self hr
  -- `|f′(z)| ≥ d/2`
  have hfz : d / 2 ≤ ‖deriv f z‖ := by
    have h1 := hL z hzr ζ hζr
    have h2 : L * ‖z - ζ‖ ≤ d / 2 := by
      calc L * ‖z - ζ‖ ≤ L * (d / (2 * (L + 1))) :=
            mul_le_mul_of_nonneg_left (hz.le.trans hδ2) hL0
        _ ≤ (L + 1) * (d / (2 * (L + 1))) := by gcongr; linarith
        _ = d / 2 := by field_simp
    have h3 := norm_sub_norm_le (deriv f ζ) (deriv f ζ - deriv f z)
    rw [sub_sub_cancel, norm_sub_rev] at h3
    linarith
  have hest := newton_sq_estimate hL0 hf hL hζ (z := z) (by linarith)
  have hq : ‖newtonStep f z - ζ‖ ≤ K * ‖z - ζ‖ ^ 2 := by
    have hpos : 0 < ‖deriv f z‖ := by linarith
    have : ‖newtonStep f z - ζ‖ * (d / 2) ≤ L * ‖z - ζ‖ ^ 2 :=
      (mul_le_mul_of_nonneg_left hfz (norm_nonneg _)).trans hest
    rw [show K * ‖z - ζ‖ ^ 2 = L * ‖z - ζ‖ ^ 2 / (d / 2) by simp only [K]; field_simp]
    rw [le_div_iff₀ (by positivity)]
    exact this
  have hhalf : ‖newtonStep f z - ζ‖ ≤ ‖z - ζ‖ / 2 := by
    refine hq.trans ?_
    have hKd : K * δ ≤ 1 / 2 := by
      calc K * δ ≤ K * (1 / (2 * (K + 1))) := mul_le_mul_of_nonneg_left hδ3 hK0
        _ ≤ (K + 1) * (1 / (2 * (K + 1))) := by gcongr; linarith
        _ = 1 / 2 := by field_simp
    calc K * ‖z - ζ‖ ^ 2 = (K * ‖z - ζ‖) * ‖z - ζ‖ := by ring
      _ ≤ (K * δ) * ‖z - ζ‖ := by gcongr
      _ ≤ 1 / 2 * ‖z - ζ‖ := by gcongr
      _ = ‖z - ζ‖ / 2 := by ring
  refine ⟨?_, hq, hhalf⟩
  rw [mem_ball, dist_eq_norm]
  have := norm_nonneg (z - ζ)
  linarith

/-- **DLMF §3.8(ii)**: "If `ζ` is a simple zero, then the iteration converges locally and
quadratically" — for `f′` Lipschitz near `ζ` (in particular for `f ∈ C²`, real or complex,
`dlmf_3_8_ii_simple_of_contDiffAt`). The errors satisfy `|e_{n+1}| ≤ K |eₙ|²`, and 3.8.3 holds
with `p = 2` whenever no iterate lands exactly on `ζ`. -/
theorem dlmf_3_8_ii_simple {f : 𝕜 → 𝕜} {ζ : 𝕜} {r L : ℝ} (hr : 0 < r) (hL0 : 0 ≤ L)
    (hf : ∀ z ∈ ball ζ r, DifferentiableAt 𝕜 f z)
    (hL : ∀ w ∈ ball ζ r, ∀ z ∈ ball ζ r, ‖deriv f w - deriv f z‖ ≤ L * ‖w - z‖)
    (hζ : f ζ = 0) (hd : deriv f ζ ≠ 0) :
    ConvergesLocally (newtonStep f) ζ ∧ ∃ δ > 0, ∃ K ≥ 0, ∀ z₀ ∈ ball ζ δ,
      (∀ n, ‖(newtonStep f)^[n + 1] z₀ - ζ‖ ≤ K * ‖(newtonStep f)^[n] z₀ - ζ‖ ^ 2) ∧
      ((∀ n, (newtonStep f)^[n] z₀ ≠ ζ) → IsQuadraticConv (fun n => (newtonStep f)^[n] z₀) ζ) := by
  obtain ⟨δ, hδ, K, hK, hball⟩ := newton_simple_zero_ball hr hL0 hf hL hζ hd
  have hmem : ∀ z₀ ∈ ball ζ δ, ∀ n, (newtonStep f)^[n] z₀ ∈ ball ζ δ := fun z₀ hz n => by
    induction n with
    | zero => exact hz
    | succ n ih => rw [Function.iterate_succ_apply']; exact (hball _ ih).1
  refine ⟨(convergesLocally_of_contract hδ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    fun z hz => by have := (hball z hz).2.2; linarith).1, δ, hδ, K, hK, fun z₀ hz => ?_⟩
  have hq : ∀ n, ‖(newtonStep f)^[n + 1] z₀ - ζ‖ ≤ K * ‖(newtonStep f)^[n] z₀ - ζ‖ ^ 2 :=
    fun n => by rw [Function.iterate_succ_apply']; exact (hball _ (hmem z₀ hz n)).2.1
  refine ⟨hq, fun hne => ⟨K + 1, Eventually.of_forall fun n => ?_⟩⟩
  have hpos : 0 < ‖(newtonStep f)^[n] z₀ - ζ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hne n))
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc ‖(newtonStep f)^[n + 1] z₀ - ζ‖ ≤ K * ‖(newtonStep f)^[n] z₀ - ζ‖ ^ 2 := hq n
    _ < (K + 1) * ‖(newtonStep f)^[n] z₀ - ζ‖ ^ 2 := by gcongr; linarith

/-- The hypotheses of `dlmf_3_8_ii_simple` hold for `f` of class `C²` near `ζ` (real
twice-continuously differentiable or complex analytic `f`). -/
theorem dlmf_3_8_ii_simple_of_contDiffAt {f : 𝕜 → 𝕜} {ζ : 𝕜} (hf : ContDiffAt 𝕜 2 f ζ)
    (hζ : f ζ = 0) (hd : deriv f ζ ≠ 0) :
    ConvergesLocally (newtonStep f) ζ ∧ ∃ δ > 0, ∃ K ≥ 0, ∀ z₀ ∈ ball ζ δ,
      (∀ n, ‖(newtonStep f)^[n + 1] z₀ - ζ‖ ≤ K * ‖(newtonStep f)^[n] z₀ - ζ‖ ^ 2) ∧
      ((∀ n, (newtonStep f)^[n] z₀ ≠ ζ) → IsQuadraticConv (fun n => (newtonStep f)^[n] z₀) ζ) := by
  have h1 : ContDiffAt 𝕜 1 (deriv f) ζ := by
    have := (hf.fderiv_right (m := 1) (by norm_num)).clm_apply
      (contDiffAt_const (c := (1 : 𝕜)))
    exact this
  obtain ⟨K, t, ht, hK⟩ := h1.exists_lipschitzOnWith
  have hev : ∀ᶠ z in 𝓝 ζ, DifferentiableAt 𝕜 f z :=
    (hf.eventually (by norm_num)).mono fun z hz => hz.differentiableAt (by norm_num)
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem ht hev)
  refine dlmf_3_8_ii_simple hr K.coe_nonneg (fun z hz => (hrt hz).2) (fun w hw z hz => ?_) hζ hd
  have := hK.dist_le_mul w (hrt hw).1 z (hrt hz).1
  rwa [dist_eq_norm, dist_eq_norm] at this

end Simple

/-! ### Multiple zeros -/

section Multiple

/-- Newton's rule with the ratio `f/f′` multiplied by `m`. -/
noncomputable def newtonStepMul (m : ℕ) (f : 𝕜 → 𝕜) (z : 𝕜) : 𝕜 := z - m * (f z / deriv f z)

variable {f g : 𝕜 → 𝕜} {ζ : 𝕜} {r B : ℝ} {m : ℕ}

/-- `f′ = (z − ζ)^{m−1} (m g + (z − ζ) g′)` for `f = (z − ζ)ᵐ g` near `ζ`. -/
theorem deriv_eq_of_factor (hm : 1 ≤ m) (hfg : ∀ z ∈ ball ζ r, f z = (z - ζ) ^ m * g z)
    (hg : ∀ z ∈ ball ζ r, DifferentiableAt 𝕜 g z) {z : 𝕜} (hz : z ∈ ball ζ r) :
    deriv f z = (z - ζ) ^ (m - 1) * (m * g z + (z - ζ) * deriv g z) := by
  have hev : f =ᶠ[𝓝 z] fun w => (w - ζ) ^ m * g w := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hfg w hw
  have hp : HasDerivAt (fun w => (w - ζ) ^ m) ((m : 𝕜) * (z - ζ) ^ (m - 1)) z :=
    ((hasDerivAt_pow m (z - ζ)).comp z ((hasDerivAt_id z).sub_const ζ)).congr_deriv (by simp)
  have hd : HasDerivAt (fun w => (w - ζ) ^ m * g w)
      ((m : 𝕜) * (z - ζ) ^ (m - 1) * g z + (z - ζ) ^ m * deriv g z) z :=
    hp.mul (hg z hz).hasDerivAt
  rw [hev.deriv_eq, hd.deriv]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  ring

/-- The error of Newton's rule near a zero `f = (z − ζ)ᵐ g`:
`N(z) − ζ = (z − ζ) ((m − 1) g + (z − ζ) g′)/(m g + (z − ζ) g′)`, and for the rule with factor
`m`, `(z − ζ)² g′/(m g + (z − ζ) g′)`. -/
theorem newton_error_of_factor (hm : 2 ≤ m) (hfg : ∀ z ∈ ball ζ r, f z = (z - ζ) ^ m * g z)
    (hg : ∀ z ∈ ball ζ r, DifferentiableAt 𝕜 g z) {z : 𝕜} (hz : z ∈ ball ζ r)
    (hD : (m : 𝕜) * g z + (z - ζ) * deriv g z ≠ 0) :
    newtonStep f z - ζ = (z - ζ) * (((m : 𝕜) - 1) * g z + (z - ζ) * deriv g z) /
        ((m : 𝕜) * g z + (z - ζ) * deriv g z) ∧
      newtonStepMul m f z - ζ = (z - ζ) ^ 2 * deriv g z /
        ((m : 𝕜) * g z + (z - ζ) * deriv g z) := by
  have hdf := deriv_eq_of_factor (by omega) hfg hg hz
  have hfz := hfg z hz
  rcases eq_or_ne z ζ with rfl | hne
  · have hf0 : f z = 0 := by rw [hfz, sub_self, zero_pow (by omega), zero_mul]
    simp [newtonStep, newtonStepMul, hf0]
  · have he : z - ζ ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hdf
    set D := ((k + 1 : ℕ) : 𝕜) * g z + (z - ζ) * deriv g z
    have hq : f z / deriv f z = (z - ζ) * g z / D := by
      rw [hfz, hdf, pow_succ, mul_assoc, mul_div_mul_left _ _ (pow_ne_zero k he)]
    simp only [newtonStep, newtonStepMul]
    rw [hq]
    constructor
    · rw [eq_div_iff hD, sub_mul, sub_mul, div_mul_cancel₀ _ hD]
      simp only [D]; push_cast; ring
    · rw [eq_div_iff hD, sub_mul, sub_mul, mul_div_assoc', div_mul_cancel₀ _ hD]
      simp only [D]; push_cast; ring

/-- **DLMF §3.8(ii)**: "For multiple zeros the convergence is linear, but if the multiplicity `m`
is known then quadratic convergence can be restored by multiplying the ratio `f(zₙ)/f′(zₙ)` in
3.8.4 by `m`". Here `f = (z − ζ)ᵐ g` near `ζ`, `m ≥ 2`, `g(ζ) ≠ 0`, `g′` bounded:
* Newton's rule converges locally; from any `z₀ ≠ ζ` near `ζ` the convergence is linear
  (`IsLinearConv`), with error ratio `e_{n+1}/eₙ → (m − 1)/m`, and has no order `p > 1`.
* The modified rule converges locally with `|e_{n+1}| ≤ K |eₙ|²`, quadratically when no iterate
  lands on `ζ`. -/
theorem dlmf_3_8_ii_multiple (hm : 2 ≤ m) (hr : 0 < r)
    (hfg : ∀ z ∈ ball ζ r, f z = (z - ζ) ^ m * g z) (hg : ∀ z ∈ ball ζ r, DifferentiableAt 𝕜 g z)
    (hgζ : g ζ ≠ 0) (hB : ∀ z ∈ ball ζ r, ‖deriv g z‖ ≤ B) :
    ∃ δ > 0, (ConvergesLocally (newtonStep f) ζ ∧ ∀ z₀ ∈ ball ζ δ, z₀ ≠ ζ →
        IsLinearConv (fun n => (newtonStep f)^[n] z₀) ζ ∧
        Tendsto (fun n => ((newtonStep f)^[n + 1] z₀ - ζ) / ((newtonStep f)^[n] z₀ - ζ)) atTop
          (𝓝 (((m : 𝕜) - 1) / m)) ∧
        ∀ p > 1, p ∉ convIndices (fun n => (newtonStep f)^[n] z₀) ζ) ∧
      (ConvergesLocally (newtonStepMul m f) ζ ∧ ∃ K ≥ 0, ∀ z₀ ∈ ball ζ δ,
        (∀ n, ‖(newtonStepMul m f)^[n + 1] z₀ - ζ‖ ≤ K * ‖(newtonStepMul m f)^[n] z₀ - ζ‖ ^ 2) ∧
        ((∀ n, (newtonStepMul m f)^[n] z₀ ≠ ζ) →
          IsQuadraticConv (fun n => (newtonStepMul m f)^[n] z₀) ζ)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB ζ (mem_ball_self hr))
  set G := ‖g ζ‖
  have hG : 0 < G := norm_pos_iff.mpr hgζ
  set M : ℝ := (m : ℝ)
  have hM : (2 : ℝ) ≤ M := by simp only [M]; exact_mod_cast hm
  obtain ⟨ρ, hρ, hgρ⟩ := Metric.continuousAt_iff.mp (hg ζ (mem_ball_self hr)).continuousAt
    (G / 4) (by positivity)
  set δ := min r (min ρ (G / (4 * (B + 1))))
  have hδ0 : 0 < δ := lt_min hr (lt_min hρ (by positivity))
  have hδr : δ ≤ r := min_le_left _ _
  have hδρ : δ ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hδB : δ * B ≤ G / 4 := by
    have h1 : δ ≤ G / (4 * (B + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    calc δ * B ≤ G / (4 * (B + 1)) * B := mul_le_mul_of_nonneg_right h1 hB0
      _ ≤ G / (4 * (B + 1)) * (B + 1) := by gcongr; linarith
      _ = G / 4 := by field_simp
  set c : 𝕜 := ((m : 𝕜) - 1) / m
  have hc : ‖c‖ = (M - 1) / M := by
    have : c = (((M - 1) / M : ℝ) : 𝕜) := by simp [c, M]
    rw [this, RCLike.norm_ofReal, abs_of_nonneg (div_nonneg (by linarith) (by linarith))]
  set A := (4 * M - 3) / (4 * M)
  set a := (4 * M - 5) / (4 * M)
  have hA1 : A < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hA0 : 0 ≤ A := div_nonneg (by linarith) (by linarith)
  have ha0 : 0 < a := div_pos (by linarith) (by linarith)
  -- pointwise estimates
  have key : ∀ z ∈ ball ζ δ,
      ‖(newtonStep f z - ζ) - c * (z - ζ)‖ ≤ B / (M * G) * ‖z - ζ‖ ^ 2 ∧
      ‖newtonStep f z - ζ‖ ≤ A * ‖z - ζ‖ ∧ a * ‖z - ζ‖ ≤ ‖newtonStep f z - ζ‖ ∧
      ‖newtonStepMul m f z - ζ‖ ≤ B / G * ‖z - ζ‖ ^ 2 ∧
      ‖newtonStepMul m f z - ζ‖ ≤ ‖z - ζ‖ / 2 := by
    intro z hz
    have hzd : ‖z - ζ‖ < δ := by rwa [mem_ball, dist_eq_norm] at hz
    have hzr : z ∈ ball ζ r := ball_subset_ball hδr hz
    have hgz : 3 * G / 4 ≤ ‖g z‖ := by
      have := hgρ (show dist z ζ < ρ from lt_of_lt_of_le (by rwa [dist_eq_norm]) hδρ)
      rw [dist_eq_norm] at this
      have h2 := norm_sub_norm_le (g ζ) (g ζ - g z)
      rw [sub_sub_cancel, norm_sub_rev] at h2
      linarith
    obtain ⟨D, hDdef⟩ : ∃ D, D = (m : 𝕜) * g z + (z - ζ) * deriv g z := ⟨_, rfl⟩
    have hgB := hB z hzr
    have heB : ‖(z - ζ) * deriv g z‖ ≤ G / 4 := by
      rw [norm_mul]
      calc ‖z - ζ‖ * ‖deriv g z‖ ≤ δ * B := mul_le_mul hzd.le hgB (norm_nonneg _) hδ0.le
        _ ≤ G / 4 := hδB
    have hDG : G ≤ ‖D‖ := by
      have h1 : ‖(m : 𝕜) * g z‖ = M * ‖g z‖ := by
        rw [norm_mul, RCLike.norm_natCast]
      have h2 := norm_sub_norm_le ((m : 𝕜) * g z) (-((z - ζ) * deriv g z))
      rw [sub_neg_eq_add, norm_neg, ← hDdef] at h2
      nlinarith
    have hD : D ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hG hDG)
    obtain ⟨hN, hMf⟩ := newton_error_of_factor hm hfg hg hzr (hDdef ▸ hD)
    rw [← hDdef] at hN hMf
    have hDpos : 0 < ‖D‖ := lt_of_lt_of_le hG hDG
    -- `N(z) − ζ − c (z − ζ) = (z − ζ)² g′/(m D)`
    have hdiff : (newtonStep f z - ζ) - c * (z - ζ) = (z - ζ) ^ 2 * deriv g z / (m * D) := by
      have hm0 : (m : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hX : ∀ X : 𝕜, X / D * ((m : 𝕜) * D) = X * m := fun X => by
        rw [mul_comm (m : 𝕜) D, ← mul_assoc, div_mul_cancel₀ _ hD]
      have hcm : c * (m : 𝕜) = m - 1 := div_mul_cancel₀ _ hm0
      rw [hN, eq_div_iff (mul_ne_zero hm0 hD), sub_mul, hX,
        show c * (z - ζ) * ((m : 𝕜) * D) = (c * m) * (z - ζ) * D by ring, hcm, hDdef]
      ring
    have h1 : ‖(newtonStep f z - ζ) - c * (z - ζ)‖ ≤ B / (M * G) * ‖z - ζ‖ ^ 2 := by
      rw [hdiff, norm_div, norm_mul, norm_mul, norm_pow, RCLike.norm_natCast,
        div_le_iff₀ (by positivity)]
      calc ‖z - ζ‖ ^ 2 * ‖deriv g z‖ ≤ ‖z - ζ‖ ^ 2 * B := by gcongr
        _ = B / (M * G) * ‖z - ζ‖ ^ 2 * (M * G) := by field_simp
        _ ≤ B / (M * G) * ‖z - ζ‖ ^ 2 * (M * ‖D‖) := by gcongr
    have hsmall : B / (M * G) * ‖z - ζ‖ ^ 2 ≤ 1 / (4 * M) * ‖z - ζ‖ := by
      have : B * ‖z - ζ‖ ≤ G / 4 := by nlinarith [norm_nonneg (z - ζ)]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left this (norm_nonneg (z - ζ))
      field_simp
      nlinarith [norm_nonneg (z - ζ)]
    have hcz : ‖c * (z - ζ)‖ = (M - 1) / M * ‖z - ζ‖ := by rw [norm_mul, hc]
    have hupper : ‖newtonStep f z - ζ‖ ≤ A * ‖z - ζ‖ := by
      have := norm_add_le ((newtonStep f z - ζ) - c * (z - ζ)) (c * (z - ζ))
      rw [sub_add_cancel] at this
      have e : A * ‖z - ζ‖ = (M - 1) / M * ‖z - ζ‖ + 1 / (4 * M) * ‖z - ζ‖ := by
        simp only [A]; field_simp; ring
      linarith
    have hlower : a * ‖z - ζ‖ ≤ ‖newtonStep f z - ζ‖ := by
      have := norm_sub_norm_le (c * (z - ζ)) (c * (z - ζ) - (newtonStep f z - ζ))
      rw [sub_sub_cancel, norm_sub_rev] at this
      have e : a * ‖z - ζ‖ = (M - 1) / M * ‖z - ζ‖ - 1 / (4 * M) * ‖z - ζ‖ := by
        simp only [a]; field_simp; ring
      linarith
    have hmod : ‖newtonStepMul m f z - ζ‖ ≤ B / G * ‖z - ζ‖ ^ 2 := by
      rw [hMf, norm_div, norm_mul, norm_pow, div_le_iff₀ hDpos]
      calc ‖z - ζ‖ ^ 2 * ‖deriv g z‖ ≤ ‖z - ζ‖ ^ 2 * B := by gcongr
        _ = B / G * ‖z - ζ‖ ^ 2 * G := by field_simp
        _ ≤ B / G * ‖z - ζ‖ ^ 2 * ‖D‖ := by gcongr
    refine ⟨h1, hupper, hlower, hmod, hmod.trans ?_⟩
    have : B * ‖z - ζ‖ ≤ G / 4 := by nlinarith [norm_nonneg (z - ζ)]
    rw [div_mul_eq_mul_div, div_le_iff₀ hG]
    nlinarith [norm_nonneg (z - ζ)]
  -- Newton's rule
  obtain ⟨hNloc, hNbd⟩ := convergesLocally_of_contract hδ0 hA0 hA1 fun z hz => (key z hz).2.1
  have hmemN : ∀ z₀ ∈ ball ζ δ, ∀ n, (newtonStep f)^[n] z₀ ∈ ball ζ δ := fun z₀ hz n => by
    rw [mem_ball, dist_eq_norm]
    have hz' : ‖z₀ - ζ‖ < δ := by rwa [mem_ball, dist_eq_norm] at hz
    calc ‖(newtonStep f)^[n] z₀ - ζ‖ ≤ A ^ n * ‖z₀ - ζ‖ := hNbd z₀ hz n
      _ ≤ 1 * ‖z₀ - ζ‖ := by gcongr; exact pow_le_one₀ hA0 hA1.le
      _ < δ := by linarith
  refine ⟨δ, hδ0, ⟨hNloc, fun z₀ hz hne => ?_⟩, ?_⟩
  · set e : ℕ → 𝕜 := fun n => (newtonStep f)^[n] z₀ - ζ
    have hstep : ∀ n, (newtonStep f)^[n + 1] z₀ - ζ = newtonStep f ((newtonStep f)^[n] z₀) - ζ :=
      fun n => by rw [Function.iterate_succ_apply']
    have hpos : ∀ n, 0 < ‖e n‖ := by
      intro n
      induction n with
      | zero => exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      | succ n ih =>
        have := (key _ (hmemN z₀ hz n)).2.2.1
        simp only [e] at ih ⊢
        rw [hstep]
        nlinarith
    have he0 : Tendsto (fun n => ‖e n‖) atTop (𝓝 0) := by
      obtain ⟨N, hN, hconv⟩ := hNloc
      have : Tendsto (fun n => (newtonStep f)^[n] z₀) atTop (𝓝 ζ) := by
        refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun n => norm_nonneg _)
          (fun n => hNbd z₀ hz n) ?_)
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hA0 hA1).mul_const ‖z₀ - ζ‖
      exact tendsto_iff_norm_sub_tendsto_zero.mp this
    refine ⟨⟨(A + 1) / 2, by linarith, Eventually.of_forall fun n => ?_⟩, ?_, ?_⟩
    · rw [Real.rpow_one]
      have := (key _ (hmemN z₀ hz n)).2.1
      rw [hstep]
      have hp := hpos n
      simp only [e] at hp
      nlinarith
    · rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
        (by simpa using he0.const_mul (B / (M * G)))
      have h1 := (key _ (hmemN z₀ hz n)).1
      have hp := hpos n
      simp only [e] at hp
      have hne' : (newtonStep f)^[n] z₀ - ζ ≠ 0 := norm_pos_iff.mp hp
      have hid : (newtonStep f ((newtonStep f)^[n] z₀) - ζ) / ((newtonStep f)^[n] z₀ - ζ) - c =
          ((newtonStep f ((newtonStep f)^[n] z₀) - ζ) - c * ((newtonStep f)^[n] z₀ - ζ)) /
            ((newtonStep f)^[n] z₀ - ζ) := by
        rw [eq_div_iff hne', sub_mul, div_mul_cancel₀ _ hne']
      rw [hstep, hid, norm_div, div_le_iff₀ hp]
      calc _ ≤ B / (M * G) * ‖(newtonStep f)^[n] z₀ - ζ‖ ^ 2 := h1
        _ = _ := by simp only [e]; ring
    · rintro p hp ⟨A₀, hA₀⟩
      have hev : ∀ᶠ n in atTop, ‖e n‖ ^ (p - 1) < a / (|A₀| + 1) := by
        have ht : Tendsto (fun n => ‖e n‖ ^ (p - 1)) atTop (𝓝 0) := by
          have := (Real.continuousAt_rpow_const 0 (p - 1) (Or.inr (by linarith))).tendsto.comp he0
          simpa [Function.comp_def, Real.zero_rpow (by linarith : p - 1 ≠ 0)] using this
        exact ht.eventually (gt_mem_nhds (by positivity))
      obtain ⟨n, h1, h2⟩ := (hA₀.and hev).exists
      have hl := (key _ (hmemN z₀ hz n)).2.2.1
      rw [← hstep] at hl
      have hp' := hpos n
      have hsplit : ‖e n‖ ^ p = ‖e n‖ ^ (p - 1) * ‖e n‖ := by
        rw [← Real.rpow_add_one hp'.ne', sub_add_cancel]
      have h3 : a * ‖e n‖ < A₀ * (‖e n‖ ^ (p - 1) * ‖e n‖) := by
        rw [← hsplit]; exact lt_of_le_of_lt hl h1
      have h6 : A₀ * ‖e n‖ ^ (p - 1) ≤ |A₀| * (a / (|A₀| + 1)) :=
        calc A₀ * ‖e n‖ ^ (p - 1) ≤ |A₀| * ‖e n‖ ^ (p - 1) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (norm_nonneg _) _)
          _ ≤ |A₀| * (a / (|A₀| + 1)) := mul_le_mul_of_nonneg_left h2.le (abs_nonneg _)
      have h4 : A₀ * (‖e n‖ ^ (p - 1) * ‖e n‖) ≤ |A₀| * (a / (|A₀| + 1)) * ‖e n‖ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right h6 hp'.le
      have h5 : |A₀| * (a / (|A₀| + 1)) < a := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [abs_nonneg A₀]
      nlinarith
  · -- the modified rule
    have hmemM : ∀ z₀ ∈ ball ζ δ, ∀ n, (newtonStepMul m f)^[n] z₀ ∈ ball ζ δ := fun z₀ hz n => by
      induction n with
      | zero => exact hz
      | succ n ih =>
        rw [Function.iterate_succ_apply', mem_ball, dist_eq_norm]
        have := (key _ ih).2.2.2.2
        have h' : ‖(newtonStepMul m f)^[n] z₀ - ζ‖ < δ := by rwa [mem_ball, dist_eq_norm] at ih
        linarith [norm_nonneg ((newtonStepMul m f)^[n] z₀ - ζ)]
    refine ⟨(convergesLocally_of_contract hδ0 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      fun z hz => by have := (key z hz).2.2.2.2; linarith).1, B / G, by positivity,
      fun z₀ hz => ?_⟩
    have hq : ∀ n, ‖(newtonStepMul m f)^[n + 1] z₀ - ζ‖ ≤
        B / G * ‖(newtonStepMul m f)^[n] z₀ - ζ‖ ^ 2 :=
      fun n => by rw [Function.iterate_succ_apply']; exact (key _ (hmemM z₀ hz n)).2.2.2.1
    refine ⟨hq, fun hne => ⟨B / G + 1, Eventually.of_forall fun n => ?_⟩⟩
    have hpos : 0 < ‖(newtonStepMul m f)^[n] z₀ - ζ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hne n))
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc ‖(newtonStepMul m f)^[n + 1] z₀ - ζ‖ ≤ B / G * ‖(newtonStepMul m f)^[n] z₀ - ζ‖ ^ 2 :=
          hq n
      _ < (B / G + 1) * ‖(newtonStepMul m f)^[n] z₀ - ζ‖ ^ 2 := by gcongr; linarith

end Multiple

/-- For complex analytic `f` with a zero of multiplicity `m ≥ 1` at `ζ`, the hypotheses of
`dlmf_3_8_ii_multiple` hold: `f = (z − ζ)ᵐ g` near `ζ`, `g` differentiable, `g(ζ) ≠ 0`, `g′`
bounded. -/
theorem exists_factor_of_multiplicity {f : ℂ → ℂ} {ζ : ℂ} {m : ℕ} (hm : 1 ≤ m)
    (hf : AnalyticAt ℂ f ζ) (hz : IsZeroOfMultiplicity f ζ m) :
    ∃ g : ℂ → ℂ, ∃ r > 0, (∀ z ∈ ball ζ r, f z = (z - ζ) ^ m * g z) ∧
      (∀ z ∈ ball ζ r, DifferentiableAt ℂ g z) ∧ g ζ ≠ 0 ∧
      ∃ B, ∀ z ∈ ball ζ r, ‖deriv g z‖ ≤ B := by
  obtain ⟨g, hga, hg0, hev⟩ := (isZeroOfOrder_iff_exists hf hm).mp
    ((isZeroOfMultiplicity_iff_isZeroOfOrder hm).mp hz)
  have hd := (hga.deriv.continuousAt.norm).eventually (gt_mem_nhds
    (lt_add_one ‖deriv g ζ‖))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp ((hev.and hga.eventually_analyticAt).and hd)
  exact ⟨g, r, hr, fun z hz => (hsub hz).1.1, fun z hz => (hsub hz).1.2.differentiableAt, hg0,
    ‖deriv g ζ‖ + 1, fun z hz => (hsub hz).2.le⟩

/-! ### Real functions: monotonic convergence -/

section Real

open Set

variable {f : ℝ → ℝ} {ξ x₀ : ℝ}

theorem deriv_sign_const {a b : ℝ} (hc : ContinuousOn (deriv f) (uIcc a b))
    (h1 : ∀ x ∈ uIcc a b, deriv f x ≠ 0)
    {u v : ℝ} (hu : u ∈ uIcc a b) (hv : v ∈ uIcc a b) : 0 < deriv f u * deriv f v := by
  by_contra hneg
  push Not at hneg
  have : ∃ c ∈ uIcc u v, deriv f c = 0 := by
    rcases le_or_gt 0 (deriv f u) with hu0 | hu0
    · have hv0 : deriv f v ≤ 0 := by
        by_contra h; push Not at h
        have := mul_pos (lt_of_le_of_ne hu0 (Ne.symm (h1 u hu))) h; linarith
      exact intermediate_value_uIcc (hc.mono (uIcc_subset_uIcc hu hv)) ⟨by
        rw [min_le_iff]; right; exact hv0, by rw [le_max_iff]; left; exact hu0⟩
    · have hv0 : 0 ≤ deriv f v := by
        by_contra h; push Not at h
        have := mul_pos_of_neg_of_neg hu0 h; linarith
      exact intermediate_value_uIcc (hc.mono (uIcc_subset_uIcc hu hv)) ⟨by
        rw [min_le_iff]; left; exact hu0.le, by rw [le_max_iff]; right; exact hv0⟩
  obtain ⟨c, hc', hc0⟩ := this
  exact h1 c (uIcc_subset_uIcc hu hv hc') hc0

theorem exists_deriv_eq_div_of_zero {x : ℝ} (hd : ∀ y ∈ uIcc ξ x, DifferentiableAt ℝ f y)
    (hξ : f ξ = 0) (hne : x ≠ ξ) : ∃ c ∈ uIcc ξ x, deriv f c = f x / (x - ξ) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [uIcc_of_ge hlt.le] at hd
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hlt
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (Ioo_subset_Icc_self hy)).differentiableWithinAt)
    refine ⟨c, ?_, ?_⟩
    · rw [uIcc_of_ge hlt.le]; exact Ioo_subset_Icc_self hc
    · rw [hcd, hξ]; field_simp; ring
  · rw [uIcc_of_le hgt.le] at hd
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hgt
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (Ioo_subset_Icc_self hy)).differentiableWithinAt)
    refine ⟨c, ?_, ?_⟩
    · rw [uIcc_of_le hgt.le]; exact Ioo_subset_Icc_self hc
    · rw [hcd, hξ, sub_zero]

theorem contDiffAt_two_facts {x : ℝ} (h : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ (deriv f) x :=
  ⟨h.differentiableAt (by norm_num),
    ((h.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)⟩

/-- One Newton step towards a zero `ξ` on `I = [ξ, x₀]` (either order) when `f′ ≠ 0` there and
`|f′|` increases away from `ξ` (`(x₀ − ξ) f′ f″ ≥ 0`): `N(x) − ξ = (x − ξ)(1 − t)` with
`|f′(ξ)|/|f′(x₀)| ≤ t ≤ 1`. -/
theorem newton_real_step (hf : ∀ x ∈ uIcc ξ x₀, ContDiffAt ℝ 2 f x) (hξ : f ξ = 0)
    (h1 : ∀ x ∈ uIcc ξ x₀, deriv f x ≠ 0)
    (hdir : ∀ x ∈ uIcc ξ x₀, 0 ≤ (x₀ - ξ) * (deriv f x * deriv (deriv f) x))
    {x : ℝ} (hx : x ∈ uIcc ξ x₀) :
    newtonStep f x ∈ uIcc ξ x ∧ |newtonStep f x - ξ| ≤
      (1 - |deriv f ξ| / |deriv f x₀|) * |x - ξ| := by
  have hd1 : ∀ y ∈ uIcc ξ x₀, DifferentiableAt ℝ f y := fun y hy =>
    (contDiffAt_two_facts (hf y hy)).1
  have hd2 : ∀ y ∈ uIcc ξ x₀, DifferentiableAt ℝ (deriv f) y := fun y hy =>
    (contDiffAt_two_facts (hf y hy)).2
  have hc1 : ContinuousOn (deriv f) (uIcc ξ x₀) := fun y hy =>
    (hd2 y hy).continuousAt.continuousWithinAt
  have hξI : ξ ∈ uIcc ξ x₀ := left_mem_uIcc
  have hx0I : x₀ ∈ uIcc ξ x₀ := right_mem_uIcc
  -- `f′` has constant sign on `I`
  have hsign : ∀ a ∈ uIcc ξ x₀, ∀ b ∈ uIcc ξ x₀, 0 < deriv f a * deriv f b := by
    intro a ha b hb
    by_contra hneg
    push Not at hneg
    have : ∃ c ∈ uIcc a b, deriv f c = 0 := by
      rcases le_or_gt 0 (deriv f a) with ha0 | ha0
      · have hb0 : deriv f b ≤ 0 := by
          by_contra h; push Not at h
          have := mul_pos (lt_of_le_of_ne ha0 (Ne.symm (h1 a ha))) h; linarith
        exact intermediate_value_uIcc (hc1.mono (uIcc_subset_uIcc ha hb)) ⟨by
          rw [min_le_iff]; right; exact hb0, by rw [le_max_iff]; left; exact ha0⟩
      · have hb0 : 0 ≤ deriv f b := by
          by_contra h; push Not at h
          have := mul_pos_of_neg_of_neg ha0 h; linarith
        exact intermediate_value_uIcc (hc1.mono (uIcc_subset_uIcc ha hb)) ⟨by
          rw [min_le_iff]; left; exact ha0.le, by rw [le_max_iff]; right; exact hb0⟩
    obtain ⟨c, hc, hc0⟩ := this
    exact h1 c (uIcc_subset_uIcc ha hb hc) hc0
  -- `(f′)²` is monotone away from `ξ`
  have hmon : ∀ a ∈ uIcc ξ x₀, ∀ b ∈ uIcc ξ x₀, a ∈ uIcc ξ b → deriv f a ^ 2 ≤ deriv f b ^ 2 := by
    intro a ha b hb hab
    have hderiv : ∀ y ∈ uIcc ξ x₀, HasDerivAt (fun y => deriv f y ^ 2)
        (2 * deriv f y * deriv (deriv f) y) y := fun y hy => by
      exact (((hd2 y hy).hasDerivAt.mul (hd2 y hy).hasDerivAt).congr_deriv
        (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun z => sq (deriv f z))
    rcases le_total ξ x₀ with h | h
    · rw [uIcc_of_le h] at ha hb hdir hderiv
      rw [uIcc_of_le (show ξ ≤ b from hb.1)] at hab
      have hm : MonotoneOn (fun y => deriv f y ^ 2) (Icc ξ x₀) :=
        monotoneOn_of_deriv_nonneg (convex_Icc ξ x₀)
          (fun y hy => (hderiv y hy).continuousAt.continuousWithinAt)
          (fun y hy => (hderiv y (interior_subset hy)).differentiableAt.differentiableWithinAt)
          fun y hy => by
            rw [(hderiv y (interior_subset hy)).deriv]
            rw [interior_Icc] at hy
            have := hdir y (Ioo_subset_Icc_self hy)
            have hpos : 0 < x₀ - ξ := by linarith [hy.1, hy.2]
            nlinarith
      exact hm ha hb hab.2
    · rw [uIcc_of_ge h] at ha hb hdir hderiv
      rw [uIcc_of_ge (show b ≤ ξ from hb.2)] at hab
      have hm : AntitoneOn (fun y => deriv f y ^ 2) (Icc x₀ ξ) :=
        antitoneOn_of_deriv_nonpos (convex_Icc x₀ ξ)
          (fun y hy => (hderiv y hy).continuousAt.continuousWithinAt)
          (fun y hy => (hderiv y (interior_subset hy)).differentiableAt.differentiableWithinAt)
          fun y hy => by
            rw [(hderiv y (interior_subset hy)).deriv]
            rw [interior_Icc] at hy
            have := hdir y (Ioo_subset_Icc_self hy)
            have hneg : x₀ - ξ < 0 := by linarith [hy.1, hy.2]
            nlinarith
      exact hm hb ha hab.1
  have habs : ∀ a ∈ uIcc ξ x₀, ∀ b ∈ uIcc ξ x₀, a ∈ uIcc ξ b → |deriv f a| ≤ |deriv f b| :=
    fun a ha b hb hab => sq_le_sq.mp (hmon a ha b hb hab)
  rcases eq_or_ne x ξ with rfl | hne
  · simp [newtonStep, hξ]
  have hxI : uIcc ξ x ⊆ uIcc ξ x₀ := uIcc_subset_uIcc hξI hx
  -- the mean value theorem
  obtain ⟨c, hcI, hc⟩ := exists_deriv_eq_div_of_zero (fun y hy => hd1 y (hxI hy)) hξ hne
  have hfx : deriv f x ≠ 0 := h1 x hx
  set t := deriv f c / deriv f x
  have hN : newtonStep f x - ξ = (x - ξ) * (1 - t) := by
    have : f x = deriv f c * (x - ξ) := by rw [hc]; field_simp [sub_ne_zero.mpr hne]
    simp only [newtonStep, t, this]
    field_simp
    ring
  have ht0 : 0 < t := by
    have := hsign c (hxI hcI) x hx
    simp only [t]
    rw [div_pos_iff]
    rcases lt_or_gt_of_ne hfx with h | h
    · right; exact ⟨by nlinarith, h⟩
    · left; exact ⟨by nlinarith, h⟩
  have ht1 : t ≤ 1 := by
    have h := habs c (hxI hcI) x hx hcI
    have : |t| ≤ 1 := by
      simp only [t]; rw [abs_div, div_le_one (abs_pos.mpr hfx)]; exact h
    exact (le_abs_self t).trans this
  have htlow : |deriv f ξ| / |deriv f x₀| ≤ t := by
    have h1' := habs ξ hξI c (hxI hcI) left_mem_uIcc
    have h2' := habs x hx x₀ hx0I hx
    have hpos : 0 < |deriv f x₀| := abs_pos.mpr (h1 x₀ hx0I)
    have : |t| = t := abs_of_pos ht0
    rw [← this, abs_div, div_le_div_iff₀ hpos (abs_pos.mpr hfx)]
    exact mul_le_mul h1' h2' (abs_nonneg _) (abs_nonneg _)
  refine ⟨?_, ?_⟩
  · have h01 : 0 ≤ 1 - t := by linarith
    have h11 : 1 - t ≤ 1 := by linarith
    rcases le_total ξ x with h | h
    · rw [uIcc_of_le h]
      constructor <;> nlinarith
    · rw [uIcc_of_ge h]
      constructor <;> nlinarith
  · rw [hN, abs_mul, mul_comm, abs_of_nonneg (by linarith)]
    gcongr

/-- Newton iterates from `x₀` under the hypotheses of `newton_real_step` stay in `[ξ, x₀]`,
approach `ξ` monotonically and converge geometrically. -/
theorem newton_real_monotone (hf : ∀ x ∈ uIcc ξ x₀, ContDiffAt ℝ 2 f x) (hξ : f ξ = 0)
    (h1 : ∀ x ∈ uIcc ξ x₀, deriv f x ≠ 0)
    (hdir : ∀ x ∈ uIcc ξ x₀, 0 ≤ (x₀ - ξ) * (deriv f x * deriv (deriv f) x)) :
    (∀ n, (newtonStep f)^[n] x₀ ∈ uIcc ξ x₀) ∧
      (∀ n, (newtonStep f)^[n + 1] x₀ ∈ uIcc ξ ((newtonStep f)^[n] x₀)) ∧
      Tendsto (fun n => (newtonStep f)^[n] x₀) atTop (𝓝 ξ) := by
  set q := 1 - |deriv f ξ| / |deriv f x₀|
  have hpos : 0 < |deriv f x₀| := abs_pos.mpr (h1 x₀ right_mem_uIcc)
  have hq1 : q < 1 := by
    have : 0 < |deriv f ξ| / |deriv f x₀| := div_pos (abs_pos.mpr (h1 ξ left_mem_uIcc)) hpos
    linarith
  have hq0 : 0 ≤ q := by
    rcases eq_or_ne x₀ ξ with h | h
    · simp only [q, h]; rw [div_self (abs_pos.mpr (h1 ξ left_mem_uIcc)).ne']; norm_num
    · have hb' := (newton_real_step hf hξ h1 hdir (x := x₀) right_mem_uIcc).2
      have : 0 < |x₀ - ξ| := abs_pos.mpr (sub_ne_zero.mpr h)
      nlinarith [abs_nonneg (newtonStep f x₀ - ξ)]
  have hmem : ∀ n, (newtonStep f)^[n] x₀ ∈ uIcc ξ x₀ ∧
      |(newtonStep f)^[n] x₀ - ξ| ≤ q ^ n * |x₀ - ξ| := by
    intro n
    induction n with
    | zero => exact ⟨right_mem_uIcc, by simp⟩
    | succ n ih =>
      obtain ⟨hI, hb⟩ := newton_real_step hf hξ h1 hdir ih.1
      rw [Function.iterate_succ_apply']
      refine ⟨uIcc_subset_uIcc left_mem_uIcc ih.1 hI, hb.trans ?_⟩
      calc q * |(newtonStep f)^[n] x₀ - ξ| ≤ q * (q ^ n * |x₀ - ξ|) :=
            mul_le_mul_of_nonneg_left ih.2 hq0
        _ = q ^ (n + 1) * |x₀ - ξ| := by ring
  refine ⟨fun n => (hmem n).1, fun n => ?_, ?_⟩
  · rw [Function.iterate_succ_apply']
    exact (newton_real_step hf hξ h1 hdir (hmem n).1).1
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hmem n).2) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const |x₀ - ξ|

end Real

/-- Once Newton iterates converging to a simple zero of a `C²` function are close to it, the
convergence is quadratic. -/
theorem newton_eventually_quadratic {f : 𝕜 → 𝕜} {ζ z₀ : 𝕜} (hf : ContDiffAt 𝕜 2 f ζ)
    (hζ : f ζ = 0) (hd : deriv f ζ ≠ 0)
    (hx : Tendsto (fun n => (newtonStep f)^[n] z₀) atTop (𝓝 ζ)) :
    ∃ K ≥ 0, ∀ᶠ n in atTop,
      ‖(newtonStep f)^[n + 1] z₀ - ζ‖ ≤ K * ‖(newtonStep f)^[n] z₀ - ζ‖ ^ 2 := by
  obtain ⟨-, δ, hδ, K, hK, hball⟩ := dlmf_3_8_ii_simple_of_contDiffAt hf hζ hd
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hx.eventually (ball_mem_nhds ζ hδ))
  refine ⟨K, hK, eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
  have := (hball _ (hN N le_rfl)).1 (n - N)
  rwa [← Function.iterate_add_apply, ← Function.iterate_add_apply,
    show n - N + 1 + N = n + 1 by omega, show n - N + N = n by omega] at this

section RealConditions

open Set

variable {f : ℝ → ℝ} {ξ x₀ : ℝ}

/-- **DLMF §3.8(ii)(a)**: if `f(x₀) f″(x₀) > 0` and `f′`, `f″` do not change sign between `x₀`
and `ξ` (`f′ ≠ 0`), Newton's iterates converge to `ξ` monotonically, and quadratically. -/
theorem dlmf_3_8_ii_a (hf : ∀ x ∈ uIcc ξ x₀, ContDiffAt ℝ 2 f x) (hξ : f ξ = 0)
    (h0 : 0 < f x₀ * deriv (deriv f) x₀) (h1 : ∀ x ∈ uIcc ξ x₀, deriv f x ≠ 0)
    (h2 : ∀ x ∈ uIcc ξ x₀, 0 ≤ deriv (deriv f) x * deriv (deriv f) x₀) :
    (∀ n, (newtonStep f)^[n] x₀ ∈ uIcc ξ x₀) ∧
      (∀ n, (newtonStep f)^[n + 1] x₀ ∈ uIcc ξ ((newtonStep f)^[n] x₀)) ∧
      Tendsto (fun n => (newtonStep f)^[n] x₀) atTop (𝓝 ξ) ∧
      ∃ K ≥ 0, ∀ᶠ n in atTop,
        |(newtonStep f)^[n + 1] x₀ - ξ| ≤ K * |(newtonStep f)^[n] x₀ - ξ| ^ 2 := by
  have hc1 : ContinuousOn (deriv f) (uIcc ξ x₀) := fun y hy =>
    (contDiffAt_two_facts (hf y hy)).2.continuousAt.continuousWithinAt
  have hne : x₀ ≠ ξ := by rintro rfl; rw [hξ, zero_mul] at h0; exact lt_irrefl 0 h0
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_div_of_zero (fun y hy => (contDiffAt_two_facts
    (hf y hy)).1) hξ hne
  have hfx : f x₀ = deriv f c * (x₀ - ξ) := by rw [hcd]; field_simp [sub_ne_zero.mpr hne]
  have hdir : ∀ x ∈ uIcc ξ x₀, 0 ≤ (x₀ - ξ) * (deriv f x * deriv (deriv f) x) := by
    intro x hx
    have hs := deriv_sign_const hc1 h1 hx hc
    have hs2 := h2 x hx
    have hQ : 0 < (x₀ - ξ) * deriv f c * deriv (deriv f) x₀ := by rw [hfx] at h0; linarith
    have hPQ : 0 * ((x₀ - ξ) * deriv f c * deriv (deriv f) x₀) ≤
        ((x₀ - ξ) * (deriv f x * deriv (deriv f) x)) *
          ((x₀ - ξ) * deriv f c * deriv (deriv f) x₀) := by
      rw [zero_mul]
      have := mul_nonneg (mul_nonneg (sq_nonneg (x₀ - ξ)) hs.le) hs2
      calc (0 : ℝ) ≤ _ := this
        _ = _ := by ring
    exact le_of_mul_le_mul_right hPQ hQ
  obtain ⟨hI, hstep, hlim⟩ := newton_real_monotone hf hξ h1 hdir
  refine ⟨hI, hstep, hlim, ?_⟩
  simpa [Real.norm_eq_abs] using
    newton_eventually_quadratic (hf ξ left_mem_uIcc) hξ (h1 ξ left_mem_uIcc) hlim

/-- **DLMF §3.8(ii)(b)**: if `f(x₀) f″(x₀) < 0`, `f′`, `f″` do not change sign between `x₀` and
`x₁ = N(x₀)` (`f′ ≠ 0`), and `ξ` lies between `x₀` and `x₁`, then from `x₁` on the iterates
converge to `ξ` monotonically, and quadratically. -/
theorem dlmf_3_8_ii_b (hf : ∀ x ∈ uIcc x₀ (newtonStep f x₀), ContDiffAt ℝ 2 f x) (hξ : f ξ = 0)
    (h0 : f x₀ * deriv (deriv f) x₀ < 0) (h1 : ∀ x ∈ uIcc x₀ (newtonStep f x₀), deriv f x ≠ 0)
    (h2 : ∀ x ∈ uIcc x₀ (newtonStep f x₀), 0 ≤ deriv (deriv f) x * deriv (deriv f) x₀)
    (hξI : ξ ∈ uIcc x₀ (newtonStep f x₀)) :
    (∀ n, (newtonStep f)^[n + 1] x₀ ∈ uIcc ξ (newtonStep f x₀)) ∧
      (∀ n, (newtonStep f)^[n + 2] x₀ ∈ uIcc ξ ((newtonStep f)^[n + 1] x₀)) ∧
      Tendsto (fun n => (newtonStep f)^[n] x₀) atTop (𝓝 ξ) ∧
      ∃ K ≥ 0, ∀ᶠ n in atTop,
        |(newtonStep f)^[n + 1] x₀ - ξ| ≤ K * |(newtonStep f)^[n] x₀ - ξ| ^ 2 := by
  set x₁ := newtonStep f x₀
  have hc1 : ContinuousOn (deriv f) (uIcc x₀ x₁) := fun y hy =>
    (contDiffAt_two_facts (hf y hy)).2.continuousAt.continuousWithinAt
  have hsub : uIcc ξ x₁ ⊆ uIcc x₀ x₁ := uIcc_subset_uIcc hξI right_mem_uIcc
  have hsub0 : uIcc ξ x₀ ⊆ uIcc x₀ x₁ := uIcc_subset_uIcc hξI left_mem_uIcc
  have hne : x₀ ≠ ξ := by rintro rfl; rw [hξ, zero_mul] at h0; exact lt_irrefl 0 h0
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_div_of_zero (fun y hy => (contDiffAt_two_facts
    (hf y (hsub0 hy))).1) hξ hne
  have hcI : c ∈ uIcc x₀ x₁ := hsub0 hc
  have hfx : f x₀ = deriv f c * (x₀ - ξ) := by rw [hcd]; field_simp [sub_ne_zero.mpr hne]
  have hR : (x₁ - ξ) * (x₀ - ξ) ≤ 0 := by
    rcases hξI with ⟨ha, hb⟩
    rcases le_total x₀ x₁ with h | h
    · rw [min_eq_left h] at ha; rw [max_eq_right h] at hb; nlinarith
    · rw [min_eq_right h] at ha; rw [max_eq_left h] at hb; nlinarith
  have hdir : ∀ x ∈ uIcc ξ x₁, 0 ≤ (x₁ - ξ) * (deriv f x * deriv (deriv f) x) := by
    intro x hx
    have hs := deriv_sign_const hc1 h1 (hsub hx) hcI
    have hs2 := h2 x (hsub hx)
    have hQ : (x₀ - ξ) * deriv f c * deriv (deriv f) x₀ < 0 := by rw [hfx] at h0; linarith
    nlinarith [mul_nonneg hs.le hs2]
  obtain ⟨hI, hstep, hlim⟩ := newton_real_monotone (fun x hx => hf x (hsub hx)) hξ
    (fun x hx => h1 x (hsub hx)) hdir
  have hshift : ∀ n, (newtonStep f)^[n + 1] x₀ = (newtonStep f)^[n] x₁ := fun n =>
    Function.iterate_succ_apply _ _ _
  have hlim' : Tendsto (fun n => (newtonStep f)^[n] x₀) atTop (𝓝 ξ) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    simpa [hshift] using hlim
  refine ⟨fun n => by rw [hshift]; exact hI n, fun n => by rw [hshift, hshift]; exact hstep n,
    hlim', ?_⟩
  simpa [Real.norm_eq_abs] using
    newton_eventually_quadratic (hf ξ hξI) hξ (h1 ξ hξI) hlim'

end RealConditions

end Azurite.DLMF
