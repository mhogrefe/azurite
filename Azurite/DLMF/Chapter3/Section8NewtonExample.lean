/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section8Newton
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# DLMF §3.8(ii), Example: `x − tan x = 0`

* 3.8.5: Newton's rule for `f(x) = x − tan x` (`tanExF`) is `φ(x) = x + x cot² x − cot x`
  (`exPhi`, `dlmf_3_8_5`; `f′ = −tan²`, `f″ = −2 sin/cos³`).
* On `(π, 3π/2)`, `f` is strictly decreasing (`exF_strictAntiOn`), and `f` has no zero in
  `(0, π]` (`exF_ne_zero_of_mem_Ioc`).
* From every `x₀ ∈ (ζ, 3π/2)` the iteration converges monotonically and quadratically to the zero
  `ζ`, by condition (a) (`exF_newton_converges`).

The numerics (Table 3.8.1, `ζ`, the starting-value claim) are in `Section8NewtonTable`.
-/

open Filter Topology Set Real

namespace Azurite.DLMF

/-- The function `f(x) = x − tan x` of the Example. -/
noncomputable def tanExF (x : ℝ) : ℝ := x - tan x

/-- **DLMF 3.8.5**: `φ(x) = x + x cot² x − cot x`. -/
noncomputable def exPhi (x : ℝ) : ℝ := x + x * cot x ^ 2 - cot x

theorem hasDerivAt_exF {x : ℝ} (h : cos x ≠ 0) : HasDerivAt tanExF (1 - 1 / cos x ^ 2) x :=
  (hasDerivAt_id x).sub (hasDerivAt_tan h)

theorem contDiffAt_exF {x : ℝ} (h : cos x ≠ 0) : ContDiffAt ℝ 2 tanExF x :=
  contDiffAt_id.sub (contDiffAt_tan.mpr h)

theorem deriv_exF {x : ℝ} (h : cos x ≠ 0) : deriv tanExF x = -tan x ^ 2 := by
  rw [(hasDerivAt_exF h).deriv, tan_eq_sin_div_cos]
  have := sin_sq_add_cos_sq x
  field_simp
  linarith

theorem deriv2_exF {x : ℝ} (h : cos x ≠ 0) :
    deriv (deriv tanExF) x = -(2 * sin x / cos x ^ 3) := by
  have hev : deriv tanExF =ᶠ[𝓝 x] fun y => 1 - (cos y ^ 2)⁻¹ := by
    filter_upwards [(continuous_cos.continuousAt (x := x)).eventually_ne h] with y hy
    rw [(hasDerivAt_exF hy).deriv, one_div]
  have hd : HasDerivAt (fun y => 1 - (cos y ^ 2)⁻¹)
      (-(-(2 * cos x * -sin x) / (cos x ^ 2) ^ 2)) x := by
    have h1 : HasDerivAt (fun y => cos y ^ 2) (2 * cos x * -sin x) x := by
      exact (((hasDerivAt_cos x).mul (hasDerivAt_cos x)).congr_deriv
        (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun z => sq (cos z))
    have := (h1.inv (pow_ne_zero 2 h)).const_sub 1
    simpa using this
  rw [hev.deriv_eq, hd.deriv]
  field_simp

/-- **DLMF 3.8.5**: Newton's rule for `x − tan x` is `x ↦ x + x cot² x − cot x`
(where `cos x ≠ 0` and `sin x ≠ 0`). -/
theorem dlmf_3_8_5 {x : ℝ} (hc : cos x ≠ 0) (hs : sin x ≠ 0) : newtonStep tanExF x = exPhi x := by
  simp only [newtonStep, exPhi, tanExF, cot_eq_cos_div_sin, deriv_exF hc, tan_eq_sin_div_cos]
  field_simp
  ring

/-! ### The interval `(π, 3π/2)` -/

theorem cos_neg_of_mem {x : ℝ} (hx : x ∈ Ioo π (3 * π / 2)) : cos x < 0 :=
  cos_neg_of_pi_div_two_lt_of_lt (by linarith [hx.1, pi_pos]) (by linarith [hx.2])

theorem sin_neg_of_mem {x : ℝ} (hx : x ∈ Ioo π (3 * π / 2)) : sin x < 0 := by
  have : 0 < sin (x - π) :=
    sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, pi_pos])
  rw [sin_sub_pi] at this
  linarith

theorem tan_pos_of_mem {x : ℝ} (hx : x ∈ Ioo π (3 * π / 2)) : 0 < tan x := by
  rw [tan_eq_sin_div_cos]
  exact div_pos_of_neg_of_neg (sin_neg_of_mem hx) (cos_neg_of_mem hx)

theorem exF_strictAntiOn : StrictAntiOn tanExF (Ioo π (3 * π / 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) (fun x hx =>
    (hasDerivAt_exF (cos_neg_of_mem hx).ne).continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Ioo] at hx
  rw [deriv_exF (cos_neg_of_mem hx).ne]
  have := tan_pos_of_mem hx
  nlinarith

/-- `x − tan x` has no zero in `(0, π]`: the first positive zero lies beyond `π`. -/
theorem exF_ne_zero_of_mem_Ioc {x : ℝ} (hx : x ∈ Ioc 0 π) : tanExF x ≠ 0 := by
  rcases lt_trichotomy x (π / 2) with h | h | h
  · have := lt_tan hx.1 h
    simp only [tanExF]; linarith
  · rw [h]
    simp only [tanExF, tan_eq_sin_div_cos, cos_pi_div_two, div_zero, sub_zero]
    exact (by linarith [pi_pos] : π / 2 ≠ 0)
  · have hc : cos x < 0 := cos_neg_of_pi_div_two_lt_of_lt h (by linarith [hx.2, pi_pos])
    have hs : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi hx.1.le hx.2
    have ht : tan x ≤ 0 := by rw [tan_eq_sin_div_cos]; exact div_nonpos_of_nonneg_of_nonpos hs hc.le
    simp only [tanExF]; linarith [hx.1]

/-- Newton's rule for `x − tan x` converges monotonically (and quadratically) to the zero
`ζ ∈ (π, 3π/2)` from every `x₀ ∈ (ζ, 3π/2)` — DLMF's condition (a); the iterates are those of
`φ` (3.8.5). -/
theorem exF_newton_converges {ζ x₀ : ℝ} (hζ : ζ ∈ Ioo π (3 * π / 2)) (hz : tanExF ζ = 0)
    (hx : x₀ ∈ Ioo ζ (3 * π / 2)) :
    (∀ n, (newtonStep tanExF)^[n] x₀ = exPhi^[n] x₀) ∧
      (∀ n, (newtonStep tanExF)^[n] x₀ ∈ Icc ζ x₀) ∧
      Antitone (fun n => (newtonStep tanExF)^[n] x₀) ∧
      Tendsto (fun n => (newtonStep tanExF)^[n] x₀) atTop (𝓝 ζ) ∧
      ∃ K ≥ 0, ∀ᶠ n in atTop,
        |(newtonStep tanExF)^[n + 1] x₀ - ζ| ≤ K * |(newtonStep tanExF)^[n] x₀ - ζ| ^ 2 := by
  have hle : ζ ≤ x₀ := hx.1.le
  have hI : uIcc ζ x₀ = Icc ζ x₀ := uIcc_of_le hle
  have hsub : Icc ζ x₀ ⊆ Ioo π (3 * π / 2) := fun y hy => ⟨lt_of_lt_of_le hζ.1 hy.1,
    lt_of_le_of_lt hy.2 hx.2⟩
  have hx0 : x₀ ∈ Ioo π (3 * π / 2) := hsub ⟨hle, le_rfl⟩
  have hfx0 : tanExF x₀ < 0 := by rw [← hz]; exact exF_strictAntiOn hζ hx0 hx.1
  have hf2 : ∀ y ∈ Ioo π (3 * π / 2), deriv (deriv tanExF) y < 0 := fun y hy => by
    rw [deriv2_exF (cos_neg_of_mem hy).ne]
    have hc := cos_neg_of_mem hy
    have hs := sin_neg_of_mem hy
    have : 0 < 2 * sin y / cos y ^ 3 := div_pos_of_neg_of_neg (by linarith) (by
      have : cos y ^ 3 = cos y * cos y ^ 2 := by ring
      rw [this]; exact mul_neg_of_neg_of_pos hc (by nlinarith))
    linarith
  obtain ⟨hmem, hstep, hlim, hquad⟩ := dlmf_3_8_ii_a (f := tanExF) (ξ := ζ) (x₀ := x₀)
    (fun y hy => contDiffAt_exF (cos_neg_of_mem (hsub (hI ▸ hy))).ne) hz
    (mul_pos_of_neg_of_neg hfx0 (hf2 x₀ hx0))
    (fun y hy => by
      rw [deriv_exF (cos_neg_of_mem (hsub (hI ▸ hy))).ne]
      have := tan_pos_of_mem (hsub (hI ▸ hy))
      nlinarith)
    (fun y hy => (mul_pos_of_neg_of_neg (hf2 y (hsub (hI ▸ hy))) (hf2 x₀ hx0)).le)
  have hmem' : ∀ n, (newtonStep tanExF)^[n] x₀ ∈ Icc ζ x₀ := fun n => hI ▸ hmem n
  refine ⟨fun n => ?_, hmem', ?_, hlim, hquad⟩
  · induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      have hy := hsub (hmem' n)
      exact dlmf_3_8_5 (cos_neg_of_mem hy).ne (sin_neg_of_mem hy).ne
  · refine antitone_nat_of_succ_le fun n => ?_
    have h := hstep n
    rw [uIcc_of_le (hmem' n).1] at h
    exact h.2

end Azurite.DLMF
