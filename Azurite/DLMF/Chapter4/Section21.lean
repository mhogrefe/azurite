/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# DLMF §4.21 Identities

## §4.21(i) Addition Formulas

* 4.21.1, 4.21.1_5: `dlmf_4_21_1`, `dlmf_4_21_1_5` (`ph` is `Complex.arg`).
* 4.21.2–4.21.5: `dlmf_4_21_2`, …, `dlmf_4_21_5`. Each `±` is stated as two conjuncts. The `tan`
  and `cot` formulas need `cos u, cos v ≠ 0`, respectively `sin u, sin v ≠ 0`. Where the left
  side has a pole, both sides are `0` in Lean's convention `x/0 = 0`.
* 4.21.6–4.21.9: `dlmf_4_21_6`, …, `dlmf_4_21_9`.
* 4.21.10–4.21.11: `dlmf_4_21_10`, `dlmf_4_21_11`.
-/

open Complex
open scoped Real

namespace Azurite.DLMF

/-- **DLMF 4.21.1**: `sin u ± cos u = √2 sin(u ± π/4) = ±√2 cos(u ∓ π/4)`. -/
theorem dlmf_4_21_1 (u : ℂ) :
    (sin u + cos u = (√2 : ℝ) * sin (u + π / 4) ∧ (√2 : ℝ) * sin (u + π / 4) =
      (√2 : ℝ) * cos (u - π / 4)) ∧
    (sin u - cos u = (√2 : ℝ) * sin (u - π / 4) ∧ (√2 : ℝ) * sin (u - π / 4) =
      -((√2 : ℝ) * cos (u + π / 4))) := by
  have hc : cos ((π : ℂ) / 4) = ((√2 / 2 : ℝ) : ℂ) := by
    rw [show (π : ℂ) / 4 = ((π / 4 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
      Real.cos_pi_div_four]
  have hs : sin ((π : ℂ) / 4) = ((√2 / 2 : ℝ) : ℂ) := by
    rw [show (π : ℂ) / 4 = ((π / 4 : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin,
      Real.sin_pi_div_four]
  have h2 : ((√2 : ℝ) : ℂ) * ((√2 / 2 : ℝ) : ℂ) = 1 := by
    rw [← ofReal_mul, show √2 * (√2 / 2) = (√2 * √2) / 2 by ring,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  simp only [sin_add, sin_sub, cos_add, cos_sub, hc, hs]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · linear_combination (-(sin u + cos u)) * h2
  · ring
  · linear_combination (-(sin u - cos u)) * h2
  · ring

/-- **DLMF 4.21.1_5**: `A cos u + B sin u = √(A² + B²) cos(u − ph(A + Bi))`, `A, B ∈ ℝ`. -/
theorem dlmf_4_21_1_5 (A B : ℝ) (u : ℂ) :
    A * cos u + B * sin u = (√(A ^ 2 + B ^ 2) : ℝ) * cos (u - arg (A + B * I)) := by
  set ζ : ℂ := A + B * I with hζ
  have hn : ‖ζ‖ = √(A ^ 2 + B ^ 2) := norm_add_mul_I A B
  rcases eq_or_ne ζ 0 with h0 | h0
  · have hA := congrArg re h0
    have hB := congrArg im h0
    simp [hζ] at hA hB
    simp [hA, hB]
  have hnz : (‖ζ‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
  have hc : (Real.cos (arg ζ) : ℂ) * ‖ζ‖ = A := by
    rw [cos_arg h0]; push_cast; rw [div_mul_cancel₀ _ hnz]; simp [hζ]
  have hs : (Real.sin (arg ζ) : ℂ) * ‖ζ‖ = B := by
    rw [sin_arg]; push_cast; rw [div_mul_cancel₀ _ hnz]; simp [hζ]
  rw [cos_sub, ← ofReal_cos, ← ofReal_sin, ← hn]
  rw [← hc, ← hs]
  push_cast
  ring

/-- **DLMF 4.21.2**: `sin(u ± v) = sin u cos v ± cos u sin v`. -/
theorem dlmf_4_21_2 (u v : ℂ) :
    sin (u + v) = sin u * cos v + cos u * sin v ∧ sin (u - v) = sin u * cos v - cos u * sin v :=
  ⟨sin_add u v, sin_sub u v⟩

/-- **DLMF 4.21.3**: `cos(u ± v) = cos u cos v ∓ sin u sin v`. -/
theorem dlmf_4_21_3 (u v : ℂ) :
    cos (u + v) = cos u * cos v - sin u * sin v ∧ cos (u - v) = cos u * cos v + sin u * sin v :=
  ⟨cos_add u v, cos_sub u v⟩

/-- **DLMF 4.21.4**: `tan(u ± v) = (tan u ± tan v)/(1 ∓ tan u tan v)` (`cos u, cos v ≠ 0`). -/
theorem dlmf_4_21_4 {u v : ℂ} (hu : cos u ≠ 0) (hv : cos v ≠ 0) :
    tan (u + v) = (tan u + tan v) / (1 - tan u * tan v) ∧
      tan (u - v) = (tan u - tan v) / (1 + tan u * tan v) := by
  have huv := mul_ne_zero hu hv
  simp only [tan_eq_sin_div_cos, sin_add, cos_add, sin_sub, cos_sub]
  constructor
  · rw [show sin u / cos u + sin v / cos v = (sin u * cos v + cos u * sin v) / (cos u * cos v) by
        field_simp,
      show 1 - sin u / cos u * (sin v / cos v) = (cos u * cos v - sin u * sin v) /
        (cos u * cos v) by field_simp, div_div_div_cancel_right₀ huv]
  · rw [show sin u / cos u - sin v / cos v = (sin u * cos v - cos u * sin v) / (cos u * cos v) by
        field_simp,
      show 1 + sin u / cos u * (sin v / cos v) = (cos u * cos v + sin u * sin v) /
        (cos u * cos v) by field_simp, div_div_div_cancel_right₀ huv]

/-- **DLMF 4.21.5**: `cot(u ± v) = (±cot u cot v − 1)/(cot u ± cot v)` (`sin u, sin v ≠ 0`). -/
theorem dlmf_4_21_5 {u v : ℂ} (hu : sin u ≠ 0) (hv : sin v ≠ 0) :
    cot (u + v) = (cot u * cot v - 1) / (cot u + cot v) ∧
      cot (u - v) = (-(cot u * cot v) - 1) / (cot u - cot v) := by
  have huv := mul_ne_zero hu hv
  simp only [cot_eq_cos_div_sin, sin_add, cos_add, sin_sub, cos_sub]
  constructor
  · rw [show cos u / sin u * (cos v / sin v) - 1 = (cos u * cos v - sin u * sin v) /
        (sin u * sin v) by field_simp,
      show cos u / sin u + cos v / sin v = (sin u * cos v + cos u * sin v) / (sin u * sin v) by
        field_simp; ring, div_div_div_cancel_right₀ huv]
  · rw [show -(cos u / sin u * (cos v / sin v)) - 1 = -(cos u * cos v + sin u * sin v) /
        (sin u * sin v) by field_simp; ring,
      show cos u / sin u - cos v / sin v = -(sin u * cos v - cos u * sin v) / (sin u * sin v) by
        field_simp; ring, div_div_div_cancel_right₀ huv, neg_div_neg_eq]

theorem half_sum_diff (u v : ℂ) : u = (u + v) / 2 + (u - v) / 2 ∧ v = (u + v) / 2 - (u - v) / 2 :=
  ⟨by ring, by ring⟩

/-- **DLMF 4.21.6**: `sin u + sin v = 2 sin((u + v)/2) cos((u − v)/2)`. -/
theorem dlmf_4_21_6 (u v : ℂ) : sin u + sin v = 2 * sin ((u + v) / 2) * cos ((u - v) / 2) := by
  conv_lhs => rw [(half_sum_diff u v).1, (half_sum_diff u v).2]
  rw [sin_add, sin_sub]; ring_nf

/-- **DLMF 4.21.7**: `sin u − sin v = 2 cos((u + v)/2) sin((u − v)/2)`. -/
theorem dlmf_4_21_7 (u v : ℂ) : sin u - sin v = 2 * cos ((u + v) / 2) * sin ((u - v) / 2) := by
  conv_lhs => rw [(half_sum_diff u v).1, (half_sum_diff u v).2]
  rw [sin_add, sin_sub]; ring_nf

/-- **DLMF 4.21.8**: `cos u + cos v = 2 cos((u + v)/2) cos((u − v)/2)`. -/
theorem dlmf_4_21_8 (u v : ℂ) : cos u + cos v = 2 * cos ((u + v) / 2) * cos ((u - v) / 2) := by
  conv_lhs => rw [(half_sum_diff u v).1, (half_sum_diff u v).2]
  rw [cos_add, cos_sub]; ring_nf

/-- **DLMF 4.21.9**: `cos u − cos v = −2 sin((u + v)/2) sin((u − v)/2)`. -/
theorem dlmf_4_21_9 (u v : ℂ) : cos u - cos v = -2 * sin ((u + v) / 2) * sin ((u - v) / 2) := by
  conv_lhs => rw [(half_sum_diff u v).1, (half_sum_diff u v).2]
  rw [cos_add, cos_sub]; ring_nf

/-- **DLMF 4.21.10**: `tan u ± tan v = sin(u ± v)/(cos u cos v)` (`cos u, cos v ≠ 0`). -/
theorem dlmf_4_21_10 {u v : ℂ} (hu : cos u ≠ 0) (hv : cos v ≠ 0) :
    tan u + tan v = sin (u + v) / (cos u * cos v) ∧
      tan u - tan v = sin (u - v) / (cos u * cos v) := by
  simp only [tan_eq_sin_div_cos, sin_add, sin_sub]
  constructor <;> field_simp

/-- **DLMF 4.21.11**: `cot u ± cot v = sin(v ± u)/(sin u sin v)` (`sin u, sin v ≠ 0`). -/
theorem dlmf_4_21_11 {u v : ℂ} (hu : sin u ≠ 0) (hv : sin v ≠ 0) :
    cot u + cot v = sin (v + u) / (sin u * sin v) ∧
      cot u - cot v = sin (v - u) / (sin u * sin v) := by
  simp only [cot_eq_cos_div_sin, sin_add, sin_sub]
  constructor <;> field_simp

end Azurite.DLMF
