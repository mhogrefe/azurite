/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Azurite.DLMF.Chapter4.Section18
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# DLMF §4.21 Identities

## §4.21(i) Addition Formulas

* 4.21.1, 4.21.1_5: `dlmf_4_21_1`, `dlmf_4_21_1_5` (`ph` is `Complex.arg`).
* 4.21.2–4.21.5: `dlmf_4_21_2`, …, `dlmf_4_21_5`. Each `±` is stated as two conjuncts. The `tan`
  and `cot` formulas need `cos u, cos v ≠ 0`, respectively `sin u, sin v ≠ 0`. Where the left
  side has a pole, both sides are `0` in Lean's convention `x/0 = 0`.
* 4.21.6–4.21.9: `dlmf_4_21_6`, …, `dlmf_4_21_9`.
* 4.21.10–4.21.11: `dlmf_4_21_10`, `dlmf_4_21_11`.

## §4.21(ii) Squares and Products

* 4.21.12–4.21.14: `dlmf_4_21_12`, `dlmf_4_21_13` (`cos z ≠ 0`), `dlmf_4_21_14` (`sin z ≠ 0`).
  At the poles both `sec² z` and `tan² z` are `0` in Lean, so the hypotheses are needed.
* 4.21.15–4.21.20: `dlmf_4_21_15`, …, `dlmf_4_21_20`.

## §4.21(iii) Multiples of the Argument

* 4.21.21–4.21.23: `dlmf_4_21_21`, `dlmf_4_21_22`, `dlmf_4_21_23`. The `±` square roots are
  stated as "the value is `±` the principal root". The sign for real arguments is resolved in
  `dlmf_4_21_21_real`, `dlmf_4_21_22_real`, `dlmf_4_21_23_real`. The other forms of 4.21.23 hold
  everywhere in Lean's convention.
* 4.21.24–4.21.33: `dlmf_4_21_24`, …, `dlmf_4_21_33`. The forms in `tan`, `cot` need
  `cos z ≠ 0`, `sin z ≠ 0` (`dlmf_4_21_27_tan`, `dlmf_4_21_28_tan`, `dlmf_4_21_29`).
* De Moivre 4.21.34: `dlmf_4_21_34` (`n ∈ ℤ`) and `dlmf_4_21_34_complex` (principal power,
  `n ∈ ℂ`, `−π < Re z ≤ π`). **Erratum** `dlmf_4_21_34_erratum`: at `Re z = −π`, which DLMF
  allows, the identity holds only for `n ∈ ℤ`. For example `z = −π`, `n = 1/2` gives
  `−i ≠ (−1)^{1/2} = i`.
* 4.21.35: `dlmf_4_21_35` (via `∏ₖ (1 − ζᵏ w) = 1 − wⁿ` for `ζ = e^{2πi/n}`).
* 4.21.36: `dlmf_4_21_36` (`t = tan(z/2)`, `cos(z/2) ≠ 0`; `dz = 2 dt/(1 + t²)` as
  `dt/dz = (1 + t²)/2`).

## §4.21(iv) Real and Imaginary Parts; Moduli

* 4.21.37–4.21.43 (`z = x + iy`): `dlmf_4_21_37`, …, `dlmf_4_21_43`. The `tan`, `cot` and
  `|tan|` formulas hold everywhere in Lean's convention: at a pole, the denominator
  `cos 2x + cosh 2y = 2|cos z|²` (respectively `cosh 2y − cos 2x = 2|sin z|²`) vanishes too.
-/

open Complex
open scoped Real ComplexConjugate

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

/-! ### §4.21(ii) Squares and Products -/

/-- **DLMF 4.21.12**: `sin² z + cos² z = 1`. -/
theorem dlmf_4_21_12 (z : ℂ) : sin z ^ 2 + cos z ^ 2 = 1 := sin_sq_add_cos_sq z

/-- **DLMF 4.21.13**: `sec² z = 1 + tan² z` (`cos z ≠ 0`). -/
theorem dlmf_4_21_13 {z : ℂ} (hz : cos z ≠ 0) : secC z ^ 2 = 1 + tan z ^ 2 := by
  rw [secC, tan_eq_sin_div_cos]
  field_simp
  linear_combination -sin_sq_add_cos_sq z

/-- **DLMF 4.21.14**: `csc² z = 1 + cot² z` (`sin z ≠ 0`). -/
theorem dlmf_4_21_14 {z : ℂ} (hz : sin z ≠ 0) : cscC z ^ 2 = 1 + cot z ^ 2 := by
  rw [cscC, cot_eq_cos_div_sin]
  field_simp
  linear_combination -sin_sq_add_cos_sq z

/-- **DLMF 4.21.15**: `2 sin u sin v = cos(u − v) − cos(u + v)`. -/
theorem dlmf_4_21_15 (u v : ℂ) : 2 * sin u * sin v = cos (u - v) - cos (u + v) := by
  rw [cos_sub, cos_add]; ring

/-- **DLMF 4.21.16**: `2 cos u cos v = cos(u − v) + cos(u + v)`. -/
theorem dlmf_4_21_16 (u v : ℂ) : 2 * cos u * cos v = cos (u - v) + cos (u + v) := by
  rw [cos_sub, cos_add]; ring

/-- **DLMF 4.21.17**: `2 sin u cos v = sin(u − v) + sin(u + v)`. -/
theorem dlmf_4_21_17 (u v : ℂ) : 2 * sin u * cos v = sin (u - v) + sin (u + v) := by
  rw [sin_sub, sin_add]; ring

/-- **DLMF 4.21.18**: `sin² u − sin² v = sin(u + v) sin(u − v)`. -/
theorem dlmf_4_21_18 (u v : ℂ) : sin u ^ 2 - sin v ^ 2 = sin (u + v) * sin (u - v) := by
  rw [sin_add, sin_sub]
  linear_combination sin v ^ 2 * sin_sq_add_cos_sq u - sin u ^ 2 * sin_sq_add_cos_sq v

/-- **DLMF 4.21.19**: `cos² u − cos² v = −sin(u + v) sin(u − v)`. -/
theorem dlmf_4_21_19 (u v : ℂ) : cos u ^ 2 - cos v ^ 2 = -(sin (u + v) * sin (u - v)) := by
  rw [sin_add, sin_sub]
  linear_combination cos v ^ 2 * sin_sq_add_cos_sq u - cos u ^ 2 * sin_sq_add_cos_sq v

/-- **DLMF 4.21.20**: `cos² u − sin² v = cos(u + v) cos(u − v)`. -/
theorem dlmf_4_21_20 (u v : ℂ) : cos u ^ 2 - sin v ^ 2 = cos (u + v) * cos (u - v) := by
  rw [cos_add, cos_sub]
  linear_combination sin v ^ 2 * sin_sq_add_cos_sq u - cos u ^ 2 * sin_sq_add_cos_sq v

/-! ### §4.21(iii) Multiples of the Argument -/

/-- A square root is `±` the principal one. -/
theorem eq_or_eq_neg_cpow_half {w q : ℂ} (h : w ^ 2 = q) :
    w = q ^ (1 / 2 : ℂ) ∨ w = -q ^ (1 / 2 : ℂ) := by
  have h2 := sq_cpow_one_half q
  have : (w - q ^ (1 / 2 : ℂ)) * (w + q ^ (1 / 2 : ℂ)) = 0 := by linear_combination h - h2
  rcases mul_eq_zero.mp this with h' | h'
  · left; linear_combination h'
  · right; linear_combination h'

theorem one_sub_cos_eq (z : ℂ) : 1 - cos z = 2 * sin (z / 2) ^ 2 := by
  have h := cos_two_mul (z / 2)
  rw [show 2 * (z / 2) = z by ring] at h
  linear_combination -h - 2 * sin_sq_add_cos_sq (z / 2)

theorem one_add_cos_eq (z : ℂ) : 1 + cos z = 2 * cos (z / 2) ^ 2 := by
  have h := cos_two_mul (z / 2)
  rw [show 2 * (z / 2) = z by ring] at h
  linear_combination h

theorem sin_eq_two_mul_half (z : ℂ) : sin z = 2 * sin (z / 2) * cos (z / 2) := by
  rw [← sin_two_mul, show 2 * (z / 2) = z by ring]

/-- **DLMF 4.21.21**: `sin(z/2) = ±((1 − cos z)/2)^{1/2}`. -/
theorem dlmf_4_21_21 (z : ℂ) :
    sin (z / 2) = ((1 - cos z) / 2) ^ (1 / 2 : ℂ) ∨
      sin (z / 2) = -((1 - cos z) / 2) ^ (1 / 2 : ℂ) :=
  eq_or_eq_neg_cpow_half (by rw [one_sub_cos_eq]; ring)

/-- **DLMF 4.21.22**: `cos(z/2) = ±((1 + cos z)/2)^{1/2}`. -/
theorem dlmf_4_21_22 (z : ℂ) :
    cos (z / 2) = ((1 + cos z) / 2) ^ (1 / 2 : ℂ) ∨
      cos (z / 2) = -((1 + cos z) / 2) ^ (1 / 2 : ℂ) :=
  eq_or_eq_neg_cpow_half (by rw [one_add_cos_eq]; ring)

/-- **DLMF 4.21.23**: `tan(z/2) = ±((1 − cos z)/(1 + cos z))^{1/2} = (1 − cos z)/sin z =
sin z/(1 + cos z)`. -/
theorem dlmf_4_21_23 (z : ℂ) :
    (tan (z / 2) = ((1 - cos z) / (1 + cos z)) ^ (1 / 2 : ℂ) ∨
      tan (z / 2) = -((1 - cos z) / (1 + cos z)) ^ (1 / 2 : ℂ)) ∧
    tan (z / 2) = (1 - cos z) / sin z ∧ tan (z / 2) = sin z / (1 + cos z) := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  refine ⟨eq_or_eq_neg_cpow_half ?_, ?_, ?_⟩
  · rw [tan_eq_sin_div_cos, one_sub_cos_eq z, one_add_cos_eq z, div_pow,
      mul_div_mul_left _ _ h2]
  · rw [tan_eq_sin_div_cos, one_sub_cos_eq z, sin_eq_two_mul_half z]
    rcases eq_or_ne (sin (z / 2)) 0 with hs | hs
    · simp [hs]
    · symm
      rw [show (2 : ℂ) * sin (z / 2) ^ 2 = (2 * sin (z / 2)) * sin (z / 2) by ring]
      exact mul_div_mul_left _ _ (mul_ne_zero h2 hs)
  · rw [tan_eq_sin_div_cos, one_add_cos_eq z, sin_eq_two_mul_half z]
    rcases eq_or_ne (cos (z / 2)) 0 with hc | hc
    · simp [hc]
    · symm
      rw [show 2 * sin (z / 2) * cos (z / 2) = (2 * cos (z / 2)) * sin (z / 2) by ring,
        show 2 * cos (z / 2) ^ 2 = (2 * cos (z / 2)) * cos (z / 2) by ring]
      exact mul_div_mul_left _ _ (mul_ne_zero h2 hc)

/-- **DLMF 4.21.21**, real sign: `sin(x/2) = √((1 − cos x)/2)` for `0 ≤ x ≤ 2π`. -/
theorem dlmf_4_21_21_real {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    Real.sin (x / 2) = √((1 - Real.cos x) / 2) := by
  rw [← Real.sqrt_sq (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))]
  congr 1
  have := Real.cos_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at this
  linear_combination -this + Real.sin_sq_add_cos_sq (x / 2)

/-- **DLMF 4.21.22**, real sign: `cos(x/2) = √((1 + cos x)/2)` for `−π ≤ x ≤ π`. -/
theorem dlmf_4_21_22_real {x : ℝ} (h0 : -π ≤ x) (h1 : x ≤ π) :
    Real.cos (x / 2) = √((1 + Real.cos x) / 2) := by
  rw [← Real.sqrt_sq (Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩)]
  congr 1
  have := Real.cos_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at this
  linear_combination this

/-- **DLMF 4.21.23**, real sign: `tan(x/2) = √((1 − cos x)/(1 + cos x))` for `0 ≤ x < π`. -/
theorem dlmf_4_21_23_real {x : ℝ} (h0 : 0 ≤ x) (h1 : x < π) :
    Real.tan (x / 2) = √((1 - Real.cos x) / (1 + Real.cos x)) := by
  have hs : 0 ≤ Real.sin (x / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hc : 0 < Real.cos (x / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  rw [Real.tan_eq_sin_div_cos, ← Real.sqrt_sq (div_nonneg hs hc.le)]
  congr 1
  have := Real.cos_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at this
  have h1c : 1 + Real.cos x = 2 * Real.cos (x / 2) ^ 2 := by linarith
  have h1s : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (x / 2)]
  rw [h1c, h1s, div_pow, mul_div_mul_left _ _ two_ne_zero]

/-- **DLMF 4.21.24–4.21.26**: `sin(−z) = −sin z`, `cos(−z) = cos z`, `tan(−z) = −tan z`. -/
theorem dlmf_4_21_24 (z : ℂ) : sin (-z) = -sin z := sin_neg z

theorem dlmf_4_21_25 (z : ℂ) : cos (-z) = cos z := cos_neg z

theorem dlmf_4_21_26 (z : ℂ) : tan (-z) = -tan z := tan_neg z

/-- **DLMF 4.21.27**: `sin(2z) = 2 sin z cos z`. -/
theorem dlmf_4_21_27 (z : ℂ) : sin (2 * z) = 2 * sin z * cos z := sin_two_mul z

/-- **DLMF 4.21.27**: `sin(2z) = 2 tan z/(1 + tan² z)` (`cos z ≠ 0`). -/
theorem dlmf_4_21_27_tan {z : ℂ} (hz : cos z ≠ 0) :
    sin (2 * z) = 2 * tan z / (1 + tan z ^ 2) := by
  rw [sin_two_mul, tan_eq_sin_div_cos]
  field_simp
  linear_combination sin z * sin_sq_add_cos_sq z

/-- **DLMF 4.21.28**: `cos(2z) = 2cos² z − 1 = 1 − 2 sin² z = cos² z − sin² z`. -/
theorem dlmf_4_21_28 (z : ℂ) :
    cos (2 * z) = 2 * cos z ^ 2 - 1 ∧ cos (2 * z) = 1 - 2 * sin z ^ 2 ∧
      cos (2 * z) = cos z ^ 2 - sin z ^ 2 := by
  refine ⟨cos_two_mul z, ?_, ?_⟩ <;> rw [cos_two_mul]
  · linear_combination 2 * sin_sq_add_cos_sq z
  · linear_combination sin_sq_add_cos_sq z

/-- **DLMF 4.21.28**: `cos(2z) = (1 − tan² z)/(1 + tan² z)` (`cos z ≠ 0`). -/
theorem dlmf_4_21_28_tan {z : ℂ} (hz : cos z ≠ 0) :
    cos (2 * z) = (1 - tan z ^ 2) / (1 + tan z ^ 2) := by
  rw [cos_two_mul, tan_eq_sin_div_cos]
  field_simp
  linear_combination 2 * cos z ^ 2 * sin_sq_add_cos_sq z

/-- **DLMF 4.21.29**: `tan(2z) = 2 tan z/(1 − tan² z) = 2 cot z/(cot² z − 1) = 2/(cot z − tan z)`
(`cos z ≠ 0`, `sin z ≠ 0` respectively). -/
theorem dlmf_4_21_29 {z : ℂ} :
    (cos z ≠ 0 → tan (2 * z) = 2 * tan z / (1 - tan z ^ 2)) ∧
    (sin z ≠ 0 → tan (2 * z) = 2 * cot z / (cot z ^ 2 - 1)) ∧
    (cos z ≠ 0 → sin z ≠ 0 → tan (2 * z) = 2 / (cot z - tan z)) := by
  have hT : tan (2 * z) = 2 * sin z * cos z / (cos z ^ 2 - sin z ^ 2) := by
    rw [tan_eq_sin_div_cos, sin_two_mul, (dlmf_4_21_28 z).2.2]
  refine ⟨fun hc => ?_, fun hs => ?_, fun hc hs => ?_⟩
  · rw [hT, tan_eq_sin_div_cos, ← mul_div_mul_right (2 * (sin z / cos z))
      (1 - (sin z / cos z) ^ 2) (pow_ne_zero 2 hc)]
    congr 1 <;> field_simp
  · rw [hT, cot_eq_cos_div_sin, ← mul_div_mul_right (2 * (cos z / sin z))
      ((cos z / sin z) ^ 2 - 1) (pow_ne_zero 2 hs)]
    congr 1 <;> field_simp
  · rw [hT, cot_eq_cos_div_sin, tan_eq_sin_div_cos,
      show cos z / sin z - sin z / cos z = (cos z ^ 2 - sin z ^ 2) / (sin z * cos z) by
        field_simp, div_div_eq_mul_div]
    ring

/-- **DLMF 4.21.30–4.21.31**: `sin 3z = 3 sin z − 4 sin³ z`, `cos 3z = −3 cos z + 4 cos³ z`. -/
theorem dlmf_4_21_30 (z : ℂ) : sin (3 * z) = 3 * sin z - 4 * sin z ^ 3 := sin_three_mul z

theorem dlmf_4_21_31 (z : ℂ) : cos (3 * z) = -3 * cos z + 4 * cos z ^ 3 := by
  rw [cos_three_mul]; ring

/-- **DLMF 4.21.32–4.21.33**: `sin 4z = 8 cos³ z sin z − 4 cos z sin z`,
`cos 4z = 8 cos⁴ z − 8 cos² z + 1`. -/
theorem dlmf_4_21_32 (z : ℂ) : sin (4 * z) = 8 * cos z ^ 3 * sin z - 4 * cos z * sin z := by
  rw [show 4 * z = 2 * (2 * z) by ring, sin_two_mul, sin_two_mul, cos_two_mul]; ring

theorem dlmf_4_21_33 (z : ℂ) : cos (4 * z) = 8 * cos z ^ 4 - 8 * cos z ^ 2 + 1 := by
  rw [show 4 * z = 2 * (2 * z) by ring, cos_two_mul, cos_two_mul]; ring

theorem cos_add_I_mul_sin (z : ℂ) : cos z + I * sin z = exp (z * I) := by
  rw [exp_mul_I]; ring

/-- **DLMF 4.21.34** (De Moivre): `cos(nz) + i sin(nz) = (cos z + i sin z)ⁿ`, `n ∈ ℤ`. -/
theorem dlmf_4_21_34 (n : ℤ) (z : ℂ) :
    cos (n * z) + I * sin (n * z) = (cos z + I * sin z) ^ n := by
  rw [cos_add_I_mul_sin, cos_add_I_mul_sin, ← exp_int_mul, mul_assoc]

/-- **DLMF 4.21.34** for complex `n` (principal power), valid for `−π < Re z ≤ π`. -/
theorem dlmf_4_21_34_complex (n : ℂ) {z : ℂ} (h1 : -π < z.re) (h2 : z.re ≤ π) :
    cos (n * z) + I * sin (n * z) = (cos z + I * sin z) ^ n := by
  rw [cos_add_I_mul_sin, cos_add_I_mul_sin, cpow_def_of_ne_zero (exp_ne_zero _),
    log_exp (by simpa using h1) (by simpa using h2)]
  ring_nf

/-- **Erratum to DLMF 4.21.34**: DLMF allows `−π ≤ Re z ≤ π` for fractional or complex `n`, but
at `Re z = −π` the identity holds exactly when `n ∈ ℤ`. -/
theorem dlmf_4_21_34_erratum (n : ℂ) {z : ℂ} (hz : z.re = -π) :
    cos (n * z) + I * sin (n * z) = (cos z + I * sin z) ^ n ↔ ∃ k : ℤ, n = k := by
  have hlog : log (exp (z * I)) = z * I + 2 * π * I := by
    have h : exp (z * I) = exp (z * I + 2 * π * I) := by rw [exp_add, exp_two_pi_mul_I, mul_one]
    rw [h, log_exp] <;> simp [hz] <;> linarith [Real.pi_pos]
  rw [cos_add_I_mul_sin, cos_add_I_mul_sin, cpow_def_of_ne_zero (exp_ne_zero _), hlog,
    show (z * I + 2 * π * I) * n = n * z * I + n * (2 * π * I) by ring, exp_add]
  constructor
  · intro h
    have h1 : exp (n * (2 * π * I)) = 1 := by
      have := mul_left_cancel₀ (exp_ne_zero (n * z * I)) (h.symm.trans (mul_one _).symm)
      exact this
    obtain ⟨k, hk⟩ := exp_eq_one_iff.mp h1
    refine ⟨k, ?_⟩
    have h2πI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    exact mul_right_cancel₀ h2πI hk
  · rintro ⟨k, rfl⟩
    rw [exp_int_mul_two_pi_mul_I, mul_one]

/-- `∏_{k<n} (1 − ζᵏ w) = 1 − wⁿ` for `ζ = e^{2πi/n}`. -/
theorem prod_one_sub_rootsOfUnity_mul {n : ℕ} (hn : 0 < n) (w : ℂ) :
    ∏ k ∈ Finset.range n, (1 - exp (2 * π * I / n) ^ k * w) = 1 - w ^ n := by
  have h := X_pow_sub_C_eq_prod (isPrimitiveRoot_exp n hn.ne') hn (rfl : w ^ n = w ^ n)
  have := congrArg (Polynomial.eval 1) h
  simpa [Polynomial.eval_prod] using this.symm

/-- `sin θ = (i/2) e^{−iθ} (1 − e^{2iθ})`. -/
theorem sin_eq_exp_form (θ : ℂ) : sin θ = I / 2 * exp (-I * θ) * (1 - exp (2 * I * θ)) := by
  have hE := exp_ne_zero (I * θ)
  rw [dlmf_4_14_1, show -I * θ = -(I * θ) by ring, exp_neg,
    show 2 * I * θ = I * θ + I * θ by ring, exp_add]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- **DLMF 4.21.35**: `sin(nz) = 2^{n−1} ∏_{k=0}^{n−1} sin(z + kπ/n)`, `n = 1, 2, 3, …`. -/
theorem dlmf_4_21_35 {n : ℕ} (hn : 0 < n) (z : ℂ) :
    sin (n * z) = 2 ^ (n - 1) * ∏ k ∈ Finset.range n, sin (z + k * π / n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [sin_eq_exp_form]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← exp_sum]
  have hroot : ∀ k : ℕ,
      exp (2 * I * (z + k * π / n)) = exp (2 * π * I / n) ^ k * exp (2 * I * z) := by
    intro k
    rw [← exp_nat_mul, ← exp_add]; congr 1; field_simp; ring
  simp only [hroot]
  rw [prod_one_sub_rootsOfUnity_mul hn, ← exp_nat_mul, show (n : ℂ) * (2 * I * z) = 2 * I * (n * z)
    by ring]
  have hs : (∑ k ∈ Finset.range n, (k : ℂ)) = n * (n - 1 : ℕ) / 2 := by
    rw [eq_div_iff two_ne_zero]
    have h := congrArg (Nat.cast : ℕ → ℂ) (Finset.sum_range_id_mul_two n)
    rwa [Nat.cast_mul, Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] at h
  have hsum : ∑ k ∈ Finset.range n, -I * (z + k * π / n) =
      -I * (n * z) + (n - 1 : ℕ) * (-(I * π / 2)) := by
    calc ∑ k ∈ Finset.range n, -I * (z + k * π / n)
        = ∑ k ∈ Finset.range n, (-I * z + (k : ℂ) * (-(I * π / n))) :=
          Finset.sum_congr rfl (fun k _ => by ring)
      _ = n * (-I * z) + (∑ k ∈ Finset.range n, (k : ℂ)) * (-(I * π / n)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            Finset.sum_mul]
      _ = _ := by rw [hs]; field_simp
  rw [hsum, exp_add, exp_nat_mul]
  have hiπ : exp (-(I * π / 2)) = -I := by
    rw [show -(I * π / 2) = (-(π / 2)) * I by ring, exp_mul_I, cos_neg, sin_neg,
      cos_pi_div_two, sin_pi_div_two]; ring
  rw [hiπ]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  have : (2 : ℂ) ^ m * (I / 2) ^ m * (-I) ^ m = 1 := by
    rw [← mul_pow, ← mul_pow]
    have : (2 : ℂ) * (I / 2) * -I = 1 := by
      field_simp; linear_combination -I_sq
    rw [this, one_pow]
  linear_combination (-(I / 2) * exp (-I * (↑(m + 1) * z)) * (1 - exp (2 * I * (↑(m + 1) * z))))
    * this

/-- **DLMF 4.21.36**: with `t = tan(z/2)` (`cos(z/2) ≠ 0`), `sin z = 2t/(1 + t²)`,
`cos z = (1 − t²)/(1 + t²)`, and `dt/dz = (1 + t²)/2`, i.e. `dz = 2 dt/(1 + t²)`. -/
theorem dlmf_4_21_36 {z : ℂ} (hz : cos (z / 2) ≠ 0) :
    sin z = 2 * tan (z / 2) / (1 + tan (z / 2) ^ 2) ∧
      cos z = (1 - tan (z / 2) ^ 2) / (1 + tan (z / 2) ^ 2) ∧
      HasDerivAt (fun z => tan (z / 2)) ((1 + tan (z / 2) ^ 2) / 2) z ∧
      (1 + tan (z / 2) ^ 2) / 2 ≠ 0 := by
  have h2 : z = 2 * (z / 2) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [h2]
    exact dlmf_4_21_27_tan hz
  · conv_lhs => rw [h2]
    exact dlmf_4_21_28_tan hz
  · have := (Complex.hasDerivAt_tan hz).comp z ((hasDerivAt_id z).div_const 2)
    refine this.congr_deriv ?_
    rw [tan_eq_sin_div_cos]
    field_simp
    linear_combination -sin_sq_add_cos_sq (z / 2)
  · rw [tan_eq_sin_div_cos]
    field_simp
    rw [show cos (z / 2) ^ 2 + sin (z / 2) ^ 2 = 1 by linear_combination sin_sq_add_cos_sq (z / 2)]
    exact div_ne_zero one_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 hz))

/-! ### §4.21(iv) Real and Imaginary Parts; Moduli -/

/-- **DLMF 4.21.37**: `sin z = sin x cosh y + i cos x sinh y`. -/
theorem dlmf_4_21_37 (x y : ℝ) :
    sin (x + y * I) = (Real.sin x * Real.cosh y : ℝ) + I * (Real.cos x * Real.sinh y : ℝ) := by
  rw [sin_add_mul_I]; push_cast; ring

/-- **DLMF 4.21.38**: `cos z = cos x cosh y − i sin x sinh y`. -/
theorem dlmf_4_21_38 (x y : ℝ) :
    cos (x + y * I) = (Real.cos x * Real.cosh y : ℝ) - I * (Real.sin x * Real.sinh y : ℝ) := by
  rw [cos_add_mul_I]; push_cast; ring

theorem conj_add_mul_I (x y : ℝ) : conj ((x : ℂ) + y * I) = x - y * I := by
  simp [map_add, map_mul, conj_ofReal, conj_I]; ring

/-- Expanding a quotient by a factor that is nonzero whenever the denominator is. -/
theorem div_eq_mul_div_mul_of_imp {a b k : ℂ} (hk : b ≠ 0 → k ≠ 0) :
    a / b = a * k / (b * k) := by
  rcases eq_or_ne b 0 with hb | hb
  · simp [hb]
  · exact (mul_div_mul_right a b (hk hb)).symm

/-- **DLMF 4.21.39**: `tan z = (sin 2x + i sinh 2y)/(cos 2x + cosh 2y)`. -/
theorem dlmf_4_21_39 (x y : ℝ) :
    tan (x + y * I) =
      ((Real.sin (2 * x) : ℝ) + I * (Real.sinh (2 * y) : ℝ)) /
        ((Real.cos (2 * x) + Real.cosh (2 * y) : ℝ) : ℂ) := by
  set u : ℂ := x + y * I
  set v : ℂ := x - y * I
  have hv : v = conj u := (conj_add_mul_I x y).symm
  have hk : cos u ≠ 0 → 2 * cos v ≠ 0 := fun h => by
    rw [hv, cos_conj]; exact mul_ne_zero two_ne_zero ((map_ne_zero _).mpr h)
  rw [tan_eq_sin_div_cos, div_eq_mul_div_mul_of_imp hk]
  congr 1
  · rw [← mul_assoc, mul_comm (sin u) 2, dlmf_4_21_17,
      show u - v = (2 * y : ℝ) * I by push_cast; ring,
      show u + v = ((2 * x : ℝ) : ℂ) by push_cast; ring, sin_mul_I, ofReal_sinh, ofReal_sin]
    ring
  · rw [← mul_assoc, mul_comm (cos u) 2, dlmf_4_21_16,
      show u - v = (2 * y : ℝ) * I by push_cast; ring,
      show u + v = ((2 * x : ℝ) : ℂ) by push_cast; ring, cos_mul_I]
    push_cast; ring

/-- **DLMF 4.21.40**: `cot z = (sin 2x − i sinh 2y)/(cosh 2y − cos 2x)`. -/
theorem dlmf_4_21_40 (x y : ℝ) :
    cot (x + y * I) =
      ((Real.sin (2 * x) : ℝ) - I * (Real.sinh (2 * y) : ℝ)) /
        ((Real.cosh (2 * y) - Real.cos (2 * x) : ℝ) : ℂ) := by
  set u : ℂ := x + y * I
  set v : ℂ := x - y * I
  have hv : v = conj u := (conj_add_mul_I x y).symm
  have hk : sin u ≠ 0 → 2 * sin v ≠ 0 := fun h => by
    rw [hv, sin_conj]; exact mul_ne_zero two_ne_zero ((map_ne_zero _).mpr h)
  rw [cot_eq_cos_div_sin, div_eq_mul_div_mul_of_imp hk]
  congr 1
  · rw [show cos u * (2 * sin v) = 2 * sin v * cos u by ring, dlmf_4_21_17,
      show v - u = -((2 * y : ℝ) * I) by push_cast; ring,
      show v + u = ((2 * x : ℝ) : ℂ) by push_cast; ring, sin_neg, sin_mul_I, ofReal_sinh,
      ofReal_sin]
    ring
  · rw [← mul_assoc, mul_comm (sin u) 2, dlmf_4_21_15,
      show u - v = (2 * y : ℝ) * I by push_cast; ring,
      show u + v = ((2 * x : ℝ) : ℂ) by push_cast; ring, cos_mul_I]
    push_cast; ring

/-- **DLMF 4.21.41**: `|sin z| = (sin² x + sinh² y)^{1/2} = (½(cosh 2y − cos 2x))^{1/2}`. -/
theorem dlmf_4_21_41 (x y : ℝ) :
    ‖sin (x + y * I)‖ = √(Real.sin x ^ 2 + Real.sinh y ^ 2) ∧
      √(Real.sin x ^ 2 + Real.sinh y ^ 2) = √((Real.cosh (2 * y) - Real.cos (2 * x)) / 2) := by
  constructor
  · rw [← Real.sqrt_sq (norm_nonneg _), norm_sin_sq_eq]; simp
  · congr 1
    rw [Real.cosh_two_mul, Real.cos_two_mul, Real.cosh_sq]
    linear_combination Real.sin_sq_add_cos_sq x

/-- **DLMF 4.21.42**: `|cos z| = (cos² x + sinh² y)^{1/2} = (½(cosh 2y + cos 2x))^{1/2}`. -/
theorem dlmf_4_21_42 (x y : ℝ) :
    ‖cos (x + y * I)‖ = √(Real.cos x ^ 2 + Real.sinh y ^ 2) ∧
      √(Real.cos x ^ 2 + Real.sinh y ^ 2) = √((Real.cosh (2 * y) + Real.cos (2 * x)) / 2) := by
  constructor
  · rw [← Real.sqrt_sq (norm_nonneg _), norm_cos_sq_eq]; simp
  · congr 1
    rw [Real.cosh_two_mul, Real.cos_two_mul, Real.cosh_sq]
    ring

/-- **DLMF 4.21.43**: `|tan z| = ((cosh 2y − cos 2x)/(cosh 2y + cos 2x))^{1/2}`. -/
theorem dlmf_4_21_43 (x y : ℝ) :
    ‖tan (x + y * I)‖ =
      √((Real.cosh (2 * y) - Real.cos (2 * x)) / (Real.cosh (2 * y) + Real.cos (2 * x))) := by
  obtain ⟨hs1, hs2⟩ := dlmf_4_21_41 x y
  obtain ⟨hc1, hc2⟩ := dlmf_4_21_42 x y
  have hb : 0 ≤ (Real.cosh (2 * y) + Real.cos (2 * x)) / 2 := by
    have : (Real.cosh (2 * y) + Real.cos (2 * x)) / 2 = Real.cos x ^ 2 + Real.sinh y ^ 2 := by
      rw [Real.cosh_two_mul, Real.cos_two_mul, Real.cosh_sq]; ring
    rw [this]; positivity
  rw [tan_eq_sin_div_cos, norm_div, hs1, hs2, hc1, hc2, ← Real.sqrt_div' _ hb,
    div_div_div_cancel_right₀ (two_ne_zero)]

end Azurite.DLMF
