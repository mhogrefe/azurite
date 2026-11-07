/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section14

/-!
# DLMF §4.16 Elementary Properties

* Figure 4.16.1 (quadrants for the angle `θ`): `inQuadrant`.
* Table 4.16.1 (signs in the four quadrants): `dlmf_table_4_16_1`.
* Table 4.16.2 (quarter periods and change of sign, complex `θ`): `dlmf_table_4_16_2_sin`, …,
  `dlmf_table_4_16_2_cot`.
* Table 4.16.3 (interrelations, principal square roots in the first quadrant, where all six
  functions are real, positive and finite): `dlmf_table_4_16_3_sin`, …, `dlmf_table_4_16_3_cot`
  (one theorem per column).

Real `csc θ`, `sec θ` are written `1 / sin θ`, `1 / cos θ` (4.14.5–4.14.6); complex ones are
`cscC`, `secC` from §4.14.
-/

open Set Complex
open scoped Real

namespace Azurite.DLMF

/-! ### Figure 4.16.1 and Table 4.16.1 -/

/-- **Figure 4.16.1**: the angle `θ` lies in quadrant `q` (`q = 1, 2, 3, 4`) when, modulo `2π`,
`(q − 1)π/2 < θ < qπ/2`. -/
def inQuadrant (q : ℕ) (θ : ℝ) : Prop :=
  ∃ k : ℤ, θ + k * (2 * π) ∈ Ioo (((q : ℝ) - 1) * (π / 2)) (q * (π / 2))

theorem sin_cos_signs_of_mem {x : ℝ} :
    (x ∈ Ioo 0 (π / 2) → 0 < Real.sin x ∧ 0 < Real.cos x) ∧
    (x ∈ Ioo (π / 2) π → 0 < Real.sin x ∧ Real.cos x < 0) ∧
    (x ∈ Ioo π (3 * (π / 2)) → Real.sin x < 0 ∧ Real.cos x < 0) ∧
    (x ∈ Ioo (3 * (π / 2)) (2 * π) → Real.sin x < 0 ∧ 0 < Real.cos x) := by
  have hpi := Real.pi_pos
  refine ⟨fun h => ⟨Real.sin_pos_of_pos_of_lt_pi h.1 (by linarith [h.2]),
      Real.cos_pos_of_mem_Ioo ⟨by linarith [h.1], h.2⟩⟩,
    fun h => ⟨Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) h.2,
      Real.cos_neg_of_pi_div_two_lt_of_lt h.1 (by linarith [h.2])⟩,
    fun h => ⟨?_, Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [h.1]) (by linarith [h.2])⟩,
    fun h => ⟨?_, ?_⟩⟩
  · have := Real.sin_pos_of_pos_of_lt_pi (x := x - π) (by linarith [h.1]) (by linarith [h.2])
    rw [Real.sin_sub_pi] at this; linarith
  · have := Real.sin_pos_of_pos_of_lt_pi (x := x - π) (by linarith [h.1]) (by linarith [h.2])
    rw [Real.sin_sub_pi] at this; linarith
  · rw [← Real.cos_sub_two_pi]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **Table 4.16.1**: signs of the trigonometric functions in the four quadrants
(`I: + + +`, `II: + − −`, `III: − − +`, `IV: − + −` for `sin, csc | cos, sec | tan, cot`). -/
theorem dlmf_table_4_16_1 (θ : ℝ) :
    (inQuadrant 1 θ → 0 < Real.sin θ ∧ 0 < 1 / Real.sin θ ∧ 0 < Real.cos θ ∧
      0 < 1 / Real.cos θ ∧ 0 < Real.tan θ ∧ 0 < Real.cot θ) ∧
    (inQuadrant 2 θ → 0 < Real.sin θ ∧ 0 < 1 / Real.sin θ ∧ Real.cos θ < 0 ∧
      1 / Real.cos θ < 0 ∧ Real.tan θ < 0 ∧ Real.cot θ < 0) ∧
    (inQuadrant 3 θ → Real.sin θ < 0 ∧ 1 / Real.sin θ < 0 ∧ Real.cos θ < 0 ∧
      1 / Real.cos θ < 0 ∧ 0 < Real.tan θ ∧ 0 < Real.cot θ) ∧
    (inQuadrant 4 θ → Real.sin θ < 0 ∧ 1 / Real.sin θ < 0 ∧ 0 < Real.cos θ ∧
      0 < 1 / Real.cos θ ∧ Real.tan θ < 0 ∧ Real.cot θ < 0) := by
  have red : ∀ k : ℤ, Real.sin θ = Real.sin (θ + k * (2 * π)) ∧
      Real.cos θ = Real.cos (θ + k * (2 * π)) := fun k =>
    ⟨(Real.sin_add_int_mul_two_pi θ k).symm, (Real.cos_add_int_mul_two_pi θ k).symm⟩
  have hsc := fun k : ℤ => sin_cos_signs_of_mem (x := θ + k * (2 * π))
  refine ⟨fun ⟨k, hk⟩ => ?_, fun ⟨k, hk⟩ => ?_, fun ⟨k, hk⟩ => ?_, fun ⟨k, hk⟩ => ?_⟩ <;>
    rw [Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin, (red k).1, (red k).2] <;>
    norm_num at hk
  · obtain ⟨hs, hc⟩ := (hsc k).1 hk
    exact ⟨hs, by positivity, hc, by positivity, div_pos hs hc, div_pos hc hs⟩
  · obtain ⟨hs, hc⟩ := (hsc k).2.1 ⟨by linarith [hk.1], by linarith [hk.2]⟩
    exact ⟨hs, by positivity, hc, one_div_neg.mpr hc, div_neg_of_pos_of_neg hs hc,
      div_neg_of_neg_of_pos hc hs⟩
  · obtain ⟨hs, hc⟩ := (hsc k).2.2.1 ⟨by linarith [hk.1], by linarith [hk.2]⟩
    exact ⟨hs, one_div_neg.mpr hs, hc, one_div_neg.mpr hc, div_pos_of_neg_of_neg hs hc,
      div_pos_of_neg_of_neg hc hs⟩
  · obtain ⟨hs, hc⟩ := (hsc k).2.2.2 ⟨by linarith [hk.1], by linarith [hk.2]⟩
    exact ⟨hs, one_div_neg.mpr hs, hc, by positivity, div_neg_of_neg_of_pos hs hc,
      div_neg_of_pos_of_neg hc hs⟩

/-! ### Table 4.16.2 -/

theorem sin_three_pi_div_two' : sin (3 * π / 2) = -1 := by
  rw [show (3 : ℂ) * π / 2 = π / 2 + π by ring, sin_add_pi, sin_pi_div_two]

theorem cos_three_pi_div_two' : cos (3 * π / 2) = 0 := by
  rw [show (3 : ℂ) * π / 2 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two, neg_zero]

/-- **Table 4.16.2**, row `sin x`, for `x = −θ, π/2 ± θ, π ± θ, 3π/2 ± θ, 2π ± θ`. -/
theorem dlmf_table_4_16_2_sin (θ : ℂ) :
    sin (-θ) = -sin θ ∧ sin (π / 2 + θ) = cos θ ∧ sin (π / 2 - θ) = cos θ ∧
      sin (π + θ) = -sin θ ∧ sin (π - θ) = sin θ ∧ sin (3 * π / 2 + θ) = -cos θ ∧
      sin (3 * π / 2 - θ) = -cos θ ∧ sin (2 * π + θ) = sin θ ∧ sin (2 * π - θ) = -sin θ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [sin_add, sin_sub, sin_three_pi_div_two', cos_three_pi_div_two']

/-- **Table 4.16.2**, row `cos x`. -/
theorem dlmf_table_4_16_2_cos (θ : ℂ) :
    cos (-θ) = cos θ ∧ cos (π / 2 + θ) = -sin θ ∧ cos (π / 2 - θ) = sin θ ∧
      cos (π + θ) = -cos θ ∧ cos (π - θ) = -cos θ ∧ cos (3 * π / 2 + θ) = sin θ ∧
      cos (3 * π / 2 - θ) = -sin θ ∧ cos (2 * π + θ) = cos θ ∧ cos (2 * π - θ) = cos θ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [cos_add, cos_sub, sin_three_pi_div_two', cos_three_pi_div_two']

/-- **Table 4.16.2**, row `tan x`. -/
theorem dlmf_table_4_16_2_tan (θ : ℂ) :
    tan (-θ) = -tan θ ∧ tan (π / 2 + θ) = -cot θ ∧ tan (π / 2 - θ) = cot θ ∧
      tan (π + θ) = tan θ ∧ tan (π - θ) = -tan θ ∧ tan (3 * π / 2 + θ) = -cot θ ∧
      tan (3 * π / 2 - θ) = cot θ ∧ tan (2 * π + θ) = tan θ ∧ tan (2 * π - θ) = -tan θ := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := dlmf_table_4_16_2_sin θ
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := dlmf_table_4_16_2_cos θ
  simp only [tan_eq_sin_div_cos, cot_eq_cos_div_sin, s1, s2, s3, s4, s5, s6, s7, s8, s9, c1, c2,
    c3, c4, c5, c6, c7, c8, c9, neg_div, div_neg, neg_neg, and_self]

/-- **Table 4.16.2**, row `csc x`. -/
theorem dlmf_table_4_16_2_csc (θ : ℂ) :
    cscC (-θ) = -cscC θ ∧ cscC (π / 2 + θ) = secC θ ∧ cscC (π / 2 - θ) = secC θ ∧
      cscC (π + θ) = -cscC θ ∧ cscC (π - θ) = cscC θ ∧ cscC (3 * π / 2 + θ) = -secC θ ∧
      cscC (3 * π / 2 - θ) = -secC θ ∧ cscC (2 * π + θ) = cscC θ ∧
      cscC (2 * π - θ) = -cscC θ := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := dlmf_table_4_16_2_sin θ
  simp only [cscC, secC, s1, s2, s3, s4, s5, s6, s7, s8, s9, div_neg, and_self]

/-- **Table 4.16.2**, row `sec x`. -/
theorem dlmf_table_4_16_2_sec (θ : ℂ) :
    secC (-θ) = secC θ ∧ secC (π / 2 + θ) = -cscC θ ∧ secC (π / 2 - θ) = cscC θ ∧
      secC (π + θ) = -secC θ ∧ secC (π - θ) = -secC θ ∧ secC (3 * π / 2 + θ) = cscC θ ∧
      secC (3 * π / 2 - θ) = -cscC θ ∧ secC (2 * π + θ) = secC θ ∧
      secC (2 * π - θ) = secC θ := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := dlmf_table_4_16_2_cos θ
  simp only [cscC, secC, c1, c2, c3, c4, c5, c6, c7, c8, c9, div_neg, and_self]

/-- **Table 4.16.2**, row `cot x`. -/
theorem dlmf_table_4_16_2_cot (θ : ℂ) :
    cot (-θ) = -cot θ ∧ cot (π / 2 + θ) = -tan θ ∧ cot (π / 2 - θ) = tan θ ∧
      cot (π + θ) = cot θ ∧ cot (π - θ) = -cot θ ∧ cot (3 * π / 2 + θ) = -tan θ ∧
      cot (3 * π / 2 - θ) = tan θ ∧ cot (2 * π + θ) = cot θ ∧ cot (2 * π - θ) = -cot θ := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := dlmf_table_4_16_2_sin θ
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := dlmf_table_4_16_2_cos θ
  simp only [tan_eq_sin_div_cos, cot_eq_cos_div_sin, s1, s2, s3, s4, s5, s6, s7, s8, s9, c1, c2,
    c3, c4, c5, c6, c7, c8, c9, neg_div, div_neg, neg_neg, and_self]

/-! ### Table 4.16.3 -/

theorem sqrt_eq_of_eq_sq {x y : ℝ} (hy : 0 ≤ y) (h : x = y ^ 2) : √x = y := by
  rw [h, Real.sqrt_sq hy]

/-- The first quadrant: `sin θ`, `cos θ` positive with `sin² θ + cos² θ = 1`. -/
theorem first_quadrant_facts {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) :
    0 < Real.sin θ ∧ 0 < Real.cos θ ∧ Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 :=
  ⟨(sin_cos_signs_of_mem.1 hθ).1, (sin_cos_signs_of_mem.1 hθ).2, Real.sin_sq_add_cos_sq θ⟩

/-- **Table 4.16.3**, column `sin θ = a` (first quadrant, principal square roots). -/
theorem dlmf_table_4_16_3_sin {θ a : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) (ha : Real.sin θ = a) :
    Real.sin θ = a ∧ Real.cos θ = √(1 - a ^ 2) ∧ Real.tan θ = a * (√(1 - a ^ 2))⁻¹ ∧
      1 / Real.sin θ = a⁻¹ ∧ 1 / Real.cos θ = (√(1 - a ^ 2))⁻¹ ∧
      Real.cot θ = a⁻¹ * √(1 - a ^ 2) := by
  subst ha
  obtain ⟨hs, hc, hsc⟩ := first_quadrant_facts hθ
  have h1 : √(1 - Real.sin θ ^ 2) = Real.cos θ := sqrt_eq_of_eq_sq hc.le (by linarith)
  rw [h1, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> field_simp

/-- **Table 4.16.3**, column `cos θ = a`. -/
theorem dlmf_table_4_16_3_cos {θ a : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) (ha : Real.cos θ = a) :
    Real.sin θ = √(1 - a ^ 2) ∧ Real.cos θ = a ∧ Real.tan θ = a⁻¹ * √(1 - a ^ 2) ∧
      1 / Real.sin θ = (√(1 - a ^ 2))⁻¹ ∧ 1 / Real.cos θ = a⁻¹ ∧
      Real.cot θ = a * (√(1 - a ^ 2))⁻¹ := by
  subst ha
  obtain ⟨hs, hc, hsc⟩ := first_quadrant_facts hθ
  have h1 : √(1 - Real.cos θ ^ 2) = Real.sin θ := sqrt_eq_of_eq_sq hs.le (by linarith)
  rw [h1, Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> field_simp

/-- **Table 4.16.3**, column `tan θ = a`. -/
theorem dlmf_table_4_16_3_tan {θ a : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) (ha : Real.tan θ = a) :
    Real.sin θ = a * (√(1 + a ^ 2))⁻¹ ∧ Real.cos θ = (√(1 + a ^ 2))⁻¹ ∧ Real.tan θ = a ∧
      1 / Real.sin θ = a⁻¹ * √(1 + a ^ 2) ∧ 1 / Real.cos θ = √(1 + a ^ 2) ∧
      Real.cot θ = a⁻¹ := by
  subst ha
  obtain ⟨hs, hc, hsc⟩ := first_quadrant_facts hθ
  rw [Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin]
  have h1 : √(1 + (Real.sin θ / Real.cos θ) ^ 2) = 1 / Real.cos θ :=
    sqrt_eq_of_eq_sq (by positivity) (by field_simp; linarith)
  rw [h1]
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_⟩ <;> field_simp

/-- **Table 4.16.3**, column `csc θ = a`. -/
theorem dlmf_table_4_16_3_csc {θ a : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) (ha : 1 / Real.sin θ = a) :
    Real.sin θ = a⁻¹ ∧ Real.cos θ = a⁻¹ * √(a ^ 2 - 1) ∧ Real.tan θ = (√(a ^ 2 - 1))⁻¹ ∧
      1 / Real.sin θ = a ∧ 1 / Real.cos θ = a * (√(a ^ 2 - 1))⁻¹ ∧
      Real.cot θ = √(a ^ 2 - 1) := by
  subst ha
  obtain ⟨hs, hc, hsc⟩ := first_quadrant_facts hθ
  rw [Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin]
  have h1 : √((1 / Real.sin θ) ^ 2 - 1) = Real.cos θ / Real.sin θ :=
    sqrt_eq_of_eq_sq (by positivity) (by field_simp; linarith)
  rw [h1]
  refine ⟨?_, ?_, ?_, rfl, ?_, rfl⟩ <;> field_simp

/-- **Table 4.16.3**, column `sec θ = a`. -/
theorem dlmf_table_4_16_3_sec {θ a : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) (ha : 1 / Real.cos θ = a) :
    Real.sin θ = a⁻¹ * √(a ^ 2 - 1) ∧ Real.cos θ = a⁻¹ ∧ Real.tan θ = √(a ^ 2 - 1) ∧
      1 / Real.sin θ = a * (√(a ^ 2 - 1))⁻¹ ∧ 1 / Real.cos θ = a ∧
      Real.cot θ = (√(a ^ 2 - 1))⁻¹ := by
  subst ha
  obtain ⟨hs, hc, hsc⟩ := first_quadrant_facts hθ
  rw [Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin]
  have h1 : √((1 / Real.cos θ) ^ 2 - 1) = Real.sin θ / Real.cos θ :=
    sqrt_eq_of_eq_sq (by positivity) (by field_simp; linarith)
  rw [h1]
  refine ⟨?_, ?_, rfl, ?_, rfl, ?_⟩ <;> field_simp

/-- **Table 4.16.3**, column `cot θ = a`. -/
theorem dlmf_table_4_16_3_cot {θ a : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) (ha : Real.cot θ = a) :
    Real.sin θ = (√(1 + a ^ 2))⁻¹ ∧ Real.cos θ = a * (√(1 + a ^ 2))⁻¹ ∧ Real.tan θ = a⁻¹ ∧
      1 / Real.sin θ = √(1 + a ^ 2) ∧ 1 / Real.cos θ = a⁻¹ * √(1 + a ^ 2) ∧
      Real.cot θ = a := by
  subst ha
  obtain ⟨hs, hc, hsc⟩ := first_quadrant_facts hθ
  rw [Real.tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin]
  have h1 : √(1 + (Real.cos θ / Real.sin θ) ^ 2) = 1 / Real.sin θ :=
    sqrt_eq_of_eq_sq (by positivity) (by field_simp; linarith)
  rw [h1]
  refine ⟨?_, ?_, ?_, rfl, ?_, rfl⟩ <;> field_simp

end Azurite.DLMF
