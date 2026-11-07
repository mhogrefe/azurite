/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section14
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv

/-!
# DLMF §4.17 Special Values and Limits

* Table 4.17.1 (values at multiples of `π/12`): one theorem per row, `dlmf_table_4_17_1_0`,
  `_pi_div_twelve`, …, `_pi`. A finite row is `TrigRow θ s c t cs se ct`
  (`sin, cos, tan, csc = 1/sin, sec = 1/cos, cot`). An entry `∞` is a pole,
  `|f(x)| → ∞` as `x → θ`, `x ≠ θ` (from §4.14).
* 4.17.1–4.17.3: `dlmf_4_17_1`, `dlmf_4_17_2`, `dlmf_4_17_3` (complex `z → 0`, `z ≠ 0`).
-/

open Set Filter Topology Complex
open scoped Real

namespace Azurite.DLMF

/-! ### Table 4.17.1 -/

/-- A finite row of Table 4.17.1: the values of `sin, cos, tan, csc, sec, cot` at `θ`. -/
def TrigRow (θ s c t cs se ct : ℝ) : Prop :=
  Real.sin θ = s ∧ Real.cos θ = c ∧ Real.tan θ = t ∧ 1 / Real.sin θ = cs ∧
    1 / Real.cos θ = se ∧ Real.cot θ = ct

theorem trigRow_of {θ s c t cs se ct : ℝ} (hs : Real.sin θ = s) (hc : Real.cos θ = c)
    (hs0 : s ≠ 0) (hc0 : c ≠ 0) (ht : t * c = s) (hcs : cs * s = 1) (hse : se * c = 1)
    (hct : ct * s = c) : TrigRow θ s c t cs se ct := by
  refine ⟨hs, hc, ?_, ?_, ?_, ?_⟩
  · rw [Real.tan_eq_sin_div_cos, hs, hc, eq_comm, eq_div_iff hc0, ht]
  · rw [hs, eq_comm, eq_div_iff hs0, hcs]
  · rw [hc, eq_comm, eq_div_iff hc0, hse]
  · rw [Real.cot_eq_cos_div_sin, hs, hc, eq_comm, eq_div_iff hs0, hct]

/-- Rows for `π − θ` from rows for `θ` (Table 4.16.2). -/
theorem trigRow_pi_sub {θ s c t cs se ct : ℝ} (h : TrigRow θ s c t cs se ct) :
    TrigRow (π - θ) s (-c) (-t) cs (-se) (-ct) := by
  obtain ⟨hs, hc, ht, hcs, hse, hct⟩ := h
  refine ⟨by rw [Real.sin_pi_sub, hs], by rw [Real.cos_pi_sub, hc], ?_,
    by rw [Real.sin_pi_sub, hcs], ?_, ?_⟩
  · rw [Real.tan_eq_sin_div_cos, Real.sin_pi_sub, Real.cos_pi_sub, div_neg,
      ← Real.tan_eq_sin_div_cos, ht]
  · rw [Real.cos_pi_sub, div_neg, hse]
  · rw [Real.cot_eq_cos_div_sin, Real.sin_pi_sub, Real.cos_pi_sub, neg_div,
      ← Real.cot_eq_cos_div_sin, hct]

/-- A complex pole at a real point gives a pole of the real function. -/
theorem tendsto_abs_of_complex_pole {f : ℂ → ℂ} {g : ℝ → ℝ} {θ : ℝ}
    (h : Tendsto (fun w => ‖f w‖) (𝓝[≠] (θ : ℂ)) atTop) (hfg : ∀ x : ℝ, f x = g x) :
    Tendsto (fun x => |g x|) (𝓝[≠] θ) atTop := by
  have ho : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] θ) (𝓝[≠] (θ : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(continuous_ofReal.tendsto θ).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun x hx => by simpa using hx⟩
  refine (h.comp ho).congr fun x => ?_
  simp [hfg, Complex.norm_real]

theorem ofReal_cscC (x : ℝ) : cscC x = ((1 / Real.sin x : ℝ) : ℂ) := by
  simp [cscC, ← ofReal_sin]

theorem ofReal_secC (x : ℝ) : secC x = ((1 / Real.cos x : ℝ) : ℂ) := by
  simp [secC, ← ofReal_cos]

/-- **Table 4.17.1**, `θ = 0`: `0, 1, 0, ∞, 1, ∞`. -/
theorem dlmf_table_4_17_1_0 :
    Real.sin 0 = 0 ∧ Real.cos 0 = 1 ∧ Real.tan 0 = 0 ∧
      Tendsto (fun x => |1 / Real.sin x|) (𝓝[≠] 0) atTop ∧ 1 / Real.cos 0 = 1 ∧
      Tendsto (fun x => |Real.cot x|) (𝓝[≠] 0) atTop := by
  refine ⟨Real.sin_zero, Real.cos_zero, Real.tan_zero, ?_, by simp, ?_⟩
  · exact tendsto_abs_of_complex_pole (θ := 0) (by simpa using dlmf_4_14_csc_poles sin_zero)
      ofReal_cscC
  · exact tendsto_abs_of_complex_pole (θ := 0) (by simpa using dlmf_4_14_cot_poles sin_zero)
      fun x => (ofReal_cot x).symm

/-- **Table 4.17.1**, `θ = π/2`: `1, 0, ∞, 1, ∞, 0`. -/
theorem dlmf_table_4_17_1_pi_div_two :
    Real.sin (π / 2) = 1 ∧ Real.cos (π / 2) = 0 ∧
      Tendsto (fun x => |Real.tan x|) (𝓝[≠] (π / 2)) atTop ∧ 1 / Real.sin (π / 2) = 1 ∧
      Tendsto (fun x => |1 / Real.cos x|) (𝓝[≠] (π / 2)) atTop ∧ Real.cot (π / 2) = 0 := by
  have hc : cos ((π / 2 : ℝ) : ℂ) = 0 := by push_cast; exact cos_pi_div_two
  refine ⟨Real.sin_pi_div_two, Real.cos_pi_div_two, ?_, by simp, ?_, ?_⟩
  · exact tendsto_abs_of_complex_pole (dlmf_4_14_tan_poles hc) fun x => (ofReal_tan x).symm
  · exact tendsto_abs_of_complex_pole (dlmf_4_14_sec_poles hc) ofReal_secC
  · rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_two, zero_div]

/-- **Table 4.17.1**, `θ = π`: `0, −1, 0, ∞, −1, ∞`. -/
theorem dlmf_table_4_17_1_pi :
    Real.sin π = 0 ∧ Real.cos π = -1 ∧ Real.tan π = 0 ∧
      Tendsto (fun x => |1 / Real.sin x|) (𝓝[≠] π) atTop ∧ 1 / Real.cos π = -1 ∧
      Tendsto (fun x => |Real.cot x|) (𝓝[≠] π) atTop := by
  have hs : sin ((π : ℝ) : ℂ) = 0 := sin_pi
  refine ⟨Real.sin_pi, Real.cos_pi, by rw [Real.tan_eq_sin_div_cos, Real.sin_pi, zero_div],
    ?_, by simp, ?_⟩
  · exact tendsto_abs_of_complex_pole (dlmf_4_14_csc_poles hs) ofReal_cscC
  · exact tendsto_abs_of_complex_pole (dlmf_4_14_cot_poles hs) fun x => (ofReal_cot x).symm

theorem sqrt_two_three_facts : (√2) ^ 2 = 2 ∧ (√3) ^ 2 = 3 ∧ 0 < √2 ∧ 1 < √3 :=
  ⟨Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num), by positivity,
    Real.lt_sqrt (by norm_num) |>.mpr (by norm_num)⟩

theorem sin_pi_div_twelve_eq : Real.sin (π / 12) = 1 / 4 * √2 * (√3 - 1) := by
  rw [show π / 12 = π / 3 - π / 4 by ring, Real.sin_sub, Real.sin_pi_div_three,
    Real.cos_pi_div_three, Real.cos_pi_div_four, Real.sin_pi_div_four]
  ring

theorem cos_pi_div_twelve_eq : Real.cos (π / 12) = 1 / 4 * √2 * (√3 + 1) := by
  rw [show π / 12 = π / 3 - π / 4 by ring, Real.cos_sub, Real.sin_pi_div_three,
    Real.cos_pi_div_three, Real.cos_pi_div_four, Real.sin_pi_div_four]
  ring

/-- **Table 4.17.1**, `θ = π/12`. -/
theorem dlmf_table_4_17_1_pi_div_twelve :
    TrigRow (π / 12) (1 / 4 * √2 * (√3 - 1)) (1 / 4 * √2 * (√3 + 1)) (2 - √3)
      (√2 * (√3 + 1)) (√2 * (√3 - 1)) (2 + √3) := by
  obtain ⟨ha, hb, ha0, hb1⟩ := sqrt_two_three_facts
  have hs0 : 1 / 4 * √2 * (√3 - 1) ≠ 0 := by
    have : 0 < √3 - 1 := by linarith
    positivity
  have hc0 : 1 / 4 * √2 * (√3 + 1) ≠ 0 := by positivity
  refine trigRow_of sin_pi_div_twelve_eq cos_pi_div_twelve_eq hs0 hc0 ?_ ?_ ?_ ?_
  · linear_combination (-√2 / 4) * hb
  · linear_combination ((√3 ^ 2 - 3) / 4 + 1 / 2) * ha + 1 / 2 * hb
  · linear_combination ((√3 ^ 2 - 3) / 4 + 1 / 2) * ha + 1 / 2 * hb
  · linear_combination (√2 / 4) * hb

/-- **Table 4.17.1**, `θ = π/6`. -/
theorem dlmf_table_4_17_1_pi_div_six :
    TrigRow (π / 6) (1 / 2) (1 / 2 * √3) (1 / 3 * √3) 2 (2 / 3 * √3) √3 := by
  obtain ⟨-, hb, -, hb1⟩ := sqrt_two_three_facts
  refine trigRow_of Real.sin_pi_div_six (by rw [Real.cos_pi_div_six]; ring) (by norm_num)
    (by positivity) ?_ (by norm_num) ?_ (by ring)
  · linear_combination hb / 6
  · linear_combination hb / 3

/-- **Table 4.17.1**, `θ = π/4`. -/
theorem dlmf_table_4_17_1_pi_div_four :
    TrigRow (π / 4) (1 / 2 * √2) (1 / 2 * √2) 1 √2 √2 1 := by
  obtain ⟨ha, -, ha0, -⟩ := sqrt_two_three_facts
  refine trigRow_of (by rw [Real.sin_pi_div_four]; ring) (by rw [Real.cos_pi_div_four]; ring)
    (by positivity) (by positivity) (by ring) ?_ ?_ (by ring)
  · linear_combination ha / 2
  · linear_combination ha / 2

/-- **Table 4.17.1**, `θ = π/3`. -/
theorem dlmf_table_4_17_1_pi_div_three :
    TrigRow (π / 3) (1 / 2 * √3) (1 / 2) √3 (2 / 3 * √3) 2 (1 / 3 * √3) := by
  obtain ⟨-, hb, -, hb1⟩ := sqrt_two_three_facts
  refine trigRow_of (by rw [Real.sin_pi_div_three]; ring) Real.cos_pi_div_three (by positivity)
    (by norm_num) (by ring) ?_ (by norm_num) ?_
  · linear_combination hb / 3
  · linear_combination hb / 6

/-- **Table 4.17.1**, `θ = 5π/12`. -/
theorem dlmf_table_4_17_1_five_pi_div_twelve :
    TrigRow (5 * π / 12) (1 / 4 * √2 * (√3 + 1)) (1 / 4 * √2 * (√3 - 1)) (2 + √3)
      (√2 * (√3 - 1)) (√2 * (√3 + 1)) (2 - √3) := by
  obtain ⟨ha, hb, ha0, hb1⟩ := sqrt_two_three_facts
  have hs0 : 1 / 4 * √2 * (√3 - 1) ≠ 0 := by
    have : 0 < √3 - 1 := by linarith
    positivity
  have hc0 : 1 / 4 * √2 * (√3 + 1) ≠ 0 := by positivity
  have e : 5 * π / 12 = π / 2 - π / 12 := by ring
  refine trigRow_of (by rw [e, Real.sin_pi_div_two_sub, cos_pi_div_twelve_eq])
    (by rw [e, Real.cos_pi_div_two_sub, sin_pi_div_twelve_eq]) hc0 hs0 ?_ ?_ ?_ ?_
  · linear_combination (√2 / 4) * hb
  · linear_combination ((√3 ^ 2 - 3) / 4 + 1 / 2) * ha + 1 / 2 * hb
  · linear_combination ((√3 ^ 2 - 3) / 4 + 1 / 2) * ha + 1 / 2 * hb
  · linear_combination (-√2 / 4) * hb

/-- **Table 4.17.1**, `θ = 7π/12`. -/
theorem dlmf_table_4_17_1_seven_pi_div_twelve :
    TrigRow (7 * π / 12) (1 / 4 * √2 * (√3 + 1)) (-(1 / 4 * √2 * (√3 - 1))) (-(2 + √3))
      (√2 * (√3 - 1)) (-(√2 * (√3 + 1))) (-(2 - √3)) := by
  rw [show 7 * π / 12 = π - 5 * π / 12 by ring]
  exact trigRow_pi_sub dlmf_table_4_17_1_five_pi_div_twelve

/-- **Table 4.17.1**, `θ = 2π/3`. -/
theorem dlmf_table_4_17_1_two_pi_div_three :
    TrigRow (2 * π / 3) (1 / 2 * √3) (-(1 / 2)) (-√3) (2 / 3 * √3) (-2) (-(1 / 3 * √3)) := by
  rw [show 2 * π / 3 = π - π / 3 by ring]
  exact trigRow_pi_sub dlmf_table_4_17_1_pi_div_three

/-- **Table 4.17.1**, `θ = 3π/4`. -/
theorem dlmf_table_4_17_1_three_pi_div_four :
    TrigRow (3 * π / 4) (1 / 2 * √2) (-(1 / 2 * √2)) (-1) √2 (-√2) (-1) := by
  rw [show 3 * π / 4 = π - π / 4 by ring]
  exact trigRow_pi_sub dlmf_table_4_17_1_pi_div_four

/-- **Table 4.17.1**, `θ = 5π/6`. -/
theorem dlmf_table_4_17_1_five_pi_div_six :
    TrigRow (5 * π / 6) (1 / 2) (-(1 / 2 * √3)) (-(1 / 3 * √3)) 2 (-(2 / 3 * √3)) (-√3) := by
  rw [show 5 * π / 6 = π - π / 6 by ring]
  exact trigRow_pi_sub dlmf_table_4_17_1_pi_div_six

/-- **Table 4.17.1**, `θ = 11π/12`. -/
theorem dlmf_table_4_17_1_eleven_pi_div_twelve :
    TrigRow (11 * π / 12) (1 / 4 * √2 * (√3 - 1)) (-(1 / 4 * √2 * (√3 + 1))) (-(2 - √3))
      (√2 * (√3 + 1)) (-(√2 * (√3 - 1))) (-(2 + √3)) := by
  rw [show 11 * π / 12 = π - π / 12 by ring]
  exact trigRow_pi_sub dlmf_table_4_17_1_pi_div_twelve

/-! ### Limits 4.17.1–4.17.3 -/

/-- **DLMF 4.17.1**: `sin z / z → 1` as `z → 0`. -/
theorem dlmf_4_17_1 : Tendsto (fun z : ℂ => sin z / z) (𝓝[≠] 0) (𝓝 1) := by
  have h := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_sin (0 : ℂ))
  rw [cos_zero] at h
  exact h.congr fun z => by rw [slope_def_field]; simp

/-- **DLMF 4.17.2**: `tan z / z → 1` as `z → 0`. -/
theorem dlmf_4_17_2 : Tendsto (fun z : ℂ => tan z / z) (𝓝[≠] 0) (𝓝 1) := by
  have h := hasDerivAt_iff_tendsto_slope.mp
    (Complex.hasDerivAt_tan (x := 0) (by simp))
  rw [cos_zero, one_pow, div_one] at h
  exact h.congr fun z => by rw [slope_def_field]; simp

/-- **DLMF 4.17.3**: `(1 − cos z)/z² → 1/2` as `z → 0`. -/
theorem dlmf_4_17_3 : Tendsto (fun z : ℂ => (1 - cos z) / z ^ 2) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  have hhalf : Tendsto (fun z : ℂ => z / 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun z hz => ?_⟩
    · have := ((continuous_id.div_const (2 : ℂ)).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
      simpa using this
    · simpa using hz
  have h := ((dlmf_4_17_1.comp hhalf).pow 2).const_mul (1 / 2 : ℂ)
  rw [one_pow, mul_one] at h
  refine h.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
  have hz0 : z ≠ 0 := hz
  have hc : cos z = 1 - 2 * sin (z / 2) ^ 2 := by
    have h2 := cos_two_mul (z / 2)
    rw [show 2 * (z / 2) = z by ring] at h2
    rw [h2]
    linear_combination 2 * sin_sq_add_cos_sq (z / 2)
  simp only [Function.comp]
  rw [hc]
  field_simp
  ring

end Azurite.DLMF
