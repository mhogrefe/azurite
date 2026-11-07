/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# DLMF §4.14 Definitions and Periodicity

* 4.14.1–4.14.3: `dlmf_4_14_1`, `dlmf_4_14_2`, `dlmf_4_14_3`.
* 4.14.4–4.14.7: `dlmf_4_14_4`, `cscC`/`dlmf_4_14_5`, `secC`/`dlmf_4_14_6`, `dlmf_4_14_7`
  (Mathlib has `Complex.tan`, `Complex.cot`; `csc`, `sec` are defined here).
* `sin`, `cos` entire (`dlmf_4_14_entire`); zeros `kπ` and `(k + ½)π` (`dlmf_4_14_sin_zeros`,
  `dlmf_4_14_cos_zeros`); `tan`, `csc`, `sec`, `cot` meromorphic (`dlmf_4_14_meromorphic`), with
  zeros and poles from 4.14.4–4.14.7 (`dlmf_4_14_tan_zeros`, …, `dlmf_4_14_tan_poles`, …; a pole
  is `|f(w)| → ∞` as `w → z₀`).
* 4.14.8–4.14.10: `dlmf_4_14_8`, `dlmf_4_14_9`, `dlmf_4_14_10`.
-/

open Set Filter Topology Complex
open scoped Real

namespace Azurite.DLMF

/-- **DLMF 4.14.1**: `sin z = (e^{iz} − e^{−iz})/(2i)`. -/
theorem dlmf_4_14_1 (z : ℂ) : sin z = (exp (I * z) - exp (-I * z)) / (2 * I) := by
  have h1 : exp (I * z) = cos z + sin z * I := by rw [mul_comm, exp_mul_I]
  have h2 : exp (-I * z) = cos z - sin z * I := by
    rw [show -I * z = (-z) * I by ring, exp_mul_I, cos_neg, sin_neg]; ring
  rw [h1, h2]
  field_simp
  ring

/-- **DLMF 4.14.2**: `cos z = (e^{iz} + e^{−iz})/2`. -/
theorem dlmf_4_14_2 (z : ℂ) : cos z = (exp (I * z) + exp (-I * z)) / 2 := by
  have h1 : exp (I * z) = cos z + sin z * I := by rw [mul_comm, exp_mul_I]
  have h2 : exp (-I * z) = cos z - sin z * I := by
    rw [show -I * z = (-z) * I by ring, exp_mul_I, cos_neg, sin_neg]; ring
  rw [h1, h2]
  ring

/-- **DLMF 4.14.3**: `cos z ± i sin z = e^{±iz}`. -/
theorem dlmf_4_14_3 (z : ℂ) :
    cos z + I * sin z = exp (I * z) ∧ cos z - I * sin z = exp (-I * z) := by
  constructor
  · rw [mul_comm I z, exp_mul_I]; ring
  · rw [show -I * z = (-z) * I by ring, exp_mul_I, cos_neg, sin_neg]; ring

/-- **DLMF 4.14.4**: `tan z = sin z/cos z`. -/
theorem dlmf_4_14_4 (z : ℂ) : tan z = sin z / cos z := tan_eq_sin_div_cos z

/-- **DLMF 4.14.5**: `csc z = 1/sin z`. -/
noncomputable def cscC (z : ℂ) : ℂ := 1 / sin z

/-- **DLMF 4.14.6**: `sec z = 1/cos z`. -/
noncomputable def secC (z : ℂ) : ℂ := 1 / cos z

theorem dlmf_4_14_5 (z : ℂ) : cscC z = 1 / sin z := rfl

theorem dlmf_4_14_6 (z : ℂ) : secC z = 1 / cos z := rfl

/-- **DLMF 4.14.7**: `cot z = cos z/sin z = 1/tan z`. -/
theorem dlmf_4_14_7 (z : ℂ) : cot z = cos z / sin z ∧ cot z = 1 / tan z := by
  refine ⟨cot_eq_cos_div_sin z, ?_⟩
  rw [cot_eq_cos_div_sin, tan_eq_sin_div_cos, one_div_div]

/-! ### Entire functions, zeros, meromorphy -/

/-- **DLMF §4.14**: `sin` and `cos` are entire. -/
theorem dlmf_4_14_entire : Differentiable ℂ sin ∧ Differentiable ℂ cos :=
  ⟨differentiable_sin, differentiable_cos⟩

/-- **DLMF §4.14**: the zeros of `sin` are `kπ`. -/
theorem dlmf_4_14_sin_zeros (z : ℂ) : sin z = 0 ↔ ∃ k : ℤ, z = k * π := sin_eq_zero_iff

/-- **DLMF §4.14**: the zeros of `cos` are `(k + ½)π`. -/
theorem dlmf_4_14_cos_zeros (z : ℂ) : cos z = 0 ↔ ∃ k : ℤ, z = (k + 1 / 2) * π := by
  rw [cos_eq_zero_iff]
  refine exists_congr fun k => ?_
  constructor <;> intro h <;> rw [h] <;> ring

theorem analyticAt_sin' (z : ℂ) : AnalyticAt ℂ sin z :=
  differentiable_sin.analyticAt z

theorem analyticAt_cos' (z : ℂ) : AnalyticAt ℂ cos z :=
  differentiable_cos.analyticAt z

/-- **DLMF §4.14**: `tan`, `csc`, `sec`, `cot` are meromorphic on `ℂ`. -/
theorem dlmf_4_14_meromorphic :
    MeromorphicOn tan univ ∧ MeromorphicOn cscC univ ∧ MeromorphicOn secC univ ∧
      MeromorphicOn cot univ := by
  have hs := fun z => (analyticAt_sin' z).meromorphicAt
  have hc := fun z => (analyticAt_cos' z).meromorphicAt
  have h1 := fun z => (analyticAt_const (𝕜 := ℂ) (v := (1 : ℂ)) (x := z)).meromorphicAt
  refine ⟨fun z _ => ?_, fun z _ => ?_, fun z _ => ?_, fun z _ => ?_⟩
  · have : tan = sin / cos := funext tan_eq_sin_div_cos
    rw [this]; exact (hs z).div (hc z)
  · exact (h1 z).div (hs z)
  · exact (h1 z).div (hc z)
  · have : cot = cos / sin := funext cot_eq_cos_div_sin
    rw [this]; exact (hc z).div (hs z)

theorem sin_ne_zero_of_cos_eq_zero {z : ℂ} (h : cos z = 0) : sin z ≠ 0 := fun hs => by
  have := sin_sq_add_cos_sq z; rw [h, hs] at this; norm_num at this

theorem cos_ne_zero_of_sin_eq_zero {z : ℂ} (h : sin z = 0) : cos z ≠ 0 := fun hc => by
  have := sin_sq_add_cos_sq z; rw [h, hc] at this; norm_num at this

/-- Zeros of `tan` (away from the poles): `tan z = 0 ↔ z = kπ`. -/
theorem dlmf_4_14_tan_zeros {z : ℂ} (hz : cos z ≠ 0) : tan z = 0 ↔ ∃ k : ℤ, z = k * π := by
  rw [tan_eq_sin_div_cos, div_eq_zero_iff, or_iff_left hz, sin_eq_zero_iff]

/-- Zeros of `cot` (away from the poles): `cot z = 0 ↔ z = (k + ½)π`. -/
theorem dlmf_4_14_cot_zeros {z : ℂ} (hz : sin z ≠ 0) :
    cot z = 0 ↔ ∃ k : ℤ, z = (k + 1 / 2) * π := by
  rw [cot_eq_cos_div_sin, div_eq_zero_iff, or_iff_left hz, dlmf_4_14_cos_zeros]

/-- `csc` and `sec` have no zeros (away from their poles). -/
theorem dlmf_4_14_csc_sec_ne_zero {z : ℂ} :
    (sin z ≠ 0 → cscC z ≠ 0) ∧ (cos z ≠ 0 → secC z ≠ 0) :=
  ⟨fun h => one_div_ne_zero h, fun h => one_div_ne_zero h⟩

/-- A quotient `f/g` with `g(z₀) = 0`, `g′(z₀) ≠ 0`, `f(z₀) ≠ 0` has a pole at `z₀`. -/
theorem tendsto_norm_div_of_simple_zero {f g : ℂ → ℂ} {z₀ g' : ℂ} (hf : ContinuousAt f z₀)
    (hf0 : f z₀ ≠ 0) (hg : HasDerivAt g g' z₀) (hg0 : g z₀ = 0) (hg' : g' ≠ 0) :
    Tendsto (fun w => ‖f w / g w‖) (𝓝[≠] z₀) atTop := by
  have hne : ∀ᶠ w in 𝓝[≠] z₀, g w ≠ 0 := hg.eventually_ne (c := 0) hg'
  have hgt : Tendsto g (𝓝[≠] z₀) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hne⟩
    rw [← hg0]; exact hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hinv : Tendsto (fun w => ‖(g w)⁻¹‖) (𝓝[≠] z₀) atTop :=
    tendsto_norm_cobounded_atTop.comp (tendsto_inv₀_nhdsNE_zero.comp hgt)
  have hfn : Tendsto (fun w => ‖f w‖) (𝓝[≠] z₀) (𝓝 ‖f z₀‖) :=
    (hf.tendsto.mono_left nhdsWithin_le_nhds).norm
  have := hfn.pos_mul_atTop (norm_pos_iff.mpr hf0) hinv
  refine this.congr fun w => ?_
  rw [div_eq_mul_inv, norm_mul]

/-- **Poles of `tan`** at the zeros `(k + ½)π` of `cos`. -/
theorem dlmf_4_14_tan_poles {z₀ : ℂ} (hz : cos z₀ = 0) :
    Tendsto (fun w => ‖tan w‖) (𝓝[≠] z₀) atTop := by
  have h := tendsto_norm_div_of_simple_zero (analyticAt_sin' z₀).continuousAt
    (sin_ne_zero_of_cos_eq_zero hz) (hasDerivAt_cos z₀) hz
    (neg_ne_zero.mpr (sin_ne_zero_of_cos_eq_zero hz))
  simpa [tan_eq_sin_div_cos] using h

/-- **Poles of `cot`** at the zeros `kπ` of `sin`. -/
theorem dlmf_4_14_cot_poles {z₀ : ℂ} (hz : sin z₀ = 0) :
    Tendsto (fun w => ‖cot w‖) (𝓝[≠] z₀) atTop := by
  have h := tendsto_norm_div_of_simple_zero (analyticAt_cos' z₀).continuousAt
    (cos_ne_zero_of_sin_eq_zero hz) (hasDerivAt_sin z₀) hz (cos_ne_zero_of_sin_eq_zero hz)
  simpa [cot_eq_cos_div_sin] using h

/-- **Poles of `csc`** at the zeros `kπ` of `sin`. -/
theorem dlmf_4_14_csc_poles {z₀ : ℂ} (hz : sin z₀ = 0) :
    Tendsto (fun w => ‖cscC w‖) (𝓝[≠] z₀) atTop :=
  tendsto_norm_div_of_simple_zero continuousAt_const one_ne_zero (hasDerivAt_sin z₀) hz
    (cos_ne_zero_of_sin_eq_zero hz)

/-- **Poles of `sec`** at the zeros `(k + ½)π` of `cos`. -/
theorem dlmf_4_14_sec_poles {z₀ : ℂ} (hz : cos z₀ = 0) :
    Tendsto (fun w => ‖secC w‖) (𝓝[≠] z₀) atTop :=
  tendsto_norm_div_of_simple_zero continuousAt_const one_ne_zero (hasDerivAt_cos z₀) hz
    (neg_ne_zero.mpr (sin_ne_zero_of_cos_eq_zero hz))

/-! ### Periodicity -/

/-- **DLMF 4.14.8**: `sin(z + 2kπ) = sin z`. -/
theorem dlmf_4_14_8 (z : ℂ) (k : ℤ) : sin (z + 2 * k * π) = sin z := by
  rw [show (2 * k * π : ℂ) = k * (2 * π) by ring, sin_add_int_mul_two_pi]

/-- **DLMF 4.14.9**: `cos(z + 2kπ) = cos z`. -/
theorem dlmf_4_14_9 (z : ℂ) (k : ℤ) : cos (z + 2 * k * π) = cos z := by
  rw [show (2 * k * π : ℂ) = k * (2 * π) by ring, cos_add_int_mul_two_pi]

/-- **DLMF 4.14.10**: `tan(z + kπ) = tan z`. -/
theorem dlmf_4_14_10 (z : ℂ) (k : ℤ) : tan (z + k * π) = tan z :=
  (tan_periodic.int_mul k) z

end Azurite.DLMF
