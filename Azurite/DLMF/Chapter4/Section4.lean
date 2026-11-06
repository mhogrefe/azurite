/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section12
import Azurite.DLMF.Chapter4.Section2Pow
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# DLMF §4.4: Special values and limits

Formalizations of <https://dlmf.nist.gov/4.4>. Powers `e^w` are principal values
(`(Real.exp 1 : ℂ) ^ w`, equal to `exp w` by 4.2.32), `ln` is `Complex.log` (with the closed
definition 4.2.7 on the cut).

* §4.4(i): 4.4.1–4.4.3 (`dlmf_4_4_1`, `dlmf_4_4_2`, `dlmf_4_4_3`).
* §4.4(ii): 4.4.4–4.4.12 (`dlmf_4_4_4` … `dlmf_4_4_12`).
* §4.4(iii): 4.4.13–4.4.15 (`dlmf_4_4_13`, `dlmf_4_4_14`, `dlmf_4_4_15`, `a ∈ ℂ`); 4.4.16 in the
  sector `|ph z| ≤ ½π − δ`, `δ ∈ (0, ½π]` (`dlmf_4_4_16`, with the filter `sectorAtInf δ` of
  `z → ∞` in the sector); 4.4.17, 4.4.18; 4.4.19 (`dlmf_4_4_19`: the limit is `γ`, with its first
  five decimals; the 20 decimals are deferred, as for 3.12.4).
-/

open Complex Set Filter Topology
open scoped Real

namespace Azurite.DLMF

/-! ### §4.4(i) Logarithms -/

/-- **DLMF 4.4.1**: `ln 1 = 0`. -/
theorem dlmf_4_4_1 : log 1 = 0 := log_one

/-- **DLMF 4.4.2**: `ln(−1 ± i0) = ±πi` (limits from the upper and lower half-planes). -/
theorem dlmf_4_4_2 :
    Tendsto log (𝓝[{z | 0 < z.im}] (-1)) (𝓝 (π * I)) ∧
      Tendsto log (𝓝[{z | z.im < 0}] (-1)) (𝓝 (-(π * I))) := by
  obtain ⟨h1, h2⟩ := dlmf_4_2_7 (x := -1) (by norm_num)
  simp only [abs_neg, abs_one, Real.log_one, ofReal_zero, zero_add, zero_sub, ofReal_neg,
    ofReal_one] at h1 h2
  exact ⟨h1, h2⟩

/-- **DLMF 4.4.3**: `ln(±i) = ±½πi`. -/
theorem dlmf_4_4_3 : log I = 1 / 2 * π * I ∧ log (-I) = -(1 / 2 * π * I) := by
  rw [log_I, log_neg_I]
  constructor <;> ring

/-! ### §4.4(ii) Powers -/

/-- `e^w = exp w` (4.2.32). -/
theorem epow (w : ℂ) : (Real.exp 1 : ℂ) ^ w = exp w := dlmf_4_2_32 w

/-- **DLMF 4.4.4**: `e⁰ = 1`. -/
theorem dlmf_4_4_4 : (Real.exp 1 : ℂ) ^ (0 : ℂ) = 1 := cpow_zero _

/-- **DLMF 4.4.5**: `e^{±πi} = −1`. -/
theorem dlmf_4_4_5 :
    (Real.exp 1 : ℂ) ^ (π * I) = -1 ∧ (Real.exp 1 : ℂ) ^ (-(π * I)) = -1 := by
  rw [epow, epow, exp_pi_mul_I, exp_neg, exp_pi_mul_I]
  norm_num

/-- `exp(θi) = cos θ + i sin θ` for real `θ`. -/
theorem exp_real_mul_I (θ : ℝ) : exp (θ * I) = Real.cos θ + Real.sin θ * I := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]

/-- **DLMF 4.4.6**: `e^{±πi/2} = ±i`. -/
theorem dlmf_4_4_6 :
    (Real.exp 1 : ℂ) ^ (π * I / 2) = I ∧ (Real.exp 1 : ℂ) ^ (-(π * I / 2)) = -I := by
  rw [epow, epow, show π * I / 2 = ((π / 2 : ℝ) : ℂ) * I by push_cast; ring,
    show -(((π / 2 : ℝ) : ℂ) * I) = ((-(π / 2) : ℝ) : ℂ) * I by push_cast; ring,
    exp_real_mul_I, exp_real_mul_I, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  constructor <;> simp

/-- **DLMF 4.4.7**: `e^{2πki} = 1`, `k ∈ ℤ`. -/
theorem dlmf_4_4_7 (k : ℤ) : (Real.exp 1 : ℂ) ^ (2 * π * k * I) = 1 := by
  rw [epow, show 2 * π * (k : ℂ) * I = k * (2 * π * I) by ring, exp_int_mul_two_pi_mul_I]

/-- `e^{±θi} = cos θ ± i sin θ` for real `θ`. -/
theorem epow_pm (θ : ℝ) :
    (Real.exp 1 : ℂ) ^ (θ * I) = Real.cos θ + I * Real.sin θ ∧
      (Real.exp 1 : ℂ) ^ (-(θ * I)) = Real.cos θ - I * Real.sin θ := by
  rw [epow, epow, show -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, exp_real_mul_I,
    exp_real_mul_I, Real.cos_neg, Real.sin_neg]
  constructor <;> push_cast <;> ring

/-- **DLMF 4.4.8**: `e^{±πi/3} = ½ ± i √3/2`. -/
theorem dlmf_4_4_8 :
    (Real.exp 1 : ℂ) ^ ((π / 3 : ℝ) * I) = 1 / 2 + I * (Real.sqrt 3 / 2) ∧
      (Real.exp 1 : ℂ) ^ (-((π / 3 : ℝ) * I)) = 1 / 2 - I * (Real.sqrt 3 / 2) := by
  obtain ⟨h1, h2⟩ := epow_pm (π / 3)
  rw [h1, h2, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  exact ⟨rfl, rfl⟩

/-- **DLMF 4.4.9**: `e^{±2πi/3} = −½ ± i √3/2`. -/
theorem dlmf_4_4_9 :
    (Real.exp 1 : ℂ) ^ ((2 * π / 3 : ℝ) * I) = -1 / 2 + I * (Real.sqrt 3 / 2) ∧
      (Real.exp 1 : ℂ) ^ (-((2 * π / 3 : ℝ) * I)) = -1 / 2 - I * (Real.sqrt 3 / 2) := by
  obtain ⟨h1, h2⟩ := epow_pm (2 * π / 3)
  have hc : Real.cos (2 * π / 3) = -1 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; ring
  have hs : Real.sin (2 * π / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [h1, h2, hc, hs]
  push_cast
  exact ⟨rfl, rfl⟩

/-- **DLMF 4.4.10**: `e^{±πi/4} = 1/√2 ± i/√2`. -/
theorem dlmf_4_4_10 :
    (Real.exp 1 : ℂ) ^ ((π / 4 : ℝ) * I) = 1 / Real.sqrt 2 + I * (1 / Real.sqrt 2) ∧
      (Real.exp 1 : ℂ) ^ (-((π / 4 : ℝ) * I)) = 1 / Real.sqrt 2 - I * (1 / Real.sqrt 2) := by
  obtain ⟨h1, h2⟩ := epow_pm (π / 4)
  have hc : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
    field_simp; rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h1, h2, Real.cos_pi_div_four, Real.sin_pi_div_four, hc]
  push_cast
  exact ⟨rfl, rfl⟩

/-- **DLMF 4.4.11**: `e^{±3πi/4} = −1/√2 ± i/√2`. -/
theorem dlmf_4_4_11 :
    (Real.exp 1 : ℂ) ^ ((3 * π / 4 : ℝ) * I) = -(1 / Real.sqrt 2) + I * (1 / Real.sqrt 2) ∧
      (Real.exp 1 : ℂ) ^ (-((3 * π / 4 : ℝ) * I)) =
        -(1 / Real.sqrt 2) - I * (1 / Real.sqrt 2) := by
  obtain ⟨h1, h2⟩ := epow_pm (3 * π / 4)
  have hq : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
    field_simp; rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hc : Real.cos (3 * π / 4) = -(1 / Real.sqrt 2) := by
    rw [show 3 * π / 4 = π - π / 4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four, hq]
  have hs : Real.sin (3 * π / 4) = 1 / Real.sqrt 2 := by
    rw [show 3 * π / 4 = π - π / 4 by ring, Real.sin_pi_sub, Real.sin_pi_div_four, hq]
  rw [h1, h2, hc, hs]
  push_cast
  exact ⟨rfl, rfl⟩

/-- **DLMF 4.4.12**: `i^{±i} = e^{∓π/2}`. -/
theorem dlmf_4_4_12 :
    I ^ I = Real.exp (-(π / 2)) ∧ I ^ (-I) = Real.exp (π / 2) := by
  rw [cpow_def_of_ne_zero I_ne_zero, cpow_def_of_ne_zero I_ne_zero, log_I]
  constructor
  · rw [ofReal_exp]; congr 1; push_cast; ring_nf; rw [I_sq]; ring
  · rw [ofReal_exp]; congr 1; push_cast; ring_nf; rw [I_sq]; ring

/-! ### §4.4(iii) Limits -/

/-- **DLMF 4.4.13**: `lim_{x→∞} x^{−a} ln x = 0`, `Re a > 0`. -/
theorem dlmf_4_4_13 {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ (-a) * Real.log x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
  refine (h.abs.congr' ?_).trans (by rw [abs_zero])
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, neg_re, norm_real, Real.norm_eq_abs,
    Real.rpow_neg hx.le, abs_div, abs_of_pos (Real.rpow_pos_of_pos hx _)]
  ring

/-- **DLMF 4.4.14**: `lim_{x→0} x^a ln x = 0`, `Re a > 0` (`x → 0+`). -/
theorem dlmf_4_4_14 {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ a * Real.log x) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_log_mul_rpow_nhdsGT_zero ha
  refine (h.abs.congr' ?_).trans (by rw [abs_zero])
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hx _)]
  ring

/-- **DLMF 4.4.15**: `lim_{x→∞} x^a e^{−x} = 0` (`a ∈ ℂ`). -/
theorem dlmf_4_4_15 (a : ℂ) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ a * exp (-x)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a.re 1 one_pos
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, norm_exp]
  simp

/-- `z → ∞` in the sector `|ph z| ≤ ½π − δ`. -/
noncomputable def sectorAtInf (δ : ℝ) : Filter ℂ :=
  Bornology.cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ π / 2 - δ}

/-- In the sector `|ph z| ≤ ½π − δ`, `Re z ≥ |z| sin δ`. -/
theorem re_ge_of_sector {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : |arg z| ≤ π / 2 - δ) :
    ‖z‖ * Real.sin δ ≤ z.re := by
  have h1 : Real.cos (π / 2 - δ) ≤ Real.cos (arg z) := by
    rw [← Real.cos_abs (arg z)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hz
  rw [Real.cos_pi_div_two_sub] at h1
  calc ‖z‖ * Real.sin δ ≤ ‖z‖ * Real.cos (arg z) := mul_le_mul_of_nonneg_left h1 (norm_nonneg z)
    _ = z.re := norm_mul_cos_arg z

/-- **DLMF 4.4.16**: `lim z^a e^{−z} = 0` as `z → ∞` in `|ph z| ≤ ½π − δ`, `δ ∈ (0, ½π]`,
`a ∈ ℂ`. -/
theorem dlmf_4_4_16 (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π / 2) :
    Tendsto (fun z : ℂ => z ^ a * exp (-z)) (sectorAtInf δ) (𝓝 0) := by
  have hs : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  set C := Real.exp (|a.im| * π)
  have hle : sectorAtInf δ ≤ Bornology.cobounded ℂ := inf_le_left
  have hg : Tendsto (fun z : ℂ => C * (‖z‖ ^ a.re * Real.exp (-Real.sin δ * ‖z‖)))
      (sectorAtInf δ) (𝓝 0) := by
    have := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a.re _ hs).comp
      ((tendsto_norm_cobounded_atTop (E := ℂ)).mono_left hle)).const_mul C
    simpa using this
  refine squeeze_zero_norm' ?_ hg
  have hne : ∀ᶠ z in sectorAtInf δ, z ≠ 0 :=
    (((tendsto_norm_cobounded_atTop (E := ℂ)).eventually_gt_atTop 0).filter_mono
      hle).mono fun z hz => norm_pos_iff.mp hz
  have hsec : ∀ᶠ z in sectorAtInf δ, |arg z| ≤ π / 2 - δ :=
    inf_le_right (a := Bornology.cobounded ℂ) (mem_principal_self _)
  filter_upwards [hne, hsec] with z hz hsec
  rw [norm_mul, dlmf_4_2_29 hz, norm_exp, neg_re]
  have h1 : Real.exp (-(a.im * arg z)) ≤ C := by
    apply Real.exp_le_exp.mpr
    have := abs_arg_le_pi z
    calc -(a.im * arg z) ≤ |a.im * arg z| := neg_le_abs _
      _ = |a.im| * |arg z| := abs_mul _ _
      _ ≤ |a.im| * π := mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have h2 : Real.exp (-z.re) ≤ Real.exp (-Real.sin δ * ‖z‖) := by
    apply Real.exp_le_exp.mpr
    have := re_ge_of_sector hδ hsec
    linarith
  have hp : 0 ≤ ‖z‖ ^ a.re := Real.rpow_nonneg (norm_nonneg z) _
  calc ‖z‖ ^ a.re * Real.exp (-(a.im * arg z)) * Real.exp (-z.re)
      ≤ ‖z‖ ^ a.re * C * Real.exp (-Real.sin δ * ‖z‖) := by
        gcongr
    _ = C * (‖z‖ ^ a.re * Real.exp (-Real.sin δ * ‖z‖)) := by ring

/-- **DLMF 4.4.17**: `lim (1 + z/n)ⁿ = e^z`. -/
theorem dlmf_4_4_17 (z : ℂ) :
    Tendsto (fun n : ℕ => (1 + z / n) ^ n) atTop (𝓝 ((Real.exp 1 : ℂ) ^ z)) := by
  rw [epow]
  exact Complex.tendsto_one_add_div_pow_exp z

/-- **DLMF 4.4.18**: `lim (1 + 1/n)ⁿ = e`. -/
theorem dlmf_4_4_18 :
    Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ n) atTop (𝓝 (Real.exp 1)) :=
  Real.tendsto_one_add_div_pow_exp 1

/-- **DLMF 4.4.19**: `lim ((∑_{k=1}^n 1/k) − ln n) = γ = 0.57721 …` (5.2.3). The first five
decimals are certified; the 20 decimals `0.57721 56649 01532 86060 …` are deferred. -/
theorem dlmf_4_4_19 :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k) - Real.log n) atTop
        (𝓝 Real.eulerMascheroniConstant) ∧
      0.57721 < Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant < 0.57722 := by
  refine ⟨(dlmf_3_12_4_def).congr fun n => ?_, dlmf_3_12_4_partial⟩
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp [one_div]

end Azurite.DLMF
