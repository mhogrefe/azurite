/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section7
import Azurite.DLMF.Chapter5.Section4Gauss

/-!
# DLMF §5.19(i): Summation of rational functions

Formalization of <https://dlmf.nist.gov/5.19>, subsection (i): the worked example.

* 5.19.1: `S = ∑_{k≥0} aₖ`, `aₖ = k / ((3k + 2)(2k + 1)(k + 1))` (`summandA`, definition).
* 5.19.2: the partial-fraction form `aₖ = (1/(k + 1) − 1/(k + ½)) − 2(1/(k + 1) − 1/(k + ⅔))`
  (`dlmf_5_19_2`).
* 5.19.3: `S = ψ(½) − 2ψ(⅔) − γ = 3 ln 3 − 2 ln 2 − ⅓π√3` (`dlmf_5_19_3`; real form
  `hasSum_summandA`), from 5.7.6, 5.4.13 and 5.4.19 (`digamma_two_thirds`).
-/

open Complex Finset
open scoped Real

namespace Azurite.DLMF

/-- DLMF 5.19.1: `aₖ = k / ((3k + 2)(2k + 1)(k + 1))`. -/
noncomputable def summandA (k : ℕ) : ℝ := k / ((3 * k + 2) * (2 * k + 1) * (k + 1))

/-- DLMF 5.19.2: `aₖ = (1/(k + 1) − 1/(k + ½)) − 2(1/(k + 1) − 1/(k + ⅔))`. -/
theorem dlmf_5_19_2 (k : ℕ) :
    summandA k = (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 / 2)) -
      2 * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2 / 3)) := by
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (k : ℝ) + 1 / 2 ≠ 0 := by positivity
  have h3 : (k : ℝ) + 2 / 3 ≠ 0 := by positivity
  have h4 : (3 * (k : ℝ) + 2) ≠ 0 := by positivity
  have h5 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  rw [summandA]
  field_simp
  ring

theorem real_cos_two_pi_div_three' : Real.cos (π * 2 / 3) = -(1 / 2) := by
  rw [show π * 2 / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]

theorem real_sin_two_pi_div_three' : Real.sin (π * 2 / 3) = √3 / 2 := by
  rw [show π * 2 / 3 = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]

/-- `ψ(⅔) = −γ − (3/2) ln 3 + π/(2√3)` (5.4.19 with `p = 2`, `q = 3`). -/
theorem digamma_two_thirds :
    digamma (2 / 3) = ((-Real.eulerMascheroniConstant - 3 / 2 * Real.log 3 +
      π * √3 / 6 : ℝ) : ℂ) := by
  have h := dlmf_5_4_19 (p := 2) (q := 3) (by norm_num) (by norm_num)
  rw [show ((2 : ℕ) : ℂ) / ((3 : ℕ) : ℂ) = 2 / 3 by norm_num] at h
  rw [h]
  congr 1
  have hIco : Finset.Ico 1 3 = {1, 2} := by decide
  rw [hIco, Finset.sum_pair (by norm_num)]
  push_cast
  have c1 : Real.cos (2 * π * 1 * 2 / 3) = -(1 / 2) := by
    rw [show 2 * π * 1 * 2 / 3 = π / 3 + π by ring, Real.cos_add_pi, Real.cos_pi_div_three]
  have c2 : Real.cos (2 * π * 2 * 2 / 3) = -(1 / 2) := by
    rw [show 2 * π * 2 * 2 / 3 = π * 2 / 3 + 2 * π by ring, Real.cos_add_two_pi,
      real_cos_two_pi_div_three']
  have c3 : Real.cos (2 * π * 1 / 3) = -(1 / 2) := by
    rw [show 2 * π * 1 / 3 = π * 2 / 3 by ring, real_cos_two_pi_div_three']
  have c4 : Real.cos (2 * π * 2 / 3) = -(1 / 2) := by
    rw [show 2 * π * 2 / 3 = π / 3 + π by ring, Real.cos_add_pi, Real.cos_pi_div_three]
  have hcot : Real.cot (π * 2 / 3) = -(1 / √3) := by
    rw [Real.cot_eq_cos_div_sin, real_cos_two_pi_div_three', real_sin_two_pi_div_three']
    have : (√3 : ℝ) ≠ 0 := by positivity
    field_simp
  rw [c1, c2, c3, c4, hcot]
  have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : (√3 : ℝ) ≠ 0 := by positivity
  rw [show (2 : ℝ) - 2 * -(1 / 2) = 3 by norm_num]
  field_simp
  linear_combination (-4 * π) * h3

/-- DLMF 5.19.3: `S = ∑ aₖ = ψ(½) − 2ψ(⅔) − γ = 3 ln 3 − 2 ln 2 − ⅓π√3`. -/
theorem dlmf_5_19_3 :
    HasSum (fun k => (summandA k : ℂ))
        (digamma (1 / 2) - 2 * digamma (2 / 3) - Real.eulerMascheroniConstant) ∧
      digamma (1 / 2) - 2 * digamma (2 / 3) - Real.eulerMascheroniConstant =
        ((3 * Real.log 3 - 2 * Real.log 2 - π * √3 / 3 : ℝ) : ℂ) := by
  have hh : (1 / 2 : ℂ) ∉ gammaPoles := not_mem_gammaPoles_of_re_pos (by norm_num)
  have ht : (2 / 3 : ℂ) ∉ gammaPoles := not_mem_gammaPoles_of_re_pos (by norm_num)
  refine ⟨?_, ?_⟩
  · have H := (dlmf_5_7_6 hh).sub ((dlmf_5_7_6 ht).mul_left 2)
    convert H using 1
    · funext k
      rw [dlmf_5_19_2]
      push_cast
      ring
    · ring
  · rw [dlmf_5_4_13, digamma_two_thirds]
    push_cast
    ring

/-- DLMF 5.19.3, real form: `∑ aₖ = 3 ln 3 − 2 ln 2 − ⅓π√3`. -/
theorem hasSum_summandA :
    HasSum summandA (3 * Real.log 3 - 2 * Real.log 2 - π * √3 / 3) := by
  obtain ⟨h1, h2⟩ := dlmf_5_19_3
  rw [h2] at h1
  exact Complex.hasSum_ofReal.1 h1

end Azurite.DLMF
