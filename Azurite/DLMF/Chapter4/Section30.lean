/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section16
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# DLMF §4.30 Elementary Properties (hyperbolic functions)

Table 4.30.1 (interrelations): "All square roots have their principal values when the functions
are real, nonnegative, and finite". For real `θ` that is `θ > 0`, where all six functions are
positive and finite (at `θ = 0`, `csch` and `coth` are infinite). One theorem per column
`f(θ) = a`: `dlmf_table_4_30_1_sinh`, …, `dlmf_table_4_30_1_coth`.

Real `csch θ`, `sech θ`, `coth θ` are written `1 / sinh θ`, `1 / cosh θ`, `1 / tanh θ`
(4.28.5–4.28.7).
-/

open Set
open scoped Real

namespace Azurite.DLMF

/-- For `θ > 0`: `sinh θ > 0`, `cosh θ > 0`, `cosh² θ − sinh² θ = 1`, `tanh θ = sinh θ/cosh θ`. -/
theorem positive_hyperbolic_facts {θ : ℝ} (hθ : 0 < θ) :
    0 < Real.sinh θ ∧ 0 < Real.cosh θ ∧ Real.cosh θ ^ 2 - Real.sinh θ ^ 2 = 1 ∧
      Real.tanh θ = Real.sinh θ / Real.cosh θ :=
  ⟨Real.sinh_pos_iff.mpr hθ, Real.cosh_pos θ, by rw [Real.cosh_sq]; ring,
    Real.tanh_eq_sinh_div_cosh θ⟩

/-- **Table 4.30.1**, column `sinh θ = a` (`θ > 0`, principal square roots). -/
theorem dlmf_table_4_30_1_sinh {θ a : ℝ} (hθ : 0 < θ) (ha : Real.sinh θ = a) :
    Real.sinh θ = a ∧ Real.cosh θ = √(1 + a ^ 2) ∧ Real.tanh θ = a * (√(1 + a ^ 2))⁻¹ ∧
      1 / Real.sinh θ = a⁻¹ ∧ 1 / Real.cosh θ = (√(1 + a ^ 2))⁻¹ ∧
      1 / Real.tanh θ = a⁻¹ * √(a ^ 2 + 1) := by
  subst ha
  obtain ⟨hs, hc, hcs, ht⟩ := positive_hyperbolic_facts hθ
  have h1 : √(1 + Real.sinh θ ^ 2) = Real.cosh θ := sqrt_eq_of_eq_sq hc.le (by linarith)
  have h2 : √(Real.sinh θ ^ 2 + 1) = Real.cosh θ := sqrt_eq_of_eq_sq hc.le (by linarith)
  rw [h1, h2, ht]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> field_simp

/-- **Table 4.30.1**, column `cosh θ = a`. -/
theorem dlmf_table_4_30_1_cosh {θ a : ℝ} (hθ : 0 < θ) (ha : Real.cosh θ = a) :
    Real.sinh θ = √(a ^ 2 - 1) ∧ Real.cosh θ = a ∧ Real.tanh θ = a⁻¹ * √(a ^ 2 - 1) ∧
      1 / Real.sinh θ = (√(a ^ 2 - 1))⁻¹ ∧ 1 / Real.cosh θ = a⁻¹ ∧
      1 / Real.tanh θ = a * (√(a ^ 2 - 1))⁻¹ := by
  subst ha
  obtain ⟨hs, hc, hcs, ht⟩ := positive_hyperbolic_facts hθ
  have h1 : √(Real.cosh θ ^ 2 - 1) = Real.sinh θ := sqrt_eq_of_eq_sq hs.le (by linarith)
  rw [h1, ht]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> field_simp

/-- **Table 4.30.1**, column `tanh θ = a`. -/
theorem dlmf_table_4_30_1_tanh {θ a : ℝ} (hθ : 0 < θ) (ha : Real.tanh θ = a) :
    Real.sinh θ = a * (√(1 - a ^ 2))⁻¹ ∧ Real.cosh θ = (√(1 - a ^ 2))⁻¹ ∧ Real.tanh θ = a ∧
      1 / Real.sinh θ = a⁻¹ * √(1 - a ^ 2) ∧ 1 / Real.cosh θ = √(1 - a ^ 2) ∧
      1 / Real.tanh θ = a⁻¹ := by
  subst ha
  obtain ⟨hs, hc, hcs, ht⟩ := positive_hyperbolic_facts hθ
  rw [ht]
  have h1 : √(1 - (Real.sinh θ / Real.cosh θ) ^ 2) = 1 / Real.cosh θ :=
    sqrt_eq_of_eq_sq (by positivity) (by field_simp; linarith)
  rw [h1]
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_⟩ <;> field_simp

/-- **Table 4.30.1**, column `csch θ = a`. -/
theorem dlmf_table_4_30_1_csch {θ a : ℝ} (hθ : 0 < θ) (ha : 1 / Real.sinh θ = a) :
    Real.sinh θ = a⁻¹ ∧ Real.cosh θ = a⁻¹ * √(1 + a ^ 2) ∧ Real.tanh θ = (√(1 + a ^ 2))⁻¹ ∧
      1 / Real.sinh θ = a ∧ 1 / Real.cosh θ = a * (√(1 + a ^ 2))⁻¹ ∧
      1 / Real.tanh θ = √(1 + a ^ 2) := by
  subst ha
  obtain ⟨hs, hc, hcs, ht⟩ := positive_hyperbolic_facts hθ
  rw [ht]
  have h1 : √(1 + (1 / Real.sinh θ) ^ 2) = Real.cosh θ / Real.sinh θ :=
    sqrt_eq_of_eq_sq (by positivity) (by field_simp; linarith)
  rw [h1]
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_⟩ <;> field_simp

/-- **Table 4.30.1**, column `sech θ = a`. -/
theorem dlmf_table_4_30_1_sech {θ a : ℝ} (hθ : 0 < θ) (ha : 1 / Real.cosh θ = a) :
    Real.sinh θ = a⁻¹ * √(1 - a ^ 2) ∧ Real.cosh θ = a⁻¹ ∧ Real.tanh θ = √(1 - a ^ 2) ∧
      1 / Real.sinh θ = a * (√(1 - a ^ 2))⁻¹ ∧ 1 / Real.cosh θ = a ∧
      1 / Real.tanh θ = (√(1 - a ^ 2))⁻¹ := by
  subst ha
  obtain ⟨hs, hc, hcs, ht⟩ := positive_hyperbolic_facts hθ
  rw [ht]
  have h1 : √(1 - (1 / Real.cosh θ) ^ 2) = Real.sinh θ / Real.cosh θ :=
    sqrt_eq_of_eq_sq (by positivity) (by field_simp; linarith)
  rw [h1]
  refine ⟨?_, ?_, rfl, ?_, rfl, ?_⟩ <;> field_simp

/-- **Table 4.30.1**, column `coth θ = a`. -/
theorem dlmf_table_4_30_1_coth {θ a : ℝ} (hθ : 0 < θ) (ha : 1 / Real.tanh θ = a) :
    Real.sinh θ = (√(a ^ 2 - 1))⁻¹ ∧ Real.cosh θ = a * (√(a ^ 2 - 1))⁻¹ ∧
      Real.tanh θ = a⁻¹ ∧ 1 / Real.sinh θ = √(a ^ 2 - 1) ∧
      1 / Real.cosh θ = a⁻¹ * √(a ^ 2 - 1) ∧ 1 / Real.tanh θ = a := by
  subst ha
  obtain ⟨hs, hc, hcs, ht⟩ := positive_hyperbolic_facts hθ
  rw [ht]
  have h1 : √((1 / (Real.sinh θ / Real.cosh θ)) ^ 2 - 1) = 1 / Real.sinh θ :=
    sqrt_eq_of_eq_sq (by positivity) (by field_simp; linarith)
  rw [h1]
  refine ⟨?_, ?_, ?_, rfl, ?_, rfl⟩ <;> field_simp

end Azurite.DLMF
