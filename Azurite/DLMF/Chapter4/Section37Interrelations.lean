/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section30
import Azurite.DLMF.Chapter4.Section37

/-!
# DLMF §4.37(vi) Interrelations (inverse hyperbolic functions)

"Table 4.30.1 can also be used to find interrelations between inverse hyperbolic functions."

* Every principal inverse hyperbolic function inverts its function on `θ > 0`
  (`inv_hyp_positive`), so each column of Table 4.30.1 (`dlmf_table_4_30_1_sinh`, …) gives five
  relations (`dlmf_4_37_vi_sinh`, …, `dlmf_4_37_vi_coth`), for the values of `a` that the
  column takes on `θ > 0`. As in §4.23(vii), the arguments are real.
* DLMF's example `arcsech a = arccoth((1 − a²)^{−1/2})` (`0 < a < 1`) is `dlmf_4_37_vi_example`.
-/

open Set Complex
open scoped Real

namespace Azurite.DLMF

/-- On `θ > 0` each principal inverse hyperbolic function inverts its function. -/
theorem inv_hyp_positive {θ : ℝ} (hθ : 0 < θ) :
    arcsinhD (Real.sinh θ) = θ ∧ arccoshD (Real.cosh θ) = θ ∧ arctanhD (Real.tanh θ) = θ ∧
      arccschD (1 / Real.sinh θ : ℝ) = θ ∧ arcsechD (1 / Real.cosh θ : ℝ) = θ ∧
      arccothD (1 / Real.tanh θ : ℝ) = θ := by
  have hS : arcsinhD (Real.sinh θ) = θ := by rw [arcsinhD_ofReal, Real.arsinh_sinh]
  have hC : arccoshD (Real.cosh θ) = θ := by
    rw [arccoshD_ofReal (Real.one_le_cosh θ), Real.arcosh_cosh hθ.le]
  have hT : arctanhD (Real.tanh θ) = θ := by
    rw [arctanhD_ofReal ⟨Real.neg_one_lt_tanh θ, Real.tanh_lt_one θ⟩, Real.artanh_tanh]
  refine ⟨hS, hC, hT, ?_, ?_, ?_⟩
  · rw [arccschD]; push_cast; rw [one_div_one_div]; exact_mod_cast hS
  · rw [arcsechD]; push_cast; rw [one_div_one_div]; exact_mod_cast hC
  · rw [arccothD]; push_cast; rw [one_div_one_div]; exact_mod_cast hT

/-- **§4.37(vi)** with Table 4.30.1, column `sinh θ = a`, `a > 0`. -/
theorem dlmf_4_37_vi_sinh {a : ℝ} (ha : 0 < a) :
    arccoshD (√(1 + a ^ 2) : ℝ) = arcsinhD a ∧
      arctanhD (a * (√(1 + a ^ 2))⁻¹ : ℝ) = arcsinhD a ∧ arccschD (a⁻¹ : ℝ) = arcsinhD a ∧
      arcsechD ((√(1 + a ^ 2))⁻¹ : ℝ) = arcsinhD a ∧
      arccothD (a⁻¹ * √(a ^ 2 + 1) : ℝ) = arcsinhD a := by
  obtain ⟨θ, hθ, hg⟩ : ∃ θ, 0 < θ ∧ Real.sinh θ = a :=
    ⟨Real.arsinh a, Real.arsinh_pos_iff.mpr ha, Real.sinh_arsinh a⟩
  obtain ⟨-, e2, e3, e4, e5, e6⟩ := dlmf_table_4_30_1_sinh hθ hg
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := inv_hyp_positive hθ
  have hv : arcsinhD a = θ := by rw [← hg]; exact i1
  rw [hv]
  exact ⟨by rw [← e2, i2], by rw [← e3, i3], by rw [← e4, i4], by rw [← e5, i5],
    by rw [← e6, i6]⟩

/-- **§4.37(vi)** with Table 4.30.1, column `cosh θ = a`, `a > 1`. -/
theorem dlmf_4_37_vi_cosh {a : ℝ} (ha : 1 < a) :
    arcsinhD (√(a ^ 2 - 1) : ℝ) = arccoshD a ∧
      arctanhD (a⁻¹ * √(a ^ 2 - 1) : ℝ) = arccoshD a ∧
      arccschD ((√(a ^ 2 - 1))⁻¹ : ℝ) = arccoshD a ∧ arcsechD (a⁻¹ : ℝ) = arccoshD a ∧
      arccothD (a * (√(a ^ 2 - 1))⁻¹ : ℝ) = arccoshD a := by
  obtain ⟨θ, hθ, hg⟩ : ∃ θ, 0 < θ ∧ Real.cosh θ = a :=
    ⟨Real.arcosh a, Real.arcosh_pos ha, Real.cosh_arcosh ha.le⟩
  obtain ⟨e1, -, e3, e4, e5, e6⟩ := dlmf_table_4_30_1_cosh hθ hg
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := inv_hyp_positive hθ
  have hv : arccoshD a = θ := by rw [← hg]; exact i2
  rw [hv]
  exact ⟨by rw [← e1, i1], by rw [← e3, i3], by rw [← e4, i4], by rw [← e5, i5],
    by rw [← e6, i6]⟩

/-- **§4.37(vi)** with Table 4.30.1, column `tanh θ = a`, `0 < a < 1`. -/
theorem dlmf_4_37_vi_tanh {a : ℝ} (ha : a ∈ Ioo 0 1) :
    arcsinhD (a * (√(1 - a ^ 2))⁻¹ : ℝ) = arctanhD a ∧
      arccoshD ((√(1 - a ^ 2))⁻¹ : ℝ) = arctanhD a ∧
      arccschD (a⁻¹ * √(1 - a ^ 2) : ℝ) = arctanhD a ∧
      arcsechD (√(1 - a ^ 2) : ℝ) = arctanhD a ∧ arccothD (a⁻¹ : ℝ) = arctanhD a := by
  obtain ⟨θ, hθ, hg⟩ : ∃ θ, 0 < θ ∧ Real.tanh θ = a :=
    ⟨Real.artanh a, Real.artanh_pos ha, Real.tanh_artanh ⟨by linarith [ha.1], ha.2⟩⟩
  obtain ⟨e1, e2, -, e4, e5, e6⟩ := dlmf_table_4_30_1_tanh hθ hg
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := inv_hyp_positive hθ
  have hv : arctanhD a = θ := by rw [← hg]; exact i3
  rw [hv]
  exact ⟨by rw [← e1, i1], by rw [← e2, i2], by rw [← e4, i4], by rw [← e5, i5],
    by rw [← e6, i6]⟩

/-- **§4.37(vi)** with Table 4.30.1, column `csch θ = a`, `a > 0`. -/
theorem dlmf_4_37_vi_csch {a : ℝ} (ha : 0 < a) :
    arcsinhD (a⁻¹ : ℝ) = arccschD a ∧ arccoshD (a⁻¹ * √(1 + a ^ 2) : ℝ) = arccschD a ∧
      arctanhD ((√(1 + a ^ 2))⁻¹ : ℝ) = arccschD a ∧
      arcsechD (a * (√(1 + a ^ 2))⁻¹ : ℝ) = arccschD a ∧
      arccothD (√(1 + a ^ 2) : ℝ) = arccschD a := by
  obtain ⟨θ, hθ, hg⟩ : ∃ θ, 0 < θ ∧ 1 / Real.sinh θ = a :=
    ⟨Real.arsinh a⁻¹, Real.arsinh_pos_iff.mpr (inv_pos.mpr ha), by
      rw [Real.sinh_arsinh, one_div, inv_inv]⟩
  obtain ⟨e1, e2, e3, -, e5, e6⟩ := dlmf_table_4_30_1_csch hθ hg
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := inv_hyp_positive hθ
  have hv : arccschD a = θ := by rw [← hg]; exact i4
  rw [hv]
  exact ⟨by rw [← e1, i1], by rw [← e2, i2], by rw [← e3, i3], by rw [← e5, i5],
    by rw [← e6, i6]⟩

/-- **§4.37(vi)** with Table 4.30.1, column `sech θ = a`, `0 < a < 1`. -/
theorem dlmf_4_37_vi_sech {a : ℝ} (ha : a ∈ Ioo 0 1) :
    arcsinhD (a⁻¹ * √(1 - a ^ 2) : ℝ) = arcsechD a ∧ arccoshD (a⁻¹ : ℝ) = arcsechD a ∧
      arctanhD (√(1 - a ^ 2) : ℝ) = arcsechD a ∧
      arccschD (a * (√(1 - a ^ 2))⁻¹ : ℝ) = arcsechD a ∧
      arccothD ((√(1 - a ^ 2))⁻¹ : ℝ) = arcsechD a := by
  have h1 : 1 < a⁻¹ := (one_lt_inv₀ ha.1).mpr ha.2
  obtain ⟨θ, hθ, hg⟩ : ∃ θ, 0 < θ ∧ 1 / Real.cosh θ = a :=
    ⟨Real.arcosh a⁻¹, Real.arcosh_pos h1, by rw [Real.cosh_arcosh h1.le, one_div, inv_inv]⟩
  obtain ⟨e1, e2, e3, e4, -, e6⟩ := dlmf_table_4_30_1_sech hθ hg
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := inv_hyp_positive hθ
  have hv : arcsechD a = θ := by rw [← hg]; exact i5
  rw [hv]
  exact ⟨by rw [← e1, i1], by rw [← e2, i2], by rw [← e3, i3], by rw [← e4, i4],
    by rw [← e6, i6]⟩

/-- **§4.37(vi)** with Table 4.30.1, column `coth θ = a`, `a > 1`. -/
theorem dlmf_4_37_vi_coth {a : ℝ} (ha : 1 < a) :
    arcsinhD ((√(a ^ 2 - 1))⁻¹ : ℝ) = arccothD a ∧
      arccoshD (a * (√(a ^ 2 - 1))⁻¹ : ℝ) = arccothD a ∧ arctanhD (a⁻¹ : ℝ) = arccothD a ∧
      arccschD (√(a ^ 2 - 1) : ℝ) = arccothD a ∧
      arcsechD (a⁻¹ * √(a ^ 2 - 1) : ℝ) = arccothD a := by
  have h0 : 0 < a⁻¹ := inv_pos.mpr (by linarith)
  have h1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  obtain ⟨θ, hθ, hg⟩ : ∃ θ, 0 < θ ∧ 1 / Real.tanh θ = a :=
    ⟨Real.artanh a⁻¹, Real.artanh_pos ⟨h0, h1⟩, by
      rw [Real.tanh_artanh ⟨by linarith, h1⟩, one_div, inv_inv]⟩
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := dlmf_table_4_30_1_coth hθ hg
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := inv_hyp_positive hθ
  have hv : arccothD a = θ := by rw [← hg]; exact i6
  rw [hv]
  exact ⟨by rw [← e1, i1], by rw [← e2, i2], by rw [← e3, i3], by rw [← e4, i4],
    by rw [← e5, i5]⟩

/-- **§4.37(vi)**, DLMF's example: `arcsech a = arccoth((1 − a²)^{−1/2})` (`0 < a < 1`). -/
theorem dlmf_4_37_vi_example {a : ℝ} (ha : a ∈ Ioo 0 1) :
    arcsechD a = arccothD ((1 - a ^ 2) ^ (-1 / 2 : ℝ) : ℝ) := by
  have h : (1 - a ^ 2) ^ (-1 / 2 : ℝ) = (√(1 - a ^ 2))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by nlinarith [ha.1, ha.2])]; norm_num
  rw [h, (dlmf_4_37_vi_sech ha).2.2.2.2]

end Azurite.DLMF
