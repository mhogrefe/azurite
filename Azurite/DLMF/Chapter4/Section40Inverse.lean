/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section26
import Azurite.DLMF.Chapter4.Section29
import Azurite.DLMF.Chapter4.Section40

/-!
# DLMF §4.40(iv) Inverse Hyperbolic Functions (indefinite integrals)

As in §4.26(iv), each formula 4.40.11–4.40.16 is stated for the principal values of §4.37
(`arcsinhD`, …, `arccothD`) as functions of real `x` on DLMF's interval (`dlmf_4_40_n`), via
Mathlib's real functions (`dlmf_4_40_n_real`: `Real.arsinh`, `Real.arcosh`, `Real.artanh`, and
`arccsch x = arsinh(1/x)` etc.) and the bridges of §4.29 (`dlmf_4_29_F2`, `dlmf_4_29_F4`,
`dlmf_4_29_F6`), with `hasDerivAt_ofReal_of_eqOn`. Mathlib has no derivative of `artanh`;
`hasDerivAt_artanh'` proves `artanh′ = 1/(1 − x²)` on `(−1, 1)`. The arcsin in 4.40.15 is the
principal `arcsinD` of §4.23.
-/

open Set Filter Topology
open scoped Real

namespace Azurite.DLMF

theorem hasDerivAt_sqrt_one_add_sq (x : ℝ) :
    HasDerivAt (fun x => √(1 + x ^ 2)) (x / √(1 + x ^ 2)) x := by
  have hp : 0 < 1 + x ^ 2 := by positivity
  refine (((hasDerivAt_pow 2 x).const_add 1).sqrt hp.ne').congr_deriv ?_
  push_cast; field_simp

/-- `artanh′ x = 1/(1 − x²)`, `−1 < x < 1`. -/
theorem hasDerivAt_artanh' {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  have h1 : 0 < 1 + x := by linarith [hx.1]
  have h2 : 0 < 1 - x := by linarith [hx.2]
  have hf : ∀ y ∈ Ioo (-1 : ℝ) 1,
      Real.artanh y = 1 / 2 * (Real.log (1 + y) - Real.log (1 - y)) := fun y hy => by
    rw [Real.artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩,
      Real.log_div (by linarith [hy.1]) (by linarith [hy.2])]
  have hd := ((((hasDerivAt_id x).const_add 1).log h1.ne').sub
    (((hasDerivAt_id x).const_sub 1).log h2.ne')).const_mul (1 / 2)
  have hq : 1 - x ^ 2 ≠ 0 := by nlinarith
  refine (hd.congr_of_eventuallyEq (eventually_of_mem (isOpen_Ioo.mem_nhds hx) hf)).congr_deriv ?_
  simp only [id]
  rw [show 1 - x ^ 2 = (1 + x) * (1 - x) by ring]
  field_simp
  ring

/-! ### 4.40.11–4.40.13 -/

/-- **DLMF 4.40.11** (Mathlib's `arsinh`). -/
theorem dlmf_4_40_11_real (x : ℝ) :
    HasDerivAt (fun x => x * Real.arsinh x - √(1 + x ^ 2)) (Real.arsinh x) x := by
  have hs : 0 < √(1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  refine (((hasDerivAt_id x).mul (Real.hasDerivAt_arsinh x)).sub
    (hasDerivAt_sqrt_one_add_sq x)).congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- **DLMF 4.40.11**: `∫ arcsinh x dx = x arcsinh x − (1 + x²)^{1/2}`. -/
theorem dlmf_4_40_11 (x : ℝ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) * arcsinhD x - (√(1 + x ^ 2) : ℝ)) (arcsinhD x) x := by
  rw [dlmf_4_29_F2.1]
  exact hasDerivAt_ofReal_of_eqOn isOpen_univ (mem_univ x)
    (fun y _ => by rw [dlmf_4_29_F2.1]; push_cast; ring) (dlmf_4_40_11_real x)

/-- **DLMF 4.40.12** (Mathlib's `arcosh`). -/
theorem dlmf_4_40_12_real {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x => x * Real.arcosh x - √(x ^ 2 - 1)) (Real.arcosh x) x := by
  have hs : 0 < √(x ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  refine (((hasDerivAt_id x).mul (Real.hasDerivAt_arcosh hx)).sub
    (hasDerivAt_sqrt_sq_sub_one hx)).congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- **DLMF 4.40.12**: `∫ arccosh x dx = x arccosh x − (x² − 1)^{1/2}`, `1 < x < ∞`. -/
theorem dlmf_4_40_12 {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x : ℝ => (x : ℂ) * arccoshD x - (√(x ^ 2 - 1) : ℝ)) (arccoshD x) x := by
  rw [dlmf_4_29_F2.2.1 x hx.le]
  exact hasDerivAt_ofReal_of_eqOn isOpen_Ioi (mem_Ioi.mpr hx)
    (fun y hy => by rw [dlmf_4_29_F2.2.1 y (le_of_lt hy)]; push_cast; ring)
    (dlmf_4_40_12_real hx)

/-- **DLMF 4.40.13** (Mathlib's `artanh`). -/
theorem dlmf_4_40_13_real {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x => x * Real.artanh x + 1 / 2 * Real.log (1 - x ^ 2)) (Real.artanh x) x := by
  have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  refine (((hasDerivAt_id x).mul (hasDerivAt_artanh' hx)).add
    ((((hasDerivAt_pow 2 x).const_sub 1).log hp.ne').const_mul (1 / 2))).congr_deriv ?_
  simp only [id]
  push_cast
  field_simp
  ring

/-- **DLMF 4.40.13**: `∫ arctanh x dx = x arctanh x + ½ ln(1 − x²)`, `−1 < x < 1`. -/
theorem dlmf_4_40_13 {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x : ℝ => (x : ℂ) * arctanhD x + 1 / 2 * (Real.log (1 - x ^ 2) : ℝ))
      (arctanhD x) x := by
  have hb : ∀ {y : ℝ}, y ∈ Ioo (-1 : ℝ) 1 → |y| < 1 := fun hy => abs_lt.mpr hy
  rw [dlmf_4_29_F4.1 x (hb hx)]
  exact hasDerivAt_ofReal_of_eqOn isOpen_Ioo hx
    (fun y hy => by rw [dlmf_4_29_F4.1 y (hb hy)]; push_cast; ring) (dlmf_4_40_13_real hx)

/-! ### 4.40.14–4.40.16 -/

/-- **DLMF 4.40.14** (`arccsch x = arsinh(1/x)`). -/
theorem dlmf_4_40_14_real {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => x * Real.arsinh (1 / x) + Real.arsinh x) (Real.arsinh (1 / x)) x := by
  have hx0 := hx.ne'
  have hi : HasDerivAt (fun x : ℝ => 1 / x) (-1 / x ^ 2) x := by
    simpa [one_div, neg_div] using hasDerivAt_inv hx0
  have hs1 : 0 < √(1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs : √(1 + (1 / x) ^ 2) = √(1 + x ^ 2) / x := by
    rw [show 1 + (1 / x) ^ 2 = (1 + x ^ 2) / x ^ 2 by field_simp; ring,
      Real.sqrt_div (by positivity), Real.sqrt_sq hx.le]
  refine (((hasDerivAt_id x).mul ((Real.hasDerivAt_arsinh (1 / x)).comp x hi)).add
    (Real.hasDerivAt_arsinh x)).congr_deriv ?_
  simp only [id, Function.comp_apply, hs]
  field_simp
  ring

/-- **DLMF 4.40.14**: `∫ arccsch x dx = x arccsch x + arcsinh x`, `0 < x < ∞`. -/
theorem dlmf_4_40_14 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (x : ℂ) * arccschD x + arcsinhD x) (arccschD x) x := by
  rw [dlmf_4_29_F6.1]
  exact hasDerivAt_ofReal_of_eqOn isOpen_Ioi (mem_Ioi.mpr hx)
    (fun y _ => by rw [dlmf_4_29_F6.1, dlmf_4_29_F2.1]; push_cast; ring) (dlmf_4_40_14_real hx)

/-- **DLMF 4.40.15** (`arcsech x = arcosh(1/x)`, Mathlib's `arcsin`). -/
theorem dlmf_4_40_15_real {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => x * Real.arcosh (1 / x) + Real.arcsin x) (Real.arcosh (1 / x)) x := by
  have hx0 := hx.1.ne'
  have hi : HasDerivAt (fun x : ℝ => 1 / x) (-1 / x ^ 2) x := by
    simpa [one_div, neg_div] using hasDerivAt_inv hx0
  have h1 : 1 < 1 / x := by rw [lt_div_iff₀ hx.1]; linarith [hx.2]
  have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hs1 : 0 < √(1 - x ^ 2) := Real.sqrt_pos.mpr hp
  have hs : √((1 / x) ^ 2 - 1) = √(1 - x ^ 2) / x := by
    rw [show (1 / x) ^ 2 - 1 = (1 - x ^ 2) / x ^ 2 by field_simp,
      Real.sqrt_div hp.le, Real.sqrt_sq hx.1.le]
  refine (((hasDerivAt_id x).mul ((Real.hasDerivAt_arcosh h1).comp x hi)).add
    (Real.hasDerivAt_arcsin (by linarith [hx.1]) hx.2.ne)).congr_deriv ?_
  simp only [id, Function.comp_apply, hs]
  field_simp
  ring

/-- **DLMF 4.40.15**: `∫ arcsech x dx = x arcsech x + arcsin x`, `0 < x < 1`. -/
theorem dlmf_4_40_15 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ => (x : ℂ) * arcsechD x + arcsinD x) (arcsechD x) x := by
  have hb : ∀ {y : ℝ}, y ∈ Ioo (0 : ℝ) 1 → y ∈ Ioo (-1 : ℝ) 1 := fun hy =>
    ⟨by linarith [hy.1], hy.2⟩
  rw [dlmf_4_29_F6.2.1 x hx.1 hx.2.le]
  exact hasDerivAt_ofReal_of_eqOn isOpen_Ioo hx
    (fun y hy => by
      rw [dlmf_4_29_F6.2.1 y hy.1 hy.2.le, arcsinD_ofReal (hb hy)]; push_cast; ring)
    (dlmf_4_40_15_real hx)

/-- **DLMF 4.40.16** (`arccoth x = artanh(1/x)`). -/
theorem dlmf_4_40_16_real {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x => x * Real.artanh (1 / x) + 1 / 2 * Real.log (x ^ 2 - 1))
      (Real.artanh (1 / x)) x := by
  have hx0 : x ≠ 0 := by positivity
  have hi : HasDerivAt (fun x : ℝ => 1 / x) (-1 / x ^ 2) x := by
    simpa [one_div, neg_div] using hasDerivAt_inv hx0
  have hm : 1 / x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by have := one_div_pos.mpr (by linarith : (0 : ℝ) < x); linarith,
      by rw [div_lt_one (by linarith)]; exact hx⟩
  have hp : 0 < x ^ 2 - 1 := by nlinarith
  have hq : 1 - (1 / x) ^ 2 ≠ 0 := by
    rw [show 1 - (1 / x) ^ 2 = (x ^ 2 - 1) / x ^ 2 by field_simp]; positivity
  refine (((hasDerivAt_id x).mul ((hasDerivAt_artanh' hm).comp x hi)).add
    ((((hasDerivAt_pow 2 x).sub_const 1).log hp.ne').const_mul (1 / 2))).congr_deriv ?_
  simp only [id, Function.comp_apply]
  rw [show 1 - (1 / x) ^ 2 = (x ^ 2 - 1) / x ^ 2 by field_simp]
  push_cast
  field_simp
  ring

/-- **DLMF 4.40.16**: `∫ arccoth x dx = x arccoth x + ½ ln(x² − 1)`, `1 < x < ∞`. -/
theorem dlmf_4_40_16 {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x : ℝ => (x : ℂ) * arccothD x + 1 / 2 * (Real.log (x ^ 2 - 1) : ℝ))
      (arccothD x) x := by
  have hb : ∀ {y : ℝ}, 1 < y → 1 < |y| := fun hy => by rw [abs_of_pos (by linarith)]; exact hy
  rw [dlmf_4_29_F4.2.1 x (hb hx)]
  exact hasDerivAt_ofReal_of_eqOn isOpen_Ioi (mem_Ioi.mpr hx)
    (fun y hy => by rw [dlmf_4_29_F4.2.1 y (hb hy)]; push_cast; ring) (dlmf_4_40_16_real hx)

end Azurite.DLMF
