/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section20
import Azurite.DLMF.Chapter4.Section28
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# DLMF §4.34 Derivatives and Differential Equations (hyperbolic functions)

* 4.34.1–4.34.6: `dlmf_4_34_1`, …, `dlmf_4_34_6` (away from the poles).
* 4.34.7/4.34.11: `dlmf_4_34_11`. On a domain `D` (open, preconnected), the solutions of
  `w″ − a²w = 0` are exactly `A cosh(az) + B sinh(az)`.
* 4.34.8/4.34.12: `dlmf_4_34_12`. The solutions of `w′² − a²w² = 1` are `(1/a) sinh(az + c)`
  together with the singular solutions `w = ±i/a` (`dlmf_4_34_12_singular`).
* 4.34.9/4.34.13: `dlmf_4_34_13`. The solutions of `w′² − a²w² = −1` are `(1/a) cosh(az + c)`
  together with the singular solutions `w = ±1/a` (`dlmf_4_34_13_singular`).
* 4.34.10/4.34.14: `dlmf_4_34_14`. The solutions of `w′ + a²w² = 1` are `(1/a) coth(az + c)`
  (with `sinh(az + c) ≠ 0` on `D`) together with the singular solutions `w = ±1/a`
  (`dlmf_4_34_14_singular`).

**Imprecision** (as in 4.20.13–4.20.14): 4.34.12–4.34.14 omit the singular solutions.

The differential equations are reduced to §4.20 with `a ↦ ia` (`(ia)² = −a²`, 4.28.8–4.28.10);
4.34.9 is 4.34.8 for `iw`.
-/

open Set Filter Topology Complex
open scoped Real

namespace Azurite.DLMF

/-! ### Derivatives -/

/-- **DLMF 4.34.1**: `d/dz sinh z = cosh z`. -/
theorem dlmf_4_34_1 (z : ℂ) : HasDerivAt sinh (cosh z) z := hasDerivAt_sinh z

/-- **DLMF 4.34.2**: `d/dz cosh z = sinh z`. -/
theorem dlmf_4_34_2 (z : ℂ) : HasDerivAt cosh (sinh z) z := hasDerivAt_cosh z

/-- **DLMF 4.34.3**: `d/dz tanh z = sech² z`. -/
theorem dlmf_4_34_3 {z : ℂ} (hz : cosh z ≠ 0) : HasDerivAt tanh (sechC z ^ 2) z := by
  have h := (hasDerivAt_sinh z).div (hasDerivAt_cosh z) hz
  rw [show tanh = fun z => sinh z / cosh z from funext tanh_eq_sinh_div_cosh]
  refine h.congr_deriv ?_
  rw [sechC]
  field_simp
  linear_combination cosh_sq_sub_sinh_sq z

/-- **DLMF 4.34.4**: `d/dz csch z = −csch z coth z`. -/
theorem dlmf_4_34_4 {z : ℂ} (hz : sinh z ≠ 0) : HasDerivAt cschC (-cschC z * cothC z) z := by
  have h := (hasDerivAt_const z (1 : ℂ)).div (hasDerivAt_sinh z) hz
  refine h.congr_deriv ?_
  rw [cschC, cothC_eq_cosh_div_sinh]
  field_simp
  ring

/-- **DLMF 4.34.5**: `d/dz sech z = −sech z tanh z`. -/
theorem dlmf_4_34_5 {z : ℂ} (hz : cosh z ≠ 0) : HasDerivAt sechC (-sechC z * tanh z) z := by
  have h := (hasDerivAt_const z (1 : ℂ)).div (hasDerivAt_cosh z) hz
  refine h.congr_deriv ?_
  rw [sechC, tanh_eq_sinh_div_cosh]
  field_simp
  ring

/-- **DLMF 4.34.6**: `d/dz coth z = −csch² z`. -/
theorem dlmf_4_34_6 {z : ℂ} (hz : sinh z ≠ 0) : HasDerivAt cothC (-cschC z ^ 2) z := by
  have h := (hasDerivAt_cosh z).div (hasDerivAt_sinh z) hz
  rw [show cothC = fun z => cosh z / sinh z from funext cothC_eq_cosh_div_sinh]
  refine h.congr_deriv ?_
  rw [cschC]
  field_simp
  linear_combination -cosh_sq_sub_sinh_sq z

/-! ### Tools -/

theorem I_mul_ne_zero {a : ℂ} (ha : a ≠ 0) : I * a ≠ 0 := mul_ne_zero I_ne_zero ha

theorem I_mul_sq (a : ℂ) : (I * a) ^ 2 = -a ^ 2 := by rw [mul_pow, I_sq]; ring

theorem one_div_I_mul {a : ℂ} (ha : a ≠ 0) : 1 / (I * a) = -(I / a) := by
  field_simp; rw [I_sq]; ring

theorem I_div_I_mul_eq {a : ℂ} (ha : a ≠ 0) : I / (I * a) = 1 / a := by
  field_simp

theorem sinh_add_pi_div_two_I (u : ℂ) : sinh (u + π / 2 * I) = I * cosh u := by
  rw [sinh_add, sinh_mul_I, cosh_mul_I, sin_pi_div_two, cos_pi_div_two]; ring

theorem cosh_add_pi_div_two_I (u : ℂ) : cosh (u + π / 2 * I) = I * sinh u := by
  rw [cosh_add, sinh_mul_I, cosh_mul_I, sin_pi_div_two, cos_pi_div_two]; ring

theorem cosh_sub_pi_div_two_I (u : ℂ) : cosh (u - π / 2 * I) = -I * sinh u := by
  rw [cosh_sub, sinh_mul_I, cosh_mul_I, sin_pi_div_two, cos_pi_div_two]; ring

/-! ### DLMF 4.34.7 / 4.34.11 -/

/-- **DLMF 4.34.7, 4.34.11**: for `a ≠ 0`, on a domain `D`, the solutions of
`d²w/dz² − a²w = 0` are exactly `w = A cosh(az) + B sinh(az)`. -/
theorem dlmf_4_34_11 {a : ℂ} (ha : a ≠ 0) {D : Set ℂ} (hD : IsOpen D) (hDc : IsPreconnected D)
    {w : ℂ → ℂ} (hw : DifferentiableOn ℂ w D) :
    (∀ z ∈ D, deriv (deriv w) z - a ^ 2 * w z = 0) ↔
      ∃ A B : ℂ, ∀ z ∈ D, w z = A * cosh (a * z) + B * sinh (a * z) := by
  have e := dlmf_4_20_12 (I_mul_ne_zero ha) hD hDc hw
  rw [I_mul_sq] at e
  have h1 : (∀ z ∈ D, deriv (deriv w) z - a ^ 2 * w z = 0) ↔
      (∀ z ∈ D, deriv (deriv w) z + -a ^ 2 * w z = 0) :=
    ⟨fun h z hz => by linear_combination h z hz, fun h z hz => by linear_combination h z hz⟩
  have hc : ∀ z, cos (I * a * z) = cosh (a * z) := fun z => by rw [mul_assoc, dlmf_4_28_9]
  have hs : ∀ z, sin (I * a * z) = I * sinh (a * z) := fun z => by rw [mul_assoc, dlmf_4_28_8]
  rw [h1, e]
  constructor
  · rintro ⟨A, B, h⟩
    exact ⟨A, I * B, fun z hz => by rw [h z hz, hc, hs]; ring⟩
  · rintro ⟨A, B, h⟩
    refine ⟨A, -I * B, fun z hz => ?_⟩
    rw [h z hz, hc, hs]
    linear_combination (B * sinh (a * z)) * I_sq

/-! ### DLMF 4.34.8 / 4.34.12 -/

theorem sin_I_family {a : ℂ} (ha : a ≠ 0) (c' z : ℂ) :
    1 / (I * a) * sin (I * a * z + I * c') = 1 / a * sinh (a * z + c') := by
  rw [show I * a * z + I * c' = I * (a * z + c') by ring, dlmf_4_28_8]
  field_simp

/-- **DLMF 4.34.8, 4.34.12**: for `a ≠ 0`, on a domain `D`, the solutions of
`(dw/dz)² − a²w² = 1` are `w = (1/a) sinh(az + c)`, together with the singular solutions
`w = ±i/a`. -/
theorem dlmf_4_34_12 {a : ℂ} (ha : a ≠ 0) {D : Set ℂ} (hD : IsOpen D) (hDc : IsPreconnected D)
    {w : ℂ → ℂ} (hw : DifferentiableOn ℂ w D) :
    (∀ z ∈ D, deriv w z ^ 2 - a ^ 2 * w z ^ 2 = 1) ↔
      (∃ c : ℂ, ∀ z ∈ D, w z = 1 / a * sinh (a * z + c)) ∨ (∀ z ∈ D, w z = I / a) ∨
        (∀ z ∈ D, w z = -(I / a)) := by
  have e := dlmf_4_20_13 (I_mul_ne_zero ha) hD hDc hw
  rw [I_mul_sq, one_div_I_mul ha, neg_neg] at e
  have h1 : (∀ z ∈ D, deriv w z ^ 2 - a ^ 2 * w z ^ 2 = 1) ↔
      (∀ z ∈ D, deriv w z ^ 2 + -a ^ 2 * w z ^ 2 = 1) :=
    ⟨fun h z hz => by linear_combination h z hz, fun h z hz => by linear_combination h z hz⟩
  rw [h1, e]
  have hfam : (∃ c : ℂ, ∀ z ∈ D, w z = -(I / a) * sin (I * a * z + c)) ↔
      ∃ c : ℂ, ∀ z ∈ D, w z = 1 / a * sinh (a * z + c) := by
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨-I * c, fun z hz => ?_⟩
      rw [hc z hz, ← one_div_I_mul ha, ← sin_I_family ha, show I * (-I * c) = c by
        rw [← mul_assoc, mul_neg, I_mul_I]; ring]
    · rintro ⟨c, hc⟩
      exact ⟨I * c, fun z hz => by rw [hc z hz, ← one_div_I_mul ha, sin_I_family ha]⟩
  rw [hfam]
  tauto

/-- **DLMF 4.34.12**: the singular solutions `w = ±i/a` of 4.34.8 are not of the form
`(1/a) sinh(az + c)` on any nonempty open set. -/
theorem dlmf_4_34_12_singular {a : ℂ} (ha : a ≠ 0) {D : Set ℂ} (hD : IsOpen D)
    (hne : D.Nonempty) (s : ℂ) (hs : s = I ∨ s = -I) (c : ℂ) :
    ¬ ∀ z ∈ D, 1 / a * sinh (a * z + c) = s / a := by
  intro h
  obtain ⟨z₀, hz₀⟩ := hne
  have hsinh : ∀ z ∈ D, sinh (a * z + c) = s := fun z hz => by
    have := h z hz; field_simp at this; linear_combination this
  -- then `cosh(az + c) = 0` on `D`, so its derivative `a sinh(az + c) = a s` vanishes
  have hcosh : ∀ z ∈ D, cosh (a * z + c) = 0 := fun z hz => by
    have h1 := cosh_sq_sub_sinh_sq (a * z + c)
    rw [hsinh z hz] at h1
    have : cosh (a * z + c) ^ 2 = 0 := by
      rcases hs with rfl | rfl <;> linear_combination h1 + I_sq
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  have hd := eqOn_deriv_of_eqOn hD (f := fun _ => (0 : ℂ)) hcosh z₀ hz₀
  have hder : HasDerivAt (fun z => cosh (a * z + c)) (a * sinh (a * z₀ + c)) z₀ := by
    have := ((hasDerivAt_id' z₀).const_mul a |>.add_const c).ccosh
    exact this.congr_deriv (by ring)
  rw [hder.deriv, deriv_const, hsinh z₀ hz₀] at hd
  rcases mul_eq_zero.mp hd with h0 | h0
  · exact ha h0
  · rcases hs with rfl | rfl
    · exact I_ne_zero h0
    · exact I_ne_zero (neg_eq_zero.mp h0)

/-! ### DLMF 4.34.9 / 4.34.13 -/

/-- **DLMF 4.34.9, 4.34.13**: for `a ≠ 0`, on a domain `D`, the solutions of
`(dw/dz)² − a²w² = −1` are `w = (1/a) cosh(az + c)`, together with the singular solutions
`w = ±1/a`. -/
theorem dlmf_4_34_13 {a : ℂ} (ha : a ≠ 0) {D : Set ℂ} (hD : IsOpen D) (hDc : IsPreconnected D)
    {w : ℂ → ℂ} (hw : DifferentiableOn ℂ w D) :
    (∀ z ∈ D, deriv w z ^ 2 - a ^ 2 * w z ^ 2 = -1) ↔
      (∃ c : ℂ, ∀ z ∈ D, w z = 1 / a * cosh (a * z + c)) ∨ (∀ z ∈ D, w z = 1 / a) ∨
        (∀ z ∈ D, w z = -(1 / a)) := by
  set v : ℂ → ℂ := fun z => I * w z with hv
  have hvd : DifferentiableOn ℂ v D := hw.const_mul I
  have hdv : ∀ z ∈ D, deriv v z = I * deriv w z := fun z hz =>
    deriv_const_mul I ((hw z hz).differentiableAt (hD.mem_nhds hz))
  have e := dlmf_4_34_12 ha hD hDc hvd
  have h1 : (∀ z ∈ D, deriv w z ^ 2 - a ^ 2 * w z ^ 2 = -1) ↔
      (∀ z ∈ D, deriv v z ^ 2 - a ^ 2 * v z ^ 2 = 1) := by
    constructor <;> intro h z hz <;> have := h z hz <;> rw [hdv z hz] at * <;> simp only [hv] at *
    · linear_combination -this + (deriv w z ^ 2 - a ^ 2 * w z ^ 2) * I_sq
    · linear_combination -this + (deriv w z ^ 2 - a ^ 2 * w z ^ 2) * I_sq
  rw [h1, e]
  have hw' : ∀ z, w z = -I * v z := fun z => by
    simp only [hv]; rw [← mul_assoc, neg_mul, I_mul_I]; ring
  constructor
  · rintro (⟨c, hc⟩ | hc | hc)
    · refine Or.inl ⟨c - π / 2 * I, fun z hz => ?_⟩
      rw [hw', hc z hz, show a * z + (c - π / 2 * I) = (a * z + c) - π / 2 * I by ring,
        cosh_sub_pi_div_two_I]
      ring
    · refine Or.inr (Or.inl fun z hz => ?_)
      rw [hw', hc z hz]; field_simp; rw [I_sq]; ring
    · refine Or.inr (Or.inr fun z hz => ?_)
      rw [hw', hc z hz]; field_simp; rw [I_sq]
  · rintro (⟨c, hc⟩ | hc | hc)
    · refine Or.inl ⟨c + π / 2 * I, fun z hz => ?_⟩
      simp only [hv]
      rw [hc z hz, show a * z + (c + π / 2 * I) = (a * z + c) + π / 2 * I by ring,
        sinh_add_pi_div_two_I]
      ring
    · refine Or.inr (Or.inl fun z hz => ?_)
      simp only [hv]; rw [hc z hz]; ring
    · refine Or.inr (Or.inr fun z hz => ?_)
      simp only [hv]; rw [hc z hz]; ring

/-- **DLMF 4.34.13**: the singular solutions `w = ±1/a` of 4.34.9 are not of the form
`(1/a) cosh(az + c)` on any nonempty open set. -/
theorem dlmf_4_34_13_singular {a : ℂ} (ha : a ≠ 0) {D : Set ℂ} (hD : IsOpen D)
    (hne : D.Nonempty) (s : ℂ) (hs : s = 1 ∨ s = -1) (c : ℂ) :
    ¬ ∀ z ∈ D, 1 / a * cosh (a * z + c) = s / a := by
  intro h
  obtain ⟨z₀, hz₀⟩ := hne
  have hcosh : ∀ z ∈ D, cosh (a * z + c) = s := fun z hz => by
    have := h z hz; field_simp at this; linear_combination this
  -- the derivative `a sinh(az + c)` vanishes, so `sinh(az + c) = 0`: then `cosh² = 1` is fine,
  -- but the derivative of `sinh(az + c)`, `a cosh(az + c) = a s`, must vanish too
  have hd1 := eqOn_deriv_of_eqOn hD (f := fun _ => s) hcosh
  have hder : ∀ z, HasDerivAt (fun z => cosh (a * z + c)) (a * sinh (a * z + c)) z := fun z => by
    have := ((hasDerivAt_id' z).const_mul a |>.add_const c).ccosh
    exact this.congr_deriv (by ring)
  have hsinh : ∀ z ∈ D, sinh (a * z + c) = 0 := fun z hz => by
    have := hd1 z hz
    rw [(hder z).deriv, deriv_const] at this
    exact (mul_eq_zero.mp this).resolve_left ha
  have hd2 := eqOn_deriv_of_eqOn hD (f := fun _ => (0 : ℂ)) hsinh z₀ hz₀
  have hder2 : HasDerivAt (fun z => sinh (a * z + c)) (a * cosh (a * z₀ + c)) z₀ := by
    have := ((hasDerivAt_id' z₀).const_mul a |>.add_const c).csinh
    exact this.congr_deriv (by ring)
  rw [hder2.deriv, deriv_const, hcosh z₀ hz₀] at hd2
  rcases mul_eq_zero.mp hd2 with h0 | h0
  · exact ha h0
  · rcases hs with rfl | rfl <;> norm_num at h0

/-! ### DLMF 4.34.10 / 4.34.14 -/

theorem tan_I_family {a : ℂ} (ha : a ≠ 0) (c' z : ℂ) :
    (cos (I * (a * z + c' - π / 2 * I)) ≠ 0 ↔ sinh (a * z + c') ≠ 0) ∧
      1 / (I * a) * tan (I * (a * z + c' - π / 2 * I)) = 1 / a * cothC (a * z + c') := by
  set u := a * z + c' - π / 2 * I with hu
  have hu' : a * z + c' = u + π / 2 * I := by rw [hu]; ring
  rw [dlmf_4_28_9, hu', sinh_add_pi_div_two_I, dlmf_4_28_10, cothC_eq_cosh_div_sinh,
    cosh_add_pi_div_two_I, sinh_add_pi_div_two_I, mul_div_mul_left _ _ I_ne_zero,
    ← tanh_eq_sinh_div_cosh]
  refine ⟨⟨fun h => mul_ne_zero I_ne_zero h, fun h h0 => h (by rw [h0, mul_zero])⟩, ?_⟩
  field_simp

/-- **DLMF 4.34.10, 4.34.14**: for `a ≠ 0`, on a domain `D`, the solutions of
`dw/dz + a²w² = 1` are `w = (1/a) coth(az + c)` (with `sinh(az + c) ≠ 0` on `D`), together with
the singular solutions `w = ±1/a`. -/
theorem dlmf_4_34_14 {a : ℂ} (ha : a ≠ 0) {D : Set ℂ} (hD : IsOpen D) (hDc : IsPreconnected D)
    {w : ℂ → ℂ} (hw : DifferentiableOn ℂ w D) :
    (∀ z ∈ D, deriv w z + a ^ 2 * w z ^ 2 = 1) ↔
      (∃ c : ℂ, ∀ z ∈ D, sinh (a * z + c) ≠ 0 ∧ w z = 1 / a * cothC (a * z + c)) ∨
        (∀ z ∈ D, w z = 1 / a) ∨ (∀ z ∈ D, w z = -(1 / a)) := by
  have e := dlmf_4_20_14 (I_mul_ne_zero ha) hD hDc hw
  rw [I_mul_sq, I_div_I_mul_eq ha] at e
  have h1 : (∀ z ∈ D, deriv w z + a ^ 2 * w z ^ 2 = 1) ↔
      (∀ z ∈ D, deriv w z - -a ^ 2 * w z ^ 2 = 1) :=
    ⟨fun h z hz => by linear_combination h z hz, fun h z hz => by linear_combination h z hz⟩
  rw [h1, e]
  have harg : ∀ c' z : ℂ, I * a * z + (I * c' + π / 2) = I * (a * z + c' - π / 2 * I) :=
    fun c' z => by linear_combination (π / 2 : ℂ) * I_sq
  have hfam : (∃ c : ℂ, ∀ z ∈ D, cos (I * a * z + c) ≠ 0 ∧
      w z = 1 / (I * a) * tan (I * a * z + c)) ↔
      ∃ c : ℂ, ∀ z ∈ D, sinh (a * z + c) ≠ 0 ∧ w z = 1 / a * cothC (a * z + c) := by
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨-I * c + π / 2 * I, fun z hz => ?_⟩
      have hcc : I * (-I * c + π / 2 * I) + π / 2 = c := by
        linear_combination (-c + π / 2 : ℂ) * I_sq
      obtain ⟨h1, h2⟩ := hc z hz
      rw [← hcc, harg] at h1 h2
      exact ⟨(tan_I_family ha _ z).1.mp h1, h2.trans (tan_I_family ha _ z).2⟩
    · rintro ⟨c, hc⟩
      refine ⟨I * c + π / 2, fun z hz => ?_⟩
      obtain ⟨h1, h2⟩ := hc z hz
      rw [harg]
      exact ⟨(tan_I_family ha c z).1.mpr h1, h2.trans (tan_I_family ha c z).2.symm⟩
  rw [hfam]

/-- **DLMF 4.34.14**: the singular solutions `w = ±1/a` of 4.34.10 are not of the form
`(1/a) coth(az + c)` at any point where `sinh(az + c) ≠ 0`. -/
theorem dlmf_4_34_14_singular {a : ℂ} (ha : a ≠ 0) (s : ℂ) (hs : s = 1 ∨ s = -1) (c z : ℂ)
    (hsz : sinh (a * z + c) ≠ 0) : 1 / a * cothC (a * z + c) ≠ s / a := by
  intro h
  rw [cothC_eq_cosh_div_sinh] at h
  field_simp at h
  have h1 := cosh_sq_sub_sinh_sq (a * z + c)
  rw [h] at h1
  have : sinh (a * z + c) ^ 2 * (s ^ 2 - 1) = 1 := by linear_combination h1
  rcases hs with rfl | rfl <;> norm_num at this

end Azurite.DLMF
