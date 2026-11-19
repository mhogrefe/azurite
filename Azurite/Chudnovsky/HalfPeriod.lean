/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The half-period integral of a solution of `f′² = 4f³ − af − b`

Let `f` be a real function on `(0, ℓ]` with derivative `q`, `q² = 4f³ − af − b`, with
`f(ℓ) = e`, `f → +∞` at `0⁺`, and `4t³ − at − b > 0` for `t > e`.

* `gt_or_const`: if `f ≥ e`, then `f > e` on `(0, ℓ)` or `f` is constant near `ℓ` (an interior
  maximum above `e` would be a zero of the cubic);
* `half_period_integral`: if `f > e` on `(0, ℓ)`, then `f` is strictly decreasing with image
  `(e, ∞)`, and the substitution `t = f(x)` gives `∫_{t > e} dt/√(4t³ − at − b) = ℓ`.
-/

namespace Azurite.Chudnovsky

open Set MeasureTheory Filter Topology

variable {f q : ℝ → ℝ} {ℓ e a b : ℝ}

/-- `f > e` on `(0, ℓ)`, or `f` is constant on an interval ending at `ℓ`. -/
theorem gt_or_const (hderiv : ∀ x ∈ Ioo 0 ℓ, HasDerivAt f (q x) x)
    (hcont : ContinuousOn f (Ioc 0 ℓ))
    (hode : ∀ x ∈ Ioo 0 ℓ, q x ^ 2 = 4 * f x ^ 3 - a * f x - b) (hend : f ℓ = e)
    (hge : ∀ x ∈ Ioo 0 ℓ, e ≤ f x) (hcubic : ∀ t, e < t → 0 < 4 * t ^ 3 - a * t - b) :
    (∀ x ∈ Ioo 0 ℓ, e < f x) ∨ ∃ x₁ ∈ Ioo 0 ℓ, ∀ x ∈ Icc x₁ ℓ, f x = e := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x₁, hx₁, hfx₁⟩, hnc⟩ := hcon
  have hx₁e : f x₁ = e := le_antisymm hfx₁ (hge x₁ hx₁)
  have hsub : Icc x₁ ℓ ⊆ Ioc 0 ℓ := fun x hx => ⟨lt_of_lt_of_le hx₁.1 hx.1, hx.2⟩
  obtain ⟨x₂, hx₂, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hx₁.2.le)
    (hcont.mono hsub)
  have hmax' : ∀ x ∈ Icc x₁ ℓ, f x ≤ f x₂ := fun x hx => hmax hx
  -- the maximum is `e`
  have hfx₂ : f x₂ = e := by
    by_contra hne
    have hgt : e < f x₂ := lt_of_le_of_ne (by
      have := hmax' x₁ (left_mem_Icc.mpr hx₁.2.le)
      linarith) (Ne.symm hne)
    have hx₂1 : x₁ < x₂ := lt_of_le_of_ne hx₂.1 (fun h => by rw [← h] at hgt; linarith)
    have hx₂2 : x₂ < ℓ := lt_of_le_of_ne hx₂.2 (fun h => by rw [h] at hgt; linarith)
    have hx₂mem : x₂ ∈ Ioo 0 ℓ := ⟨lt_trans hx₁.1 hx₂1, hx₂2⟩
    have hloc : IsLocalMax f x₂ := by
      have hnhds : Icc x₁ ℓ ∈ 𝓝 x₂ := Icc_mem_nhds hx₂1 hx₂2
      exact Filter.mem_of_superset hnhds fun x hx => hmax' x hx
    have hq0 : q x₂ = 0 := hloc.hasDerivAt_eq_zero (hderiv x₂ hx₂mem)
    have := hode x₂ hx₂mem
    have hpos := hcubic _ hgt
    rw [hq0] at this
    nlinarith
  obtain ⟨x, hx, hne⟩ := hnc x₁ hx₁
  apply hne
  have h1 := hmax' x hx
  rw [hfx₂] at h1
  rcases eq_or_lt_of_le hx.2 with h | h
  · rw [h, hend]
  · exact le_antisymm h1 (hge x ⟨lt_of_lt_of_le hx₁.1 hx.1, h⟩)

/-- **The half-period integral.** -/
theorem half_period_integral (hℓ : 0 < ℓ) (hderiv : ∀ x ∈ Ioo 0 ℓ, HasDerivAt f (q x) x)
    (hcont : ContinuousOn f (Ioc 0 ℓ)) (hqcont : ContinuousOn q (Ioo 0 ℓ))
    (hode : ∀ x ∈ Ioo 0 ℓ, q x ^ 2 = 4 * f x ^ 3 - a * f x - b) (hend : f ℓ = e)
    (hgt : ∀ x ∈ Ioo 0 ℓ, e < f x) (hcubic : ∀ t, e < t → 0 < 4 * t ^ 3 - a * t - b)
    (hpole : ∀ B : ℝ, ∃ δ > 0, ∀ x ∈ Ioo 0 δ, B < f x) :
    ∫ t in Ioi e, (√(4 * t ^ 3 - a * t - b))⁻¹ = ℓ := by
  have hq0 : ∀ x ∈ Ioo 0 ℓ, q x ≠ 0 := by
    intro x hx h0
    have := hode x hx
    have hpos := hcubic _ (hgt x hx)
    rw [h0] at this
    nlinarith
  -- `q < 0`
  have hqneg : ∀ x ∈ Ioo 0 ℓ, q x < 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x₁, hx₁, hqx₁⟩ := hcon
    have hqx₁' : 0 < q x₁ := lt_of_le_of_ne hqx₁ (Ne.symm (hq0 x₁ hx₁))
    have hall : ∀ x ∈ Ioo 0 ℓ, 0 < q x := by
      intro x hx
      by_contra hneg
      have hneg' : q x < 0 := lt_of_le_of_ne (not_lt.mp hneg) (hq0 x hx)
      have hsub : uIcc x₁ x ⊆ Ioo 0 ℓ := by
        intro y hy
        rcases le_total x₁ x with h | h
        · rw [uIcc_of_le h] at hy
          exact ⟨lt_of_lt_of_le hx₁.1 hy.1, lt_of_le_of_lt hy.2 hx.2⟩
        · rw [uIcc_of_ge h] at hy
          exact ⟨lt_of_lt_of_le hx.1 hy.1, lt_of_le_of_lt hy.2 hx₁.2⟩
      have hiv := intermediate_value_uIcc (hqcont.mono hsub)
      have h0mem : (0 : ℝ) ∈ uIcc (q x₁) (q x) := by
        rw [uIcc_of_ge (hneg'.le.trans hqx₁'.le)]
        exact ⟨hneg'.le, hqx₁'.le⟩
      obtain ⟨c, hc, hqc⟩ := hiv h0mem
      exact hq0 c (hsub hc) hqc
    -- then `f` is increasing, against `f > e = f ℓ`
    have hmono : StrictMonoOn f (Ioo 0 ℓ) :=
      strictMonoOn_of_deriv_pos (convex_Ioo 0 ℓ) (hcont.mono Ioo_subset_Ioc_self) fun x hx => by
        rw [interior_Ioo] at hx
        rw [(hderiv x hx).deriv]
        exact hall x hx
    have hx₁e := hgt x₁ hx₁
    have htend : Tendsto f (𝓝[<] ℓ) (𝓝 (f ℓ)) := by
      have hle' : 𝓝[<] ℓ ≤ 𝓝[Ioc 0 ℓ] ℓ := by
        rw [← nhdsWithin_Ioo_eq_nhdsLT hℓ]
        exact nhdsWithin_mono _ Ioo_subset_Ioc_self
      exact (hcont ℓ (right_mem_Ioc.mpr hℓ)).tendsto.mono_left hle'
    have hle : f x₁ ≤ f ℓ := by
      refine ge_of_tendsto htend ?_
      filter_upwards [Ioo_mem_nhdsLT hx₁.2] with y hy
      exact (hmono hx₁ ⟨lt_trans hx₁.1 hy.1, hy.2⟩ hy.1).le
    rw [hend] at hle
    linarith
  have hanti : StrictAntiOn f (Ioo 0 ℓ) :=
    strictAntiOn_of_deriv_neg (convex_Ioo 0 ℓ) (hcont.mono Ioo_subset_Ioc_self) fun x hx => by
      rw [interior_Ioo] at hx
      rw [(hderiv x hx).deriv]
      exact hqneg x hx
  -- the image
  have himage : f '' Ioo 0 ℓ = Ioi e := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hgt x hx
    · intro ht
      obtain ⟨δ, hδ, hB⟩ := hpole t
      set x₀ := min δ ℓ / 2 with hx₀
      have hm : 0 < min δ ℓ := lt_min hδ hℓ
      have hx₀δ : x₀ ∈ Ioo 0 δ := ⟨by positivity, by
        have := min_le_left δ ℓ
        linarith⟩
      have hx₀ℓ : x₀ < ℓ := by
        have := min_le_right δ ℓ
        linarith
      have hfx₀ := hB x₀ hx₀δ
      have hsub : Icc x₀ ℓ ⊆ Ioc 0 ℓ := fun x hx => ⟨lt_of_lt_of_le hx₀δ.1 hx.1, hx.2⟩
      have hiv := intermediate_value_Icc' hx₀ℓ.le (hcont.mono hsub)
      obtain ⟨x, hx, hfx⟩ := hiv ⟨by rw [hend]; exact (mem_Ioi.mp ht).le, hfx₀.le⟩
      have hxℓ : x ≠ ℓ := fun h => by
        rw [h, hend] at hfx
        exact absurd hfx (ne_of_lt ht)
      exact ⟨x, ⟨lt_of_lt_of_le hx₀δ.1 hx.1, lt_of_le_of_ne hx.2 hxℓ⟩, hfx⟩
  -- the change of variables
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Ioo 0 ℓ) (f := f) (f' := q)
    measurableSet_Ioo (fun x hx => (hderiv x hx).hasDerivWithinAt) hanti.injOn
    (fun t => (√(4 * t ^ 3 - a * t - b))⁻¹)
  rw [himage] at hcov
  rw [hcov]
  have hint : ∫ x in Ioo 0 ℓ, |q x| • (√(4 * f x ^ 3 - a * f x - b))⁻¹
      = ∫ _x in Ioo 0 ℓ, (1 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    simp only [smul_eq_mul]
    rw [← hode x hx, Real.sqrt_sq_eq_abs]
    exact mul_inv_cancel₀ (abs_ne_zero.mpr (hq0 x hx))
  rw [hint]
  simp [hℓ.le]

end Azurite.Chudnovsky
