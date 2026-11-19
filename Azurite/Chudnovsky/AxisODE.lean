/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.RealStructure
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# `℘` along a symmetry axis through the origin

For a lattice stable under conjugation and a direction `v` with `conj v = ±v` (the real and
the imaginary axis), the function `axF x = v² ℘(v x)` of the real variable `x` is real, with
real derivative `axQ x = v³ ℘′(v x)` (`hasDerivAt_axF`), satisfies
`axQ² = 4 axF³ − g₂ v⁴ axF − g₃ v⁶` (`axQ_sq`), tends to `+∞` at `0⁺` (`axF_pole`), and is not
constant on any interval (`axF_not_const`).
-/

namespace Azurite.Chudnovsky

open Complex ComplexConjugate Filter Topology Set

variable (L : PeriodPair) (v : ℂ)

/-- `v² ℘(v x)` as a real function. -/
noncomputable def axF (x : ℝ) : ℝ := (v ^ 2 * L.weierstrassP (v * x)).re

/-- `v³ ℘′(v x)` as a real function. -/
noncomputable def axQ (x : ℝ) : ℝ := (v ^ 3 * L.derivWeierstrassP (v * x)).re

variable {L v} (hc : ∀ l ∈ L.lattice, conj l ∈ L.lattice) (hvc : conj v = v ∨ conj v = -v)

include hc hvc in
theorem axF_eq (x : ℝ) : v ^ 2 * L.weierstrassP (v * x) = (axF L v x : ℂ) := by
  have h : conj (v ^ 2 * L.weierstrassP (v * x)) = v ^ 2 * L.weierstrassP (v * x) := by
    rw [map_mul, map_pow, ← weierstrassP_conj hc, map_mul, conj_ofReal]
    rcases hvc with h | h
    · rw [h]
    · rw [h, neg_mul, L.weierstrassP_neg]
      ring
  apply Complex.ext
  · simp [axF]
  · rw [ofReal_im]
    exact Complex.conj_eq_iff_im.mp h

include hc hvc in
theorem axQ_eq (x : ℝ) : v ^ 3 * L.derivWeierstrassP (v * x) = (axQ L v x : ℂ) := by
  have h : conj (v ^ 3 * L.derivWeierstrassP (v * x)) = v ^ 3 * L.derivWeierstrassP (v * x) := by
    rw [map_mul, map_pow, ← derivWeierstrassP_conj hc, map_mul, conj_ofReal]
    rcases hvc with h | h
    · rw [h]
    · rw [h, neg_mul, L.derivWeierstrassP_neg]
      ring
  apply Complex.ext
  · simp [axQ]
  · rw [ofReal_im]
    exact Complex.conj_eq_iff_im.mp h

theorem hasDerivAt_axF {x : ℝ} (hx : v * x ∉ L.lattice) :
    HasDerivAt (axF L v) (axQ L v x) x := by
  have hU := L.isClosed_lattice.isOpen_compl.mem_nhds hx
  have h1 : HasDerivAt L.weierstrassP (L.derivWeierstrassP (v * x)) (v * x) := by
    have h := (L.differentiableOn_weierstrassP.differentiableAt hU).hasDerivAt
    rwa [L.deriv_weierstrassP] at h
  have h2 : HasDerivAt (fun z : ℂ => v * z) v (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).const_mul v
  have h3 := (h1.comp (x : ℂ) h2).const_mul (v ^ 2)
  have h4 := h3.real_of_complex
  have e : (v ^ 2 * (L.derivWeierstrassP (v * x) * v)).re = axQ L v x := by
    unfold axQ
    congr 1
    ring
  rw [e] at h4
  exact h4

theorem continuousAt_axQ {x : ℝ} (hx : v * x ∉ L.lattice) : ContinuousAt (axQ L v) x := by
  have hU := L.isClosed_lattice.isOpen_compl.mem_nhds hx
  have h1 : ContinuousAt L.derivWeierstrassP (v * x) :=
    (L.differentiableOn_derivWeierstrassP.differentiableAt hU).continuousAt
  have h2 : ContinuousAt (fun t : ℝ => v * (t : ℂ)) x := by fun_prop
  have h3 : ContinuousAt (fun t : ℝ => L.derivWeierstrassP (v * (t : ℂ))) x :=
    ContinuousAt.comp (f := fun t : ℝ => v * (t : ℂ)) h1 h2
  unfold axQ
  exact Complex.continuous_re.continuousAt.comp (continuousAt_const.mul h3)

include hc hvc in
/-- The differential equation along the axis. -/
theorem axQ_sq {x : ℝ} (hx : v * x ∉ L.lattice) :
    ((axQ L v x : ℂ)) ^ 2
      = 4 * (axF L v x : ℂ) ^ 3 - L.g₂ * v ^ 4 * (axF L v x) - L.g₃ * v ^ 6 := by
  rw [← axQ_eq hc hvc, ← axF_eq hc hvc]
  have h := L.derivWeierstrassP_sq (v * x) hx
  linear_combination v ^ 6 * h

/-- The pole at the origin: `axF → +∞` at `0⁺`. -/
theorem axF_pole (hv0 : v ≠ 0) (B : ℝ) : ∃ δ > 0, ∀ x ∈ Ioo (0 : ℝ) δ, B < axF L v x := by
  have hcont : ContinuousAt (fun z : ℂ => v ^ 2 * L.weierstrassPExcept 0 (v * z)) 0 := by
    have h1 : ContinuousAt (L.weierstrassPExcept 0) (v * 0) := by
      rw [mul_zero]
      exact ((L.differentiableOn_weierstrassPExcept 0).differentiableAt
        (L.isOpen_compl_lattice_sdiff.mem_nhds (by simp))).continuousAt
    have h2 : ContinuousAt (fun z : ℂ => v * z) 0 := by fun_prop
    exact continuousAt_const.mul (ContinuousAt.comp (f := fun z : ℂ => v * z) h1 h2)
  obtain ⟨δ₁, hδ₁, hclose⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
  set M : ℝ := ‖v ^ 2 * L.weierstrassPExcept 0 (v * 0)‖ + 1 with hM
  have hM0 : 0 < M := by positivity
  set N : ℝ := |B| + M + 1 with hN
  have hN0 : 0 < N := by positivity
  refine ⟨min δ₁ (min 1 (1 / N)), by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := hx.1
  have hxδ : x < δ₁ := lt_of_lt_of_le hx.2 (min_le_left _ _)
  have hx1 : x < 1 := lt_of_lt_of_le hx.2 ((min_le_right _ _).trans (min_le_left _ _))
  have hxN : x < 1 / N := lt_of_lt_of_le hx.2 ((min_le_right _ _).trans (min_le_right _ _))
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  -- the decomposition
  have hdec : v ^ 2 * L.weierstrassP (v * x)
      = v ^ 2 * L.weierstrassPExcept 0 (v * x) + ((1 / x ^ 2 : ℝ) : ℂ) := by
    have h := L.weierstrassPExcept_add (0 : L.lattice) (v * x)
    simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, div_zero] at h
    rw [← h]
    push_cast
    field_simp
  have hre : axF L v x = (v ^ 2 * L.weierstrassPExcept 0 (v * x)).re + 1 / x ^ 2 := by
    unfold axF
    rw [hdec, add_re, ofReal_re]
  have hbound : -M ≤ (v ^ 2 * L.weierstrassPExcept 0 (v * x)).re := by
    have h1 := hclose (x := (x : ℂ)) (by
      rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact hxδ)
    rw [dist_eq_norm] at h1
    have h2 := norm_sub_norm_le (v ^ 2 * L.weierstrassPExcept 0 (v * x))
      (v ^ 2 * L.weierstrassPExcept 0 (v * 0))
    have h3 := Complex.abs_re_le_norm (v ^ 2 * L.weierstrassPExcept 0 (v * x))
    have h4 := neg_abs_le (v ^ 2 * L.weierstrassPExcept 0 (v * x)).re
    rw [hM]
    linarith
  have hinv : N < 1 / x ^ 2 := by
    have h1 : x ^ 2 ≤ x := by nlinarith
    have h2 : N < 1 / x := by
      rw [lt_div_iff₀ hx0]
      have := (lt_div_iff₀ hN0).mp hxN
      linarith
    have h3 : 1 / x ≤ 1 / x ^ 2 := one_div_le_one_div_of_le (by positivity) h1
    linarith
  rw [hre, hN] at *
  have := le_abs_self B
  linarith

include hc hvc in
/-- `axF` is not constant on an interval. -/
theorem axF_not_const (hv0 : v ≠ 0) {x₁ x₂ : ℝ} (h12 : x₁ < x₂)
    (hlat : ∀ x ∈ Ioo x₁ x₂, v * x ∉ L.lattice) {c : ℝ} (hconst : ∀ x ∈ Ioo x₁ x₂, axF L v x = c) :
    False := by
  -- the derivative vanishes on the interval
  have hQ0 : ∀ x ∈ Ioo x₁ x₂, L.derivWeierstrassP (v * x) = 0 := by
    intro x hx
    have hev : axF L v =ᶠ[𝓝 x] fun _ => c := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hconst y hy
    have h0 : HasDerivAt (axF L v) 0 x := (hasDerivAt_const x c).congr_of_eventuallyEq hev
    have hq : axQ L v x = 0 := (hasDerivAt_axF (hlat x hx)).unique h0
    have h := axQ_eq hc hvc x
    rw [hq, ofReal_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 3 hv0)
  -- accumulation at the midpoint
  set x₀ := (x₁ + x₂) / 2 with hx₀
  set r := (x₂ - x₁) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hx₀mem : x₀ ∈ Ioo x₁ x₂ := ⟨by rw [hx₀]; linarith, by rw [hx₀]; linarith⟩
  set u : ℕ → ℂ := fun n => v * ((x₀ + r / ((n : ℝ) + 2) : ℝ) : ℂ) with hu
  have hpos : ∀ n : ℕ, 0 < r / ((n : ℝ) + 2) := fun n => by positivity
  have hlt : ∀ n : ℕ, r / ((n : ℝ) + 2) < r := fun n => by
    rw [div_lt_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hmem : ∀ n : ℕ, x₀ + r / ((n : ℝ) + 2) ∈ Ioo x₁ x₂ := fun n =>
    ⟨by have := hpos n; rw [hx₀]; linarith, by have := hlt n; rw [hx₀, hr] at *; linarith⟩
  have htend : Tendsto u atTop (𝓝[≠] (v * (x₀ : ℂ))) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h1 : Tendsto (fun n : ℕ => r / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        have := (tendsto_const_div_atTop_nhds_zero_nat r).comp (tendsto_add_atTop_nat 2)
        refine this.congr fun n => ?_
        simp
      have h2 : Tendsto (fun n : ℕ => x₀ + r / ((n : ℝ) + 2)) atTop (𝓝 x₀) := by
        simpa using tendsto_const_nhds.add h1
      have h3 : Tendsto (fun n : ℕ => ((x₀ + r / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝 (x₀ : ℂ)) :=
        (Complex.continuous_ofReal.tendsto x₀).comp h2
      exact h3.const_mul v
    · refine Eventually.of_forall fun n => ?_
      intro h
      have h' : ((x₀ + r / ((n : ℝ) + 2) : ℝ) : ℂ) = (x₀ : ℂ) := mul_left_cancel₀ hv0 h
      have := (hpos n).ne'
      apply this
      have h'' : x₀ + r / ((n : ℝ) + 2) = x₀ := by exact_mod_cast h'
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (v * (x₀ : ℂ)), L.derivWeierstrassP z = 0 :=
    htend.frequently (Eventually.of_forall fun n => hQ0 _ (hmem n)).frequently
  have hzero := L.analyticOnNhd_derivWeierstrassP.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (isPreconnected_compl_lattice L) (hlat x₀ hx₀mem) hfreq
  exact derivWeierstrassP_not_eqOn_zero L fun z hz => hzero hz

end Azurite.Chudnovsky
