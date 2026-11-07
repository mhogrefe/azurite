/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section7
import Azurite.DLMF.Chapter4.Section14
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv

/-!
# DLMF §4.20 Derivatives and Differential Equations

* 4.20.1–4.20.6: `dlmf_4_20_1`, …, `dlmf_4_20_6` (away from the poles).
* 4.20.7–4.20.8: `dlmf_4_20_7`, `dlmf_4_20_8`.
* 4.20.9/4.20.12: `dlmf_4_20_12`. On a domain `D` (open, preconnected), the solutions of
  `w″ + a²w = 0` are exactly `A cos(az) + B sin(az)`.
* 4.20.10/4.20.13: `dlmf_4_20_13`. The solutions of `w′² + a²w² = 1` are `(1/a) sin(az + c)`
  together with the singular solutions `w = ±1/a`, which are not of that form
  (`dlmf_4_20_13_singular`).
* 4.20.11/4.20.14: `dlmf_4_20_14`. The solutions of `w′ − a²w² = 1` are `(1/a) tan(az + c)`
  together with the singular solutions `w = ±i/a`, which are not of that form
  (`dlmf_4_20_14_singular`).

The proofs use the identity theorem twice: in `mul_eq_zero_dichotomy` (a product of
holomorphic functions vanishing on a domain has a vanishing factor), and in
`zero_propagation_of_deriv_eq_mul` (a solution of `h′ = k h` vanishing at one point vanishes
identically; there is a local primitive of `k` on a disc).
-/

open Set Filter Topology Complex
open scoped Real

namespace Azurite.DLMF

/-! ### Derivatives -/

/-- **DLMF 4.20.1**: `d/dz sin z = cos z`. -/
theorem dlmf_4_20_1 (z : ℂ) : HasDerivAt sin (cos z) z := hasDerivAt_sin z

/-- **DLMF 4.20.2**: `d/dz cos z = −sin z`. -/
theorem dlmf_4_20_2 (z : ℂ) : HasDerivAt cos (-sin z) z := hasDerivAt_cos z

/-- **DLMF 4.20.3**: `d/dz tan z = sec² z`. -/
theorem dlmf_4_20_3 {z : ℂ} (hz : cos z ≠ 0) : HasDerivAt tan (secC z ^ 2) z := by
  have := Complex.hasDerivAt_tan hz
  rwa [show secC z ^ 2 = 1 / cos z ^ 2 by rw [secC, div_pow, one_pow]]

/-- **DLMF 4.20.4**: `d/dz csc z = −csc z cot z`. -/
theorem dlmf_4_20_4 {z : ℂ} (hz : sin z ≠ 0) : HasDerivAt cscC (-cscC z * cot z) z := by
  have h := (hasDerivAt_const z (1 : ℂ)).div (hasDerivAt_sin z) hz
  refine h.congr_deriv ?_
  rw [cscC, cot_eq_cos_div_sin]
  field_simp
  ring

/-- **DLMF 4.20.5**: `d/dz sec z = sec z tan z`. -/
theorem dlmf_4_20_5 {z : ℂ} (hz : cos z ≠ 0) : HasDerivAt secC (secC z * tan z) z := by
  have h := (hasDerivAt_const z (1 : ℂ)).div (hasDerivAt_cos z) hz
  refine h.congr_deriv ?_
  rw [secC, tan_eq_sin_div_cos]
  field_simp
  ring

/-- **DLMF 4.20.6**: `d/dz cot z = −csc² z`. -/
theorem dlmf_4_20_6 {z : ℂ} (hz : sin z ≠ 0) : HasDerivAt cot (-cscC z ^ 2) z := by
  have h := (hasDerivAt_cos z).div (hasDerivAt_sin z) hz
  rw [show cot = fun z => cos z / sin z from funext fun _ => cot_eq_cos_div_sin _]
  refine h.congr_deriv ?_
  rw [cscC]
  field_simp
  linear_combination -sin_sq_add_cos_sq z

/-- **DLMF 4.20.7**: `dⁿ/dzⁿ sin z = sin(z + nπ/2)`. -/
theorem dlmf_4_20_7 (n : ℕ) (z : ℂ) : iteratedDeriv n sin z = sin (z + n * π / 2) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv n sin = fun z => sin (z + n * π / 2) from
      funext ih]
    rw [((hasDerivAt_id' z).add_const ((n : ℂ) * π / 2)).csin.deriv]
    push_cast
    rw [show z + (n + 1) * π / 2 = (z + n * π / 2) + π / 2 by ring, sin_add_pi_div_two]
    simp

/-- **DLMF 4.20.8**: `dⁿ/dzⁿ cos z = cos(z + nπ/2)`. -/
theorem dlmf_4_20_8 (n : ℕ) (z : ℂ) : iteratedDeriv n cos z = cos (z + n * π / 2) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv n cos = fun z => cos (z + n * π / 2) from
      funext ih]
    rw [((hasDerivAt_id' z).add_const ((n : ℂ) * π / 2)).ccos.deriv]
    push_cast
    rw [show z + (n + 1) * π / 2 = (z + n * π / 2) + π / 2 by ring, cos_add_pi_div_two]
    simp

/-! ### Tools for the differential equations -/

theorem eqOn_deriv_of_eqOn {D : Set ℂ} (hD : IsOpen D) {w f : ℂ → ℂ} (h : ∀ z ∈ D, w z = f z) :
    ∀ z ∈ D, deriv w z = deriv f z := fun _ hz =>
  Filter.EventuallyEq.deriv_eq (Filter.mem_of_superset (hD.mem_nhds hz) fun y hy => h y hy)

/-- On a domain, a product of holomorphic functions vanishing identically has a vanishing
factor. -/
theorem mul_eq_zero_dichotomy {D : Set ℂ} (hD : IsOpen D) (hDc : IsPreconnected D)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
    (h : ∀ z ∈ D, f z * g z = 0) : (∀ z ∈ D, f z = 0) ∨ (∀ z ∈ D, g z = 0) := by
  by_cases hf0 : ∀ z ∈ D, f z = 0
  · exact Or.inl hf0
  right
  push Not at hf0
  obtain ⟨z₀, hz₀, hfz₀⟩ := hf0
  have hev : g =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hD.mem_nhds hz₀,
      ((hf z₀ hz₀).differentiableAt (hD.mem_nhds hz₀)).continuousAt.eventually_ne hfz₀]
      with y hy hy'
    exact (mul_eq_zero.mp (h y hy)).resolve_left hy'
  intro z hz
  exact (hg.analyticOnNhd hD).eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc hz₀ hev hz

/-- A solution of `h′ = k h` on a domain that vanishes at one point vanishes identically. -/
theorem zero_propagation_of_deriv_eq_mul {D : Set ℂ} (hD : IsOpen D) (hDc : IsPreconnected D)
    {h k : ℂ → ℂ} (hh : DifferentiableOn ℂ h D) (hk : DifferentiableOn ℂ k D)
    (hde : ∀ z ∈ D, deriv h z = k z * h z) {z₁ : ℂ} (hz₁ : z₁ ∈ D) (h0 : h z₁ = 0) :
    ∀ z ∈ D, h z = 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD z₁ hz₁
  obtain ⟨K, hK⟩ := (hk.mono hball).isExactOn_ball
  have hd : ∀ z ∈ Metric.ball z₁ r, HasDerivAt (fun z => h z * exp (-K z)) 0 z := by
    intro z hz
    have hhz : HasDerivAt h (deriv h z) z :=
      ((hh z (hball hz)).differentiableAt (hD.mem_nhds (hball hz))).hasDerivAt
    have := hhz.mul (hK z hz).neg.cexp
    refine this.congr_deriv ?_
    rw [hde z (hball hz)]
    ring
  obtain ⟨c, hc⟩ := Metric.isOpen_ball.exists_is_const_of_deriv_eq_zero
    (convex_ball z₁ r).isPreconnected
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv)
  have hc0 : c = 0 := by
    rw [← hc z₁ (Metric.mem_ball_self hr), h0, zero_mul]
  have hev : h =ᶠ[𝓝 z₁] 0 := by
    filter_upwards [Metric.ball_mem_nhds z₁ hr] with y hy
    have := hc y hy
    rw [hc0] at this
    exact (mul_eq_zero.mp this).resolve_right (exp_ne_zero _)
  intro z hz
  exact (hh.analyticOnNhd hD).eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc hz₁ hev hz

theorem hasDerivAt_sin_mul (a c z : ℂ) :
    HasDerivAt (fun z => sin (a * z + c)) (a * cos (a * z + c)) z := by
  have := ((hasDerivAt_id' z).const_mul a |>.add_const c).csin
  exact this.congr_deriv (by ring)

theorem hasDerivAt_cos_mul (a c z : ℂ) :
    HasDerivAt (fun z => cos (a * z + c)) (-(a * sin (a * z + c))) z := by
  have := ((hasDerivAt_id' z).const_mul a |>.add_const c).ccos
  exact this.congr_deriv (by ring)

/-! ### DLMF 4.20.9 / 4.20.12 -/

/-- **DLMF 4.20.9, 4.20.12**: for `a ≠ 0`, on a domain `D`, the solutions of
`d²w/dz² + a²w = 0` are exactly `w = A cos(az) + B sin(az)`. -/
theorem dlmf_4_20_12 {a : ℂ} (ha : a ≠ 0) {D : Set ℂ} (hD : IsOpen D) (hDc : IsPreconnected D)
    {w : ℂ → ℂ} (hw : DifferentiableOn ℂ w D) :
    (∀ z ∈ D, deriv (deriv w) z + a ^ 2 * w z = 0) ↔
      ∃ A B : ℂ, ∀ z ∈ D, w z = A * cos (a * z) + B * sin (a * z) := by
  have hw' : DifferentiableOn ℂ (deriv w) D := hw.deriv hD
  have dw : ∀ z ∈ D, HasDerivAt w (deriv w z) z := fun z hz =>
    ((hw z hz).differentiableAt (hD.mem_nhds hz)).hasDerivAt
  have ddw : ∀ z ∈ D, HasDerivAt (deriv w) (deriv (deriv w) z) z := fun z hz =>
    ((hw' z hz).differentiableAt (hD.mem_nhds hz)).hasDerivAt
  have hs := hasDerivAt_sin_mul a 0
  have hc := hasDerivAt_cos_mul a 0
  simp only [add_zero] at hs hc
  constructor
  · intro h
    have h1 : ∀ z ∈ D, HasDerivAt (fun z => w z * cos (a * z) - deriv w z * sin (a * z) / a)
        0 z := by
      intro z hz
      refine (((dw z hz).mul (hc z)).sub (((ddw z hz).mul (hs z)).div_const a)).congr_deriv ?_
      rw [show deriv (deriv w) z = -(a ^ 2 * w z) by linear_combination h z hz]
      field_simp
      ring
    have h2 : ∀ z ∈ D, HasDerivAt (fun z => w z * sin (a * z) + deriv w z * cos (a * z) / a)
        0 z := by
      intro z hz
      refine (((dw z hz).mul (hs z)).add (((ddw z hz).mul (hc z)).div_const a)).congr_deriv ?_
      rw [show deriv (deriv w) z = -(a ^ 2 * w z) by linear_combination h z hz]
      field_simp
      ring
    obtain ⟨A, hA⟩ := hD.exists_is_const_of_deriv_eq_zero hDc
      (fun z hz => (h1 z hz).differentiableAt.differentiableWithinAt) (fun z hz => (h1 z hz).deriv)
    obtain ⟨B, hB⟩ := hD.exists_is_const_of_deriv_eq_zero hDc
      (fun z hz => (h2 z hz).differentiableAt.differentiableWithinAt) (fun z hz => (h2 z hz).deriv)
    refine ⟨A, B, fun z hz => ?_⟩
    rw [← hA z hz, ← hB z hz]
    field_simp
    linear_combination (-(a * w z)) * sin_sq_add_cos_sq (a * z)
  · rintro ⟨A, B, hAB⟩
    set f : ℂ → ℂ := fun z => A * cos (a * z) + B * sin (a * z) with hf
    set f' : ℂ → ℂ := fun z => -(A * (a * sin (a * z))) + B * (a * cos (a * z)) with hf'
    have hfd : ∀ z, HasDerivAt f (f' z) z := fun z =>
      (((hc z).const_mul A).add ((hs z).const_mul B)).congr_deriv (by simp only [hf']; ring)
    have hfd' : ∀ z, HasDerivAt f' (-(a ^ 2) * f z) z := fun z => by
      refine (((hs z).const_mul a |>.const_mul A).neg.add
        (((hc z).const_mul a).const_mul B)).congr_deriv ?_
      simp only [hf]; ring
    have e1 : ∀ z ∈ D, deriv w z = f' z := fun z hz => by
      rw [eqOn_deriv_of_eqOn hD hAB z hz, (hfd z).deriv]
    intro z hz
    rw [eqOn_deriv_of_eqOn hD e1 z hz, (hfd' z).deriv, hAB z hz]
    ring

/-! ### DLMF 4.20.10 / 4.20.13 -/

/-- **DLMF 4.20.10, 4.20.13**: for `a ≠ 0`, on a domain `D`, the solutions of
`(dw/dz)² + a²w² = 1` are `w = (1/a) sin(az + c)`, together with the singular solutions
`w = ±1/a`. -/
theorem dlmf_4_20_13 {a : ℂ} (ha : a ≠ 0) {D : Set ℂ} (hD : IsOpen D) (hDc : IsPreconnected D)
    {w : ℂ → ℂ} (hw : DifferentiableOn ℂ w D) :
    (∀ z ∈ D, deriv w z ^ 2 + a ^ 2 * w z ^ 2 = 1) ↔
      (∃ c : ℂ, ∀ z ∈ D, w z = 1 / a * sin (a * z + c)) ∨ (∀ z ∈ D, w z = 1 / a) ∨
        (∀ z ∈ D, w z = -(1 / a)) := by
  have hw' : DifferentiableOn ℂ (deriv w) D := hw.deriv hD
  have dw : ∀ z ∈ D, HasDerivAt w (deriv w z) z := fun z hz =>
    ((hw z hz).differentiableAt (hD.mem_nhds hz)).hasDerivAt
  have ddw : ∀ z ∈ D, HasDerivAt (deriv w) (deriv (deriv w) z) z := fun z hz =>
    ((hw' z hz).differentiableAt (hD.mem_nhds hz)).hasDerivAt
  constructor
  · intro h
    rcases D.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
    · exact Or.inl ⟨0, fun z hz => absurd hz (Set.notMem_empty z)⟩
    -- differentiate: `2 w′ (w″ + a² w) = 0`
    have hprod : ∀ z ∈ D, deriv w z * (deriv (deriv w) z + a ^ 2 * w z) = 0 := by
      intro z hz
      have hE : HasDerivAt (fun z => deriv w z ^ 2 + a ^ 2 * w z ^ 2)
          (2 * deriv w z * deriv (deriv w) z + a ^ 2 * (2 * w z * deriv w z)) z := by
        have := ((ddw z hz).pow 2).add (((dw z hz).pow 2).const_mul (a ^ 2))
        refine this.congr_deriv ?_
        simp only [Nat.cast_ofNat]; ring
      have hconst : deriv (fun z => deriv w z ^ 2 + a ^ 2 * w z ^ 2) z = 0 := by
        rw [Filter.EventuallyEq.deriv_eq (f := fun _ => (1 : ℂ))
          (Filter.mem_of_superset (hD.mem_nhds hz) fun y hy => h y hy)]
        simp
      rw [hE.deriv] at hconst
      linear_combination hconst / 2
    rcases mul_eq_zero_dichotomy hD hDc hw'
      ((hw'.deriv hD).add (hw.const_mul (a ^ 2))) hprod with h0 | h0
    · -- `w′ ≡ 0`: `w` is a constant `c` with `a²c² = 1`
      obtain ⟨c, hc⟩ := hD.exists_is_const_of_deriv_eq_zero hDc hw h0
      have hc1 := h z₀ hz₀
      rw [h0 z₀ hz₀, hc z₀ hz₀] at hc1
      have : (a * c - 1) * (a * c + 1) = 0 := by linear_combination hc1
      rcases mul_eq_zero.mp this with h1 | h1
      · right; left
        intro z hz; rw [hc z hz]; field_simp; linear_combination h1
      · right; right
        intro z hz; rw [hc z hz]; field_simp; linear_combination h1
    · -- `w″ + a²w ≡ 0`
      obtain ⟨A, B, hAB⟩ := (dlmf_4_20_12 ha hD hDc hw).mp h0
      left
      have hs := hasDerivAt_sin_mul a 0
      have hcs := hasDerivAt_cos_mul a 0
      simp only [add_zero] at hs hcs
      have hd : deriv w z₀ = -(A * (a * sin (a * z₀))) + B * (a * cos (a * z₀)) := by
        rw [eqOn_deriv_of_eqOn hD hAB z₀ hz₀]
        exact ((((hcs z₀).const_mul A).add ((hs z₀).const_mul B)).congr_deriv
          (by ring)).deriv
      have hn := h z₀ hz₀
      rw [hd, hAB z₀ hz₀] at hn
      have hAB1 : (a * A) ^ 2 + (a * B) ^ 2 = 1 := by
        linear_combination hn - a ^ 2 * (A ^ 2 + B ^ 2) * sin_sq_add_cos_sq (a * z₀)
      -- `aB + i aA = e^{ic}`
      have hprod1 : (a * B + I * (a * A)) * (a * B - I * (a * A)) = 1 := by
        linear_combination hAB1 - (a * A) ^ 2 * I_sq
      have hne : a * B + I * (a * A) ≠ 0 := fun h0' => by
        rw [h0', zero_mul] at hprod1; exact zero_ne_one hprod1
      set c := -I * log (a * B + I * (a * A)) with hcdef
      have hIc : I * c = log (a * B + I * (a * A)) := by
        rw [hcdef]; ring_nf; rw [I_sq]; ring
      have hE : exp (I * c) = a * B + I * (a * A) := by rw [hIc, exp_log hne]
      have hE' : exp (-I * c) = a * B - I * (a * A) := by
        rw [show -I * c = -(I * c) by ring, exp_neg, hE]
        exact (eq_inv_of_mul_eq_one_right hprod1).symm
      have hcc : cos c = a * B := by rw [dlmf_4_14_2, hE, hE']; ring
      have hsc : sin c = a * A := by
        rw [dlmf_4_14_1, hE, hE']; field_simp; ring
      refine ⟨c, fun z hz => ?_⟩
      rw [hAB z hz, sin_add, hcc, hsc]
      field_simp
      ring
  · rintro (⟨c, hc⟩ | hc | hc) z hz
    · rw [eqOn_deriv_of_eqOn hD hc z hz, ((hasDerivAt_sin_mul a c z).const_mul (1 / a)).deriv,
        hc z hz]
      field_simp
      linear_combination sin_sq_add_cos_sq (a * z + c)
    · rw [eqOn_deriv_of_eqOn hD (f := fun _ => 1 / a) hc z hz, deriv_const, hc z hz]
      field_simp
      ring
    · rw [eqOn_deriv_of_eqOn hD (f := fun _ => -(1 / a)) hc z hz, deriv_const, hc z hz]
      field_simp
      ring

/-- **DLMF 4.20.13**: the singular solutions `w = ±1/a` of 4.20.10 are not of the form
`(1/a) sin(az + c)` on any nonempty domain. -/
theorem dlmf_4_20_13_singular {a : ℂ} (ha : a ≠ 0) {D : Set ℂ} (hD : IsOpen D)
    (hne : D.Nonempty) (s : ℂ) (hs : s = 1 ∨ s = -1) (c : ℂ) :
    ¬ ∀ z ∈ D, 1 / a * sin (a * z + c) = s / a := by
  intro h
  obtain ⟨z₀, hz₀⟩ := hne
  have hsin : ∀ z ∈ D, sin (a * z + c) = s := fun z hz => by
    have := h z hz; field_simp at this; linear_combination this
  -- then `cos(az + c) = 0` on `D`, so its derivative `−a sin(az + c) = −a s` vanishes
  have hcos : ∀ z ∈ D, cos (a * z + c) = 0 := fun z hz => by
    have h1 := sin_sq_add_cos_sq (a * z + c)
    rw [hsin z hz] at h1
    have : cos (a * z + c) ^ 2 = 0 := by rcases hs with rfl | rfl <;> linear_combination h1
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  have hd := eqOn_deriv_of_eqOn hD (f := fun _ => (0 : ℂ)) hcos z₀ hz₀
  rw [(hasDerivAt_cos_mul a c z₀).deriv, deriv_const, hsin z₀ hz₀] at hd
  rcases hs with rfl | rfl
  · exact ha (by linear_combination -hd)
  · exact ha (by linear_combination hd)

/-! ### DLMF 4.20.11 / 4.20.14 -/

/-- **DLMF 4.20.11, 4.20.14**: for `a ≠ 0`, on a domain `D`, the solutions of
`dw/dz − a²w² = 1` are `w = (1/a) tan(az + c)` (with `cos(az + c) ≠ 0` on `D`), together with the
singular solutions `w = ±i/a`. -/
theorem dlmf_4_20_14 {a : ℂ} (ha : a ≠ 0) {D : Set ℂ} (hD : IsOpen D) (hDc : IsPreconnected D)
    {w : ℂ → ℂ} (hw : DifferentiableOn ℂ w D) :
    (∀ z ∈ D, deriv w z - a ^ 2 * w z ^ 2 = 1) ↔
      (∃ c : ℂ, ∀ z ∈ D, cos (a * z + c) ≠ 0 ∧ w z = 1 / a * tan (a * z + c)) ∨
        (∀ z ∈ D, w z = I / a) ∨ (∀ z ∈ D, w z = -(I / a)) := by
  have dw : ∀ z ∈ D, HasDerivAt w (deriv w z) z := fun z hz =>
    ((hw z hz).differentiableAt (hD.mem_nhds hz)).hasDerivAt
  constructor
  · intro h
    -- `p = a w` satisfies `p′ = a (1 + p²) = a (p + i)(p − i)`
    have hp : ∀ z ∈ D, deriv (fun z => a * w z) z = a * (1 + (a * w z) ^ 2) := fun z hz => by
      rw [((dw z hz).const_mul a).deriv]; linear_combination a * h z hz
    have hdiff : ∀ s : ℂ, DifferentiableOn ℂ (fun z => a * w z - s) D := fun s =>
      (hw.const_mul a).sub_const s
    have hk : ∀ s : ℂ, DifferentiableOn ℂ (fun z => a * (a * w z + s)) D := fun s =>
      ((hw.const_mul a).add_const s).const_mul a
    have hde : ∀ s : ℂ, s ^ 2 = -1 → ∀ z ∈ D,
        deriv (fun z => a * w z - s) z = a * (a * w z + s) * (a * w z - s) := by
      intro s hs z hz
      rw [deriv_sub_const, hp z hz]
      linear_combination a * hs
    by_cases h1 : ∃ z₁ ∈ D, a * w z₁ = I
    · obtain ⟨z₁, hz₁, hw₁⟩ := h1
      right; left
      intro z hz
      have := zero_propagation_of_deriv_eq_mul hD hDc (hdiff I) (hk I) (hde I I_sq) hz₁
        (by simp [hw₁]) z hz
      field_simp; linear_combination this
    by_cases h2 : ∃ z₁ ∈ D, a * w z₁ = -I
    · obtain ⟨z₁, hz₁, hw₁⟩ := h2
      right; right
      intro z hz
      have := zero_propagation_of_deriv_eq_mul hD hDc (hdiff (-I)) (hk (-I))
        (hde (-I) (by rw [neg_sq, I_sq])) hz₁ (by simp [hw₁]) z hz
      field_simp; linear_combination this
    push Not at h1 h2
    left
    -- `g = (p − i)/(p + i)` satisfies `g′ = 2ia g`
    have hpI : ∀ z ∈ D, a * w z + I ≠ 0 := fun z hz h0 => h2 z hz (by linear_combination h0)
    set g : ℂ → ℂ := fun z => (a * w z - I) / (a * w z + I) with hg
    have hgd : ∀ z ∈ D, HasDerivAt g (2 * I * a * g z) z := by
      intro z hz
      have := (((dw z hz).const_mul a).sub_const I).div (((dw z hz).const_mul a).add_const I)
        (hpI z hz)
      refine this.congr_deriv ?_
      have hpz : deriv w z = 1 + a ^ 2 * w z ^ 2 := by linear_combination h z hz
      have hpI' := hpI z hz
      simp only [hg]
      rw [hpz]
      field_simp
      linear_combination 2 * I * I_sq
    have hgD : DifferentiableOn ℂ g D := fun z hz =>
      (hgd z hz).differentiableAt.differentiableWithinAt
    have hlin : ∀ z ∈ D, HasDerivAt (fun z => 2 * I * a * z) (2 * I * a) z := fun z _ => by
      simpa using (hasDerivAt_id z).const_mul (2 * I * a)
    obtain ⟨C, hC⟩ := (dlmf_4_7_13 hD hDc (f := fun _ => 2 * I * a) hlin hgD).mp
      (fun z hz => (hgd z hz).deriv)
    rcases D.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
    · exact ⟨0, fun z hz => absurd hz (Set.notMem_empty z)⟩
    have hC0 : C ≠ 0 := by
      intro hC0
      have := hC z₀ hz₀
      rw [hC0, zero_mul] at this
      simp only [hg] at this
      rcases div_eq_zero_iff.mp this with h0 | h0
      · exact h1 z₀ hz₀ (by linear_combination h0)
      · exact hpI z₀ hz₀ h0
    set c := log (-C) / (2 * I) with hcdef
    have hEc : exp (2 * I * c) = -C := by
      rw [hcdef, show 2 * I * (log (-C) / (2 * I)) = log (-C) by field_simp,
        exp_log (neg_ne_zero.mpr hC0)]
    refine ⟨c, fun z hz => ?_⟩
    set θ := a * z + c with hθ
    have hgz : g z = -exp (2 * I * θ) := by
      rw [hC z hz, hθ, mul_add, exp_add, hEc]; ring_nf
    have hE := exp_ne_zero (I * θ)
    have hsq : exp (2 * I * θ) = exp (I * θ) ^ 2 := by rw [← exp_nat_mul]; ring_nf
    have hEn : exp (-I * θ) = (exp (I * θ))⁻¹ := by rw [neg_mul, exp_neg]
    have hcos : cos θ = (exp (I * θ) + (exp (I * θ))⁻¹) / 2 := by rw [dlmf_4_14_2, hEn]
    have hsin : sin θ = (exp (I * θ) - (exp (I * θ))⁻¹) / (2 * I) := by rw [dlmf_4_14_1, hEn]
    have hg1 : 1 + exp (I * θ) ^ 2 ≠ 0 := by
      intro h0
      have : g z = 1 := by rw [hgz, hsq]; linear_combination -h0
      simp only [hg] at this
      rw [div_eq_one_iff_eq (hpI z hz)] at this
      have := congrArg (· - a * w z) this
      simp at this
      have h2I : (2 : ℂ) * I = 0 := by linear_combination -this
      simp [I_ne_zero] at h2I
    have hcos0 : cos θ ≠ 0 := by
      rw [hcos]
      intro h0
      apply hg1
      field_simp at h0
      linear_combination h0
    refine ⟨hcos0, ?_⟩
    -- solve `g = (p − i)/(p + i)` for `p`
    have hgdef : g z * (a * w z + I) = a * w z - I := by
      have := hpI z hz
      simp only [hg]; field_simp
    rw [hgz, hsq] at hgdef
    have hp : a * w z * (1 + exp (I * θ) ^ 2) = I * (1 - exp (I * θ) ^ 2) := by
      linear_combination -hgdef
    have htan : tan θ = I * (1 - exp (I * θ) ^ 2) / (1 + exp (I * θ) ^ 2) := by
      have hI : I ≠ 0 := I_ne_zero
      have hs' : sin θ = (exp (I * θ) ^ 2 - 1) / (2 * I * exp (I * θ)) := by
        rw [hsin]; field_simp
      have hc' : cos θ = (exp (I * θ) ^ 2 + 1) / (2 * exp (I * θ)) := by
        rw [hcos]; field_simp
      have hg1' : exp (I * θ) ^ 2 + 1 ≠ 0 := by rw [add_comm]; exact hg1
      rw [tan_eq_sin_div_cos, hs', hc', div_div_div_eq, div_eq_div_iff
        (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hI) hE) hg1') hg1]
      linear_combination (2 * exp (I * θ) * (exp (I * θ) ^ 2 - 1) * (1 + exp (I * θ) ^ 2)) * I_sq
    rw [htan, eq_comm, ← eq_div_iff hg1 |>.mpr hp]
    field_simp
  · rintro (⟨c, hc⟩ | hc | hc) z hz
    · have hcz := (hc z hz).1
      have hev : ∀ y ∈ D, w y = 1 / a * tan (a * y + c) := fun y hy => (hc y hy).2
      have hdt : HasDerivAt (fun z => 1 / a * tan (a * z + c)) (1 / cos (a * z + c) ^ 2) z := by
        have := ((Complex.hasDerivAt_tan hcz).comp z
          ((hasDerivAt_id' z).const_mul a |>.add_const c)).const_mul (1 / a)
        exact this.congr_deriv (by field_simp)
      rw [eqOn_deriv_of_eqOn hD hev z hz, hdt.deriv, (hc z hz).2, tan_eq_sin_div_cos]
      field_simp
      linear_combination -sin_sq_add_cos_sq (a * z + c)
    · rw [eqOn_deriv_of_eqOn hD (f := fun _ => I / a) hc z hz, deriv_const, hc z hz]
      field_simp
      rw [I_sq]; ring
    · rw [eqOn_deriv_of_eqOn hD (f := fun _ => -(I / a)) hc z hz, deriv_const, hc z hz]
      field_simp
      rw [I_sq]; ring

/-- **DLMF 4.20.14**: the singular solutions `w = ±i/a` of 4.20.11 are not of the form
`(1/a) tan(az + c)` at any point where `cos(az + c) ≠ 0`. -/
theorem dlmf_4_20_14_singular {a : ℂ} (ha : a ≠ 0) (s : ℂ) (hs : s = I ∨ s = -I) (c z : ℂ)
    (hcz : cos (a * z + c) ≠ 0) : 1 / a * tan (a * z + c) ≠ s / a := by
  intro h
  rw [tan_eq_sin_div_cos] at h
  field_simp at h
  have h1 := sin_sq_add_cos_sq (a * z + c)
  rw [h] at h1
  have : cos (a * z + c) ^ 2 * (s ^ 2 + 1) = 1 := by linear_combination h1
  rcases hs with rfl | rfl <;> simp [I_sq] at this

end Azurite.DLMF
