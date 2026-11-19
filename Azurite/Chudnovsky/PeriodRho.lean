/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.AxisODE
import Azurite.Chudnovsky.Bounds
import Azurite.Chudnovsky.CM
import Azurite.Chudnovsky.HalfPeriod
import Azurite.Transcendental.GammaAGM

/-!
# The half-period integrals of the lattice `ℤ[ρ]`

With `e = ℘(1/2)` (real, `rhoE`), `g₂ = 0` and `g₃ = 4e³`:

* on the real axis `℘′² = 4℘³ − 4e³`, and `∫_{t > e} dt/√(4t³ − 4e³) = 1/2`
  (`integral_rho_real`);
* on the imaginary axis `F(x) = −℘(ix)` satisfies `F′² = 4F³ + 4e³`, `F(√3/2) = −e`, and
  `∫_{t > −e} dt/√(4t³ + 4e³) = √3/2` (`integral_rho_imag`).

Both hold whatever the sign of `e`.
-/

namespace Azurite.Chudnovsky

open Complex ComplexConjugate Set UpperHalfPlane MeasureTheory

theorem real_notMem_lattice (τ : ℍ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (1 : ℂ) * x ∉ (pairOf τ).lattice := by
  intro h
  obtain ⟨m, n, hmn⟩ := mem_lattice_pairOf.mp h
  rw [one_mul] at hmn
  have him := congrArg Complex.im hmn
  simp only [ofReal_im, add_im, intCast_im, mul_im, intCast_re, zero_mul, add_zero, zero_add]
    at him
  have hn : (n : ℝ) = 0 := by
    rcases mul_eq_zero.mp him.symm with h0 | h0
    · exact h0
    · exact absurd h0 (ne_of_gt τ.im_pos)
  have hre := congrArg Complex.re hmn
  simp only [ofReal_re, add_re, intCast_re, mul_re, intCast_im, zero_mul, sub_zero] at hre
  rw [hn, zero_mul, add_zero] at hre
  have h1 : (0 : ℝ) < m := by rw [← hre]; exact hx.1
  have h2 : (m : ℝ) < 1 := by rw [← hre]; exact hx.2
  have h1' : (0 : ℤ) < m := by exact_mod_cast h1
  have h2' : m < (1 : ℤ) := by exact_mod_cast h2
  omega

theorem rho_re : (ρ : ℂ).re = -1 / 2 := by simp [UpperHalfPlane.ρ]

theorem rho_im : (ρ : ℂ).im = Real.sqrt 3 / 2 := by simp [UpperHalfPlane.ρ]

theorem imag_notMem_latRho {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (Real.sqrt 3)) :
    Complex.I * x ∉ latRho.lattice := by
  intro h
  obtain ⟨m, n, hmn⟩ := mem_lattice_pairOf.mp h
  have h3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  have hre := congrArg Complex.re hmn
  have him := congrArg Complex.im hmn
  simp only [mul_re, Complex.I_re, ofReal_re, Complex.I_im, ofReal_im, mul_zero, sub_zero,
    zero_mul, add_re, intCast_re, intCast_im, rho_re, mul_im, one_mul, add_im, zero_add, rho_im,
    add_zero] at hre him
  -- `x = n √3 / 2`, `0 < n < 2`, `2m = n`
  have hn1 : (0 : ℝ) < n := by
    by_contra hcon
    have : (n : ℝ) * (Real.sqrt 3 / 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hcon) (by positivity)
    linarith [hx.1]
  have hn2 : (n : ℝ) < 2 := by
    by_contra hcon
    have : Real.sqrt 3 ≤ (n : ℝ) * (Real.sqrt 3 / 2) := by nlinarith [not_lt.mp hcon]
    linarith [hx.2]
  have hn1' : (0 : ℤ) < n := by exact_mod_cast hn1
  have hn2' : n < (2 : ℤ) := by exact_mod_cast hn2
  have hn : n = 1 := by omega
  rw [hn] at hre
  have h2m : (2 * m : ℝ) = 1 := by push_cast at hre; linarith
  have h2m' : (2 * m : ℤ) = 1 := by exact_mod_cast h2m
  omega

theorem latRho_conj : ∀ l ∈ latRho.lattice, conj l ∈ latRho.lattice :=
  fun _ hl => latRho_conj_mem hl

/-- `e = ℘(1/2)` of the lattice `ℤ[ρ]`, as a real number. -/
noncomputable def rhoE : ℝ := axF latRho 1 (1 / 2)

theorem halfValue_latRho : halfValue latRho = (rhoE : ℂ) := by
  have h := axF_eq latRho_conj (v := 1) (Or.inl (map_one _)) (1 / 2)
  rw [← rhoE] at h
  rw [← h, halfValue, pairOf_ω₁]
  push_cast
  ring_nf

theorem g₃_latRho : latRho.g₃ = 4 * (rhoE : ℂ) ^ 3 := by
  have h := four_mul_halfValue_cube latRho
  rw [g₂_latRho, halfValue_latRho] at h
  linear_combination -h

/-- The real axis: `∫_{t > e} dt/√(4t³ − 4e³) = 1/2`. -/
theorem integral_rho_real :
    ∫ t in Ioi rhoE, (√(4 * t ^ 3 - 0 * t - 4 * rhoE ^ 3))⁻¹ = 1 / 2 := by
  have hlat : ∀ x ∈ Ioo (0 : ℝ) 1, (1 : ℂ) * x ∉ latRho.lattice := fun x hx =>
    real_notMem_lattice ρ hx
  have hsub : Ioc (0 : ℝ) (1 / 2) ⊆ Ioo 0 1 := fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  have hsub' : Ioo (0 : ℝ) (1 / 2) ⊆ Ioo 0 1 := fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  have hvc : conj (1 : ℂ) = 1 ∨ conj (1 : ℂ) = -1 := Or.inl (map_one _)
  have hode : ∀ x ∈ Ioo (0 : ℝ) 1,
      axQ latRho 1 x ^ 2 = 4 * axF latRho 1 x ^ 3 - 0 * axF latRho 1 x - 4 * rhoE ^ 3 := by
    intro x hx
    have h := axQ_sq latRho_conj hvc (hlat x hx)
    rw [g₂_latRho, g₃_latRho] at h
    have h' : ((axQ latRho 1 x ^ 2 : ℝ) : ℂ)
        = ((4 * axF latRho 1 x ^ 3 - 0 * axF latRho 1 x - 4 * rhoE ^ 3 : ℝ) : ℂ) := by
      push_cast
      linear_combination h
    exact_mod_cast h'
  have hcube : ∀ {s t : ℝ}, s < t → s ^ 3 < t ^ 3 := fun {s t} hst =>
    (Odd.strictMono_pow (by decide : Odd 3)) hst
  have hge : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), rhoE ≤ axF latRho 1 x := by
    intro x hx
    by_contra hlt
    have h1 := hcube (not_le.mp hlt)
    have h2 := hode x (hsub' hx)
    nlinarith [sq_nonneg (axQ latRho 1 x)]
  have hcubic : ∀ t, rhoE < t → 0 < 4 * t ^ 3 - 0 * t - 4 * rhoE ^ 3 := fun t ht => by
    have := hcube ht
    linarith
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
      HasDerivAt (axF latRho 1) (axQ latRho 1 x) x := fun x hx =>
    hasDerivAt_axF (hlat x (hsub' hx))
  have hcont : ContinuousOn (axF latRho 1) (Ioc (0 : ℝ) (1 / 2)) := fun x hx =>
    (hasDerivAt_axF (hlat x (hsub hx))).continuousAt.continuousWithinAt
  have hqcont : ContinuousOn (axQ latRho 1) (Ioo (0 : ℝ) (1 / 2)) := fun x hx =>
    (continuousAt_axQ (hlat x (hsub' hx))).continuousWithinAt
  have hgt : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), rhoE < axF latRho 1 x := by
    rcases gt_or_const hderiv hcont (fun x hx => hode x (hsub' hx)) rfl hge hcubic with h | h
    · exact h
    · obtain ⟨x₁, hx₁, hconst⟩ := h
      exact (axF_not_const latRho_conj hvc one_ne_zero hx₁.2
        (fun x hx => hlat x ⟨lt_trans hx₁.1 hx.1, by linarith [hx.2]⟩)
        (fun x hx => hconst x ⟨hx.1.le, hx.2.le⟩)).elim
  exact half_period_integral (by norm_num) hderiv hcont hqcont
    (fun x hx => hode x (hsub' hx)) rfl hgt hcubic (axF_pole one_ne_zero)

theorem rho_eq : (ρ : ℂ) = -1 / 2 + (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  apply Complex.ext
  · rw [rho_re]; simp
  · rw [rho_im]; simp

theorem axF_I_half : axF latRho Complex.I (Real.sqrt 3 / 2) = -rhoE := by
  have h1 : Complex.I * ((Real.sqrt 3 / 2 : ℝ) : ℂ)
      = (1 / 2 : ℂ) + ((⟨(ρ : ℂ), latRho.ω₂_mem_lattice⟩ : latRho.lattice) : ℂ) := by
    simp only [rho_eq]
    push_cast
    ring
  have h2 : latRho.weierstrassP (1 / 2) = (rhoE : ℂ) := by
    rw [← halfValue_latRho, halfValue, pairOf_ω₁]
  unfold axF
  rw [h1, latRho.weierstrassP_add_coe, h2, Complex.I_sq]
  simp

/-- The imaginary axis: `∫_{t > −e} dt/√(4t³ + 4e³) = √3/2`. -/
theorem integral_rho_imag :
    ∫ t in Ioi (-rhoE), (√(4 * t ^ 3 - 0 * t - 4 * (-rhoE) ^ 3))⁻¹ = Real.sqrt 3 / 2 := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  have hlat : ∀ x ∈ Ioo (0 : ℝ) (Real.sqrt 3), Complex.I * x ∉ latRho.lattice := fun x hx =>
    imag_notMem_latRho hx
  have hsub : Ioc (0 : ℝ) (Real.sqrt 3 / 2) ⊆ Ioo 0 (Real.sqrt 3) := fun x hx =>
    ⟨hx.1, by linarith [hx.2]⟩
  have hsub' : Ioo (0 : ℝ) (Real.sqrt 3 / 2) ⊆ Ioo 0 (Real.sqrt 3) := fun x hx =>
    ⟨hx.1, by linarith [hx.2]⟩
  have hvc : conj Complex.I = Complex.I ∨ conj Complex.I = -Complex.I := Or.inr Complex.conj_I
  have hI6 : (Complex.I : ℂ) ^ 6 = -1 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Complex.I_sq]
    norm_num
  have hode : ∀ x ∈ Ioo (0 : ℝ) (Real.sqrt 3), axQ latRho Complex.I x ^ 2
      = 4 * axF latRho Complex.I x ^ 3 - 0 * axF latRho Complex.I x - 4 * (-rhoE) ^ 3 := by
    intro x hx
    have h := axQ_sq latRho_conj hvc (hlat x hx)
    rw [g₂_latRho, g₃_latRho, hI6] at h
    have h' : ((axQ latRho Complex.I x ^ 2 : ℝ) : ℂ)
        = ((4 * axF latRho Complex.I x ^ 3 - 0 * axF latRho Complex.I x
          - 4 * (-rhoE) ^ 3 : ℝ) : ℂ) := by
      push_cast
      linear_combination h
    exact_mod_cast h'
  have hcube : ∀ {s t : ℝ}, s < t → s ^ 3 < t ^ 3 := fun {s t} hst =>
    (Odd.strictMono_pow (by decide : Odd 3)) hst
  have hge : ∀ x ∈ Ioo (0 : ℝ) (Real.sqrt 3 / 2), -rhoE ≤ axF latRho Complex.I x := by
    intro x hx
    by_contra hlt
    have h1 := hcube (not_le.mp hlt)
    have h2 := hode x (hsub' hx)
    nlinarith [sq_nonneg (axQ latRho Complex.I x)]
  have hcubic : ∀ t, -rhoE < t → 0 < 4 * t ^ 3 - 0 * t - 4 * (-rhoE) ^ 3 := fun t ht => by
    have := hcube ht
    linarith
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) (Real.sqrt 3 / 2),
      HasDerivAt (axF latRho Complex.I) (axQ latRho Complex.I x) x := fun x hx =>
    hasDerivAt_axF (hlat x (hsub' hx))
  have hcont : ContinuousOn (axF latRho Complex.I) (Ioc (0 : ℝ) (Real.sqrt 3 / 2)) :=
    fun x hx => (hasDerivAt_axF (hlat x (hsub hx))).continuousAt.continuousWithinAt
  have hqcont : ContinuousOn (axQ latRho Complex.I) (Ioo (0 : ℝ) (Real.sqrt 3 / 2)) :=
    fun x hx => (continuousAt_axQ (hlat x (hsub' hx))).continuousWithinAt
  have hgt : ∀ x ∈ Ioo (0 : ℝ) (Real.sqrt 3 / 2), -rhoE < axF latRho Complex.I x := by
    rcases gt_or_const hderiv hcont (fun x hx => hode x (hsub' hx)) axF_I_half hge hcubic
      with h | h
    · exact h
    · obtain ⟨x₁, hx₁, hconst⟩ := h
      exact (axF_not_const latRho_conj hvc Complex.I_ne_zero hx₁.2
        (fun x hx => hlat x ⟨lt_trans hx₁.1 hx.1, by linarith [hx.2]⟩)
        (fun x hx => hconst x ⟨hx.1.le, hx.2.le⟩)).elim
  exact half_period_integral (by positivity) hderiv hcont hqcont
    (fun x hx => hode x (hsub' hx)) axF_I_half hgt hcubic (axF_pole Complex.I_ne_zero)

/-! ### The integral `I₊ = ∫₁^∞ du/√(u³ − 1)` -/

/-- `I₊ = ∫₁^∞ du/√(u³ − 1)`. -/
noncomputable def Iplus : ℝ := ∫ u in Ioi (1 : ℝ), (√(u ^ 3 - 1))⁻¹

theorem integral_cube_scale {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi a, (√(4 * t ^ 3 - 0 * t - 4 * a ^ 3))⁻¹ = Iplus / (2 * √a) := by
  have hsa : 0 < √a := Real.sqrt_pos.mpr ha
  have h := MeasureTheory.integral_comp_mul_left_Ioi
    (fun t => (√(4 * t ^ 3 - 0 * t - 4 * a ^ 3))⁻¹) 1 ha
  rw [mul_one, smul_eq_mul] at h
  have hpt : ∀ x ∈ Ioi (1 : ℝ), (√(4 * (a * x) ^ 3 - 0 * (a * x) - 4 * a ^ 3))⁻¹
      = (2 * a * √a)⁻¹ * (√(x ^ 3 - 1))⁻¹ := by
    intro x hx
    have hx1 : (1 : ℝ) < x := hx
    have hx3 : 0 ≤ x ^ 3 - 1 := by
      have : (1 : ℝ) ≤ x ^ 3 := one_le_pow₀ hx1.le
      linarith
    have e : 4 * (a * x) ^ 3 - 0 * (a * x) - 4 * a ^ 3 = (2 * a * √a) ^ 2 * (x ^ 3 - 1) := by
      have : √a ^ 2 = a := Real.sq_sqrt ha.le
      rw [mul_pow, mul_pow, this]
      ring
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), mul_inv]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt,
    MeasureTheory.integral_const_mul] at h
  rw [← Iplus] at h
  have hne : a ≠ 0 := ha.ne'
  field_simp at h ⊢
  linarith

theorem Iplus_eq_agm :
    Iplus = 2 * BZ.agmIntegral (√((√3 + 3 / 2) / 2)) (√√3) := by
  have hs3 : (0 : ℝ) < √3 := by positivity
  have hinj : InjOn (fun s : ℝ => 1 + s ^ 2) (Ioi 0) := by
    intro s hs t ht hst
    have hs0 : (0 : ℝ) < s := hs
    have ht0 : (0 : ℝ) < t := ht
    simp only at hst
    nlinarith
  have himage : (fun s : ℝ => 1 + s ^ 2) '' Ioi 0 = Ioi 1 := by
    ext u
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs0 : (0 : ℝ) < s := hs
      show (1 : ℝ) < 1 + s ^ 2
      nlinarith
    · intro hu
      have hu1 : (1 : ℝ) < u := hu
      refine ⟨√(u - 1), Real.sqrt_pos.mpr (by linarith), ?_⟩
      show 1 + √(u - 1) ^ 2 = u
      rw [Real.sq_sqrt (by linarith)]
      ring
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := fun s : ℝ => 1 + s ^ 2) (f' := fun s => 2 * s) measurableSet_Ioi
    (fun s _ => by
      have := ((hasDerivAt_pow 2 s).const_add 1).hasDerivWithinAt (s := Ioi (0 : ℝ))
      simpa using this) hinj (fun u => (√(u ^ 3 - 1))⁻¹)
  rw [himage] at hcov
  rw [Iplus, hcov]
  have hpt : ∀ s ∈ Ioi (0 : ℝ), |2 * s| • (√((1 + s ^ 2) ^ 3 - 1))⁻¹
      = 2 * quarticKernel (3 / 2) (√3) s := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have e : (1 + s ^ 2) ^ 3 - 1 = s ^ 2 * (s ^ 4 + 2 * (3 / 2) * s ^ 2 + √3 ^ 2) := by
      rw [Real.sq_sqrt (by norm_num)]
      ring
    rw [quarticKernel, e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs0.le, smul_eq_mul,
      abs_of_pos (by positivity), mul_inv]
    field_simp
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt,
    MeasureTheory.integral_const_mul, integral_quarticKernel hs3 (by positivity)]

/-- `I₊ = Γ(1/3)³/(2 · 2^(1/3) · π)`. -/
theorem Iplus_eq {c : ℝ} (hc0 : 0 < c) (hc : c ^ 3 = 2) :
    Iplus = Real.Gamma (1 / 3) ^ 3 / (2 * c * Real.pi) := by
  have hs3 : (0 : ℝ) < √3 := by positivity
  have hA : 0 < √((√3 + 3 / 2) / 2) := Real.sqrt_pos.mpr (by positivity)
  have hBp : 0 < √√3 := Real.sqrt_pos.mpr hs3
  have hM : 0 < BZ.AGM (√((√3 + 3 / 2) / 2)) (√√3) :=
    lt_of_lt_of_le (lt_min hA hBp) (BZ.min_le_AGM hA hBp)
  have hG := gamma_one_third_cube hc0 hc
  rw [Iplus_eq_agm, BZ.agmIntegral_eq_pi_div_AGM hA hBp, hG]
  have hπ := Real.pi_pos
  field_simp

/-- **`℘(1/2)³` of the lattice `ℤ[ρ]` as a Gamma value**, up to the sign of `℘(1/2)`. -/
theorem rhoE_cube (hne : rhoE ≠ 0) :
    rhoE ^ 3 = Real.Gamma (1 / 3) ^ 18 / (256 * Real.pi ^ 6) ∨
      rhoE ^ 3 = -(Real.Gamma (1 / 3) ^ 18 / (6912 * Real.pi ^ 6)) := by
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ c ^ 3 = 2 :=
    ⟨(2 : ℝ) ^ (1 / 3 : ℝ), by positivity, by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num⟩
  have hI := Iplus_eq hc0 hc
  have hπ := Real.pi_pos
  have hc6 : c ^ 6 = 4 := by
    have : c ^ 6 = (c ^ 3) ^ 2 := by ring
    rw [this, hc]
    norm_num
  have hI6 : Iplus ^ 6 = Real.Gamma (1 / 3) ^ 18 / (256 * Real.pi ^ 6) := by
    rw [hI, div_pow]
    have : (2 * c * Real.pi) ^ 6 = 256 * Real.pi ^ 6 := by
      have : (2 * c * Real.pi) ^ 6 = 64 * c ^ 6 * Real.pi ^ 6 := by ring
      rw [this, hc6]
      ring
    rw [this]
    ring
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · right
    have ha : 0 < -rhoE := by linarith
    have h := integral_rho_imag
    rw [integral_cube_scale ha] at h
    have hsa : 0 < √(-rhoE) := Real.sqrt_pos.mpr ha
    have h3 : (0 : ℝ) < √3 := by positivity
    have hsq : √(-rhoE) * √3 = Iplus := by
      field_simp at h
      linarith
    have hval : -rhoE * 3 = Iplus ^ 2 := by
      rw [← hsq, mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt (by norm_num)]
    have : (-rhoE * 3) ^ 3 = Iplus ^ 6 := by rw [hval]; ring
    rw [hI6] at this
    have e : Real.Gamma (1 / 3) ^ 18 / (6912 * Real.pi ^ 6)
        = Real.Gamma (1 / 3) ^ 18 / (256 * Real.pi ^ 6) / 27 := by
      rw [div_div]
      congr 1
      ring
    rw [e, ← this]
    ring
  · left
    have h := integral_rho_real
    rw [integral_cube_scale hpos] at h
    have hsa : 0 < √rhoE := Real.sqrt_pos.mpr hpos
    have hsq : √rhoE = Iplus := by
      field_simp at h
      linarith
    have hval : rhoE = Iplus ^ 2 := by rw [← hsq, Real.sq_sqrt hpos.le]
    rw [← hI6, hval]
    ring

end Azurite.Chudnovsky
