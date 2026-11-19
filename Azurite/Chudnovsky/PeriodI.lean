/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.PeriodRho

/-!
# The lattice `ℤ[i]`: `g₂ = 4e²` and `e = Γ(1/4)⁴/(8π)`

With `e = ℘(1/2)` (real, `iE`) and `g₃ = 0`:

* on the line `Re z = 1/2` the function `℘` is real with mean value `π` (`integral_gyI`), and
  `℘′` is purely imaginary, so `g₂` is real and `≥ 4π²` (`exists_g₂_latI`);
* on the real axis `℘′² = 4℘(℘² − g₂/4) ≥ 0` and `℘ → +∞` at `0`, so `℘ ≥ √g₂/2` on `(0, 1)`
  by connectedness, hence `e = √g₂/2 > 0` and **`g₂ = 4e²`** (`g₂_latI`);
* `∫_{t > e} dt/√(4t³ − 4e²t) = 1/2` (`integral_i_real`), and `t = e(1 + s²)` turns the integral
  into `e^(−1/2) ∫₀^∞ ds/√((s² + 1)(s² + 2))`, so **`8π e = Γ(1/4)⁴`** (`iE_eq`).
-/

namespace Azurite.Chudnovsky

open Complex ComplexConjugate Set UpperHalfPlane MeasureTheory

theorem latI_conj : ∀ l ∈ latI.lattice, conj l ∈ latI.lattice := fun _ hl => latI_conj_mem hl

theorem one_mem_latI : (1 : ℂ) ∈ latI.lattice := by
  simpa using latI.ω₁_mem_lattice

theorem I_mem_latI : Complex.I ∈ latI.lattice := by
  simpa using latI.ω₂_mem_lattice

theorem half_add_I_notMem (t : ℝ) : (1 / 2 : ℂ) + t * Complex.I ∉ latI.lattice := by
  intro h
  obtain ⟨m, n, hmn⟩ := mem_lattice_pairOf.mp h
  have hre := congrArg Complex.re hmn
  simp at hre
  have h2 : (2 * m : ℝ) = 1 := by linarith
  have h2' : (2 * m : ℤ) = 1 := by exact_mod_cast h2
  omega

/-- `℘(1/2 + it)` as a real function. -/
noncomputable def gyI (t : ℝ) : ℝ := (latI.weierstrassP (1 / 2 + t * Complex.I)).re

theorem gyI_eq (t : ℝ) : latI.weierstrassP (1 / 2 + t * Complex.I) = (gyI t : ℂ) := by
  apply Complex.ext
  · simp [gyI]
  · rw [ofReal_im]
    exact weierstrassP_half_add_I_im latI_conj one_mem_latI t

theorem continuous_gyI : Continuous gyI := by
  rw [continuous_iff_continuousAt]
  intro t
  have hU := latI.isClosed_lattice.isOpen_compl.mem_nhds (half_add_I_notMem t)
  have h1 : ContinuousAt latI.weierstrassP (1 / 2 + t * Complex.I) :=
    (latI.differentiableOn_weierstrassP.differentiableAt hU).continuousAt
  have h2 : ContinuousAt (fun s : ℝ => (1 / 2 : ℂ) + s * Complex.I) t := by fun_prop
  exact Complex.continuous_re.continuousAt.comp
    (ContinuousAt.comp (f := fun s : ℝ => (1 / 2 : ℂ) + s * Complex.I) h1 h2)

/-- The mean value of `℘` on the line `Re z = 1/2` is `π`. -/
theorem integral_gyI : ∫ t in (0 : ℝ)..1, gyI t = Real.pi := by
  have h := integral_weierstrassP_segment latI (1 / 2) Complex.I
    (fun t _ => half_add_I_notMem t)
  have h0 : (1 / 2 : ℂ) ∉ latI.lattice := by
    have := half_add_I_notMem 0
    simpa using this
  have hζ := weierstrassZeta_add_coe latI ⟨Complex.I, I_mem_latI⟩ h0
  simp only at hζ
  rw [hζ, quasiPeriod_latI_I] at h
  simp only [gyI_eq] at h
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal] at h
  have h2 : ((∫ t in (0 : ℝ)..1, gyI t : ℝ) : ℂ) = (Real.pi : ℂ) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    rw [h]
    ring
  exact_mod_cast h2

theorem derivWeierstrassP_half_add_I_re (t : ℝ) :
    (latI.derivWeierstrassP (1 / 2 + t * Complex.I)).re = 0 := by
  have h := derivWeierstrassP_conj latI_conj (1 / 2 + t * Complex.I)
  have e : conj ((1 : ℂ) / 2 + t * Complex.I)
      = -(1 / 2 + t * Complex.I) + ((⟨1, one_mem_latI⟩ : latI.lattice) : ℂ) := by
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one,
      map_ofNat]
    ring
  rw [e, latI.derivWeierstrassP_add_coe, latI.derivWeierstrassP_neg] at h
  have hre := congrArg Complex.re h
  simp only [neg_re, conj_re] at hre
  linarith

/-- `g₂` of `ℤ[i]` is real and `≥ 4π²`. -/
theorem exists_g₂_latI : ∃ γ : ℝ, latI.g₂ = (γ : ℂ) ∧ 4 * Real.pi ^ 2 ≤ γ := by
  have hπ := Real.pi_pos
  -- a point with `℘ ≥ π`
  obtain ⟨t₀, -, ht₀⟩ : ∃ t ∈ Icc (0 : ℝ) 1, Real.pi ≤ gyI t := by
    by_contra hcon
    push Not at hcon
    have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (a := 0) (b := 1) zero_lt_one continuous_gyI.continuousOn
      (continuousOn_const (c := Real.pi))
      (fun x hx => (hcon x ⟨hx.1.le, hx.2⟩).le)
      ⟨0, by simp, hcon 0 (by simp)⟩
    rw [integral_gyI] at hlt
    simp at hlt
  set g := gyI t₀ with hg
  have hg0 : 0 < g := lt_of_lt_of_le hπ ht₀
  set b := (latI.derivWeierstrassP (1 / 2 + t₀ * Complex.I)).im with hb
  have hP' : latI.derivWeierstrassP (1 / 2 + t₀ * Complex.I) = (b : ℂ) * Complex.I := by
    apply Complex.ext
    · rw [derivWeierstrassP_half_add_I_re]
      simp
    · simp [hb]
  have hode := latI.derivWeierstrassP_sq _ (half_add_I_notMem t₀)
  rw [hP', gyI_eq, g₃_latI, ← hg] at hode
  have hgc : (g : ℂ) ≠ 0 := by exact_mod_cast hg0.ne'
  refine ⟨(4 * g ^ 3 + b ^ 2) / g, ?_, ?_⟩
  · push_cast
    rw [eq_div_iff hgc]
    have hI : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
    linear_combination hode - (b : ℂ) ^ 2 * hI
  · rw [le_div_iff₀ hg0]
    nlinarith [sq_nonneg b, pow_pos hg0 3, mul_pos hg0 hg0, mul_le_mul ht₀ ht₀ hπ.le hg0.le]

/-- `e = ℘(1/2)` of the lattice `ℤ[i]`, as a real number. -/
noncomputable def iE : ℝ := axF latI 1 (1 / 2)

theorem halfValue_latI : halfValue latI = (iE : ℂ) := by
  have h := axF_eq latI_conj (v := 1) (Or.inl (map_one _)) (1 / 2)
  rw [← iE] at h
  rw [← h, halfValue, pairOf_ω₁]
  push_cast
  ring_nf

theorem latI_real_notMem {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : (1 : ℂ) * x ∉ latI.lattice :=
  real_notMem_lattice UpperHalfPlane.I hx

/-- **`e > 0`, `g₂ = 4e²`** and `℘ ≥ e` on `(0, 1)` for `ℤ[i]`. -/
theorem latI_real_axis :
    0 < iE ∧ latI.g₂ = 4 * (iE : ℂ) ^ 2 ∧ ∀ x ∈ Ioo (0 : ℝ) 1, iE ≤ axF latI 1 x := by
  obtain ⟨γ, hγ, hγπ⟩ := exists_g₂_latI
  have hπ := Real.pi_pos
  have hγ0 : 0 < γ := by nlinarith
  set A := √γ / 2 with hA
  have hA0 : 0 < A := by positivity
  have hγA : γ = 4 * A ^ 2 := by
    rw [hA, div_pow, Real.sq_sqrt hγ0.le]
    ring
  have hvc : conj (1 : ℂ) = 1 ∨ conj (1 : ℂ) = -1 := Or.inl (map_one _)
  have hode : ∀ x ∈ Ioo (0 : ℝ) 1,
      axQ latI 1 x ^ 2 = 4 * axF latI 1 x ^ 3 - γ * axF latI 1 x := by
    intro x hx
    have h := axQ_sq latI_conj hvc (latI_real_notMem hx)
    rw [hγ, g₃_latI] at h
    have h' : ((axQ latI 1 x ^ 2 : ℝ) : ℂ)
        = ((4 * axF latI 1 x ^ 3 - γ * axF latI 1 x : ℝ) : ℂ) := by
      push_cast
      linear_combination h
    exact_mod_cast h'
  -- the values avoid `(0, A)`
  have hallow : ∀ x ∈ Ioo (0 : ℝ) 1, axF latI 1 x ≤ 0 ∨ A ≤ axF latI 1 x := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have h := hode x hx
    have h1 : 0 < axF latI 1 x * (A - axF latI 1 x) := mul_pos hcon.1 (by linarith)
    have h2 : 0 < axF latI 1 x * (A - axF latI 1 x) * (A + axF latI 1 x) :=
      mul_pos h1 (by linarith)
    have h3 : 4 * axF latI 1 x ^ 3 - γ * axF latI 1 x
        = -4 * (axF latI 1 x * (A - axF latI 1 x) * (A + axF latI 1 x)) := by
      rw [hγA]
      ring
    nlinarith [sq_nonneg (axQ latI 1 x)]
  have hcontF : ContinuousOn (axF latI 1) (Ioo (0 : ℝ) 1) := fun x hx =>
    (hasDerivAt_axF (latI_real_notMem hx)).continuousAt.continuousWithinAt
  obtain ⟨δ, hδ, hB⟩ := axF_pole (L := latI) (v := 1) one_ne_zero A
  set x₂ := min δ 1 / 2 with hx₂def
  have hm : 0 < min δ 1 := lt_min hδ one_pos
  have hx₂ : x₂ ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by
    have := min_le_right δ 1
    linarith⟩
  have hFx₂ : A < axF latI 1 x₂ := hB x₂ ⟨by positivity, by
    have := min_le_left δ 1
    linarith⟩
  have hge : ∀ x ∈ Ioo (0 : ℝ) 1, A ≤ axF latI 1 x := by
    intro x hx
    by_contra hlt
    push Not at hlt
    have hle0 : axF latI 1 x ≤ 0 := (hallow x hx).resolve_right (not_le.mpr hlt)
    have hsub : uIcc x x₂ ⊆ Ioo (0 : ℝ) 1 := ordConnected_Ioo.uIcc_subset hx hx₂
    have hiv := intermediate_value_uIcc (hcontF.mono hsub)
    have hmem : A / 2 ∈ uIcc (axF latI 1 x) (axF latI 1 x₂) := by
      rw [uIcc_of_le (by linarith)]
      exact ⟨by linarith, by linarith⟩
    obtain ⟨c, hc, hFc⟩ := hiv hmem
    rcases hallow c (hsub hc) with h | h <;> linarith
  have he := four_mul_halfValue_cube latI
  rw [hγ, g₃_latI, halfValue_latI] at he
  have heR : 4 * iE ^ 3 - γ * iE = 0 := by
    have h' : ((4 * iE ^ 3 - γ * iE : ℝ) : ℂ) = 0 := by
      push_cast
      linear_combination he
    exact_mod_cast h'
  have hiA : A ≤ iE := hge (1 / 2) ⟨by norm_num, by norm_num⟩
  have hi0 : 0 < iE := lt_of_lt_of_le hA0 hiA
  have hsq : iE ^ 2 = A ^ 2 := by
    have h1 : iE * (4 * iE ^ 2 - 4 * A ^ 2) = 0 := by
      rw [hγA] at heR
      linarith
    rcases mul_eq_zero.mp h1 with h | h
    · linarith
    · linarith
  have hAe : A = iE := by
    have := sq_eq_sq₀ hA0.le hi0.le |>.mp hsq.symm
    exact this
  refine ⟨hi0, ?_, fun x hx => hAe ▸ hge x hx⟩
  rw [hγ, hγA, ← hsq]
  push_cast
  ring

/-- **`g₂ = 4e²` for `ℤ[i]`.** -/
theorem g₂_latI : latI.g₂ = 4 * halfValue latI ^ 2 := by
  rw [halfValue_latI]
  exact latI_real_axis.2.1

/-- The real axis: `∫_{t > e} dt/√(4t³ − 4e²t) = 1/2`. -/
theorem integral_i_real :
    ∫ t in Ioi iE, (√(4 * t ^ 3 - 4 * iE ^ 2 * t - 0))⁻¹ = 1 / 2 := by
  obtain ⟨hi0, hg₂, hgeall⟩ := latI_real_axis
  have hsub : Ioc (0 : ℝ) (1 / 2) ⊆ Ioo 0 1 := fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  have hsub' : Ioo (0 : ℝ) (1 / 2) ⊆ Ioo 0 1 := fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  have hvc : conj (1 : ℂ) = 1 ∨ conj (1 : ℂ) = -1 := Or.inl (map_one _)
  have hode : ∀ x ∈ Ioo (0 : ℝ) 1,
      axQ latI 1 x ^ 2 = 4 * axF latI 1 x ^ 3 - 4 * iE ^ 2 * axF latI 1 x - 0 := by
    intro x hx
    have h := axQ_sq latI_conj hvc (latI_real_notMem hx)
    rw [hg₂, g₃_latI] at h
    have h' : ((axQ latI 1 x ^ 2 : ℝ) : ℂ)
        = ((4 * axF latI 1 x ^ 3 - 4 * iE ^ 2 * axF latI 1 x - 0 : ℝ) : ℂ) := by
      push_cast
      linear_combination h
    exact_mod_cast h'
  have hcubic : ∀ t, iE < t → 0 < 4 * t ^ 3 - 4 * iE ^ 2 * t - 0 := fun t ht => by
    have h1 : 0 < t * (t - iE) := mul_pos (by linarith) (by linarith)
    have h2 : 0 < t * (t - iE) * (t + iE) := mul_pos h1 (by linarith)
    nlinarith
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
      HasDerivAt (axF latI 1) (axQ latI 1 x) x := fun x hx =>
    hasDerivAt_axF (latI_real_notMem (hsub' hx))
  have hcont : ContinuousOn (axF latI 1) (Ioc (0 : ℝ) (1 / 2)) := fun x hx =>
    (hasDerivAt_axF (latI_real_notMem (hsub hx))).continuousAt.continuousWithinAt
  have hqcont : ContinuousOn (axQ latI 1) (Ioo (0 : ℝ) (1 / 2)) := fun x hx =>
    (continuousAt_axQ (latI_real_notMem (hsub' hx))).continuousWithinAt
  have hgt : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), iE < axF latI 1 x := by
    rcases gt_or_const hderiv hcont (fun x hx => hode x (hsub' hx)) rfl
      (fun x hx => hgeall x (hsub' hx)) hcubic with h | h
    · exact h
    · obtain ⟨x₁, hx₁, hconst⟩ := h
      exact (axF_not_const latI_conj hvc one_ne_zero hx₁.2
        (fun x hx => latI_real_notMem ⟨lt_trans hx₁.1 hx.1, by linarith [hx.2]⟩)
        (fun x hx => hconst x ⟨hx.1.le, hx.2.le⟩)).elim
  exact half_period_integral (by norm_num) hderiv hcont hqcont
    (fun x hx => hode x (hsub' hx)) rfl hgt hcubic (axF_pole one_ne_zero)

/-- **`8π ℘(1/2) = Γ(1/4)⁴`** for the lattice `ℤ[i]`. -/
theorem iE_eq : 8 * Real.pi * iE = Real.Gamma (1 / 4) ^ 4 := by
  obtain ⟨hi0, -, -⟩ := latI_real_axis
  have hsi : 0 < √iE := Real.sqrt_pos.mpr hi0
  have hsi2 : √iE ^ 2 = iE := Real.sq_sqrt hi0.le
  have hs2 : (0 : ℝ) < √2 := by positivity
  have hinj : InjOn (fun s : ℝ => iE * (1 + s ^ 2)) (Ioi 0) := by
    intro s hs t ht hst
    have hs0 : (0 : ℝ) < s := hs
    have ht0 : (0 : ℝ) < t := ht
    have h1 : 1 + s ^ 2 = 1 + t ^ 2 := mul_left_cancel₀ hi0.ne' hst
    nlinarith
  have himage : (fun s : ℝ => iE * (1 + s ^ 2)) '' Ioi 0 = Ioi iE := by
    ext u
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs0 : (0 : ℝ) < s := hs
      show iE < iE * (1 + s ^ 2)
      nlinarith [mul_pos hi0 (pow_pos hs0 2)]
    · intro hu
      have hu1 : iE < u := hu
      have hq : 0 < u / iE - 1 := by
        rw [sub_pos, lt_div_iff₀ hi0]
        linarith
      refine ⟨√(u / iE - 1), Real.sqrt_pos.mpr hq, ?_⟩
      show iE * (1 + √(u / iE - 1) ^ 2) = u
      rw [Real.sq_sqrt hq.le]
      field_simp
      ring
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := fun s : ℝ => iE * (1 + s ^ 2)) (f' := fun s => iE * (2 * s)) measurableSet_Ioi
    (fun s _ => by
      have := (((hasDerivAt_pow 2 s).const_add 1).const_mul iE).hasDerivWithinAt
        (s := Ioi (0 : ℝ))
      simpa using this) hinj (fun t => (√(4 * t ^ 3 - 4 * iE ^ 2 * t - 0))⁻¹)
  rw [himage, integral_i_real] at hcov
  have hpt : ∀ s ∈ Ioi (0 : ℝ),
      |iE * (2 * s)| • (√(4 * (iE * (1 + s ^ 2)) ^ 3 - 4 * iE ^ 2 * (iE * (1 + s ^ 2)) - 0))⁻¹
        = (√iE)⁻¹ * BZ.agmKernel 1 (√2) s := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have e : 4 * (iE * (1 + s ^ 2)) ^ 3 - 4 * iE ^ 2 * (iE * (1 + s ^ 2)) - 0
        = (2 * iE * √iE * s) ^ 2 * ((s ^ 2 + 1 ^ 2) * (s ^ 2 + √2 ^ 2)) := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      have : (2 * iE * √iE * s) ^ 2 = 4 * iE ^ 2 * √iE ^ 2 * s ^ 2 := by ring
      rw [this, hsi2]
      ring
    rw [BZ.agmKernel, e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), smul_eq_mul,
      abs_of_pos (by positivity), mul_inv]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul] at hcov
  have hJ : ∫ s in Ioi (0 : ℝ), BZ.agmKernel 1 (√2) s = Real.pi / (2 * BZ.AGM 1 (√2)) :=
    BZ.agmIntegral_eq_pi_div_AGM one_pos hs2
  rw [hJ] at hcov
  have hM : 0 < BZ.AGM 1 (√2) := lt_of_lt_of_le (lt_min one_pos hs2) (BZ.min_le_AGM one_pos hs2)
  have hπ := Real.pi_pos
  -- `√e · AGM = π`
  have h1 : √iE * BZ.AGM 1 (√2) = Real.pi := by
    field_simp at hcov
    linarith
  have hG := gamma_one_quarter_sq
  have h2 : Real.Gamma (1 / 4) ^ 2 * BZ.AGM 1 (√2) = 2 * Real.pi * √(2 * Real.pi) := by
    rw [hG]
    field_simp
  -- `Γ(1/4)² = 2 √(2π) √e`
  have h3 : Real.Gamma (1 / 4) ^ 2 = 2 * √(2 * Real.pi) * √iE := by
    have : Real.Gamma (1 / 4) ^ 2 * BZ.AGM 1 (√2)
        = 2 * √(2 * Real.pi) * √iE * BZ.AGM 1 (√2) := by
      rw [h2]
      calc 2 * Real.pi * √(2 * Real.pi) = 2 * √(2 * Real.pi) * Real.pi := by ring
        _ = 2 * √(2 * Real.pi) * (√iE * BZ.AGM 1 (√2)) := by rw [h1]
        _ = _ := by ring
    exact mul_right_cancel₀ hM.ne' this
  have h4 : Real.Gamma (1 / 4) ^ 4 = (Real.Gamma (1 / 4) ^ 2) ^ 2 := by ring
  rw [h4, h3, mul_pow, mul_pow, Real.sq_sqrt (by positivity), hsi2]
  ring

end Azurite.Chudnovsky
