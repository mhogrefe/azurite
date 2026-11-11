/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter2.Section5Rectangle

/-!
# DLMF §2.10(iii): the contour `𝒞` of Figure 2.10.1

The contour `𝒞` of 2.10.20 (Figure 2.10.1) consists of the right half of the circle
`|t| = R` (`R = n − ½`), the segment of the imaginary axis from `iR` down to `i/2`, the left half
of the circle `|t| = ½`, and the segment from `−i/2` down to `−iR`, traversed counterclockwise.
It is parametrized on `[0, 4]` (`cotSide`, `cotCurve`) as a closed piecewise-`C¹` curve
(`cotPath`). It lies in the star-shaped compact set
`K = {|t| ≤ R, ℜt ≥ 0} ∪ {|t| ≤ ½, ℜt ≤ 0}` (`cotK`); its winding number is `0` off `K`
(`cotPath_windingNumber_eq_zero`, by moving outwards along rays) and `1` at every real point of
`[0, R)` (`cotPath_windingNumber_eq_one`, from `∮ dt/t = 2πi` computed piece by piece).
-/

open Set Filter Topology Complex MeasureTheory Metric
open scoped Real

namespace Azurite.DLMF

open Azurite.JordanCurve

theorem cexp_ofReal_mul_I (θ : ℝ) : cexp ((θ : ℂ) * I) = Real.cos θ + Real.sin θ * I := by
  rw [Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]

/-- The four pieces of `𝒞`, the `i`-th parametrized on `[i, i + 1]`. -/
noncomputable def cotSide (R : ℝ) : ℕ → ℝ → ℂ
  | 0 => fun s => (R : ℂ) * cexp (((π * s - π / 2 : ℝ) : ℂ) * I)
  | 1 => fun s => (((1 / 2 - R) * s + (2 * R - 1 / 2) : ℝ) : ℂ) * I
  | 2 => fun s => (1 / 2 : ℂ) * cexp (((π * s - 3 * π / 2 : ℝ) : ℂ) * I)
  | _ => fun s => (((1 / 2 - R) * s + (3 * R - 2) : ℝ) : ℂ) * I

/-- `𝒞`, parametrized on `[0, 4]`. -/
noncomputable def cotCurve (R : ℝ) (s : ℝ) : ℂ :=
  if s ≤ 1 then cotSide R 0 s else if s ≤ 2 then cotSide R 1 s
  else if s ≤ 3 then cotSide R 2 s else cotSide R 3 s

theorem cotSide_zero_zero (R : ℝ) : cotSide R 0 0 = -(R * I) := by
  simp only [cotSide, cexp_ofReal_mul_I]
  rw [show π * (0 : ℝ) - π / 2 = -(π / 2) by ring, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  push_cast; ring

theorem cotSide_junction₁ (R : ℝ) : cotSide R 0 1 = cotSide R 1 1 := by
  simp only [cotSide, cexp_ofReal_mul_I]
  rw [show π * (1 : ℝ) - π / 2 = π / 2 by ring, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

theorem cotSide_junction₂ (R : ℝ) : cotSide R 1 2 = cotSide R 2 2 := by
  simp only [cotSide, cexp_ofReal_mul_I]
  rw [show π * (2 : ℝ) - 3 * π / 2 = π / 2 by ring, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

theorem cotSide_junction₃ (R : ℝ) : cotSide R 2 3 = cotSide R 3 3 := by
  simp only [cotSide, cexp_ofReal_mul_I]
  rw [show π * (3 : ℝ) - 3 * π / 2 = π + π / 2 by ring, Real.cos_add_pi_div_two,
    Real.sin_add_pi_div_two, Real.cos_pi, Real.sin_pi]
  push_cast; ring

theorem cotSide_three_four (R : ℝ) : cotSide R 3 4 = -(R * I) := by
  simp only [cotSide]
  push_cast; ring

theorem hasDerivAt_cotSide₀ (R s : ℝ) :
    HasDerivAt (cotSide R 0) (cotSide R 0 s * (π * I)) s := by
  have h1 : HasDerivAt (fun s : ℝ => (((π * s - π / 2 : ℝ) : ℂ) * I)) (π * I) s := by
    have := (((hasDerivAt_id' s).const_mul π).sub_const (π / 2)).ofReal_comp.mul_const I
    simpa using this
  have := (h1.cexp).const_mul (R : ℂ)
  simp only [cotSide]
  convert this using 1
  ring

theorem hasDerivAt_cotSide₁ (R s : ℝ) :
    HasDerivAt (cotSide R 1) (((1 / 2 - R : ℝ) : ℂ) * I) s := by
  have := ((((hasDerivAt_id' s).const_mul (1 / 2 - R)).add_const (2 * R - 1 / 2)).ofReal_comp
    ).mul_const I
  simpa [cotSide] using this

theorem hasDerivAt_cotSide₂ (R s : ℝ) :
    HasDerivAt (cotSide R 2) (cotSide R 2 s * (π * I)) s := by
  have h1 : HasDerivAt (fun s : ℝ => (((π * s - 3 * π / 2 : ℝ) : ℂ) * I)) (π * I) s := by
    have := (((hasDerivAt_id' s).const_mul π).sub_const (3 * π / 2)).ofReal_comp.mul_const I
    simpa using this
  have := (h1.cexp).const_mul (1 / 2 : ℂ)
  simp only [cotSide]
  convert this using 1
  ring

theorem hasDerivAt_cotSide₃ (R s : ℝ) :
    HasDerivAt (cotSide R 3) (((1 / 2 - R : ℝ) : ℂ) * I) s := by
  have := ((((hasDerivAt_id' s).const_mul (1 / 2 - R)).add_const (3 * R - 2)).ofReal_comp
    ).mul_const I
  simpa [cotSide] using this

theorem contDiff_cotSide (R : ℝ) (i : ℕ) : ContDiff ℝ 1 (cotSide R i) := by
  have hA : ∀ c d : ℝ, ContDiff ℝ 1 fun s : ℝ => ((c * s + d : ℝ) : ℂ) := fun c d =>
    Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)
  have hE : ∀ (r : ℂ) (d : ℝ), ContDiff ℝ 1 fun s : ℝ => r * cexp (((π * s - d : ℝ) : ℂ) * I) :=
    fun r d => contDiff_const.mul (Complex.contDiff_exp.comp
      ((Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
        contDiff_const))
  rcases i with _ | _ | _ | _ | i
  · exact hE _ _
  · exact (hA _ _).mul contDiff_const
  · exact hE _ _
  · exact (hA _ _).mul contDiff_const
  · exact (hA _ _).mul contDiff_const

/-- `𝒞` as a closed piecewise-`C¹` curve. -/
noncomputable def cotPath (R : ℝ) : ClosedPiecewiseC1 (cotCurve R) 0 4 where
  n := 4
  t i := i
  g := cotSide R
  lt i _ := by exact_mod_cast Nat.lt_succ_self i
  first := by simp
  last := by simp
  contDiff i _ := contDiff_cotSide R i
  eqOn i hi := by
    intro s hs
    interval_cases i
    · norm_num at hs
      show cotCurve R s = cotSide R 0 s
      rw [cotCurve]
      simp only [hs.2, ↓reduceIte]
    · norm_num at hs
      show cotCurve R s = cotSide R 1 s
      rw [cotCurve]
      by_cases h1 : s ≤ 1
      · have : s = 1 := le_antisymm h1 hs.1
        rw [this]
        simp only [le_refl, ↓reduceIte, cotSide_junction₁]
      · simp only [h1, hs.2, ↓reduceIte]
    · norm_num at hs
      show cotCurve R s = cotSide R 2 s
      rw [cotCurve]
      have h1 : ¬ s ≤ 1 := by linarith [hs.1]
      by_cases h2 : s ≤ 2
      · have : s = 2 := le_antisymm h2 hs.1
        rw [this]
        simp only [show ¬ ((2 : ℝ) ≤ 1) by norm_num, le_refl, ↓reduceIte, cotSide_junction₂]
      · simp only [h1, h2, hs.2, ↓reduceIte]
    · norm_num at hs
      show cotCurve R s = cotSide R 3 s
      rw [cotCurve]
      have h1 : ¬ s ≤ 1 := by linarith [hs.1]
      have h2 : ¬ s ≤ 2 := by linarith [hs.1]
      by_cases h3 : s ≤ 3
      · have : s = 3 := le_antisymm h3 hs.1
        rw [this]
        simp only [show ¬ ((3 : ℝ) ≤ 1) by norm_num, show ¬ ((3 : ℝ) ≤ 2) by norm_num, le_refl,
          ↓reduceIte, cotSide_junction₃]
      · simp only [h1, h2, h3, ↓reduceIte]
  closed := by
    simp only [cotCurve, show (0 : ℝ) ≤ 1 by norm_num, show ¬ ((4 : ℝ) ≤ 1) by norm_num,
      show ¬ ((4 : ℝ) ≤ 2) by norm_num, show ¬ ((4 : ℝ) ≤ 3) by norm_num, ↓reduceIte,
      cotSide_zero_zero, cotSide_three_four]

theorem norm_ofReal_mul_I (v : ℝ) : ‖(v : ℂ) * I‖ = |v| := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem norm_mul_cexp_ofReal_mul_I (r θ : ℝ) : ‖(r : ℂ) * cexp ((θ : ℂ) * I)‖ = |r| := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem re_mul_cexp_ofReal_mul_I (r θ : ℝ) :
    ((r : ℂ) * cexp ((θ : ℂ) * I)).re = r * Real.cos θ := by
  rw [cexp_ofReal_mul_I]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  ring

/-- Points of `𝒞`: on the big arc, on the imaginary axis between `½` and `R` in modulus, or on the
small arc. -/
theorem cotCurve_mem {R : ℝ} (hR : 1 / 2 ≤ R) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 4) :
    (‖cotCurve R s‖ = R ∧ 0 ≤ (cotCurve R s).re) ∨
      ((cotCurve R s).re = 0 ∧ 1 / 2 ≤ ‖cotCurve R s‖ ∧ ‖cotCurve R s‖ ≤ R) ∨
      (‖cotCurve R s‖ = 1 / 2 ∧ (cotCurve R s).re ≤ 0) := by
  obtain ⟨hs0, hs4⟩ := hs
  have hπ := Real.pi_pos
  unfold cotCurve
  split_ifs with h1 h2 h3
  · left
    simp only [cotSide]
    refine ⟨by rw [norm_mul_cexp_ofReal_mul_I, abs_of_nonneg (by linarith)], ?_⟩
    rw [re_mul_cexp_ofReal_mul_I]
    exact mul_nonneg (by linarith) (Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩)
  · right; left
    simp only [cotSide, norm_ofReal_mul_I]
    have hv : 1 / 2 ≤ (1 / 2 - R) * s + (2 * R - 1 / 2) := by nlinarith
    have hv' : (1 / 2 - R) * s + (2 * R - 1 / 2) ≤ R := by nlinarith
    refine ⟨by simp, ?_, ?_⟩ <;> rw [abs_of_pos (by linarith)] <;> linarith
  · right; right
    simp only [cotSide]
    have e : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [e, norm_mul_cexp_ofReal_mul_I, re_mul_cexp_ofReal_mul_I]
    refine ⟨by norm_num, mul_nonpos_of_nonneg_of_nonpos (by norm_num) ?_⟩
    exact Real.cos_nonpos_of_pi_div_two_le_of_le (by nlinarith) (by nlinarith)
  · right; left
    simp only [cotSide, norm_ofReal_mul_I]
    have hv : (1 / 2 - R) * s + (3 * R - 2) ≤ -(1 / 2) := by nlinarith
    have hv' : -R ≤ (1 / 2 - R) * s + (3 * R - 2) := by nlinarith
    refine ⟨by simp, ?_, ?_⟩ <;> rw [abs_of_neg (by linarith)] <;> linarith

/-- The compact star-shaped set `K = {|t| ≤ R, ℜt ≥ 0} ∪ {|t| ≤ ½, ℜt ≤ 0}` bounded by `𝒞`. -/
def cotK (R : ℝ) : Set ℂ := {z | (‖z‖ ≤ R ∧ 0 ≤ z.re) ∨ (‖z‖ ≤ 1 / 2 ∧ z.re ≤ 0)}

theorem cotPath_curve_subset {R : ℝ} (hR : 1 / 2 ≤ R) : (cotPath R).curve ⊆ cotK R := by
  rintro z ⟨s, hs, rfl⟩
  rcases cotCurve_mem hR hs with ⟨h1, h2⟩ | ⟨h1, -, h3⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.le, h2⟩
  · exact Or.inl ⟨h3, h1.ge⟩
  · exact Or.inr ⟨h1.le, h2⟩

theorem smul_mem_cotK {R : ℝ} {z : ℂ} (hz : z ∈ cotK R) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (c : ℂ) * z ∈ cotK R := by
  have hn : ‖(c : ℂ) * z‖ = c * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0]
  have hr : ((c : ℂ) * z).re = c * z.re := by simp
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨?_, ?_⟩
    · rw [hn]; nlinarith [norm_nonneg z]
    · rw [hr]; exact mul_nonneg hc0 h2
  · refine Or.inr ⟨?_, ?_⟩
    · rw [hn]; nlinarith [norm_nonneg z]
    · rw [hr]; exact mul_nonpos_of_nonneg_of_nonpos hc0 h2

/-- Off `K` the winding number of `𝒞` vanishes: move outwards along the ray through the point. -/
theorem cotPath_windingNumber_eq_zero {R : ℝ} (hR : 1 / 2 ≤ R) {p : ℂ} (hp : p ∉ cotK R) :
    (cotPath R).windingNumber p = 0 := by
  have hp0 : p ≠ 0 := by
    rintro rfl; exact hp (Or.inl ⟨by simp; linarith, by simp⟩)
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  obtain ⟨R₁, hR₁⟩ := (cotPath R).exists_forall_windingNumber_eq_zero
  set L := max 1 ((|R₁| + 1) / ‖p‖) with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  set S := (fun r : ℝ => (r : ℂ) * p) '' Icc 1 L
  have hS : IsPreconnected S :=
    isPreconnected_Icc.image _ (by fun_prop : Continuous fun r : ℝ => (r : ℂ) * p).continuousOn
  have hSc : S ⊆ (cotPath R).curveᶜ := by
    rintro _ ⟨r, hr, rfl⟩ hmem
    apply hp
    have h1 := smul_mem_cotK (cotPath_curve_subset hR hmem) (c := r⁻¹) (by
      have := hr.1; positivity) (inv_le_one_of_one_le₀ hr.1)
    rwa [← mul_assoc, ← ofReal_mul, inv_mul_cancel₀ (by linarith [hr.1]), ofReal_one,
      one_mul] at h1
  rw [(cotPath R).windingNumber_eq_of_isPreconnected hS hSc ⟨1, ⟨le_rfl, hL1⟩, by simp⟩
    ⟨L, ⟨hL1, le_rfl⟩, rfl⟩]
  refine hR₁ _ ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have : (|R₁| + 1) / ‖p‖ * ‖p‖ = |R₁| + 1 := div_mul_cancel₀ _ hpn.ne'
  nlinarith [le_max_right 1 ((|R₁| + 1) / ‖p‖), le_abs_self R₁]

theorem cotPath_windingSupport_subset {R : ℝ} (hR : 1 / 2 ≤ R) :
    (cotPath R).windingSupport ⊆ cotK R := by
  rintro z (hz | ⟨-, hW⟩)
  · exact cotPath_curve_subset hR hz
  · by_contra h; exact hW (cotPath_windingNumber_eq_zero hR h)

/-- Real points of `[0, R)` are not on `𝒞`. -/
theorem notMem_cotPath_curve {R : ℝ} (hR : 1 / 2 ≤ R) {x : ℝ} (hx0 : 0 ≤ x) (hxR : x < R) :
    (x : ℂ) ∉ (cotPath R).curve := by
  rintro ⟨s, hs, hsx⟩
  have hn : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_of_nonneg hx0]
  have hre : (x : ℂ).re = x := ofReal_re x
  have h := cotCurve_mem hR hs
  rw [hsx, hn, hre] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2⟩
  · linarith
  · linarith
  · linarith

theorem deriv_cotSide₀ (R : ℝ) : deriv (cotSide R 0) = fun s => cotSide R 0 s * (π * I) :=
  funext fun s => (hasDerivAt_cotSide₀ R s).deriv

theorem deriv_cotSide₁ (R : ℝ) : deriv (cotSide R 1) = fun _ => ((1 / 2 - R : ℝ) : ℂ) * I :=
  funext fun s => (hasDerivAt_cotSide₁ R s).deriv

theorem deriv_cotSide₂ (R : ℝ) : deriv (cotSide R 2) = fun s => cotSide R 2 s * (π * I) :=
  funext fun s => (hasDerivAt_cotSide₂ R s).deriv

theorem deriv_cotSide₃ (R : ℝ) : deriv (cotSide R 3) = fun _ => ((1 / 2 - R : ℝ) : ℂ) * I :=
  funext fun s => (hasDerivAt_cotSide₃ R s).deriv

/-- `∫ dt/t` along a vertical segment `t = (as + b)i` avoiding `0`. -/
theorem integral_seg_inv (a b c d : ℝ) (h : ∀ s ∈ uIcc c d, a * s + b ≠ 0) :
    ∫ s in c..d, ((((a * s + b : ℝ) : ℂ) * I) - 0)⁻¹ * ((a : ℂ) * I) =
      ((Real.log (a * d + b) - Real.log (a * c + b) : ℝ) : ℂ) := by
  have e : ∀ s ∈ uIcc c d, ((((a * s + b : ℝ) : ℂ) * I) - 0)⁻¹ * ((a : ℂ) * I) =
      ((a / (a * s + b) : ℝ) : ℂ) := fun s hs => by
    have h1 : ((a * s + b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h s hs
    push_cast at h1 ⊢
    rw [sub_zero]
    field_simp
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_ofReal]
  congr 1
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => Real.log (a * s + b))
    (fun s hs => ?_) ?_
  · have := (Real.hasDerivAt_log (h s hs)).comp s (((hasDerivAt_id' s).const_mul a).add_const b)
    convert this using 1
    · rfl
    · ring
  · refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.div (by fun_prop) h

theorem cotSide_ne_zero₀ {R : ℝ} (hR : 0 < R) (s : ℝ) : cotSide R 0 s ≠ 0 :=
  mul_ne_zero (by exact_mod_cast hR.ne') (Complex.exp_ne_zero _)

theorem cotSide_ne_zero₂ (R s : ℝ) : cotSide R 2 s ≠ 0 :=
  mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)

/-- `∮_𝒞 dt/t = 2πi`. -/
theorem cotPath_contourIntegral_inv {R : ℝ} (hR : 1 / 2 ≤ R) :
    (cotPath R).contourIntegral (fun z => (z - 0)⁻¹) = 2 * π * I := by
  have hR0 : 0 < R := by linarith
  show ∑ i ∈ Finset.range 4, ∫ s in ((i : ℕ) : ℝ)..((i + 1 : ℕ) : ℝ),
    (cotSide R i s - 0)⁻¹ * deriv (cotSide R i) s = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, deriv_cotSide₀,
    deriv_cotSide₁, deriv_cotSide₂, deriv_cotSide₃, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, Nat.cast_add]
  have a0 : ∫ s in (0 : ℝ)..1, (cotSide R 0 s - 0)⁻¹ * (cotSide R 0 s * (π * I)) = π * I := by
    rw [intervalIntegral.integral_congr (g := fun _ => (π : ℂ) * I) fun s _ => by
      simp only [sub_zero]; field_simp [cotSide_ne_zero₀ hR0 s]]
    simp
  have a2 : ∫ s in (2 : ℝ)..2 + 1, (cotSide R 2 s - 0)⁻¹ * (cotSide R 2 s * (π * I)) = π * I := by
    rw [intervalIntegral.integral_congr (g := fun _ => (π : ℂ) * I) fun s _ => by
      simp only [sub_zero]; field_simp [cotSide_ne_zero₂ R s]]
    simp
  have a1 := integral_seg_inv (1 / 2 - R) (2 * R - 1 / 2) 1 (1 + 1) fun s hs => by
    rw [uIcc_of_le (by norm_num)] at hs
    nlinarith [hs.1, hs.2]
  have a3 := integral_seg_inv (1 / 2 - R) (3 * R - 2) 3 (3 + 1) fun s hs => by
    rw [uIcc_of_le (by norm_num)] at hs
    nlinarith [hs.1, hs.2]
  rw [a0, a2]
  rw [show (fun s : ℝ => (cotSide R 1 s - 0)⁻¹ * (((1 / 2 - R : ℝ) : ℂ) * I)) =
      fun s : ℝ => ((((1 / 2 - R) * s + (2 * R - 1 / 2) : ℝ) : ℂ) * I - 0)⁻¹ *
        (((1 / 2 - R : ℝ) : ℂ) * I) from rfl,
    show (fun s : ℝ => (cotSide R 3 s - 0)⁻¹ * (((1 / 2 - R : ℝ) : ℂ) * I)) =
      fun s : ℝ => ((((1 / 2 - R) * s + (3 * R - 2) : ℝ) : ℂ) * I - 0)⁻¹ *
        (((1 / 2 - R : ℝ) : ℂ) * I) from rfl, a1, a3]
  have l1 : Real.log ((1 / 2 - R) * (1 + 1) + (2 * R - 1 / 2)) = Real.log (1 / 2) := by ring_nf
  have l2 : Real.log ((1 / 2 - R) * 1 + (2 * R - 1 / 2)) = Real.log R := by ring_nf
  have l3 : Real.log ((1 / 2 - R) * (3 + 1) + (3 * R - 2)) = Real.log R := by
    rw [show (1 / 2 - R) * (3 + 1) + (3 * R - 2) = -R by ring, Real.log_neg_eq_log]
  have l4 : Real.log ((1 / 2 - R) * 3 + (3 * R - 2)) = Real.log (1 / 2) := by
    rw [show (1 / 2 - R) * 3 + (3 * R - 2) = -(1 / 2) by ring, Real.log_neg_eq_log]
  rw [l1, l2, l3, l4]
  push_cast
  ring

theorem cotPath_windingNumber_zero_eq_one {R : ℝ} (hR : 1 / 2 ≤ R) :
    (cotPath R).windingNumber 0 = 1 := by
  have hnot : (0 : ℂ) ∉ (cotPath R).curve := by
    simpa using notMem_cotPath_curve hR le_rfl (by linarith : (0 : ℝ) < R)
  have h := (cotPath R).windingQuot_eq_windingNumber hnot
  rw [ClosedPiecewiseC1.windingQuot, cotPath_contourIntegral_inv hR,
    div_self (by simp [Real.pi_ne_zero])] at h
  exact_mod_cast h.symm

/-- The winding number of `𝒞` is `1` at every real point of `[0, R)`. -/
theorem cotPath_windingNumber_eq_one {R : ℝ} (hR : 1 / 2 ≤ R) {x : ℝ} (hx0 : 0 ≤ x)
    (hxR : x < R) : (cotPath R).windingNumber x = 1 := by
  set S := (fun r : ℝ => (r : ℂ)) '' Icc 0 x
  have hS : IsPreconnected S := isPreconnected_Icc.image _ continuous_ofReal.continuousOn
  have hSc : S ⊆ (cotPath R).curveᶜ := by
    rintro _ ⟨r, hr, rfl⟩
    exact notMem_cotPath_curve hR hr.1 (lt_of_le_of_lt hr.2 hxR)
  rw [(cotPath R).windingNumber_eq_of_isPreconnected hS hSc ⟨x, ⟨hx0, le_rfl⟩, rfl⟩
    (q := 0) ⟨0, ⟨le_rfl, hx0⟩, ofReal_zero⟩, cotPath_windingNumber_zero_eq_one hR]

end Azurite.DLMF
