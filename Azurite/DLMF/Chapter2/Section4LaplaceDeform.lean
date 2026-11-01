/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section4LaplaceBranch

/-!
# DLMF §2.4(iii): deformation of the path near the endpoint onto a ray

The integral along the path `𝒫` near `t = a` is, in the uniformizing variable `w`, an integral
of an analytic function `F` along a curve `σ(u)` in a sector `|ph w − ω'| < α`, `|w| < δ₀`, with
`σ(u) → 0`. We move it onto the ray `ph w = ω'`:

`∫₀^{u₁} F(σ(u)) σ′(u) du = ∫₀^{r₁} F(re^{iω'}) e^{iω'} dr + ∫_{ω'}^{φ₁} F(r₁e^{iy}) i r₁e^{iy} dy`

(`deform_to_ray`), where `r₁ = |σ(u₁)|` and `φ₁ = ph σ(u₁)`: the remaining term is the arc of
radius `r₁` joining the ray to the end of the curve.

The proof works in the logarithmic coordinate `ζ = logBr ω' w`, where the sector becomes an open
rectangle; a holomorphic function on an open rectangle has a primitive built from Mathlib's
Cauchy theorem on rectangles (`exists_primitive_rect`), so the integrals along the curve, the
ray and the vertical segments are differences of the primitive. The small vertical segment at
`|w| = ε` vanishes as `ε → 0` because `|F(w)| ≤ C|w|^{β−1}`, `β > 0`.
-/

open Set Filter Topology Complex MeasureTheory
open scoped Interval

namespace Azurite.DLMF

/-! ### A primitive on an open rectangle -/

/-- The candidate primitive: integrate from `x₀ + iy₀` horizontally to `ζ.re + iy₀`, then
vertically to `ζ`. -/
noncomputable def rectPrimitive (F : ℂ → ℂ) (x₀ y₀ : ℝ) (ζ : ℂ) : ℂ :=
  (∫ s in x₀..ζ.re, F (s + y₀ * I)) + I * ∫ t in y₀..ζ.im, F (ζ.re + t * I)

theorem mem_rect_iff {x₁ x₂ y₁ y₂ : ℝ} {ζ : ℂ} :
    ζ ∈ Ioo x₁ x₂ ×ℂ Ioo y₁ y₂ ↔ x₁ < ζ.re ∧ ζ.re < x₂ ∧ y₁ < ζ.im ∧ ζ.im < y₂ := by
  rw [Complex.mem_reProdIm, mem_Ioo, mem_Ioo]
  tauto

theorem isOpen_rect (x₁ x₂ y₁ y₂ : ℝ) : IsOpen (Ioo x₁ x₂ ×ℂ Ioo y₁ y₂) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

theorem uIcc_subset_Ioo {a b x y : ℝ} (ha : a ∈ Ioo x y) (hb : b ∈ Ioo x y) :
    [[a, b]] ⊆ Ioo x y :=
  ordConnected_Ioo.uIcc_subset ha hb

theorem continuousOn_rect_line {F : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (hF : ContinuousOn F (Ioo x₁ x₂ ×ℂ Ioo y₁ y₂)) {y : ℝ} (hy : y ∈ Ioo y₁ y₂) :
    ContinuousOn (fun s : ℝ => F (s + y * I)) (Ioo x₁ x₂) := by
  refine hF.comp (by fun_prop) fun s hs => ?_
  exact Complex.mem_reProdIm.mpr ⟨by simpa using hs, by simpa using hy⟩

theorem continuousOn_rect_column {F : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (hF : ContinuousOn F (Ioo x₁ x₂ ×ℂ Ioo y₁ y₂)) {x : ℝ} (hx : x ∈ Ioo x₁ x₂) :
    ContinuousOn (fun t : ℝ => F (x + t * I)) (Ioo y₁ y₂) := by
  refine hF.comp (by fun_prop) fun t ht => ?_
  exact Complex.mem_reProdIm.mpr ⟨by simpa using hx, by simpa using ht⟩

/-- The increment of `rectPrimitive` along an L-shaped path, from Cauchy's theorem on the
rectangle. -/
theorem rectPrimitive_sub {F : ℂ → ℂ} {x₁ x₂ y₁ y₂ x₀ y₀ : ℝ}
    (hF : DifferentiableOn ℂ F (Ioo x₁ x₂ ×ℂ Ioo y₁ y₂)) (hx₀ : x₀ ∈ Ioo x₁ x₂)
    (hy₀ : y₀ ∈ Ioo y₁ y₂) {ζ ζ' : ℂ} (hζ : ζ ∈ Ioo x₁ x₂ ×ℂ Ioo y₁ y₂)
    (hζ' : ζ' ∈ Ioo x₁ x₂ ×ℂ Ioo y₁ y₂) :
    rectPrimitive F x₀ y₀ ζ' - rectPrimitive F x₀ y₀ ζ =
      (∫ s in ζ.re..ζ'.re, F (s + ζ.im * I)) + I * ∫ t in ζ.im..ζ'.im, F (ζ'.re + t * I) := by
  obtain ⟨hx1, hx2, hy1, hy2⟩ := mem_rect_iff.mp hζ
  obtain ⟨hx1', hx2', hy1', hy2'⟩ := mem_rect_iff.mp hζ'
  have hFc := hF.continuousOn
  have hline : ∀ y ∈ Ioo y₁ y₂, ∀ a b, a ∈ Ioo x₁ x₂ → b ∈ Ioo x₁ x₂ →
      IntervalIntegrable (fun s : ℝ => F (s + y * I)) volume a b := fun y hy a b ha hb =>
    ((continuousOn_rect_line hFc hy).mono (uIcc_subset_Ioo ha hb)).intervalIntegrable
  have hcol : ∀ x ∈ Ioo x₁ x₂, ∀ a b, a ∈ Ioo y₁ y₂ → b ∈ Ioo y₁ y₂ →
      IntervalIntegrable (fun t : ℝ => F (x + t * I)) volume a b := fun x hx a b ha hb =>
    ((continuousOn_rect_column hFc hx).mono (uIcc_subset_Ioo ha hb)).intervalIntegrable
  -- Cauchy on the rectangle with corners `ζ.re + y₀ i` and `ζ'.re + ζ.im i`
  have hrect : DifferentiableOn ℂ F ([[ζ.re, ζ'.re]] ×ℂ [[y₀, ζ.im]]) := by
    refine hF.mono fun w hw => ?_
    rw [Complex.mem_reProdIm] at hw ⊢
    exact ⟨uIcc_subset_Ioo ⟨hx1, hx2⟩ ⟨hx1', hx2'⟩ hw.1, uIcc_subset_Ioo hy₀ ⟨hy1, hy2⟩ hw.2⟩
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    ((ζ.re : ℂ) + (y₀ : ℂ) * I) ((ζ'.re : ℂ) + (ζ.im : ℂ) * I) (by simpa using hrect)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add, smul_eq_mul] at hc
  unfold rectPrimitive
  have e1 : (∫ s in x₀..ζ'.re, F (s + y₀ * I)) - ∫ s in x₀..ζ.re, F (s + y₀ * I) =
      ∫ s in ζ.re..ζ'.re, F (s + y₀ * I) :=
    intervalIntegral.integral_interval_sub_left (hline y₀ hy₀ _ _ hx₀ ⟨hx1', hx2'⟩)
      (hline y₀ hy₀ _ _ hx₀ ⟨hx1, hx2⟩)
  have e2 : (∫ t in y₀..ζ'.im, F (ζ'.re + t * I)) - ∫ t in y₀..ζ.im, F (ζ'.re + t * I) =
      ∫ t in ζ.im..ζ'.im, F (ζ'.re + t * I) :=
    intervalIntegral.integral_interval_sub_left (hcol _ ⟨hx1', hx2'⟩ _ _ hy₀ ⟨hy1', hy2'⟩)
      (hcol _ ⟨hx1', hx2'⟩ _ _ hy₀ ⟨hy1, hy2⟩)
  linear_combination e1 + I * e2 + hc

/-- A holomorphic function on an open rectangle has a primitive. -/
theorem hasDerivAt_rectPrimitive {F : ℂ → ℂ} {x₁ x₂ y₁ y₂ x₀ y₀ : ℝ}
    (hF : DifferentiableOn ℂ F (Ioo x₁ x₂ ×ℂ Ioo y₁ y₂)) (hx₀ : x₀ ∈ Ioo x₁ x₂)
    (hy₀ : y₀ ∈ Ioo y₁ y₂) {ζ : ℂ} (hζ : ζ ∈ Ioo x₁ x₂ ×ℂ Ioo y₁ y₂) :
    HasDerivAt (rectPrimitive F x₀ y₀) (F ζ) ζ := by
  have hR := isOpen_rect x₁ x₂ y₁ y₂
  have hFc : ContinuousAt F ζ := hF.continuousOn.continuousAt (hR.mem_nhds hζ)
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hε := Metric.continuousAt_iff.mp hFc (c / 2) (by positivity)
  obtain ⟨δ₁, hδ₁, hδ⟩ := hε
  obtain ⟨δ₂, hδ₂, hball⟩ := Metric.isOpen_iff.mp hR ζ hζ
  filter_upwards [Metric.ball_mem_nhds ζ (lt_min (half_pos hδ₁) hδ₂)] with ζ' hζ'
  have hζ'R : ζ' ∈ Ioo x₁ x₂ ×ℂ Ioo y₁ y₂ :=
    hball (Metric.ball_subset_ball (min_le_right _ _) hζ')
  have hdist : ‖ζ' - ζ‖ < δ₁ / 2 := by
    rw [← dist_eq_norm]
    exact lt_of_lt_of_le (Metric.mem_ball.mp hζ') (min_le_left _ _)
  obtain ⟨hx1, hx2, hy1, hy2⟩ := mem_rect_iff.mp hζ
  obtain ⟨hx1', hx2', hy1', hy2'⟩ := mem_rect_iff.mp hζ'R
  rw [rectPrimitive_sub hF hx₀ hy₀ hζ hζ'R]
  have hre : |ζ'.re - ζ.re| ≤ ‖ζ' - ζ‖ := by
    rw [← sub_re]
    exact abs_re_le_norm _
  have him : |ζ'.im - ζ.im| ≤ ‖ζ' - ζ‖ := by
    rw [← sub_im]
    exact abs_im_le_norm _
  -- the two pieces of the L-shaped path, with `F(ζ)` subtracted
  have h1 : ‖(∫ s in ζ.re..ζ'.re, F (s + ζ.im * I)) - (ζ'.re - ζ.re : ℝ) * F ζ‖ ≤
      c / 2 * |ζ'.re - ζ.re| := by
    have : (ζ'.re - ζ.re : ℝ) * F ζ = ∫ s in ζ.re..ζ'.re, F ζ := by
      rw [intervalIntegral.integral_const, Complex.real_smul]
    rw [this, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
      rw [← dist_eq_norm]
      refine (hδ ?_).le
      have hs' : s ∈ uIcc ζ.re ζ'.re := uIoc_subset_uIcc hs
      rw [dist_eq_norm]
      calc ‖(s : ℂ) + ζ.im * I - ζ‖ = |s - ζ.re| := by
            rw [show (s : ℂ) + ζ.im * I - ζ = ((s - ζ.re : ℝ) : ℂ) by
              apply Complex.ext <;> simp]
            rw [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ |ζ'.re - ζ.re| := by
            rw [uIcc_eq_union] at hs'
            have h1 := le_abs_self (ζ'.re - ζ.re)
            have h2 := neg_abs_le (ζ'.re - ζ.re)
            rcases hs' with hs' | hs' <;> rw [abs_le] <;> constructor <;>
              linarith [hs'.1, hs'.2]
        _ ≤ ‖ζ' - ζ‖ := hre
        _ < δ₁ := by linarith
    · exact ((continuousOn_rect_line hF.continuousOn ⟨hy1, hy2⟩).mono
        (uIcc_subset_Ioo ⟨hx1, hx2⟩ ⟨hx1', hx2'⟩)).intervalIntegrable
    · exact intervalIntegrable_const
  have h2 : ‖(∫ t in ζ.im..ζ'.im, F (ζ'.re + t * I)) - (ζ'.im - ζ.im : ℝ) * F ζ‖ ≤
      c / 2 * |ζ'.im - ζ.im| := by
    have : (ζ'.im - ζ.im : ℝ) * F ζ = ∫ t in ζ.im..ζ'.im, F ζ := by
      rw [intervalIntegral.integral_const, Complex.real_smul]
    rw [this, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
      rw [← dist_eq_norm]
      refine (hδ ?_).le
      have ht' : t ∈ uIcc ζ.im ζ'.im := uIoc_subset_uIcc ht
      rw [dist_eq_norm]
      have hpt : (ζ'.re : ℂ) + t * I - ζ = ((ζ'.re - ζ.re : ℝ) : ℂ) + ((t - ζ.im : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp
      calc ‖(ζ'.re : ℂ) + t * I - ζ‖ ≤ |ζ'.re - ζ.re| + |t - ζ.im| := by
            rw [hpt]
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ |ζ'.re - ζ.re| + |ζ'.im - ζ.im| := by
            have h3 : |t - ζ.im| ≤ |ζ'.im - ζ.im| := by
              rw [uIcc_eq_union] at ht'
              have h1 := le_abs_self (ζ'.im - ζ.im)
              have h2 := neg_abs_le (ζ'.im - ζ.im)
              rcases ht' with ht' | ht' <;> rw [abs_le] <;> constructor <;>
                linarith [ht'.1, ht'.2]
            linarith
        _ ≤ ‖ζ' - ζ‖ + ‖ζ' - ζ‖ := add_le_add hre him
        _ = 2 * ‖ζ' - ζ‖ := by ring
        _ < δ₁ := by linarith
    · exact ((continuousOn_rect_column hF.continuousOn ⟨hx1', hx2'⟩).mono
        (uIcc_subset_Ioo ⟨hy1, hy2⟩ ⟨hy1', hy2'⟩)).intervalIntegrable
    · exact intervalIntegrable_const
  have hsplit : (∫ s in ζ.re..ζ'.re, F (s + ζ.im * I)) +
      I * (∫ t in ζ.im..ζ'.im, F (ζ'.re + t * I)) - (ζ' - ζ) • F ζ =
      ((∫ s in ζ.re..ζ'.re, F (s + ζ.im * I)) - (ζ'.re - ζ.re : ℝ) * F ζ) +
        I * ((∫ t in ζ.im..ζ'.im, F (ζ'.re + t * I)) - (ζ'.im - ζ.im : ℝ) * F ζ) := by
    rw [smul_eq_mul]
    have : ζ' - ζ = ((ζ'.re - ζ.re : ℝ) : ℂ) + ((ζ'.im - ζ.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [this]
    ring
  rw [hsplit]
  calc _ ≤ ‖(∫ s in ζ.re..ζ'.re, F (s + ζ.im * I)) - (ζ'.re - ζ.re : ℝ) * F ζ‖ +
        ‖I * ((∫ t in ζ.im..ζ'.im, F (ζ'.re + t * I)) - (ζ'.im - ζ.im : ℝ) * F ζ)‖ :=
        norm_add_le _ _
    _ = ‖(∫ s in ζ.re..ζ'.re, F (s + ζ.im * I)) - (ζ'.re - ζ.re : ℝ) * F ζ‖ +
        ‖(∫ t in ζ.im..ζ'.im, F (ζ'.re + t * I)) - (ζ'.im - ζ.im : ℝ) * F ζ‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ c / 2 * |ζ'.re - ζ.re| + c / 2 * |ζ'.im - ζ.im| := add_le_add h1 h2
    _ ≤ c / 2 * ‖ζ' - ζ‖ + c / 2 * ‖ζ' - ζ‖ := by gcongr
    _ = c * ‖ζ' - ζ‖ := by ring

/-! ### The sector-disc and the logarithmic coordinate -/

/-- The sector-disc `|ph w − ω'| < α`, `|w| < δ₀`. -/
def sectorDisc (ω' α δ₀ : ℝ) : Set ℂ := {w | w ∈ sectorBr ω' α ∧ ‖w‖ < δ₀}

theorem isOpen_sectorDisc {ω' α δ₀ : ℝ} (hα : α ≤ Real.pi) : IsOpen (sectorDisc ω' α δ₀) :=
  (isOpen_sectorBr hα).inter (isOpen_lt continuous_norm continuous_const)

theorem cexp_eq_polar (ζ : ℂ) : cexp ζ = (Real.exp ζ.re : ℂ) * cexp (ζ.im * I) := by
  conv_lhs => rw [← re_add_im ζ]
  rw [Complex.exp_add, ofReal_exp]

theorem cexp_mem_sectorDisc {ω' α δ₀ : ℝ} (hα : α ≤ Real.pi) (hδ₀ : 0 < δ₀) {ζ : ℂ}
    (h1 : ζ.re < Real.log δ₀) (h2 : |ζ.im - ω'| < α) : cexp ζ ∈ sectorDisc ω' α δ₀ := by
  rw [cexp_eq_polar]
  refine ⟨polar_mem_sectorBr (Real.exp_pos _) h2 hα, ?_⟩
  rw [norm_polar (Real.exp_pos _).le, ← Real.exp_log hδ₀]
  exact Real.exp_lt_exp.mpr h1

theorem logBr_mem_rect {ω' α δ₀ m : ℝ} {w : ℂ} (hw : w ∈ sectorDisc ω' α δ₀)
    (hm : m < Real.log ‖w‖) :
    logBr ω' w ∈ Ioo m (Real.log δ₀) ×ℂ Ioo (ω' - α) (ω' + α) := by
  rw [mem_rect_iff, logBr_re w]
  have := abs_lt.mp hw.1.2
  exact ⟨hm, Real.log_lt_log (norm_pos_iff.mpr hw.1.1) hw.2, by linarith, by linarith⟩

theorem polar_mem_rect {ω' α δ₀ m x y : ℝ} (hx1 : m < x) (hx2 : x < Real.log δ₀)
    (hy : |y - ω'| < α) : (x : ℂ) + y * I ∈ Ioo m (Real.log δ₀) ×ℂ Ioo (ω' - α) (ω' + α) := by
  rw [mem_rect_iff]
  have := abs_lt.mp hy
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    add_zero, add_im, mul_im, zero_add]
  exact ⟨hx1, hx2, by linarith, by linarith⟩

/-- `F̃(ζ) = F(e^ζ) e^ζ`, the integrand in the logarithmic coordinate. -/
noncomputable def logIntegrand (F : ℂ → ℂ) (ζ : ℂ) : ℂ := F (cexp ζ) * cexp ζ

theorem differentiableOn_logIntegrand {ω' α δ₀ : ℝ} (hα : α ≤ Real.pi) (hδ₀ : 0 < δ₀)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (sectorDisc ω' α δ₀)) (m : ℝ) :
    DifferentiableOn ℂ (logIntegrand F) (Ioo m (Real.log δ₀) ×ℂ Ioo (ω' - α) (ω' + α)) := by
  intro ζ hζ
  obtain ⟨-, h2, h3, h4⟩ := mem_rect_iff.mp hζ
  have hmem : cexp ζ ∈ sectorDisc ω' α δ₀ :=
    cexp_mem_sectorDisc hα hδ₀ h2 (abs_lt.mpr ⟨by linarith, by linarith⟩)
  have hFd : DifferentiableAt ℂ F (cexp ζ) :=
    hF.differentiableAt ((isOpen_sectorDisc hα).mem_nhds hmem)
  exact ((hFd.comp ζ differentiableAt_id.cexp).mul differentiableAt_id.cexp).differentiableWithinAt

theorem logIntegrand_polar (F : ℂ → ℂ) (x y : ℝ) :
    logIntegrand F ((x : ℂ) + y * I) =
      F ((Real.exp x : ℂ) * cexp (y * I)) * ((Real.exp x : ℂ) * cexp (y * I)) := by
  rw [logIntegrand, Complex.exp_add, ofReal_exp]

theorem hasDerivAt_re_add_mul_I (x : ℝ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => (x : ℂ) + y * I) I y := by
  have := ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (x : ℂ)
  simpa using this

/-! ### The deformation -/

/-- **Deformation onto the ray.** Let `F` be analytic on the sector-disc `|ph w − ω'| < α`,
`|w| < δ₀`, with `|F(w)| ≤ C|w|^{β−1}`, `β > 0`, and let `σ` be a `C¹` curve on `(0, u₁]` in
the sector-disc with `σ(u) → 0` as `u → 0+`. Then, with `r₁ = |σ(u₁)|` and `φ₁ = ph σ(u₁)`,
`∫₀^{u₁} F(σ(u)) σ′(u) du = ∫₀^{r₁} F(re^{iω'}) e^{iω'} dr
  + ∫_{ω'}^{φ₁} F(r₁e^{iy}) i r₁e^{iy} dy`. -/
theorem deform_to_ray {ω' α δ₀ : ℝ} (hα : 0 < α) (hαπ : α ≤ Real.pi) (hδ₀ : 0 < δ₀)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (sectorDisc ω' α δ₀)) {C β : ℝ} (hβ : 0 < β)
    (hbound : ∀ w ∈ sectorDisc ω' α δ₀, ‖F w‖ ≤ C * ‖w‖ ^ (β - 1))
    {σ σ' : ℝ → ℂ} {u₁ : ℝ} (hu₁ : 0 < u₁)
    (hσ : ∀ u ∈ Ioc 0 u₁, HasDerivAt σ (σ' u) u)
    (hσS : ∀ u ∈ Ioc 0 u₁, σ u ∈ sectorDisc ω' α δ₀) (hσ0 : Tendsto σ (𝓝[>] 0) (𝓝 0))
    (hint : IntegrableOn (fun u => F (σ u) * σ' u) (Ioo 0 u₁)) :
    ∫ u in Ioo 0 u₁, F (σ u) * σ' u =
      (∫ r in Ioo 0 ‖σ u₁‖, F (r * cexp (ω' * I)) * cexp (ω' * I)) +
        ∫ y in ω'..(logBr ω' (σ u₁)).im,
          F ((‖σ u₁‖ : ℂ) * cexp (y * I)) * ((‖σ u₁‖ : ℂ) * cexp (y * I) * I) := by
  have hopen := isOpen_sectorDisc (ω' := ω') (δ₀ := δ₀) hαπ
  have hFc : ∀ w ∈ sectorDisc ω' α δ₀, ContinuousAt F w := fun w hw =>
    (hF.differentiableAt (hopen.mem_nhds hw)).continuousAt
  have hC : 0 ≤ C := by
    have h := hbound _ (hσS u₁ ⟨hu₁, le_rfl⟩)
    have hp : 0 < ‖σ u₁‖ ^ (β - 1) :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (hσS u₁ ⟨hu₁, le_rfl⟩).1.1) _
    nlinarith [norm_nonneg (F (σ u₁))]
  set r₁ := ‖σ u₁‖ with hr₁
  set φ₁ := (logBr ω' (σ u₁)).im with hφ₁
  have hr₁0 : 0 < r₁ := norm_pos_iff.mpr (hσS u₁ ⟨hu₁, le_rfl⟩).1.1
  have hr₁δ : r₁ < δ₀ := (hσS u₁ ⟨hu₁, le_rfl⟩).2
  -- the ray integrand `g r = F(r e^{iω'}) e^{iω'}`
  set g : ℝ → ℂ := fun r => F (r * cexp (ω' * I)) * cexp (ω' * I) with hg
  have hray_mem : ∀ r : ℝ, 0 < r → r < δ₀ → (r : ℂ) * cexp (ω' * I) ∈ sectorDisc ω' α δ₀ :=
    fun r hr hrδ => ⟨polar_mem_sectorBr hr (by simpa using hα) hαπ, by
      rw [norm_polar hr.le]; exact hrδ⟩
  have hgc : ContinuousOn g (Ioo 0 δ₀) := fun r hr =>
    ((ContinuousAt.comp (g := F) (f := fun r : ℝ => (r : ℂ) * cexp (ω' * I))
      (hFc _ (hray_mem r hr.1 hr.2)) (by fun_prop)).mul continuousAt_const).continuousWithinAt
  have hgb : ∀ r ∈ Ioo 0 δ₀, ‖g r‖ ≤ C * r ^ (β - 1) := fun r hr => by
    simp only [hg]
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]
    have := hbound _ (hray_mem r hr.1 hr.2)
    rwa [norm_polar hr.1.le] at this
  have hgI : IntegrableOn g (Ioc 0 r₁) := by
    have hp := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := r₁)
      (by linarith : -1 < β - 1)).const_mul C
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr₁0.le] at hp
    refine Integrable.mono' hp
      ((hgc.mono fun r hr => ⟨hr.1, hr.2.trans_lt hr₁δ⟩).aestronglyMeasurable measurableSet_Ioc)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun r hr => ?_))
    exact hgb r ⟨hr.1, hr.2.trans_lt hr₁δ⟩
  -- the identity for a cut `u₀ ∈ (0, u₁)`
  have key : ∀ u₀ ∈ Ioo 0 u₁,
      ∫ u in u₀..u₁, F (σ u) * σ' u =
        (∫ y in ω'..φ₁, F ((r₁ : ℂ) * cexp (y * I)) * ((r₁ : ℂ) * cexp (y * I) * I)) +
          (∫ r in ‖σ u₀‖..r₁, g r) -
          ∫ y in ω'..(logBr ω' (σ u₀)).im, F ((‖σ u₀‖ : ℂ) * cexp (y * I)) *
            ((‖σ u₀‖ : ℂ) * cexp (y * I) * I) := by
    intro u₀ hu₀
    -- a positive lower bound for `|σ|` on `[u₀, u₁]`
    have hσcont : ContinuousOn σ (Icc u₀ u₁) := fun u hu =>
      (hσ u ⟨hu₀.1.trans_le hu.1, hu.2⟩).continuousAt.continuousWithinAt
    obtain ⟨um, hum, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hu₀.2.le)
      (continuous_norm.comp_continuousOn hσcont)
    set ρ₀ := ‖σ um‖ with hρ₀
    have hρ₀0 : 0 < ρ₀ := norm_pos_iff.mpr (hσS um ⟨hu₀.1.trans_le hum.1, hum.2⟩).1.1
    have hρ₀le : ∀ u ∈ Icc u₀ u₁, ρ₀ ≤ ‖σ u‖ := fun u hu => hmin hu
    set m := Real.log ρ₀ - 1 with hm
    have hmδ : m < Real.log δ₀ := by
      have : ρ₀ ≤ r₁ := hρ₀le u₁ ⟨hu₀.2.le, le_rfl⟩
      have := Real.log_le_log hρ₀0 this
      have := Real.log_lt_log hr₁0 hr₁δ
      linarith
    set R := Ioo m (Real.log δ₀) ×ℂ Ioo (ω' - α) (ω' + α) with hR
    have hx₀ : (m + Real.log δ₀) / 2 ∈ Ioo m (Real.log δ₀) := ⟨by linarith, by linarith⟩
    have hy₀ : ω' ∈ Ioo (ω' - α) (ω' + α) := ⟨by linarith, by linarith⟩
    have hFt := differentiableOn_logIntegrand hαπ hδ₀ hF m
    set Φ := rectPrimitive (logIntegrand F) ((m + Real.log δ₀) / 2) ω' with hΦ
    have hΦd : ∀ ζ ∈ R, HasDerivAt Φ (logIntegrand F ζ) ζ := fun ζ hζ =>
      hasDerivAt_rectPrimitive hFt hx₀ hy₀ hζ
    -- the curve `ζ(u) = logBr ω' (σ u)` lies in `R` for `u ∈ [u₀, u₁]`
    have hζmem : ∀ u ∈ Icc u₀ u₁, logBr ω' (σ u) ∈ R := fun u hu => by
      have hS := hσS u ⟨hu₀.1.trans_le hu.1, hu.2⟩
      refine logBr_mem_rect hS ?_
      have := Real.log_le_log hρ₀0 (hρ₀le u hu)
      linarith
    have hζd : ∀ u ∈ Icc u₀ u₁, HasDerivAt (fun u => logBr ω' (σ u)) (σ' u / σ u) u := by
      intro u hu
      have hS := hσS u ⟨hu₀.1.trans_le hu.1, hu.2⟩
      have := (hasDerivAt_logBr (mem_slitPlane_of_mem_sectorBr hαπ hS.1)).comp u
        (hσ u ⟨hu₀.1.trans_le hu.1, hu.2⟩)
      rw [div_eq_inv_mul]
      exact this
    -- (i) the curve piece
    have hcurve : ∫ u in u₀..u₁, F (σ u) * σ' u = Φ (logBr ω' (σ u₁)) - Φ (logBr ω' (σ u₀)) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => Φ (logBr ω' (σ u)))
        (fun u hu => ?_) ?_
      · rw [uIcc_of_le hu₀.2.le] at hu
        have hS := hσS u ⟨hu₀.1.trans_le hu.1, hu.2⟩
        have h := (hΦd _ (hζmem u hu)).comp u (hζd u hu)
        refine h.congr_deriv ?_
        rw [logIntegrand, exp_logBr hS.1.1]
        field_simp [hS.1.1]
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu₀.2.le,
          integrableOn_Ioc_iff_integrableOn_Ioo]
        exact hint.mono_set fun u hu => ⟨hu₀.1.trans hu.1, hu.2⟩
    -- (ii) the ray piece, by the substitution `r = e^x`
    have hray : ∫ r in ‖σ u₀‖..r₁, g r =
        Φ ((Real.log r₁ : ℂ) + ω' * I) - Φ ((Real.log ‖σ u₀‖ : ℂ) + ω' * I) := by
      have hε0 : 0 < ‖σ u₀‖ := norm_pos_iff.mpr (hσS u₀ ⟨hu₀.1, hu₀.2.le⟩).1.1
      have hεδ : ‖σ u₀‖ < δ₀ := (hσS u₀ ⟨hu₀.1, hu₀.2.le⟩).2
      have hερ : ρ₀ ≤ ‖σ u₀‖ := hρ₀le u₀ ⟨le_rfl, hu₀.2.le⟩
      have hr₁ρ : ρ₀ ≤ r₁ := hρ₀le u₁ ⟨hu₀.2.le, le_rfl⟩
      have hxmem : ∀ x ∈ [[Real.log ‖σ u₀‖, Real.log r₁]], (x : ℂ) + ω' * I ∈ R := by
        intro x hx
        rw [uIcc_eq_union] at hx
        have h1 := Real.log_le_log hρ₀0 hερ
        have h2 := Real.log_le_log hρ₀0 hr₁ρ
        have h3 := Real.log_lt_log hε0 hεδ
        have h4 := Real.log_lt_log hr₁0 hr₁δ
        refine polar_mem_rect ?_ ?_ (by simpa using hα) <;>
          rcases hx with hx | hx <;> linarith [hx.1, hx.2]
      have hsub : ∫ x in Real.log ‖σ u₀‖..Real.log r₁, Real.exp x • g (Real.exp x) =
          ∫ r in ‖σ u₀‖..r₁, g r := by
        have h := intervalIntegral.integral_deriv_smul_comp' (a := Real.log ‖σ u₀‖)
          (b := Real.log r₁) (f := Real.exp) (f' := Real.exp) (g := g)
          (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn
          (hgc.mono fun r ⟨x, hx, hxr⟩ => by
            rw [← hxr]
            rw [uIcc_eq_union] at hx
            have h3 := Real.log_lt_log hε0 hεδ
            have h4 := Real.log_lt_log hr₁0 hr₁δ
            refine ⟨Real.exp_pos x, ?_⟩
            rw [← Real.exp_log hδ₀]
            apply Real.exp_lt_exp.mpr
            rcases hx with hx | hx <;> linarith [hx.1, hx.2])
        rwa [Real.exp_log hε0, Real.exp_log hr₁0] at h
      rw [← hsub]
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => Φ (x + ω' * I))
        (fun x hx => ?_) ?_
      · have hl : HasDerivAt (fun x : ℝ => (x : ℂ) + ω' * I) 1 x := by
          simpa using ((hasDerivAt_id x).ofReal_comp).add_const ((ω' : ℂ) * I)
        have h := (hΦd _ (hxmem x hx)).comp x hl
        refine h.congr_deriv ?_
        rw [mul_one, logIntegrand_polar, Complex.real_smul]
        simp only [hg]
        ring
      · exact ((Real.continuous_exp.continuousOn.smul (hgc.comp Real.continuous_exp.continuousOn
          fun x hx => by
            rw [uIcc_eq_union] at hx
            have h3 := Real.log_lt_log hε0 hεδ
            have h4 := Real.log_lt_log hr₁0 hr₁δ
            refine ⟨Real.exp_pos x, ?_⟩
            rw [← Real.exp_log hδ₀]
            apply Real.exp_lt_exp.mpr
            rcases hx with hx | hx <;> linarith [hx.1, hx.2]))).intervalIntegrable
    -- (iii) the vertical pieces at `|w| = |σ u|`
    have hvert : ∀ u ∈ Icc u₀ u₁,
        Φ (logBr ω' (σ u)) - Φ ((Real.log ‖σ u‖ : ℂ) + ω' * I) =
          ∫ y in ω'..(logBr ω' (σ u)).im,
            F ((‖σ u‖ : ℂ) * cexp (y * I)) * ((‖σ u‖ : ℂ) * cexp (y * I) * I) := by
      intro u hu
      have hS := hσS u ⟨hu₀.1.trans_le hu.1, hu.2⟩
      have hr0 : 0 < ‖σ u‖ := norm_pos_iff.mpr hS.1.1
      have hζ : logBr ω' (σ u) = (Real.log ‖σ u‖ : ℂ) + (logBr ω' (σ u)).im * I := by
        conv_lhs => rw [← re_add_im (logBr ω' (σ u))]
        rw [logBr_re _]
      have hφ : |(logBr ω' (σ u)).im - ω'| < α := hS.1.2
      have hlog1 : m < Real.log ‖σ u‖ := by
        have := Real.log_le_log hρ₀0 (hρ₀le u hu)
        linarith
      have hlog2 : Real.log ‖σ u‖ < Real.log δ₀ := Real.log_lt_log hr0 hS.2
      have hymem : ∀ y ∈ [[ω', (logBr ω' (σ u)).im]], (Real.log ‖σ u‖ : ℂ) + y * I ∈ R := by
        intro y hy
        refine polar_mem_rect hlog1 hlog2 ?_
        rw [uIcc_eq_union] at hy
        have h1 := abs_lt.mp hφ
        rcases hy with hy | hy <;> rw [abs_lt] <;> constructor <;> linarith [hy.1, hy.2]
      rw [show Φ (logBr ω' (σ u)) = Φ ((Real.log ‖σ u‖ : ℂ) + (logBr ω' (σ u)).im * I) from
        congrArg Φ hζ]
      symm
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun y : ℝ => Φ ((Real.log ‖σ u‖ : ℂ) + y * I)) (fun y hy => ?_) ?_
      · have h := (hΦd _ (hymem y hy)).comp y (hasDerivAt_re_add_mul_I (Real.log ‖σ u‖) y)
        refine h.congr_deriv ?_
        rw [logIntegrand_polar, Real.exp_log hr0]
        ring
      · refine ContinuousOn.intervalIntegrable ?_
        refine ContinuousOn.mul ?_ (by fun_prop)
        intro y hy
        have hmem : (‖σ u‖ : ℂ) * cexp (y * I) ∈ sectorDisc ω' α δ₀ := by
          refine ⟨polar_mem_sectorBr hr0 ?_ hαπ, by rw [norm_polar hr0.le]; exact hS.2⟩
          rw [uIcc_eq_union] at hy
          have h1 := abs_lt.mp hφ
          rcases hy with hy | hy <;> rw [abs_lt] <;> constructor <;> linarith [hy.1, hy.2]
        exact (ContinuousAt.comp (g := F) (f := fun y : ℝ => (‖σ u‖ : ℂ) * cexp (y * I))
          (hFc _ hmem) (by fun_prop)).continuousWithinAt
    have hv₁ := hvert u₁ ⟨hu₀.2.le, le_rfl⟩
    have hv₀ := hvert u₀ ⟨le_rfl, hu₀.2.le⟩
    rw [hcurve, hray]
    linear_combination hv₁ - hv₀
  -- (iv) the limit `u₀ → 0+`
  set f : ℝ → ℂ := fun u => F (σ u) * σ' u with hf
  have hfI : IntegrableOn f (Icc 0 u₁) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact hint
  have hprim_f : Tendsto (fun u₀ => ∫ u in (0 : ℝ)..u₀, f u) (𝓝[>] 0) (𝓝 0) := by
    have hc := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := u₁)
      (f := f)
      (by rwa [uIcc_of_le hu₁.le])
    have h0 := (hc 0 (left_mem_uIcc)).tendsto
    rw [intervalIntegral.integral_same] at h0
    refine h0.mono_left ?_
    rw [nhdsWithin_le_iff, uIcc_of_le hu₁.le]
    exact mem_of_superset (Ioo_mem_nhdsGT hu₁) Ioo_subset_Icc_self
  have hL : Tendsto (fun u₀ => ∫ u in u₀..u₁, f u) (𝓝[>] 0) (𝓝 (∫ u in Ioo 0 u₁, f u)) := by
    have h1 : ∫ u in Ioo 0 u₁, f u = ∫ u in (0 : ℝ)..u₁, f u := by
      rw [intervalIntegral.integral_of_le hu₁.le,
        integral_Ioc_eq_integral_Ioo (x := (0 : ℝ)) (y := u₁)]
    rw [h1]
    have := (tendsto_const_nhds (x := ∫ u in (0 : ℝ)..u₁, f u)).sub hprim_f
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hu₁] with u₀ hu₀
    rw [intervalIntegral.integral_interval_sub_left]
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu₁.le]
      exact hfI.mono_set Ioc_subset_Icc_self
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu₀.1.le]
      exact hfI.mono_set fun u hu => ⟨hu.1.le, hu.2.trans hu₀.2.le⟩
  -- the ray piece
  have hε : Tendsto (fun u₀ => ‖σ u₀‖) (𝓝[>] 0) (𝓝 0) := by
    have := hσ0.norm
    rwa [norm_zero] at this
  have hεlt : ∀ᶠ u₀ in 𝓝[>] 0, ‖σ u₀‖ < r₁ := hε.eventually (gt_mem_nhds hr₁0)
  have hprim_g : Tendsto (fun u₀ => ∫ r in (0 : ℝ)..‖σ u₀‖, g r) (𝓝[>] 0) (𝓝 0) := by
    have hc := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := r₁)
      (f := g)
      (by rw [uIcc_of_le hr₁0.le, integrableOn_Icc_iff_integrableOn_Ioc]; exact hgI)
    have h0 := (hc 0 (left_mem_uIcc)).tendsto
    rw [intervalIntegral.integral_same] at h0
    refine h0.comp (tendsto_nhdsWithin_iff.mpr ⟨hε, ?_⟩)
    filter_upwards [hεlt] with u₀ hu₀
    rw [uIcc_of_le hr₁0.le]
    exact ⟨norm_nonneg _, hu₀.le⟩
  have hRay : Tendsto (fun u₀ => ∫ r in ‖σ u₀‖..r₁, g r) (𝓝[>] 0)
      (𝓝 (∫ r in Ioo 0 r₁, g r)) := by
    have h1 : ∫ r in Ioo 0 r₁, g r = ∫ r in (0 : ℝ)..r₁, g r := by
      rw [intervalIntegral.integral_of_le hr₁0.le,
        integral_Ioc_eq_integral_Ioo (x := (0 : ℝ)) (y := r₁)]
    rw [h1]
    have := (tendsto_const_nhds (x := ∫ r in (0 : ℝ)..r₁, g r)).sub hprim_g
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [hεlt] with u₀ hu₀
    rw [intervalIntegral.integral_interval_sub_left]
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr₁0.le]
      exact hgI
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (norm_nonneg _)]
      exact hgI.mono_set fun r hr => ⟨hr.1, hr.2.trans hu₀.le⟩
  -- the small arc
  have hArc : Tendsto (fun u₀ => ∫ y in ω'..(logBr ω' (σ u₀)).im,
      F ((‖σ u₀‖ : ℂ) * cexp (y * I)) * ((‖σ u₀‖ : ℂ) * cexp (y * I) * I)) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun u₀ => C * α * ‖σ u₀‖ ^ β) (𝓝[>] 0) (𝓝 0) := by
      have := ((Real.continuous_rpow_const hβ.le).tendsto 0).comp hε
      rw [Real.zero_rpow hβ.ne'] at this
      have := this.const_mul (C * α)
      rwa [mul_zero] at this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Ioo_mem_nhdsGT hu₁] with u₀ hu₀
    have hS := hσS u₀ ⟨hu₀.1, hu₀.2.le⟩
    have hε0 : 0 < ‖σ u₀‖ := norm_pos_iff.mpr hS.1.1
    have hφ : |(logBr ω' (σ u₀)).im - ω'| < α := hS.1.2
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C * ‖σ u₀‖ ^ β)
      fun y hy => ?_).trans ?_
    · have hy' := uIoc_subset_uIcc hy
      have hmem : (‖σ u₀‖ : ℂ) * cexp (y * I) ∈ sectorDisc ω' α δ₀ := by
        refine ⟨polar_mem_sectorBr hε0 ?_ hαπ, by rw [norm_polar hε0.le]; exact hS.2⟩
        rw [uIcc_eq_union] at hy'
        have h1 := abs_lt.mp hφ
        rcases hy' with hy' | hy' <;> rw [abs_lt] <;> constructor <;> linarith [hy'.1, hy'.2]
      have hb := hbound _ hmem
      rw [norm_polar hε0.le] at hb
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_polar hε0.le]
      calc ‖F ((‖σ u₀‖ : ℂ) * cexp (y * I))‖ * ‖σ u₀‖ ≤ C * ‖σ u₀‖ ^ (β - 1) * ‖σ u₀‖ := by
            gcongr
        _ = C * ‖σ u₀‖ ^ β := by
            rw [mul_assoc, ← Real.rpow_add_one hε0.ne', sub_add_cancel]
    · have : |(logBr ω' (σ u₀)).im - ω'| ≤ α := hφ.le
      calc C * ‖σ u₀‖ ^ β * |(logBr ω' (σ u₀)).im - ω'| ≤ C * ‖σ u₀‖ ^ β * α := by
            gcongr
        _ = C * α * ‖σ u₀‖ ^ β := by ring
  -- conclusion
  have hR := ((tendsto_const_nhds (x := ∫ y in ω'..φ₁, F ((r₁ : ℂ) * cexp (y * I)) *
    ((r₁ : ℂ) * cexp (y * I) * I))).add hRay).sub hArc
  rw [sub_zero] at hR
  have hL' := hL.congr' (Eventually.of_forall fun u₀ => rfl)
  have heq : (fun u₀ => ∫ u in u₀..u₁, f u) =ᶠ[𝓝[>] 0] fun u₀ =>
      (∫ y in ω'..φ₁, F ((r₁ : ℂ) * cexp (y * I)) * ((r₁ : ℂ) * cexp (y * I) * I)) +
        (∫ r in ‖σ u₀‖..r₁, g r) - ∫ y in ω'..(logBr ω' (σ u₀)).im,
          F ((‖σ u₀‖ : ℂ) * cexp (y * I)) * ((‖σ u₀‖ : ℂ) * cexp (y * I) * I) := by
    filter_upwards [Ioo_mem_nhdsGT hu₁] with u₀ hu₀
    exact key u₀ hu₀
  have := tendsto_nhds_unique (hL'.congr' heq) hR
  rw [this]
  ring

end Azurite.DLMF
