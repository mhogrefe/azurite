/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section9Psi
import Azurite.DLMF.Chapter5.Section9Barnes

/-!
# DLMF §5.9(ii): equation 5.9.17

Formalization of <https://dlmf.nist.gov/5.9>, equation 5.9.17,
`ψ(z + 1) = −γ + (2πi)⁻¹ ∫_{−c−i∞}^{−c+i∞} π z^{−s−1} ζ(−s)/sin(πs) ds`, `|ph z| ≤ π − δ`,
`1 < c < 2`, for every `z` in the slit plane `|ph z| < π` (`dlmf_5_9_17`); the contour integral is
written with `s = −c + iy`, `ds = i dy`, as in 5.9.11.

It is 5.9.11 differentiated (`digamma_add_eq_deriv`): `∂/∂z z^{−s} = −s z^{−s−1}` under the
integral sign, dominated on a neighbourhood of `z` where `|ph w| ≤ θ < π` and `|w|` is bounded by
`π R^{c−1} ζ(c) e^{θ|y|}/|sin(πs)| ≤ C e^{−(π−θ)|y|}` (`norm_sin_pi_mul_ge`, and
`|ζ(c − iy)| ≤ ∑ n^{−c}`, `norm_riemannZeta_le_tsum`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

theorem norm_riemannZeta_le_tsum {u : ℂ} (hu : 1 < u.re) :
    ‖riemannZeta u‖ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ u.re := by
  rw [zeta_eq_tsum_one_div_nat_cpow hu]
  have hn : ∀ n : ℕ, ‖1 / (n : ℂ) ^ u‖ = 1 / (n : ℝ) ^ u.re := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hu0 : u ≠ 0 := fun h => by rw [h] at hu; simp at hu; linarith
      have hr0 : u.re ≠ 0 := by linarith
      simp [zero_cpow hu0, Real.zero_rpow hr0]
    · rw [norm_div, norm_one, norm_natCast_cpow_of_pos hn]
  have hs : Summable fun n : ℕ => 1 / (n : ℝ) ^ u.re := Real.summable_one_div_nat_rpow.mpr hu
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr hn))
  simpa only [hn] using hs

/-- The Mellin–Barnes integrand `π w^{−s} ζ(−s)/(s sin(πs))` of 5.9.11, `s = −c + iy`. -/
noncomputable def barnesZetaKernel (c : ℝ) (w : ℂ) (y : ℝ) : ℂ :=
  π * w ^ (-(-(c : ℂ) + y * I)) * riemannZeta (-(-(c : ℂ) + y * I)) /
    ((-(c : ℂ) + y * I) * Complex.sin (π * (-(c : ℂ) + y * I)))

/-- The integrand `π w^{−s−1} ζ(−s)/sin(πs)` of 5.9.17, `s = −c + iy`. -/
noncomputable def barnesZetaKernel' (c : ℝ) (w : ℂ) (y : ℝ) : ℂ :=
  π * w ^ (-(-(c : ℂ) + y * I) - 1) * riemannZeta (-(-(c : ℂ) + y * I)) /
    Complex.sin (π * (-(c : ℂ) + y * I))

section Kernel

variable {c : ℝ} (hc1 : 1 < c) (hc2 : c < 2)
include hc1 hc2

theorem barnes_s_ne_zero (y : ℝ) : -(c : ℂ) + y * I ≠ 0 := fun h => by
  have := congrArg re h; simp at this; linarith

theorem barnes_sin_ne_zero (y : ℝ) : Complex.sin (π * (-(c : ℂ) + y * I)) ≠ 0 :=
  sin_pi_mul_ne_zero_of (m := -2) (by simp; linarith) (by simp; linarith)

omit hc2 in
theorem barnes_zeta_arg_ne_one (y : ℝ) : -(-(c : ℂ) + y * I) ≠ 1 := fun h => by
  have := congrArg re h; simp at this; linarith

theorem continuous_barnesZetaKernel {w : ℂ} (hw : w ≠ 0) : Continuous (barnesZetaKernel c w) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have hζ : ContinuousAt (fun y : ℝ => riemannZeta (-(-(c : ℂ) + y * I))) y :=
    (differentiableAt_riemannZeta (barnes_zeta_arg_ne_one hc1 y)).continuousAt.comp
      (f := fun y : ℝ => -(-(c : ℂ) + y * I)) (x := y) (by fun_prop)
  unfold barnesZetaKernel
  exact ((continuousAt_const.mul ((Continuous.const_cpow (by fun_prop) (Or.inl hw)).continuousAt
    (x := y))).mul hζ).div (by fun_prop)
    (mul_ne_zero (barnes_s_ne_zero hc1 hc2 y) (barnes_sin_ne_zero hc1 hc2 y))

theorem continuous_barnesZetaKernel' {w : ℂ} (hw : w ≠ 0) :
    Continuous (barnesZetaKernel' c w) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have hζ : ContinuousAt (fun y : ℝ => riemannZeta (-(-(c : ℂ) + y * I))) y :=
    (differentiableAt_riemannZeta (barnes_zeta_arg_ne_one hc1 y)).continuousAt.comp
      (f := fun y : ℝ => -(-(c : ℂ) + y * I)) (x := y) (by fun_prop)
  unfold barnesZetaKernel'
  exact ((continuousAt_const.mul ((Continuous.const_cpow (by fun_prop) (Or.inl hw)).continuousAt
    (x := y))).mul hζ).div (by fun_prop) (barnes_sin_ne_zero hc1 hc2 y)

theorem hasDerivAt_barnesZetaKernel {w : ℂ} (hw : w ∈ slitPlane) (y : ℝ) :
    HasDerivAt (fun w => barnesZetaKernel c w y) (-barnesZetaKernel' c w y) w := by
  have h := (hasDerivAt_id w).cpow_const (c := -(-(c : ℂ) + y * I)) hw
  have h2 := ((h.const_mul (π : ℂ)).mul_const (riemannZeta (-(-(c : ℂ) + y * I)))).div_const
    ((-(c : ℂ) + y * I) * Complex.sin (π * (-(c : ℂ) + y * I)))
  refine h2.congr_deriv ?_
  have hs := barnes_s_ne_zero hc1 hc2 y
  have hsin := barnes_sin_ne_zero hc1 hc2 y
  simp only [id, mul_one, barnesZetaKernel']
  field_simp

theorem norm_barnesZetaKernel'_le {w : ℂ} (hw : w ≠ 0) {R θ : ℝ} (hR : ‖w‖ ≤ R)
    (hθ : |arg w| ≤ θ) (y : ℝ) :
    ‖barnesZetaKernel' c w y‖ ≤ π * R ^ (c - 1) * (∑' n : ℕ, 1 / (n : ℝ) ^ c) /
      (min |Real.sin (π * -c)| 1 / 4) * Real.exp (-((π - θ) * |y|)) := by
  have hsinσ : Real.sin (π * -c) ≠ 0 := by
    have := barnes_sin_ne_zero hc1 hc2 0
    simp only [ofReal_zero, zero_mul, add_zero] at this
    rwa [← ofReal_neg, ← ofReal_mul, ← ofReal_sin, ofReal_ne_zero] at this
  set m := min |Real.sin (π * -c)| 1 / 4 with hm
  have hm0 : 0 < m := by rw [hm]; have := abs_pos.mpr hsinσ; positivity
  have hS := norm_sin_pi_mul_ge (σ := -c) y
  rw [show ((-c : ℝ) : ℂ) + y * I = -(c : ℂ) + y * I by push_cast; ring] at hS
  have hZ : ‖riemannZeta (-(-(c : ℂ) + y * I))‖ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ c := by
    have hre : (-(-(c : ℂ) + y * I)).re = c := by simp
    have := norm_riemannZeta_le_tsum (u := -(-(c : ℂ) + y * I)) (by rw [hre]; linarith)
    rwa [hre] at this
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have hRp : 0 ≤ R ^ (c - 1) := Real.rpow_nonneg hR0 _
  have hpow : ‖w ^ (-(-(c : ℂ) + y * I) - 1)‖ ≤ R ^ (c - 1) * Real.exp (θ * |y|) := by
    rw [norm_cpow_of_ne_zero hw]
    have hre : (-(-(c : ℂ) + y * I) - 1).re = c - 1 := by simp
    have him : (-(-(c : ℂ) + y * I) - 1).im = -y := by simp
    rw [hre, him, div_eq_mul_inv, ← Real.exp_neg]
    have h1 : ‖w‖ ^ (c - 1) ≤ R ^ (c - 1) := Real.rpow_le_rpow (norm_nonneg _) hR (by linarith)
    have h2 : Real.exp (-(arg w * -y)) ≤ Real.exp (θ * |y|) := by
      refine Real.exp_le_exp.mpr ?_
      calc -(arg w * -y) = arg w * y := by ring
        _ ≤ |arg w * y| := le_abs_self _
        _ = |arg w| * |y| := abs_mul _ _
        _ ≤ θ * |y| := by gcongr
    exact mul_le_mul h1 h2 (Real.exp_pos _).le hRp
  have hZ0 : 0 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ c := tsum_nonneg fun n => by positivity
  have hsin0 : 0 < ‖Complex.sin (π * (-(c : ℂ) + y * I))‖ :=
    norm_pos_iff.mpr (barnes_sin_ne_zero hc1 hc2 y)
  rw [barnesZetaKernel', norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, div_le_iff₀ hsin0]
  have he : Real.exp (-((π - θ) * |y|)) * Real.exp (π * |y|) = Real.exp (θ * |y|) := by
    rw [← Real.exp_add]; ring_nf
  have hπ := Real.pi_pos
  calc π * ‖w ^ (-(-(c : ℂ) + y * I) - 1)‖ * ‖riemannZeta (-(-(c : ℂ) + y * I))‖
      ≤ π * (R ^ (c - 1) * Real.exp (θ * |y|)) * (∑' n : ℕ, 1 / (n : ℝ) ^ c) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow hπ.le) hZ (norm_nonneg _)
          (mul_nonneg hπ.le (mul_nonneg hRp (Real.exp_pos _).le))
    _ = π * R ^ (c - 1) * (∑' n : ℕ, 1 / (n : ℝ) ^ c) / m * Real.exp (-((π - θ) * |y|)) *
        (m * Real.exp (π * |y|)) := by rw [← he]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hS (mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg hπ.le
        hRp) hZ0) hm0.le) (Real.exp_pos _).le)

end Kernel

/-- **DLMF 5.9.17**: for `|ph z| < π` and `1 < c < 2`,
`ψ(z + 1) = −γ + (2πi)⁻¹ ∫_{−c−i∞}^{−c+i∞} π z^{−s−1} ζ(−s)/sin(πs) ds`, the contour integral
written with `s = −c + iy`, `ds = i dy`. -/
theorem dlmf_5_9_17 {z : ℂ} (hz : z ∈ slitPlane) {c : ℝ} (hc1 : 1 < c) (hc2 : c < 2) :
    digamma (z + 1) = -γ + 1 / (2 * π * I) * (I * ∫ y : ℝ,
      π * z ^ (-(-(c : ℂ) + y * I) - 1) * riemannZeta (-(-(c : ℂ) + y * I)) /
        Complex.sin (π * (-(c : ℂ) + y * I))) := by
  have hz0 := slitPlane_ne_zero hz
  have hargz : |arg z| < π := abs_lt.mpr ⟨by linarith [neg_pi_lt_arg z],
    lt_of_le_of_ne (arg_le_pi z) (slitPlane_arg_ne_pi hz)⟩
  set θ := (|arg z| + π) / 2 with hθ
  have hθπ : θ < π := by rw [hθ]; linarith
  set R := ‖z‖ + 1 with hR
  set S : Set ℂ := {w | w ∈ slitPlane ∧ |arg w| < θ ∧ ‖w‖ < R} with hSdef
  have hS : S ∈ 𝓝 z := by
    have h1 : ∀ᶠ w in 𝓝 z, |arg w| < θ :=
      (continuous_abs.continuousAt.comp (continuousAt_arg hz)).eventually
        (gt_mem_nhds (show (abs ∘ arg) z < θ by simp only [Function.comp]; rw [hθ]; linarith))
    have h2 : ∀ᶠ w in 𝓝 z, ‖w‖ < R :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds (by rw [hR]; linarith))
    have h0 : ∀ᶠ w in 𝓝 z, w ∈ slitPlane := isOpen_slitPlane.mem_nhds hz
    exact h0.and (h1.and h2)
  set m := min |Real.sin (π * -c)| 1 / 4 with hm
  set C := π * R ^ (c - 1) * (∑' n : ℕ, 1 / (n : ℝ) ^ c) / m with hC
  have hbound : Integrable fun y : ℝ => C * Real.exp (-((π - θ) * |y|)) :=
    (integrable_exp_neg_abs (by linarith)).const_mul C
  -- `∫ K(z, ·)` is integrable: it is `barnesKernel z (−c) · ζ(−s)`
  have hKint : Integrable (barnesZetaKernel c z) := by
    refine ((integrable_barnesKernel hz (σ := -c) (by linarith) (by linarith)).norm.mul_const
      (∑' n : ℕ, 1 / (n : ℝ) ^ c)).mono'
      (continuous_barnesZetaKernel hc1 hc2 hz0).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    have e : barnesZetaKernel c z y =
        barnesKernel z (-c) y * riemannZeta (-(-(c : ℂ) + y * I)) := by
      simp only [barnesZetaKernel, barnesKernel]
      push_cast
      ring
    rw [e, norm_mul]
    have hre : (-(-(c : ℂ) + y * I)).re = c := by simp
    have := norm_riemannZeta_le_tsum (u := -(-(c : ℂ) + y * I)) (by rw [hre]; linarith)
    rw [hre] at this
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun w y => barnesZetaKernel c w y) (F' := fun w y => -barnesZetaKernel' c w y)
    (x₀ := z) (bound := fun y => C * Real.exp (-((π - θ) * |y|))) hS
    (eventually_of_mem hS fun w hw =>
      (continuous_barnesZetaKernel hc1 hc2 (slitPlane_ne_zero hw.1)).aestronglyMeasurable)
    hKint
    (continuous_barnesZetaKernel' hc1 hc2 hz0).aestronglyMeasurable.neg
    (ae_of_all _ fun y w hw => by
      rw [norm_neg]
      exact norm_barnesZetaKernel'_le hc1 hc2 (slitPlane_ne_zero hw.1) hw.2.2.le hw.2.1.le y)
    hbound
    (ae_of_all _ fun y w hw => hasDerivAt_barnesZetaKernel hc1 hc2 hw.1 y)
  set E : ℂ → ℂ := fun w => -(γ * w) - 1 / (2 * π * I) * (I * ∫ y : ℝ, barnesZetaKernel c w y)
    with hE
  have hD : HasDerivAt E (-(γ : ℂ) - 1 / (2 * π * I) * (I * ∫ y : ℝ, -barnesZetaKernel' c z y))
      z := by
    have := (((hasDerivAt_id z).const_mul (γ : ℂ)).neg).sub
      ((key.2.const_mul I).const_mul (1 / (2 * π * I)))
    refine this.congr_deriv ?_
    simp
  have hdig := digamma_add_eq_deriv (a := 1) isOpen_slitPlane hz hD.differentiableAt
    (fun w hw => dlmf_5_9_11 hw hc1 hc2)
  rw [hdig, hD.deriv, integral_neg]
  simp only [barnesZetaKernel']
  ring

end Azurite.DLMF
