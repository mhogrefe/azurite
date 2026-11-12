/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11BoydRotate
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# DLMF 5.11.11: the `2K^{1/2}` branch

Formalization of <https://dlmf.nist.gov/5.11.E11> (Boyd 1994) for `K ≥ 3`:
`|R_K(z)| ≤ (1 + ζ(K)) Γ(K)/(2 (2π)^{K+1} |z|^K) · (1 + min(sec(ph z), 2K^{1/2}))`,
`|ph z| ≤ ½π` (`dlmf_5_11_11`; on the imaginary axis only the `2K^{1/2}` branch,
`dlmf_5_11_11_closed`). The proof is G. Nemes's (arXiv:1310.0166, Theorem 1.3; Boyd gives no
proof of this branch).

For `0 ≤ ph z < ½π`, rotate the path of the first integral of Boyd's representation
(`boydRem`) to the ray `ph s = ϑ`, `0 < ϑ ≤ π/4` (`integral_Ioi_rotate`; on the sector
`|Γ*(is)| ≤ (1 − e^{−2π|s| cos ϑ})⁻¹` by `norm_scaledGamma_le_of_quadrant`). On that ray
`|1 − ise^{iϑ}/z| ≥ sin ϑ` and the integral is at most `(sin ϑ cos^K ϑ)⁻¹ Γ(K) ζ(K)/(2π)^K`
(`norm_integral_boydF_rot_le`); the second integral is at most `J_K` as before. With
`ϑ = arctan K^{−1/2}`, `(sin ϑ cos^K ϑ)⁻¹ = K^{1/2} (1 + 1/K)^{(K+1)/2}`, and
`ζ(K)(1 + 1/K)^{(K+1)/2} ≤ 1 + ζ(K)` for `K ≥ 3` (`zeta_mul_le`: `ζ(3) ≤ 5/4` by telescoping,
`ζ(K) ≤ ζ(4) = π⁴/90` and `(1 + 1/K)^{(K+1)/2} ≤ e^{5/8} < 1.9` for `K ≥ 4`). For `ph z < 0`
use `R_K(z̄) = conj R_K(z)`; the imaginary axis follows by continuity.

`K = 2` (Nemes uses a numerically evaluated integral) and `K = 1` (unproved in the literature,
per Nemes) are not covered for this branch; the `sec` branch holds for all `K ≥ 1`
(`dlmf_5_11_11_sec`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Nat ComplexConjugate

namespace Azurite.DLMF

/-! ### Polar coordinates -/

theorem polar_re (r ψ : ℝ) : ((r : ℂ) * cexp (ψ * I)).re = r * Real.cos ψ := by
  rw [re_ofReal_mul, exp_ofReal_mul_I_re]

theorem polar_mul_I_re (r ψ : ℝ) : ((r : ℂ) * cexp (ψ * I) * I).re = -(r * Real.sin ψ) := by
  rw [mul_I_re, im_ofReal_mul, exp_ofReal_mul_I_im]

theorem polar_mul_I_im (r ψ : ℝ) : ((r : ℂ) * cexp (ψ * I) * I).im = r * Real.cos ψ := by
  rw [mul_I_im, polar_re]

theorem norm_polar' {r : ℝ} (hr : 0 ≤ r) (ψ : ℝ) : ‖(r : ℂ) * cexp (ψ * I)‖ = r := by
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hr]

theorem differentiableAt_scaledGamma {w : ℂ} (hw : w.im ≠ 0) :
    DifferentiableAt ℂ scaledGamma w := by
  have hslit : w ∈ slitPlane := by rw [mem_slitPlane_iff]; right; exact hw
  have hpole : ∀ m : ℕ, w ≠ -m := fun m h => hw (by rw [h]; simp)
  have h0 : w ≠ 0 := slitPlane_ne_zero hslit
  have hs : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hden : ((Real.sqrt (2 * π) : ℝ) : ℂ) * cexp (-w) * w ^ (w - 1 / 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hs.ne') (Complex.exp_ne_zero _))
      (by rw [Ne, cpow_eq_zero_iff]; tauto)
  unfold scaledGamma
  refine (differentiableAt_Gamma _ hpole).div ?_ hden
  exact ((differentiableAt_const _).mul (Complex.differentiable_exp.differentiableAt.comp _
    differentiableAt_id.neg)).mul (differentiableAt_id.cpow (differentiableAt_id.sub
    (differentiableAt_const _)) hslit)

/-- `|1 − re^{iψ} i/z| ≥ (ℜz cos ψ + ℑz sin ψ)/|z|`: project `z − re^{iψ}i` on `e^{iψ}`. -/
theorem rot_denom_ge {z : ℂ} (hz0 : z ≠ 0) (r ψ : ℝ) :
    (z.re * Real.cos ψ + z.im * Real.sin ψ) / ‖z‖ ≤
      ‖1 - (r : ℂ) * cexp (ψ * I) * I / z‖ := by
  have he : cexp (ψ * I) * cexp (((-ψ : ℝ) : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]; push_cast; simp
  have hid : (z - (r : ℂ) * cexp (ψ * I) * I) * cexp (((-ψ : ℝ) : ℂ) * I) =
      z * cexp (((-ψ : ℝ) : ℂ) * I) - r * I := by
    linear_combination (-(r : ℂ) * I) * he
  have hre : ((z - (r : ℂ) * cexp (ψ * I) * I) * cexp (((-ψ : ℝ) : ℂ) * I)).re =
      z.re * Real.cos ψ + z.im * Real.sin ψ := by
    rw [hid, sub_re, mul_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, Real.cos_neg,
      Real.sin_neg]
    simp
  rw [show 1 - (r : ℂ) * cexp (ψ * I) * I / z = (z - r * cexp (ψ * I) * I) / z by field_simp,
    norm_div]
  gcongr
  calc z.re * Real.cos ψ + z.im * Real.sin ψ
      = ((z - (r : ℂ) * cexp (ψ * I) * I) * cexp (((-ψ : ℝ) : ℂ) * I)).re := hre.symm
    _ ≤ ‖(z - (r : ℂ) * cexp (ψ * I) * I) * cexp (((-ψ : ℝ) : ℂ) * I)‖ := re_le_norm _
    _ = ‖z - (r : ℂ) * cexp (ψ * I) * I‖ := by rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]

/-! ### The continued integrand -/

/-- `s ↦ sⁿ e^{−2πs} Γ*(is)/(1 − is/z)`, the first integrand of Boyd's remainder. -/
noncomputable def boydF (n : ℕ) (z s : ℂ) : ℂ :=
  s ^ n * (cexp (-(2 * π * s)) * scaledGamma (s * I)) / (1 - s * I / z)

section Sector

variable {z : ℂ} {ϑ : ℝ}

theorem cos_le_cos_of_mem {ϑ ψ : ℝ} (hϑ2 : ϑ < π / 2) (hψ : ψ ∈ Icc 0 ϑ) :
    Real.cos ϑ ≤ Real.cos ψ :=
  Real.cos_le_cos_of_nonneg_of_le_pi hψ.1 (by linarith [Real.pi_pos]) hψ.2

theorem cos_pos_of_lt {ϑ : ℝ} (hϑ0 : 0 ≤ ϑ) (hϑ2 : ϑ < π / 2) : 0 < Real.cos ϑ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hϑ2⟩

/-- The denominator on the sector `0 ≤ ψ ≤ ϑ`, for `ℜz > 0`, `ℑz ≥ 0`. -/
theorem rot_denom_ge_sector (hz : 0 < z.re) (him : 0 ≤ z.im) (hϑ2 : ϑ < π / 2) {ψ : ℝ}
    (hψ : ψ ∈ Icc 0 ϑ) (r : ℝ) :
    z.re * Real.cos ϑ / ‖z‖ ≤ ‖1 - (r : ℂ) * cexp (ψ * I) * I / z‖ := by
  have hz0 := ne_zero_of_pos_re hz
  refine le_trans ?_ (rot_denom_ge hz0 r ψ)
  gcongr
  have hs : 0 ≤ Real.sin ψ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hψ.1 (by linarith [hψ.2, Real.pi_pos])
  nlinarith [cos_le_cos_of_mem hϑ2 hψ, mul_nonneg him hs]

theorem norm_boydF_le (hz : 0 < z.re) (him : 0 ≤ z.im) (hϑ0 : 0 ≤ ϑ) (hϑ2 : ϑ < π / 2)
    (n : ℕ) {r ψ : ℝ} (hr : 0 < r) (hψ : ψ ∈ Icc 0 ϑ) :
    ‖boydF n z ((r : ℂ) * cexp (ψ * I))‖ ≤ r ^ n * (Real.exp (-(2 * π * (r * Real.cos ϑ))) *
      (1 - Real.exp (-(2 * π * (r * Real.cos ϑ))))⁻¹) * (‖z‖ / (z.re * Real.cos ϑ)) := by
  have hz0 := ne_zero_of_pos_re hz
  have hcϑ := cos_pos_of_lt hϑ0 hϑ2
  have hcψ := cos_le_cos_of_mem hϑ2 hψ
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hd := rot_denom_ge_sector hz him hϑ2 hψ r
  have hdpos : 0 < z.re * Real.cos ϑ / ‖z‖ := by positivity
  have hrc : 0 < r * Real.cos ϑ := by positivity
  set s := (r : ℂ) * cexp (ψ * I)
  -- `|e^{−2πs}|`
  have h1 : ‖cexp (-(2 * π * s))‖ ≤ Real.exp (-(2 * π * (r * Real.cos ϑ))) := by
    rw [norm_exp]
    gcongr
    have : (-(2 * π * s)).re = -(2 * π * (r * Real.cos ψ)) := by
      rw [neg_re, show (2 * π * s) = ((2 * π : ℝ) : ℂ) * s by push_cast; ring, re_ofReal_mul,
        polar_re]
    rw [this]
    have h' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcψ hr.le)
      (by positivity : (0 : ℝ) ≤ 2 * π)
    linarith
  -- `|Γ*(is)|`
  have h2 : ‖scaledGamma (s * I)‖ ≤ (1 - Real.exp (-(2 * π * (r * Real.cos ϑ))))⁻¹ := by
    have hre : (s * I).re ≤ 0 := by
      rw [polar_mul_I_re]
      have : 0 ≤ Real.sin ψ :=
        Real.sin_nonneg_of_nonneg_of_le_pi hψ.1 (by linarith [hψ.2, Real.pi_pos])
      nlinarith
    have him' : 0 < (s * I).im := by rw [polar_mul_I_im]; nlinarith
    refine (norm_scaledGamma_le_of_quadrant hre him').trans ?_
    rw [polar_mul_I_im]
    have hp1 := one_sub_exp_pos hrc
    have h' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcψ hr.le)
      (by positivity : (0 : ℝ) ≤ 2 * π)
    gcongr
  -- the denominator
  have h3 : ‖(1 - s * I / z)⁻¹‖ ≤ ‖z‖ / (z.re * Real.cos ϑ) := by
    rw [norm_inv]
    calc ‖1 - s * I / z‖⁻¹ ≤ (z.re * Real.cos ϑ / ‖z‖)⁻¹ := inv_anti₀ hdpos hd
      _ = ‖z‖ / (z.re * Real.cos ϑ) := inv_div _ _
  have hsn : ‖s ^ n‖ = r ^ n := by rw [norm_pow, norm_polar' hr.le]
  rw [boydF, div_eq_mul_inv, norm_mul, norm_mul, norm_mul, hsn]
  have hE := (Real.exp_pos (-(2 * π * (r * Real.cos ϑ)))).le
  have hI := (inv_pos.mpr (one_sub_exp_pos hrc)).le
  gcongr

theorem pow_pred_le_one_add {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    r ^ (n - 1) ≤ 1 + r ^ n := by
  rcases le_total r 1 with h | h
  · linarith [pow_le_one₀ hr h (n := n - 1), pow_nonneg hr n]
  · linarith [pow_le_pow_right₀ h (Nat.sub_le n 1), zero_le_one (α := ℝ)]

/-- The hypotheses of `integral_Ioi_rotate` for `boydF`. -/
theorem boydF_rotate (hz : 0 < z.re) (him : 0 ≤ z.im) (hϑ0 : 0 ≤ ϑ) (hϑ2 : ϑ < π / 2)
    {n : ℕ} (hn : 1 ≤ n) :
    ∫ r in Ioi (0 : ℝ), boydF n z r =
      cexp (ϑ * I) * ∫ r in Ioi (0 : ℝ), boydF n z (r * cexp (ϑ * I)) := by
  have hz0 := ne_zero_of_pos_re hz
  have hcϑ := cos_pos_of_lt hϑ0 hϑ2
  have hn' : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set c := 2 * π * Real.cos ϑ with hc
  have hc0 : 0 < c := by positivity
  refine integral_Ioi_rotate (C := (1 + 1 / c) * (‖z‖ / (z.re * Real.cos ϑ))) (c := c) (p := n)
    hϑ0 (fun r ψ hr hψ => ?_) hc0 (fun r ψ hr hψ => ?_)
  · -- differentiability
    have him' : ((r : ℂ) * cexp (ψ * I) * I).im ≠ 0 := by
      rw [polar_mul_I_im]
      exact (mul_pos hr (lt_of_lt_of_le hcϑ (cos_le_cos_of_mem hϑ2 hψ))).ne'
    have hden : 1 - (r : ℂ) * cexp (ψ * I) * I / z ≠ 0 := by
      intro h0
      have := rot_denom_ge_sector hz him hϑ2 hψ r
      rw [h0, norm_zero] at this
      exact absurd this (not_le.mpr (by positivity))
    have hG : DifferentiableAt ℂ (fun s : ℂ => scaledGamma (s * I)) ((r : ℂ) * cexp (ψ * I)) :=
      (differentiableAt_scaledGamma him').comp (𝕜 := ℂ) ((r : ℂ) * cexp (ψ * I))
        (f := fun s : ℂ => s * I) (by fun_prop)
    unfold boydF
    exact ((differentiableAt_id.pow n).mul ((Complex.differentiable_exp.differentiableAt.comp _
      (differentiableAt_id.const_mul _).neg).mul hG)).div
      ((differentiableAt_const _).sub ((differentiableAt_id.mul_const I).div_const z)) hden
  · -- the bound
    refine (norm_boydF_le hz him hϑ0 hϑ2 n hr hψ).trans ?_
    have hrc : 0 < r * Real.cos ϑ := by positivity
    have hinv := inv_one_sub_exp_le (x := 2 * π * (r * Real.cos ϑ)) (by positivity)
    have hS : 0 ≤ ‖z‖ / (z.re * Real.cos ϑ) := by positivity
    have he : Real.exp (-(2 * π * (r * Real.cos ϑ))) = Real.exp (-(c * r)) := by
      rw [hc]; ring_nf
    rw [he]
    have hE := (Real.exp_pos (-(c * r))).le
    have hkey : r ^ n * (1 + 1 / (2 * π * (r * Real.cos ϑ))) ≤ (1 + 1 / c) * (1 + r ^ n) := by
      have hpow : r ^ n = r ^ (n - 1) * r := by rw [← pow_succ, Nat.sub_add_cancel hn]
      have h1 : r ^ n * (1 / (2 * π * (r * Real.cos ϑ))) = r ^ (n - 1) / c := by
        rw [hpow, hc]; field_simp
      rw [mul_add, mul_one, h1]
      have := pow_pred_le_one_add (n := n) hr.le
      have h2 : r ^ (n - 1) / c ≤ (1 + r ^ n) / c := by gcongr
      have h3 : (1 + 1 / c) * (1 + r ^ n) = (1 + r ^ n) + (1 + r ^ n) / c := by ring
      linarith
    calc r ^ n * (Real.exp (-(c * r)) * (1 - Real.exp (-(c * r)))⁻¹) *
          (‖z‖ / (z.re * Real.cos ϑ))
        = (r ^ n * (1 - Real.exp (-(2 * π * (r * Real.cos ϑ))))⁻¹) * Real.exp (-(c * r)) *
          (‖z‖ / (z.re * Real.cos ϑ)) := by rw [← he]; ring
      _ ≤ (r ^ n * (1 + 1 / (2 * π * (r * Real.cos ϑ)))) * Real.exp (-(c * r)) *
          (‖z‖ / (z.re * Real.cos ϑ)) := by gcongr
      _ ≤ ((1 + 1 / c) * (1 + r ^ n)) * Real.exp (-(c * r)) *
          (‖z‖ / (z.re * Real.cos ϑ)) := by gcongr
      _ = (1 + 1 / c) * (‖z‖ / (z.re * Real.cos ϑ)) * ((1 + r ^ n) * Real.exp (-(c * r))) := by
          ring

/-- On the rotated ray, `|boydF(re^{iϑ})| ≤ (sin ϑ)⁻¹ (cos ϑ)^{−n} · tⁿe^{−2πt}/(1 − e^{−2πt})`
at `t = r cos ϑ`, when `sin ϑ ≤ cos ϑ`. -/
theorem norm_boydF_rot_le (hz : 0 < z.re) (him : 0 ≤ z.im) (hϑ0 : 0 < ϑ) (hϑ2 : ϑ < π / 2)
    (hsc : Real.sin ϑ ≤ Real.cos ϑ) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ‖boydF n z ((r : ℂ) * cexp (ϑ * I))‖ ≤
      (Real.sin ϑ)⁻¹ * (Real.cos ϑ ^ n)⁻¹ * zetaIntegrand n (Real.cos ϑ * r) := by
  have hz0 := ne_zero_of_pos_re hz
  have hcϑ := cos_pos_of_lt hϑ0.le hϑ2
  have hsϑ : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ0 (by linarith [Real.pi_pos])
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hrc : 0 < r * Real.cos ϑ := by positivity
  set s := (r : ℂ) * cexp (ϑ * I)
  have hd : Real.sin ϑ ≤ ‖1 - s * I / z‖ := by
    refine le_trans ?_ (rot_denom_ge hz0 r ϑ)
    rw [le_div_iff₀ hn]
    have hnorm := norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hz, abs_of_nonneg him] at hnorm
    nlinarith
  have h1 : ‖cexp (-(2 * π * s))‖ = Real.exp (-(2 * π * (r * Real.cos ϑ))) := by
    rw [norm_exp]
    congr 1
    rw [neg_re, show (2 * π * s) = ((2 * π : ℝ) : ℂ) * s by push_cast; ring, re_ofReal_mul,
      polar_re]
  have h2 : ‖scaledGamma (s * I)‖ ≤ (1 - Real.exp (-(2 * π * (r * Real.cos ϑ))))⁻¹ := by
    have hre : (s * I).re ≤ 0 := by rw [polar_mul_I_re]; nlinarith
    have him' : 0 < (s * I).im := by rw [polar_mul_I_im]; exact hrc
    refine (norm_scaledGamma_le_of_quadrant hre him').trans (le_of_eq ?_)
    rw [polar_mul_I_im]
  have h3 : ‖(1 - s * I / z)⁻¹‖ ≤ (Real.sin ϑ)⁻¹ := by
    rw [norm_inv]; exact inv_anti₀ hsϑ hd
  have hsn : ‖s ^ n‖ = r ^ n := by rw [norm_pow, norm_polar' hr.le]
  rw [boydF, div_eq_mul_inv, norm_mul, norm_mul, norm_mul, hsn, h1]
  have hzeta : r ^ n * (Real.exp (-(2 * π * (r * Real.cos ϑ))) *
      (1 - Real.exp (-(2 * π * (r * Real.cos ϑ))))⁻¹) =
      (Real.cos ϑ ^ n)⁻¹ * zetaIntegrand n (Real.cos ϑ * r) := by
    rw [zetaIntegrand, mul_pow, mul_comm (Real.cos ϑ) r, div_eq_mul_inv]
    field_simp
  have hE := (Real.exp_pos (-(2 * π * (r * Real.cos ϑ)))).le
  calc r ^ n * (Real.exp (-(2 * π * (r * Real.cos ϑ))) * ‖scaledGamma (s * I)‖) *
        ‖(1 - s * I / z)⁻¹‖
      ≤ r ^ n * (Real.exp (-(2 * π * (r * Real.cos ϑ))) *
          (1 - Real.exp (-(2 * π * (r * Real.cos ϑ))))⁻¹) * (Real.sin ϑ)⁻¹ := by
        have hI := (inv_pos.mpr (one_sub_exp_pos hrc)).le
        have hpos : 0 ≤ r ^ n * (Real.exp (-(2 * π * (r * Real.cos ϑ))) *
            (1 - Real.exp (-(2 * π * (r * Real.cos ϑ))))⁻¹) := by positivity
        gcongr
    _ = _ := by rw [hzeta]; ring

/-- The rotated first integral: `|∫₀^∞ boydF(re^{iϑ}) dr| ≤
(sin ϑ)⁻¹ (cos ϑ)^{−(n+1)} (n+1)! ζ(n+2)/(2π)^{n+2}` for `n ≥ 1` written as `j + 1`. -/
theorem norm_integral_boydF_rot_le (hz : 0 < z.re) (him : 0 ≤ z.im) (hϑ0 : 0 < ϑ)
    (hϑ2 : ϑ < π / 2) (hsc : Real.sin ϑ ≤ Real.cos ϑ) (j : ℕ) :
    ‖∫ r in Ioi (0 : ℝ), boydF (j + 1) z (r * cexp (ϑ * I))‖ ≤
      (Real.sin ϑ)⁻¹ * (Real.cos ϑ ^ (j + 2))⁻¹ *
        ((j + 1)! * (riemannZeta (j + 2)).re / (2 * π) ^ (j + 2)) := by
  have hcϑ := cos_pos_of_lt hϑ0.le hϑ2
  have hint : IntegrableOn (fun r : ℝ => zetaIntegrand (j + 1) (Real.cos ϑ * r)) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff (zetaIntegrand (j + 1)) 0 hcϑ).mpr
    rw [mul_zero] at this
    exact this (integrableOn_zetaIntegrand le_add_self)
  have hb := norm_integral_le_of_norm_le (hint.const_mul ((Real.sin ϑ)⁻¹ *
    (Real.cos ϑ ^ (j + 1))⁻¹)) ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun r hr => norm_boydF_rot_le hz him hϑ0 hϑ2 hsc (j + 1) hr))
  refine hb.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_comp_mul_left_Ioi _ 0 hcϑ, mul_zero, integral_zetaIntegrand,
    smul_eq_mul, pow_succ (Real.cos ϑ) (j + 1)]
  field_simp

end Sector

/-! ### `ζ(K)(1 + 1/K)^{(K+1)/2} ≤ 1 + ζ(K)` for `K ≥ 3` -/

theorem zeta_re_nonneg (j : ℕ) : 0 ≤ (riemannZeta (j + 2)).re :=
  (hasSum_zeta_re j).nonneg fun k => by positivity

theorem sum_inv_cube_le (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), 1 / ((k : ℝ) + 1) ^ (1 + 2) ≤
      5 / 4 - 1 / (2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hstep : 1 / (((N + 1 : ℕ) : ℝ) + 1) ^ (1 + 2) ≤
        1 / (2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) -
          1 / (2 * (((N + 1 : ℕ) : ℝ) + 1) * (((N + 1 : ℕ) : ℝ) + 2)) := by
      push_cast
      have hN : (0 : ℝ) ≤ N := N.cast_nonneg
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      ring_nf
      nlinarith [pow_nonneg hN 2, pow_nonneg hN 3, pow_nonneg hN 4, pow_nonneg hN 5,
        pow_nonneg hN 6]
    linarith

/-- `ζ(3) ≤ 5/4`. -/
theorem zeta_three_le : (riemannZeta (((1 : ℕ) : ℂ) + 2)).re ≤ 5 / 4 := by
  rw [← (hasSum_zeta_re 1).tsum_eq]
  refine Real.tsum_le_of_sum_range_le (fun k => by positivity) fun N => ?_
  rcases N with _ | N
  · norm_num
  · refine (sum_inv_cube_le N).trans ?_
    have : 0 ≤ 1 / (2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by positivity
    linarith

/-- `ζ(K) ≤ ζ(4) = π⁴/90 < 1.09` for `K ≥ 4`. -/
theorem zeta_le_of_four_le {j : ℕ} (hj : 2 ≤ j) : (riemannZeta (j + 2)).re ≤ 109 / 100 := by
  have h4 : (riemannZeta (2 + 2)).re = π ^ 4 / 90 := by
    rw [show (2 : ℂ) + 2 = 4 by norm_num, riemannZeta_four,
      show (π : ℂ) ^ 4 / 90 = ((π ^ 4 / 90 : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  have hle : (riemannZeta (j + 2)).re ≤ (riemannZeta (2 + 2)).re := by
    have h1 := hasSum_zeta_re j
    have h2 := hasSum_zeta_re 2
    have h2' : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (2 + 2)) (riemannZeta (2 + 2)).re := by
      simpa using h2
    refine hasSum_le (fun k => ?_) h1 h2'
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [k.cast_nonneg (α := ℝ)]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hk (by omega))
  rw [h4] at hle
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  have : π ^ 4 ≤ 3.1416 ^ 4 := pow_le_pow_left₀ hπ0.le hπ.le 4
  nlinarith

theorem exp_five_eighths_lt : Real.exp (5 / 8) < 1.9 := by
  have h1 := Real.exp_one_lt_d9
  have h8 : Real.exp (5 / 8) ^ 8 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h5 : Real.exp 1 ^ 5 < (2.7182818286 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
  have h : Real.exp (5 / 8) ^ 8 < (1.9 : ℝ) ^ 8 := by
    rw [h8]; refine h5.trans ?_; norm_num
  exact lt_of_pow_lt_pow_left₀ 8 (by norm_num) h

/-- `ζ(K) · ((1 + 1/K)^{1/2})^{K+1} ≤ 1 + ζ(K)` for `K = j + 2 ≥ 3`. -/
theorem zeta_mul_le {j : ℕ} (hj : 1 ≤ j) :
    (riemannZeta (j + 2)).re * Real.sqrt (1 + 1 / ((j : ℝ) + 2)) ^ (j + 3) ≤
      1 + (riemannZeta (j + 2)).re := by
  have hz0 := zeta_re_nonneg j
  set a := Real.sqrt (1 + 1 / ((j : ℝ) + 2)) with ha
  have ha1 : 1 ≤ a := by
    rw [ha, Real.one_le_sqrt]
    have : 0 ≤ 1 / ((j : ℝ) + 2) := by positivity
    linarith
  rcases (show j = 1 ∨ 2 ≤ j by omega) with rfl | hj2
  · -- `K = 3`: `a⁴ = 16/9`
    have hsq : a ^ 2 = 4 / 3 := by
      rw [ha, Real.sq_sqrt (by positivity)]; norm_num
    have h4 : a ^ (1 + 3) = 16 / 9 := by
      rw [show 1 + 3 = 2 * 2 by norm_num, pow_mul, hsq]; norm_num
    rw [h4]
    have := zeta_three_le
    push_cast at this ⊢
    nlinarith
  · -- `K ≥ 4`: `a^{K+1} ≤ e^{(K+1)/(2K)} ≤ e^{5/8}`
    have hK : (4 : ℝ) ≤ (j : ℝ) + 2 := by
      have : (2 : ℝ) ≤ j := by exact_mod_cast hj2
      linarith
    have hKpos : (0 : ℝ) < (j : ℝ) + 2 := by positivity
    have hae : a ≤ Real.exp (1 / (2 * ((j : ℝ) + 2))) := by
      have hsq : Real.exp (1 / (2 * ((j : ℝ) + 2))) ^ 2 = Real.exp (1 / ((j : ℝ) + 2)) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
      have := Real.add_one_le_exp (1 / ((j : ℝ) + 2))
      calc a = Real.sqrt (1 + 1 / ((j : ℝ) + 2)) := ha
        _ ≤ Real.sqrt (Real.exp (1 / (2 * ((j : ℝ) + 2))) ^ 2) :=
            Real.sqrt_le_sqrt (by rw [hsq]; linarith)
        _ = _ := Real.sqrt_sq (Real.exp_pos _).le
    have hpow : a ^ (j + 3) ≤ Real.exp (5 / 8) := by
      refine (pow_le_pow_left₀ (by linarith) hae _).trans ?_
      rw [← Real.exp_nat_mul]
      gcongr
      push_cast
      rw [show ((j : ℝ) + 3) * (1 / (2 * ((j : ℝ) + 2))) = ((j : ℝ) + 3) / (2 * ((j : ℝ) + 2)) by
        ring, div_le_iff₀ (by positivity)]
      linarith
    have hz := zeta_le_of_four_le hj2
    have he := exp_five_eighths_lt
    have hdiff : a ^ (j + 3) - 1 ≤ 9 / 10 := by norm_num at he; linarith
    have hnn : 0 ≤ a ^ (j + 3) - 1 := by
      have := one_le_pow₀ ha1 (n := j + 3); linarith
    have : (riemannZeta (j + 2)).re * (a ^ (j + 3) - 1) ≤ 109 / 100 * (9 / 10) :=
      mul_le_mul hz hdiff hnn (by norm_num)
    nlinarith

end Azurite.DLMF
