/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter2.Section10ContourSum
import Azurite.DLMF.Chapter5.Section6Stirling

/-!
# DLMF §2.10(iii): estimates for 2.10.23

* `norm_hypF`: `|x^t/Γ(t + 1)³| = x^{ℜt} |1/Γ(t + 1)|³`, and the Stirling lower bound
  `norm_inv_Gamma_le` (5.11.3 with Stieltjes' bound) in `ℜt ≥ 0`, `ℑt ≥ 0`.
* `norm_inv_cexp_sub_one_le_circle`: on the quarter circle `t = Re^{iθ}`, `0 ≤ θ ≤ π/2`,
  `R = n − ½`: `|1/(e^{−2πit} − 1)| ≤ 2e^{−2πℑt}` (the circle stays at distance `½` from the
  integers; near the real axis `e^{−2πit}` has negative real part).
* `norm_arc_integrand_le`: the integrand of `𝒞₁` on the big quarter circle is `O(R^{−1/2})`
  once `R³ ≥ e³x`, so that integral vanishes as `n → ∞` (5.11.7 in the DLMF).
* `norm_imag_integrand_le`: on the imaginary axis the integrand is `O(e^{−πy/2})` uniformly in
  `x`.
-/

open Set Filter Topology Complex MeasureTheory Metric
open scoped Real

namespace Azurite.DLMF

theorem norm_hypF {x : ℝ} (hx : 0 < x) (t : ℂ) :
    ‖hypF x t‖ = x ^ t.re * ‖(Gamma (t + 1))⁻¹‖ ^ 3 := by
  rw [hypF, norm_div, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hx, norm_inv, div_eq_mul_inv,
    inv_pow]

/-- The constant `e^{1/6}/√(2π)` of `norm_inv_Gamma_le`. -/
noncomputable def gammaLowC : ℝ := Real.exp (1 / 6) / Real.sqrt (2 * π)

theorem gammaLowC_pos : 0 < gammaLowC :=
  div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (by positivity))

/-- `|1/Γ(t + 1)| ≤ C |t + 1|^{−½−ℜt} e^{ℜt + 1 + πℑt/2}` for `ℜt ≥ 0`, `ℑt ≥ 0`. -/
theorem norm_inv_Gamma_add_one_le {t : ℂ} (hre : 0 ≤ t.re) (him : 0 ≤ t.im) :
    ‖(Gamma (t + 1))⁻¹‖ ≤ gammaLowC * ‖t + 1‖ ^ (-(1 / 2) - t.re) *
      Real.exp (t.re + 1 + π / 2 * t.im) := by
  have h := norm_inv_Gamma_le (w := t + 1) (by simp; linarith) (by simpa using him)
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero] at h
  rw [gammaLowC]
  convert h using 3
  ring_nf

/-- On the quarter circle `|t| = n − ½`, `0 ≤ ph t ≤ π/2`: `|1/(e^{−2πit} − 1)| ≤ 2e^{−2πℑt}`. -/
theorem norm_inv_cexp_sub_one_le_circle {n : ℕ} (hn : 1 ≤ n) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ π / 2) :
    ‖1 / (cexp (-2 * π * I * (((n : ℝ) - 1 / 2 : ℝ) * cexp ((θ : ℂ) * I))) - 1)‖ ≤
      2 * Real.exp (-(2 * π * (((n : ℝ) - 1 / 2) * Real.sin θ))) := by
  set R : ℝ := (n : ℝ) - 1 / 2 with hRdef
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : 1 / 2 ≤ R := by linarith
  have hπ := Real.pi_pos
  set y := R * Real.sin θ with hy
  set u := R * Real.cos θ with hu
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hθ1⟩
  have hy0 : 0 ≤ y := mul_nonneg (by linarith) hs0
  set W := cexp (-2 * π * I * ((R : ℂ) * cexp ((θ : ℂ) * I))) with hW
  have hWeq : W = Real.exp (2 * π * y) * cexp (((-(2 * π * u)) : ℝ) * I) := by
    rw [hW, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [cexp_ofReal_mul_I]
    simp only [hy, hu]
    push_cast
    linear_combination (-(2 * (π : ℂ) * R * Complex.sin θ)) * Complex.I_sq
  have hWn : ‖W‖ = Real.exp (2 * π * y) := by
    rw [hWeq, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  have hEy := Real.exp_pos (2 * π * y)
  have hexp : Real.exp (-(2 * π * y)) = (Real.exp (2 * π * y))⁻¹ := Real.exp_neg _
  rw [norm_div, norm_one, hexp]
  by_cases hA : 2 ≤ Real.exp (2 * π * y)
  · have hW1 : ‖W‖ / 2 ≤ ‖W - 1‖ := by
      have := norm_sub_norm_le W 1
      rw [norm_one] at this
      linarith
    rw [hWn] at hW1
    rw [div_le_iff₀ (by linarith)]
    calc 1 = 2 * (Real.exp (2 * π * y))⁻¹ * (Real.exp (2 * π * y) / 2) := by field_simp
      _ ≤ 2 * (Real.exp (2 * π * y))⁻¹ * ‖W - 1‖ := by gcongr
  · push Not at hA
    -- `y < 1/(2π)`, so `ℜt` is within `¼` of `n − ½` and `ℜ e^{−2πit} ≤ 0`
    have hy1 : 2 * π * y < 1 := by linarith [Real.add_one_le_exp (2 * π * y)]
    have hδ : R - u ≤ y ^ 2 / R := by
      have h1 : 1 - Real.cos θ ≤ Real.sin θ ^ 2 := by
        rw [Real.sin_sq]; nlinarith [Real.cos_le_one θ]
      have hR0 : 0 < R := by linarith
      rw [le_div_iff₀ hR0, hy, hu]
      nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ R ^ 2)]
    have hδ0 : 0 ≤ R - u := by
      have h1 := mul_nonneg (by linarith : (0 : ℝ) ≤ R) (by linarith [Real.cos_le_one θ] :
        (0 : ℝ) ≤ 1 - Real.cos θ)
      simp only [hu]; linarith
    have hδ1 : 2 * π * (R - u) ≤ π / 2 := by
      have hy2 : y < 1 / (2 * π) := by rw [lt_div_iff₀ (by positivity)]; linarith
      have hyR : y ^ 2 / R ≤ 2 * y ^ 2 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith [sq_nonneg y]
      have hyy : y ^ 2 ≤ 1 / (4 * π ^ 2) := by
        calc y ^ 2 ≤ (1 / (2 * π)) ^ 2 := pow_le_pow_left₀ hy0 hy2.le 2
          _ = 1 / (4 * π ^ 2) := by field_simp; ring
      have hπ3 : 3 < π := Real.pi_gt_three
      have : 2 * π * (2 / (4 * π ^ 2)) ≤ π / 2 := by
        rw [show 2 * π * (2 / (4 * π ^ 2)) = 1 / π by field_simp; ring]
        rw [div_le_div_iff₀ hπ (by norm_num)]; nlinarith
      calc 2 * π * (R - u) ≤ 2 * π * (2 * y ^ 2) := by gcongr; linarith [hδ, hyR]
        _ ≤ 2 * π * (2 / (4 * π ^ 2)) := by
            gcongr; rw [show (2 : ℝ) / (4 * π ^ 2) = 2 * (1 / (4 * π ^ 2)) by ring]; linarith
        _ ≤ π / 2 := this
    have hcos : Real.cos (-(2 * π * u)) ≤ 0 := by
      rw [Real.cos_neg, show 2 * π * u = (n : ℝ) * (2 * π) - (2 * π * (R - u) + π) by
        rw [hRdef]; ring, Real.cos_nat_mul_two_pi_sub, Real.cos_add_pi, neg_nonpos]
      exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, hδ1⟩
    have hre : (W - 1).re ≤ -1 := by
      rw [Complex.sub_re, Complex.one_re, hWeq, cexp_ofReal_mul_I]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.add_im, Complex.I_re, Complex.I_im, Complex.mul_im]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hEy.le hcos]
    have hW1 : 1 ≤ ‖W - 1‖ := by
      have := Complex.abs_re_le_norm (W - 1)
      rw [abs_of_neg (by linarith)] at this
      linarith
    rw [div_le_iff₀ (by linarith)]
    have : 1 ≤ 2 * (Real.exp (2 * π * y))⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hEy]; linarith
    nlinarith

/-- The real inequality behind the arc estimate: for `R ≥ 1`, `W ≥ R`, `a, m ≥ 0` and
`ln x + 3 ≤ 3 ln R`: `x^a (C W^{−½−a} e^{a+1+πm/2})³ · 2e^{−2πm} · πR ≤ 2πC³e³ R^{−1/2}`. -/
theorem arc_real_bound {x R a m W : ℝ} (hx : 0 < x) (hR : 1 ≤ R) (hW : R ≤ W) (ha : 0 ≤ a)
    (hm : 0 ≤ m) (hxR : Real.log x + 3 ≤ 3 * Real.log R) :
    x ^ a * (gammaLowC * W ^ (-(1 / 2) - a) * Real.exp (a + 1 + π / 2 * m)) ^ 3 *
        (2 * Real.exp (-(2 * π * m))) * (π * R) ≤
      2 * π * gammaLowC ^ 3 * Real.exp 3 * R ^ (-(1 / 2) : ℝ) := by
  have hR0 : 0 < R := by linarith
  have hC := gammaLowC_pos
  have hπ := Real.pi_pos
  have hWp : W ^ (-(1 / 2) - a) ≤ R ^ (-(1 / 2) - a) :=
    Real.rpow_le_rpow_of_nonpos hR0 hW (by linarith)
  have hlR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hcube : ∀ u : ℝ, Real.exp u ^ 3 = Real.exp (3 * u) := fun u => by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 : (gammaLowC * W ^ (-(1 / 2) - a) * Real.exp (a + 1 + π / 2 * m)) ^ 3 ≤
      (gammaLowC * R ^ (-(1 / 2) - a) * Real.exp (a + 1 + π / 2 * m)) ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))
      (Real.exp_pos _).le) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWp hC.le)
        (Real.exp_pos _).le) 3
  have hxa : 0 ≤ x ^ a := Real.rpow_nonneg hx.le a
  have hC3 : 0 ≤ 2 * π * gammaLowC ^ 3 := mul_nonneg (by positivity) (pow_nonneg hC.le 3)
  calc x ^ a * (gammaLowC * W ^ (-(1 / 2) - a) * Real.exp (a + 1 + π / 2 * m)) ^ 3 *
        (2 * Real.exp (-(2 * π * m))) * (π * R)
      ≤ x ^ a * (gammaLowC * R ^ (-(1 / 2) - a) * Real.exp (a + 1 + π / 2 * m)) ^ 3 *
        (2 * Real.exp (-(2 * π * m))) * (π * R) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left h3 hxa
    _ = 2 * π * gammaLowC ^ 3 * Real.exp (Real.log x * a +
          3 * (Real.log R * (-(1 / 2) - a) + (a + 1 + π / 2 * m)) + -(2 * π * m) +
          Real.log R) := by
        rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hR0, mul_pow, mul_pow, hcube, hcube,
          Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hR0,
          show (3 : ℝ) * (Real.log R * (-(1 / 2) - a) + (a + 1 + π / 2 * m)) =
            3 * (Real.log R * (-(1 / 2) - a)) + 3 * (a + 1 + π / 2 * m) by ring, Real.exp_add]
        ring
    _ ≤ 2 * π * gammaLowC ^ 3 * Real.exp (3 + Real.log R * (-(1 / 2))) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC3
        nlinarith [mul_le_mul_of_nonneg_left hxR ha, mul_nonneg hm hπ.le]
    _ = 2 * π * gammaLowC ^ 3 * Real.exp 3 * R ^ (-(1 / 2) : ℝ) := by
        rw [Real.exp_add, Real.rpow_def_of_pos hR0]; ring

theorem re_cotSide₀ (R s : ℝ) : (cotSide R 0 s).re = R * Real.cos (π * s - π / 2) := by
  simp only [cotSide]; exact re_mul_cexp_ofReal_mul_I _ _

theorem im_cotSide₀ (R s : ℝ) : (cotSide R 0 s).im = R * Real.sin (π * s - π / 2) := by
  simp only [cotSide, cexp_ofReal_mul_I]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im, Complex.mul_re]
  ring

/-- **The big quarter circle**: on `t = Re^{iθ}`, `0 ≤ θ ≤ π/2`, `R = n − ½ ≥ 1`,
`ln x + 3 ≤ 3 ln R`, the integrand of `𝒞₁` is at most `2πC³e³ R^{−1/2}`. -/
theorem norm_arc_integrand_le {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n)
    (hR1 : 1 ≤ (n : ℝ) - 1 / 2) (hxR : Real.log x + 3 ≤ 3 * Real.log ((n : ℝ) - 1 / 2))
    {s : ℝ} (hs : s ∈ Icc (1 / 2 : ℝ) 1) :
    ‖hypF x (cotSide ((n : ℝ) - 1 / 2) 0 s) /
        (cexp (-2 * π * I * cotSide ((n : ℝ) - 1 / 2) 0 s) - 1) *
        deriv (cotSide ((n : ℝ) - 1 / 2) 0) s‖ ≤
      2 * π * gammaLowC ^ 3 * Real.exp 3 * ((n : ℝ) - 1 / 2) ^ (-(1 / 2) : ℝ) := by
  set R : ℝ := (n : ℝ) - 1 / 2 with hRdef
  set θ := π * s - π / 2 with hθ
  have hπ := Real.pi_pos
  have hθ0 : 0 ≤ θ := by nlinarith [hs.1]
  have hθ1 : θ ≤ π / 2 := by nlinarith [hs.2]
  set t := cotSide R 0 s with ht
  have hre : t.re = R * Real.cos θ := re_cotSide₀ R s
  have him : t.im = R * Real.sin θ := im_cotSide₀ R s
  have hR0 : 0 < R := by linarith
  have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hθ1⟩
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  have hre0 : 0 ≤ t.re := by rw [hre]; positivity
  have him0 : 0 ≤ t.im := by rw [him]; positivity
  have hnt : ‖t‖ = R := by
    simp only [ht, cotSide]; rw [norm_mul_cexp_ofReal_mul_I, abs_of_pos hR0]
  have ht1 : R ≤ ‖t + 1‖ := by
    have h1 : ‖t‖ ^ 2 ≤ ‖t + 1‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero]
      nlinarith
    have := (sq_le_sq₀ (norm_nonneg t) (norm_nonneg (t + 1))).mp h1
    rwa [hnt] at this
  have hE := norm_inv_cexp_sub_one_le_circle hn hθ0 hθ1
  rw [← hRdef] at hE
  have hteq : t = (R : ℂ) * cexp ((θ : ℂ) * I) := by simp only [ht, cotSide, hθ]
  have hd : deriv (cotSide R 0) s = t * (π * I) := by rw [deriv_cotSide₀]
  rw [hd, div_eq_mul_one_div, norm_mul, norm_mul, norm_hypF hx, norm_mul, hnt]
  have hΓ := norm_inv_Gamma_add_one_le hre0 him0
  rw [← hteq] at hE
  have hπI : ‖(π : ℂ) * I‖ = π := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hπ.le]
  rw [hπI, show -(2 * π * (R * Real.sin θ)) = -(2 * π * t.im) by rw [him]] at *
  have hB : 0 ≤ gammaLowC * ‖t + 1‖ ^ (-(1 / 2) - t.re) * Real.exp (t.re + 1 + π / 2 * t.im) :=
    le_trans (norm_nonneg _) hΓ
  have h3 := pow_le_pow_left₀ (norm_nonneg _) hΓ 3
  have hxa : 0 ≤ x ^ t.re := Real.rpow_nonneg hx.le _
  calc x ^ t.re * ‖(Gamma (t + 1))⁻¹‖ ^ 3 * ‖1 / (cexp (-2 * π * I * t) - 1)‖ * (R * π)
      ≤ x ^ t.re * (gammaLowC * ‖t + 1‖ ^ (-(1 / 2) - t.re) *
          Real.exp (t.re + 1 + π / 2 * t.im)) ^ 3 * (2 * Real.exp (-(2 * π * t.im))) *
          (π * R) := by
        rw [mul_comm R π]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left h3 hxa) hE (norm_nonneg _)
          (mul_nonneg hxa (pow_nonneg hB 3))
    _ ≤ _ := arc_real_bound hx hR1 ht1 hre0 him0 hxR

theorem cexp_neg_two_pi_I_mul_I (y : ℝ) :
    cexp (-2 * π * I * ((y : ℂ) * I)) = (Real.exp (2 * π * y) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination (-(2 * (π : ℂ) * y)) * Complex.I_sq

/-- **The imaginary axis**: for `y ≥ ½`, `|x^{iy}/Γ(1 + iy)³ · i/(e^{2πy} − 1)| ≤
2C³e³ e^{−πy/2}`, uniformly in `x > 0`. -/
theorem norm_imag_integrand_le {x : ℝ} (hx : 0 < x) {y : ℝ} (hy : 1 / 2 ≤ y) :
    ‖hypF x ((y : ℂ) * I) / (cexp (-2 * π * I * ((y : ℂ) * I)) - 1) * I‖ ≤
      2 * gammaLowC ^ 3 * Real.exp 3 * Real.exp (-(π / 2 * y)) := by
  have hπ := Real.pi_pos
  have hC := gammaLowC_pos
  set t : ℂ := (y : ℂ) * I with ht
  have hre : t.re = 0 := by simp [ht]
  have him : t.im = y := by simp [ht]
  have hΓ := norm_inv_Gamma_add_one_le (t := t) (by rw [hre]) (by rw [him]; linarith)
  rw [hre, him] at hΓ
  have hn1 : 1 ≤ ‖t + 1‖ := by
    have := Complex.re_le_norm (t + 1)
    simp only [Complex.add_re, Complex.one_re, hre, zero_add] at this
    exact this
  have hpow : ‖t + 1‖ ^ (-(1 / 2) - (0 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hΓ' : ‖(Gamma (t + 1))⁻¹‖ ≤ gammaLowC * Real.exp (1 + π / 2 * y) := by
    refine hΓ.trans ?_
    rw [zero_add]
    have := Real.exp_pos (1 + π / 2 * y)
    calc gammaLowC * ‖t + 1‖ ^ (-(1 / 2) - (0 : ℝ)) * Real.exp (1 + π / 2 * y)
        ≤ gammaLowC * 1 * Real.exp (1 + π / 2 * y) := by gcongr
      _ = _ := by ring
  have hE2 : 2 ≤ Real.exp (2 * π * y) := by
    have := Real.add_one_le_exp (2 * π * y)
    have : 1 ≤ 2 * π * y := by nlinarith [Real.pi_gt_three]
    linarith
  have hden : ‖1 / ((Real.exp (2 * π * y) : ℂ) - 1)‖ ≤ 2 * Real.exp (-(2 * π * y)) := by
    rw [show ((Real.exp (2 * π * y) : ℂ) - 1) = ((Real.exp (2 * π * y) - 1 : ℝ) : ℂ) by
      push_cast; ring, norm_div, norm_one, Complex.norm_real,
      Real.norm_of_nonneg (by linarith), Real.exp_neg, div_le_iff₀ (by linarith)]
    have hp := Real.exp_pos (2 * π * y)
    rw [show 2 * (Real.exp (2 * π * y))⁻¹ * (Real.exp (2 * π * y) - 1) =
      2 - 2 * (Real.exp (2 * π * y))⁻¹ by field_simp]
    have : (Real.exp (2 * π * y))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hp (by norm_num)]; linarith
    linarith
  rw [cexp_neg_two_pi_I_mul_I, div_eq_mul_one_div, norm_mul, norm_mul, Complex.norm_I, mul_one,
    norm_hypF hx, hre, Real.rpow_zero, one_mul]
  have h3 := pow_le_pow_left₀ (norm_nonneg _) hΓ' 3
  calc ‖(Gamma (t + 1))⁻¹‖ ^ 3 * ‖1 / ((Real.exp (2 * π * y) : ℂ) - 1)‖
      ≤ (gammaLowC * Real.exp (1 + π / 2 * y)) ^ 3 * (2 * Real.exp (-(2 * π * y))) :=
        mul_le_mul h3 hden (norm_nonneg _) (by positivity)
    _ = 2 * gammaLowC ^ 3 * Real.exp 3 * Real.exp (-(π / 2 * y)) := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_assoc (2 * gammaLowC ^ 3), ← Real.exp_add,
          show gammaLowC ^ 3 * Real.exp (((3 : ℕ) : ℝ) * (1 + π / 2 * y)) *
            (2 * Real.exp (-(2 * π * y))) = 2 * gammaLowC ^ 3 *
            (Real.exp (((3 : ℕ) : ℝ) * (1 + π / 2 * y)) * Real.exp (-(2 * π * y))) by ring,
          ← Real.exp_add]
        congr 2
        push_cast; ring

/-- On the real line, `|x^t/Γ(t + 1)³| ≤ C³e³ e^{−t}` once `3 ln(t + 1) ≥ ln x + 4`. -/
theorem norm_hypF_real_le {x : ℝ} (hx : 0 < x) {t : ℝ} (ht : 0 ≤ t)
    (hxt : Real.log x + 4 ≤ 3 * Real.log (t + 1)) :
    ‖hypF x t‖ ≤ gammaLowC ^ 3 * Real.exp 3 * Real.exp (-t) := by
  have hC := gammaLowC_pos
  have ht1 : 0 < t + 1 := by linarith
  have hΓ := norm_inv_Gamma_add_one_le (t := (t : ℂ)) (by simpa using ht) (by simp)
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero] at hΓ
  rw [show ‖(t : ℂ) + 1‖ = t + 1 by
    rw [show (t : ℂ) + 1 = ((t + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg ht1.le]] at hΓ
  rw [norm_hypF hx, Complex.ofReal_re]
  have hl : 0 ≤ Real.log (t + 1) := Real.log_nonneg (by linarith)
  have h3 := pow_le_pow_left₀ (norm_nonneg _) hΓ 3
  calc x ^ t * ‖(Gamma ((t : ℂ) + 1))⁻¹‖ ^ 3
      ≤ x ^ t * (gammaLowC * (t + 1) ^ (-(1 / 2) - t) * Real.exp (t + 1)) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hx.le _)
    _ = gammaLowC ^ 3 * Real.exp (Real.log x * t +
          3 * (Real.log (t + 1) * (-(1 / 2) - t) + (t + 1))) := by
        rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos ht1, mul_pow, mul_pow,
          ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        rw [show ∀ a b c : ℝ, Real.exp a * (gammaLowC ^ 3 * Real.exp b * Real.exp c) =
          gammaLowC ^ 3 * (Real.exp a * Real.exp b * Real.exp c) from fun a b c => by ring,
          ← Real.exp_add, ← Real.exp_add]
        congr 2
        push_cast; ring
    _ ≤ gammaLowC ^ 3 * Real.exp (3 + -t) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (pow_nonneg hC.le 3)
        nlinarith [mul_le_mul_of_nonneg_left hxt ht]
    _ = _ := by rw [Real.exp_add]; ring

theorem integrableOn_hypF_Ioi {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => hypF x t) (Ioi (-(1 / 2))) := by
  set T : ℝ := Real.exp ((|Real.log x| + 4) / 3) with hT
  have hT1 : 1 ≤ T := Real.one_le_exp (by positivity)
  have hc : Continuous fun t : ℝ => hypF x t :=
    (differentiable_hypF hx).continuous.comp continuous_ofReal
  rw [← Ioc_union_Ioi_eq_Ioi (by linarith : -(1 / 2 : ℝ) ≤ T)]
  refine IntegrableOn.union ((hc.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self) ?_
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi T (b := 1) one_pos).const_mul
    (gammaLowC ^ 3 * Real.exp 3)) hc.aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
  have ht0 : 0 ≤ t := by linarith [mem_Ioi.mp ht]
  refine (norm_hypF_real_le hx ht0 ?_).trans (le_of_eq (by ring_nf))
  have hlt : Real.log T ≤ Real.log (t + 1) :=
    Real.log_le_log (by linarith) (by linarith [mem_Ioi.mp ht])
  rw [hT, Real.log_exp] at hlt
  have := le_abs_self (Real.log x)
  linarith

theorem continuousOn_imag_integrand {x : ℝ} (hx : 0 < x) :
    ContinuousOn (fun y : ℝ => hypF x ((y : ℂ) * I) / (cexp (-2 * π * I * ((y : ℂ) * I)) - 1) * I)
      (Ioi (1 / 2)) := by
  intro y hy
  have hne : cexp (-2 * π * I * ((y : ℂ) * I)) - 1 ≠ 0 := by
    rw [cexp_neg_two_pi_I_mul_I, sub_ne_zero, ← Complex.ofReal_one, Ne, Complex.ofReal_inj]
    have : 0 < 2 * π * y := by have := mem_Ioi.mp hy; have := Real.pi_pos; positivity
    exact (Real.one_lt_exp_iff.mpr this).ne'
  have h1 : ContinuousAt (fun y : ℝ => hypF x ((y : ℂ) * I)) y :=
    ((differentiable_hypF hx).continuous.comp (continuous_ofReal.mul continuous_const)).continuousAt
  have h2 : ContinuousAt (fun y : ℝ => cexp (-2 * π * I * ((y : ℂ) * I)) - 1) y := by fun_prop
  exact ((h1.div h2 hne).mul continuousAt_const).continuousWithinAt

theorem integrableOn_imag_integrand {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun y : ℝ => hypF x ((y : ℂ) * I) / (cexp (-2 * π * I * ((y : ℂ) * I)) - 1) * I)
      (Ioi (1 / 2)) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi (1 / 2) (b := π / 2) (by positivity)).const_mul
    (2 * gammaLowC ^ 3 * Real.exp 3)) ((continuousOn_imag_integrand hx).aestronglyMeasurable
      measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun y hy => ?_)
  refine (norm_imag_integrand_le hx (le_of_lt (mem_Ioi.mp hy))).trans (le_of_eq ?_)
  ring_nf

end Azurite.DLMF
