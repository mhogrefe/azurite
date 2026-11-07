/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section15
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv

/-!
# DLMF §4.18 Inequalities

* 4.18.1 (Jordan's inequality), 4.18.2, 4.18.3: `dlmf_4_18_1`, `dlmf_4_18_2`, `dlmf_4_18_3`
  (at `x = 0` the quotient `sin x / x` is read as its limit `1`, i.e. `Real.sinc`;
  `dlmf_4_18_3'` is the quotient form for `0 < x ≤ π`).
* 4.18.4: `dlmf_4_18_4`, following DLMF's proof: `f(x) = 4x(1 − x) − sin(πx) ≥ 0` on
  `[0, 1/2]` because `f′` is convex (`f‴ ≥ 0`), and similarly for the lower bound.
* 4.18.5–4.18.10 (`z = x + iy`): `dlmf_4_18_5`, …, `dlmf_4_18_10`; 4.18.7 needs `y ≠ 0`
  (`csch 0 = ∞`); 4.18.9–4.18.10 from the Maclaurin series.
-/

open Set Filter Topology Complex
open scoped Real Nat

namespace Azurite.DLMF

/-! ### Real arguments -/

/-- **DLMF 4.18.1** (Jordan's inequality): `2x/π ≤ sin x ≤ x`, `0 ≤ x ≤ π/2`. -/
theorem dlmf_4_18_1 {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ π / 2) :
    2 * x / π ≤ Real.sin x ∧ Real.sin x ≤ x :=
  ⟨by have := Real.mul_le_sin h0 h1; rwa [div_mul_eq_mul_div] at this, Real.sin_le h0⟩

/-- **DLMF 4.18.2**: `x ≤ tan x`, `0 ≤ x < π/2`. -/
theorem dlmf_4_18_2 {x : ℝ} (h0 : 0 ≤ x) (h1 : x < π / 2) : x ≤ Real.tan x :=
  Real.le_tan h0 h1

/-- **DLMF 4.18.3**: `cos x ≤ sin x / x ≤ 1`, `0 ≤ x ≤ π`, with `sin x / x` at `x = 0` meaning
its limit `1` (`Real.sinc`). -/
theorem dlmf_4_18_3 {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ π) :
    Real.cos x ≤ Real.sinc x ∧ Real.sinc x ≤ 1 := by
  refine ⟨?_, Real.sinc_le_one x⟩
  rcases lt_or_ge x (π / 2) with h | h
  · exact Real.cos_le_sinc (by rw [abs_of_nonneg h0]; exact h)
  · have hc : Real.cos x ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith)
    have hx : x ≠ 0 := by linarith [Real.pi_pos]
    rw [Real.sinc_of_ne_zero hx]
    exact hc.trans (div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 h1) h0)

/-- **DLMF 4.18.3**, quotient form for `0 < x ≤ π`. -/
theorem dlmf_4_18_3' {x : ℝ} (h0 : 0 < x) (h1 : x ≤ π) :
    Real.cos x ≤ Real.sin x / x ∧ Real.sin x / x ≤ 1 := by
  rw [← Real.sinc_of_ne_zero h0.ne']
  exact dlmf_4_18_3 h0.le h1

/-- Upper half of 4.18.4 on `[0, 1/2]`: `sin(πx) ≤ 4x(1 − x)`, via convexity of `f′` for
`f(x) = 4x(1 − x) − sin(πx)` (DLMF's proof). -/
theorem sin_pi_mul_le_four_mul {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    Real.sin (π * x) ≤ 4 * x * (1 - x) := by
  set f : ℝ → ℝ := fun x => 4 * x * (1 - x) - Real.sin (π * x) with hf
  set F : ℝ → ℝ := fun x => 4 * (1 - 2 * x) - π * Real.cos (π * x) with hF
  have hfd : ∀ x, HasDerivAt f (F x) x := by
    intro x
    have h := (((hasDerivAt_id' x).const_mul 4).mul ((hasDerivAt_id' x).const_sub 1)).sub
      ((hasDerivAt_id' x).const_mul π).sin
    exact h.congr_deriv (by simp only [hF]; ring)
  have hFd : ∀ x, HasDerivAt F (-8 + π ^ 2 * Real.sin (π * x)) x := by
    intro x
    have h := (((hasDerivAt_id' x).const_mul 2).const_sub 1 |>.const_mul 4).sub
      (((hasDerivAt_id' x).const_mul π).cos.const_mul π)
    exact h.congr_deriv (by ring)
  have hconv : ConvexOn ℝ (Icc 0 (1 / 2)) F := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc _ _)
      (fun x _ => (hFd x).continuousAt.continuousWithinAt)
      (fun x _ => (hFd x).differentiableAt.differentiableWithinAt)
    rw [interior_Icc]
    intro a ha b hb hab
    rw [(hFd a).deriv, (hFd b).deriv]
    have := Real.sin_le_sin_of_le_of_le_pi_div_two (x := π * a) (y := π * b)
      (by nlinarith [Real.pi_pos, ha.1]) (by nlinarith [Real.pi_pos, hb.2])
      (by nlinarith [Real.pi_pos])
    nlinarith [sq_nonneg π]
  have hf0 : f 0 = 0 := by simp [hf]
  have hfh : f (1 / 2) = 0 := by
    simp only [hf]
    rw [show π * (1 / 2) = π / 2 by ring, Real.sin_pi_div_two]
    norm_num
  have hFh : F (1 / 2) = 0 := by
    simp only [hF]
    rw [show π * (1 / 2) = π / 2 by ring, Real.cos_pi_div_two]
    norm_num
  by_contra hneg
  push Not at hneg
  have hfx : f x < 0 := by simp only [hf]; linarith
  have hx0 : 0 < x := by
    rcases h0.eq_or_lt with h | h
    · rw [← h] at hfx; linarith
    · exact h
  have hx1 : x < 1 / 2 := by
    rcases h1.eq_or_lt with h | h
    · rw [h] at hfx; linarith
    · exact h
  obtain ⟨a, ha, hFa⟩ := exists_hasDerivAt_eq_slope f F hx0
    (fun y _ => (hfd y).continuousAt.continuousWithinAt) (fun y _ => hfd y)
  obtain ⟨b, hb, hFb⟩ := exists_hasDerivAt_eq_slope f F hx1
    (fun y _ => (hfd y).continuousAt.continuousWithinAt) (fun y _ => hfd y)
  rw [hf0] at hFa
  rw [hfh] at hFb
  have hFa' : F a < 0 := by rw [hFa]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hFb' : 0 < F b := by rw [hFb]; exact div_pos (by linarith) (by linarith)
  have hab : a < b := ha.2.trans hb.1
  have hb1 : b < 1 / 2 := hb.2
  set μ := (1 / 2 - b) / (1 / 2 - a)
  set ν := (b - a) / (1 / 2 - a)
  have hμ : 0 ≤ μ := div_nonneg (by linarith) (by linarith)
  have hν : 0 ≤ ν := div_nonneg (by linarith) (by linarith)
  have hne : (1 / 2 - a) ≠ 0 := by linarith [ha.2]
  have hμν : μ + ν = 1 := by
    simp only [μ, ν]; rw [← add_div, div_eq_one_iff_eq hne]; ring
  have hcomb : μ • a + ν • (1 / 2 : ℝ) = b := by
    simp only [smul_eq_mul, μ, ν]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hne]; ring
  have := hconv.2 ⟨ha.1.le, by linarith [ha.2]⟩ ⟨by norm_num, le_rfl⟩ hμ hν hμν
  rw [hcomb, smul_eq_mul, smul_eq_mul, hFh, mul_zero, add_zero] at this
  have hμ' : 0 < μ := div_pos (by linarith) (by linarith)
  nlinarith [mul_neg_of_pos_of_neg hμ' hFa']

/-- Lower half of 4.18.4 on `(0, 1/2]`: `π x(1 − x) < sin(πx)`. -/
theorem pi_mul_lt_sin_pi_mul {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1 / 2) :
    π * (x * (1 - x)) < Real.sin (π * x) := by
  set g : ℝ → ℝ := fun x => Real.sin (π * x) - π * (x * (1 - x)) with hg
  have hgd : ∀ x, HasDerivAt g (π * Real.cos (π * x) - π * (1 - 2 * x)) x := by
    intro x
    have h := ((hasDerivAt_id' x).const_mul π).sin.sub
      (((hasDerivAt_id' x).mul ((hasDerivAt_id' x).const_sub 1)).const_mul π)
    exact h.congr_deriv (by ring)
  have hmono : StrictMonoOn g (Icc 0 (1 / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun x _ => (hgd x).continuousAt.continuousWithinAt)
    rw [interior_Icc]
    intro y hy
    rw [(hgd y).deriv]
    have h := Real.mul_lt_sin (x := π / 2 - π * y) (by nlinarith [Real.pi_pos, hy.2])
      (by nlinarith [Real.pi_pos, hy.1])
    rw [Real.sin_pi_div_two_sub] at h
    have : 2 / π * (π / 2 - π * y) = 1 - 2 * y := by field_simp
    rw [this] at h
    nlinarith [Real.pi_pos]
  have := hmono ⟨le_rfl, by norm_num⟩ ⟨h0.le, h1⟩ h0
  simp only [hg] at this
  simpa using this

/-- **DLMF 4.18.4**: `π < sin(πx)/(x(1 − x)) ≤ 4`, `0 < x < 1`. -/
theorem dlmf_4_18_4 {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    π < Real.sin (π * x) / (x * (1 - x)) ∧ Real.sin (π * x) / (x * (1 - x)) ≤ 4 := by
  have hp : 0 < x * (1 - x) := mul_pos h0 (by linarith)
  have key : π * (x * (1 - x)) < Real.sin (π * x) ∧ Real.sin (π * x) ≤ 4 * (x * (1 - x)) := by
    rcases le_or_gt x (1 / 2) with h | h
    · exact ⟨pi_mul_lt_sin_pi_mul h0 h, by
        have := sin_pi_mul_le_four_mul h0.le h; linarith⟩
    · have e : Real.sin (π * x) = Real.sin (π * (1 - x)) := by
        rw [show π * (1 - x) = π - π * x by ring, Real.sin_pi_sub]
      have e2 : x * (1 - x) = (1 - x) * (1 - (1 - x)) := by ring
      rw [e, e2]
      exact ⟨pi_mul_lt_sin_pi_mul (by linarith) (by linarith), by
        have := sin_pi_mul_le_four_mul (x := 1 - x) (by linarith) (by linarith); linarith⟩
  exact ⟨(lt_div_iff₀ hp).mpr key.1, (div_le_iff₀ hp).mpr key.2⟩

/-! ### Complex arguments -/

theorem norm_sin_sq_eq (z : ℂ) : ‖sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, normSq_apply, re_sin, im_sin]
  linear_combination (Real.sinh z.im ^ 2) * Real.sin_sq_add_cos_sq z.re +
    Real.sin z.re ^ 2 * Real.cosh_sq z.im

theorem norm_cos_sq_eq (z : ℂ) : ‖cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  rw [Complex.sq_norm, normSq_apply, re_cos, im_cos]
  linear_combination (Real.sinh z.im ^ 2) * Real.sin_sq_add_cos_sq z.re +
    Real.cos z.re ^ 2 * Real.cosh_sq z.im

theorem abs_sinh_le_le_cosh {u v : ℝ} (y : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v ^ 2) (hv1 : v ^ 2 ≤ 1)
    (h : u ^ 2 = v ^ 2 + Real.sinh y ^ 2) : |Real.sinh y| ≤ u ∧ u ≤ Real.cosh y := by
  constructor
  · exact (sq_le_sq₀ (abs_nonneg _) hu).mp (by rw [sq_abs, h]; linarith)
  · exact (sq_le_sq₀ hu (Real.cosh_pos y).le).mp (by rw [h, Real.cosh_sq]; linarith)

/-- **DLMF 4.18.5**: `|sinh y| ≤ |sin z| ≤ cosh y`. -/
theorem dlmf_4_18_5 (z : ℂ) : |Real.sinh z.im| ≤ ‖sin z‖ ∧ ‖sin z‖ ≤ Real.cosh z.im :=
  abs_sinh_le_le_cosh z.im (norm_nonneg _) (sq_nonneg _)
    (by nlinarith [Real.sin_sq_add_cos_sq z.re, sq_nonneg (Real.cos z.re)]) (norm_sin_sq_eq z)

/-- **DLMF 4.18.6**: `|sinh y| ≤ |cos z| ≤ cosh y`. -/
theorem dlmf_4_18_6 (z : ℂ) : |Real.sinh z.im| ≤ ‖cos z‖ ∧ ‖cos z‖ ≤ Real.cosh z.im :=
  abs_sinh_le_le_cosh z.im (norm_nonneg _) (sq_nonneg _)
    (by nlinarith [Real.sin_sq_add_cos_sq z.re, sq_nonneg (Real.sin z.re)]) (norm_cos_sq_eq z)

/-- **DLMF 4.18.7**: `|csc z| ≤ csch |y|` (`y ≠ 0`; for `y = 0` the right side is `∞`). -/
theorem dlmf_4_18_7 {z : ℂ} (hy : z.im ≠ 0) : ‖cscC z‖ ≤ 1 / Real.sinh |z.im| := by
  have hpos : 0 < Real.sinh |z.im| := Real.sinh_pos_iff.mpr (abs_pos.mpr hy)
  have h := (dlmf_4_18_5 z).1
  rw [Real.abs_sinh] at h
  rw [cscC, norm_div, norm_one]
  exact one_div_le_one_div_of_le hpos h

/-- **DLMF 4.18.8**: `|cos z| ≤ cosh |z|`. -/
theorem dlmf_4_18_8 (z : ℂ) : ‖cos z‖ ≤ Real.cosh ‖z‖ :=
  (dlmf_4_18_6 z).2.trans (Real.cosh_le_cosh.mpr (by rw [abs_norm]; exact abs_im_le_norm z))

/-- Termwise bound for the sine series. -/
theorem norm_sin_le_of_bound {z : ℂ} {g : ℕ → ℝ} {a : ℝ} (hg : HasSum g a)
    (h : ∀ n, ‖z‖ ^ (2 * n + 1) / ((2 * n + 1)! : ℝ) ≤ g n) : ‖sin z‖ ≤ a := by
  rw [← (Complex.hasSum_sin z).tsum_eq]
  refine tsum_of_norm_bounded hg fun n => ?_
  refine le_trans (le_of_eq ?_) (h n)
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow,
    Complex.norm_natCast]

/-- **DLMF 4.18.9**: `|sin z| ≤ sinh |z|`. -/
theorem dlmf_4_18_9 (z : ℂ) : ‖sin z‖ ≤ Real.sinh ‖z‖ :=
  norm_sin_le_of_bound (Real.hasSum_sinh ‖z‖) fun _ => le_rfl

theorem exp_one_lt_272 : Real.exp 1 < 2.72 := by
  have := Real.exp_one_lt_d9; norm_num at this; linarith

/-- **DLMF 4.18.10**: `|cos z| < 2`, `|sin z| ≤ (6/5)|z|`, `|z| < 1`. -/
theorem dlmf_4_18_10 {z : ℂ} (hz : ‖z‖ < 1) : ‖cos z‖ < 2 ∧ ‖sin z‖ ≤ 6 / 5 * ‖z‖ := by
  have he := exp_one_lt_272
  have he0 := Real.exp_pos 1
  have hinv : (Real.exp 1)⁻¹ < 1 ∧ 1 / 2.72 < (Real.exp 1)⁻¹ := by
    have h1 : 1 < Real.exp 1 := by
      have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith
    constructor
    · exact inv_lt_one_of_one_lt₀ h1
    · rw [one_div]; exact inv_strictAnti₀ he0 he
  constructor
  · have hc : Real.cosh ‖z‖ ≤ Real.cosh 1 :=
      Real.cosh_le_cosh.mpr (by rw [abs_norm, abs_one]; exact hz.le)
    have h1 := (dlmf_4_18_8 z).trans hc
    rw [Real.cosh_eq, Real.exp_neg] at h1
    linarith [hinv.1]
  · have hs : HasSum (fun n => ‖z‖ * (1 ^ (2 * n + 1) / ((2 * n + 1)! : ℝ)))
        (‖z‖ * Real.sinh 1) := (Real.hasSum_sinh 1).mul_left ‖z‖
    have h := norm_sin_le_of_bound hs fun n => by
      rw [one_pow, pow_succ, mul_comm _ ‖z‖, mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_one₀ (norm_nonneg z) hz.le
    have hsh : Real.sinh 1 ≤ 6 / 5 := by
      rw [Real.sinh_eq, Real.exp_neg]; linarith [hinv.2]
    calc ‖sin z‖ ≤ ‖z‖ * Real.sinh 1 := h
      _ ≤ ‖z‖ * (6 / 5) := mul_le_mul_of_nonneg_left hsh (norm_nonneg z)
      _ = 6 / 5 * ‖z‖ := by ring

end Azurite.DLMF
