/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13AsympSeries
import Azurite.DLMF.Chapter4.Section13BranchPoint
import Azurite.DLMF.Chapter4.Section13Figure
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# DLMF §4.13: convergence of 4.13.10 for `k = 0` and real `z ≥ e`

Fix `ξ₀ = ln z > 1` and `λ = ln ξ₀`. With `τ = λσ`, the series of 4.13.10 is the Taylor series in
`σ` of `g(σ) = 𝒲(1/σ) − 1/σ + λ`, where `𝒲(s) = ω(s + ln s − λ)` solves `𝒲 e^𝒲 = s eˢ/ξ₀`. The
nearest branch point is `s* = W₀(−ξ₀/e)` (in `s = 1/σ`), and `|s*| < ξ₀` because `s*` lies on the
boundary curve `ξ = −η cot η` of the `W₀` region, where `ℜ s* > −1`.

* `green_facts`, `green_re_lt`: the curve `ℑs + ph s = π`, where `|s| = η/sin η` and
  `ℜ(s + ln s) = greenF η` both increase with `η = ℑs`; `sStar_props`.
* `bigW`, `continuousAt_bigW`, `differentiableAt_bigW`: `𝒲` is analytic for `|s| > |s*|` (off the
  negative axis `ζ(s)` avoids `L±`; on it `𝒲` is `W₁` from above and `W_{−1}` from below).
* `gTilde_eqOn`: `g̃` agrees with the series `∑ Qₙ σⁿ` near `0` (identity theorem from small
  `σ > 0`, where the core expansion applies), so `g̃` is analytic on `|σ| < 1/r₀`, `r₀ < ξ₀`.
* `dlmf_4_13_10_real`: the series 4.13.10 converges to `W₀(z)` for real `z ≥ e`.
-/

open Set Filter Topology Complex
open scoped Real ComplexConjugate

namespace Azurite.DLMF

/-! ### The boundary curve `ℑs + ph s = π` -/

/-- `ℜ(s + ln s)` along the curve `s = −η cot η + iη`: `−η cot η + ln(η/sin η)`. -/
noncomputable def greenF (η : ℝ) : ℝ := -(η * Real.cos η / Real.sin η) + Real.log (η / Real.sin η)

theorem greenF_eq_omegaG {η : ℝ} (hη : η ∈ Ioo 0 π) : greenF η = omegaG π (π - η) := by
  have hm : π - η ∈ omegaDom π := ⟨by linarith [hη.2], by rw [min_self]; linarith [hη.1]⟩
  rw [omegaG_pi_eq hm, sub_sub_cancel, greenF]
  ring

theorem strictMonoOn_greenF : StrictMonoOn greenF (Ioo 0 π) := by
  intro a ha b hb hab
  rw [greenF_eq_omegaG ha, greenF_eq_omegaG hb]
  exact strictAntiOn_omegaG π ⟨by linarith [hb.2], by rw [min_self]; linarith [hb.1]⟩
    ⟨by linarith [ha.2], by rw [min_self]; linarith [ha.1]⟩ (by linarith)

theorem strictMonoOn_div_sin : StrictMonoOn (fun η : ℝ => η / Real.sin η) (Ioo 0 π) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo 0 π) ?_ fun x hx => ?_
  · intro x hx
    exact (continuousAt_id.div Real.continuous_sin.continuousAt
      (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne').continuousWithinAt
  · rw [interior_Ioo] at hx
    have hs := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
    have hd : HasDerivAt (fun η : ℝ => η / Real.sin η)
        ((1 * Real.sin x - x * Real.cos x) / Real.sin x ^ 2) x :=
      (hasDerivAt_id x).div (Real.hasDerivAt_sin x) hs.ne'
    rw [hd.deriv]
    have := mul_cos_lt_sin hx.1 hx.2
    exact div_pos (by linarith) (by positivity)

/-- On the curve `ℑs + ph s = π` (`ℑs > 0`): `η = ℑs < π`, `|s| = η/sin η`,
`ℜ(s + ln s) = greenF η`. -/
theorem green_facts {s : ℂ} (hs : 0 < s.im) (harg : s.im + arg s = π) :
    s.im < π ∧ ‖s‖ = s.im / Real.sin s.im ∧ (s + log s).re = greenF s.im := by
  have ha := arg_mem_Ioo_of_im_pos hs
  have hη : s.im < π := by linarith [ha.1]
  have hsin : 0 < Real.sin s.im := Real.sin_pos_of_pos_of_lt_pi hs hη
  have hargeq : arg s = π - s.im := by linarith
  have h1 := norm_mul_sin_arg s
  have h2 := norm_mul_cos_arg s
  rw [hargeq, Real.sin_pi_sub] at h1
  rw [hargeq, Real.cos_pi_sub] at h2
  have hn : ‖s‖ = s.im / Real.sin s.im := by field_simp; linarith
  refine ⟨hη, hn, ?_⟩
  rw [add_re, log_re, greenF, ← hn]
  congr 1
  rw [← h2, hn]; field_simp

theorem one_lt_div_sin {η : ℝ} (h0 : 0 < η) (hη : η < π) : 1 < η / Real.sin η := by
  have hs := Real.sin_pos_of_pos_of_lt_pi h0 hη
  rw [one_lt_div hs]; exact Real.sin_lt h0

/-- Along the curve, `|s| < |s'|` forces `ℜ(s + ln s) < ℜ(s' + ln s')`. -/
theorem green_re_lt {s s' : ℂ} (hs : 0 < s.im) (harg : s.im + arg s = π) (hs' : 0 < s'.im)
    (harg' : s'.im + arg s' = π) (h : ‖s‖ < ‖s'‖) : (s + log s).re < (s' + log s').re := by
  obtain ⟨h1, h2, h3⟩ := green_facts hs harg
  obtain ⟨h1', h2', h3'⟩ := green_facts hs' harg'
  rw [h3, h3']
  have hlt : s.im < s'.im := by
    by_contra hc; push Not at hc
    have := strictMonoOn_div_sin.monotoneOn ⟨hs', h1'⟩ ⟨hs, h1⟩ hc
    rw [← h2, ← h2'] at this; linarith
  exact strictMonoOn_greenF ⟨hs, h1⟩ ⟨hs', h1'⟩ hlt

/-- Along the curve, equal `ℜ(s + ln s)` forces equal `|s|`. -/
theorem green_norm_eq {s s' : ℂ} (hs : 0 < s.im) (harg : s.im + arg s = π) (hs' : 0 < s'.im)
    (harg' : s'.im + arg s' = π) (h : (s + log s).re = (s' + log s').re) : ‖s‖ = ‖s'‖ := by
  rcases lt_trichotomy ‖s‖ ‖s'‖ with hlt | heq | hgt
  · exact absurd h (green_re_lt hs harg hs' harg' hlt).ne
  · exact heq
  · exact absurd h (green_re_lt hs' harg' hs harg hgt).ne'

/-! ### The branch point `s* = W₀(−ξ₀/e)` -/

/-- `s* = W₀(−ξ₀/e)`. -/
noncomputable def sStar (ξ₀ : ℝ) : ℂ := lambertW 0 ((-(ξ₀ * Real.exp (-1)) : ℝ) : ℂ)

theorem sStar_props {ξ₀ : ℝ} (hξ : 1 < ξ₀) :
    0 < (sStar ξ₀).im ∧ (sStar ξ₀).im + arg (sStar ξ₀) = π ∧
      (sStar ξ₀ + log (sStar ξ₀)).re = Real.log ξ₀ - 1 ∧
      sStar ξ₀ * exp (sStar ξ₀) = ((-(ξ₀ * Real.exp (-1)) : ℝ) : ℂ) ∧
      1 < ‖sStar ξ₀‖ ∧ ‖sStar ξ₀‖ < ξ₀ := by
  set x : ℝ := -(ξ₀ * Real.exp (-1))
  have he := Real.exp_pos (-1)
  have hx0 : x < 0 := by simp only [x]; nlinarith
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne
  have hlog : log (x : ℂ) = ⟨Real.log ξ₀ - 1, π⟩ := by
    apply Complex.ext
    · simp only [log_re, norm_real, Real.norm_eq_abs, abs_of_neg hx0, x, neg_neg]
      rw [Real.log_mul (by linarith) he.ne', Real.log_exp]; ring
    · simp [log_im, arg_ofReal_of_neg hx0]
  have hL : ¬omegaLm (log (x : ℂ) + 2 * π * ((0 : ℤ) : ℂ) * I) := by
    rintro ⟨h, -⟩; simp [hlog] at h; linarith [Real.pi_pos]
  have hspec := wrightOmega_spec hL
  have hS : sStar ξ₀ = wrightOmega (log (x : ℂ) + 2 * π * ((0 : ℤ) : ℂ) * I) := by
    rw [sStar, lambertW_of_ne hxne]
  set y := sStar ξ₀
  rw [← hS] at hspec
  obtain ⟨hy0, hyeq, hclause⟩ := hspec
  simp only [Int.cast_zero, mul_zero, zero_mul, add_zero, hlog] at hyeq hclause
  have him : y.im + arg y = π := by have := congrArg im hyeq; rw [add_log_im] at this; exact this
  have hre : (y + log y).re = Real.log ξ₀ - 1 := by rw [hyeq]
  have hlogpos : 0 < Real.log ξ₀ := Real.log_pos hξ
  have hyim : 0 < y.im := by
    rcases lt_trichotomy y.im 0 with h | h | h
    · have := (arg_mem_Ioo_of_im_neg h).2; linarith [Real.pi_pos]
    · exfalso
      have hc := hclause trivial h
      have hy' : y = (y.re : ℂ) := Complex.ext rfl (by simp [h])
      have hr : y.re < 0 := by
        have : arg y = π := by rw [h, zero_add] at him; exact him
        exact (arg_eq_pi_iff.mp this).1
      rw [hy', add_log_of_neg_real hr] at hre
      simp only at hre
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < -y.re)
      linarith
    · exact h
  obtain ⟨hη, hn, hg⟩ := green_facts hyim him
  have hsin := Real.sin_pos_of_pos_of_lt_pi hyim hη
  refine ⟨hyim, him, hre, ?_, ?_, ?_⟩
  · have := dlmf_4_13_1 0 (x : ℂ); rwa [← sStar] at this
  · rw [hn]; exact one_lt_div_sin hyim hη
  · -- `ℜ y > −1` on the curve, so `ln|y| = ln ξ₀ − 1 − ℜ y < ln ξ₀`
    have hrey : -1 < y.re := by
      have h2 := norm_mul_cos_arg y
      rw [show arg y = π - y.im by linarith, Real.cos_pi_sub, hn] at h2
      have := mul_cos_lt_sin hyim hη
      rw [← h2]
      have : y.im * Real.cos y.im / Real.sin y.im < 1 := by rw [div_lt_one hsin]; exact this
      field_simp at this ⊢; linarith
    have h3 : (y + log y).re = y.re + Real.log ‖y‖ := by rw [add_re, log_re]
    have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hlt : Real.log ‖y‖ < Real.log ξ₀ := by linarith
    exact (Real.log_lt_log_iff hny (by linarith)).mp hlt

/-! ### The function `𝒲(s) = ω(s + ln s − λ)` -/

/-- `ζ(s) = s + ln s − λ`. -/
noncomputable def zetaS (lam : ℝ) (s : ℂ) : ℂ := s + log s - lam

/-- `𝒲(s) = ω(s + ln s − λ)`, with `ω(ζ − 2πi)` (the real branch `W_{−1}`) on the negative axis. -/
noncomputable def bigW (lam : ℝ) (s : ℂ) : ℂ :=
  if s.im = 0 ∧ s.re < 0 then wrightOmega (zetaS lam s - 2 * π * I) else wrightOmega (zetaS lam s)

/-- `Z(s) = s eˢ e^{−λ}`. -/
noncomputable def zZ (lam : ℝ) (s : ℂ) : ℂ := s * exp s * Real.exp (-lam)

theorem exp_zetaS (lam : ℝ) {s : ℂ} (hs : s ≠ 0) : exp (zetaS lam s) = zZ lam s := by
  rw [zetaS, zZ, exp_sub, exp_add, exp_log hs, ← ofReal_exp, Real.exp_neg, ofReal_inv]
  ring

theorem bigW_mul_exp (lam : ℝ) {s : ℂ} (hs : s ≠ 0) :
    bigW lam s * exp (bigW lam s) = zZ lam s := by
  unfold bigW
  split_ifs
  · rw [wrightOmega_mul_exp, exp_sub, exp_zetaS lam hs,
      show (2 * π * I : ℂ) = (1 : ℤ) * (2 * π * I) by simp, exp_int_mul_two_pi_mul_I, div_one]
  · rw [wrightOmega_mul_exp, exp_zetaS lam hs]

theorem zetaS_im (lam : ℝ) (s : ℂ) : (zetaS lam s).im = s.im + arg s := by
  simp [zetaS, log_im]

theorem zetaS_re (lam : ℝ) (s : ℂ) : (zetaS lam s).re = (s + log s).re - lam := by
  simp [zetaS]

/-- Off the negative axis and outside `|s| ≤ |s*|`, `ζ(s)` avoids `L±`. -/
theorem not_omegaL_zetaS {ξ₀ : ℝ} (hξ : 1 < ξ₀) {s : ℂ} (hs : s ∈ slitPlane)
    (hn : ‖sStar ξ₀‖ < ‖s‖) :
    ¬omegaLm (zetaS (Real.log ξ₀) s) ∧ ¬omegaLp (zetaS (Real.log ξ₀) s) := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := sStar_props hξ
  have hpi := Real.pi_pos
  -- on the curve `ℑs + ph s = π` beyond `s*`, `ℜζ > −1`
  have key : ∀ t : ℂ, 0 < t.im → t.im + arg t = π → ‖sStar ξ₀‖ < ‖t‖ →
      -1 < (t + log t).re - Real.log ξ₀ := by
    intro t ht harg htn
    have := green_re_lt h1 h2 ht harg htn
    linarith
  constructor
  · rintro ⟨him, hre⟩
    rw [zetaS_im] at him
    rw [zetaS_re] at hre
    have hsim : s.im < 0 := by
      rcases lt_trichotomy s.im 0 with h | h | h
      · exact h
      · have : 0 < s.re := by
          rcases mem_slitPlane_iff.mp hs with h' | h'
          · exact h'
          · exact absurd h h'
        rw [h, arg_eq_zero_iff.mpr ⟨this.le, h⟩] at him; linarith
      · have := (arg_mem_Ioo_of_im_pos h).1; linarith
    have hne : arg s ≠ π := fun h => by
      have := (arg_eq_pi_iff.mp h).2; linarith
    have hc1 : 0 < (conj s).im := by simp; linarith
    have hc2 : (conj s).im + arg (conj s) = π := by
      have ha : arg (conj s) = -arg s := by rw [arg_conj]; simp [hne]
      rw [ha, conj_im]; linarith
    have hc3 : ‖sStar ξ₀‖ < ‖conj s‖ := by rwa [RCLike.norm_conj]
    have := key _ hc1 hc2 hc3
    have hre' : (conj s + log (conj s)).re = (s + log s).re := by
      rw [log_conj _ hne, ← map_add, conj_re]
    linarith
  · rintro ⟨him, hre⟩
    rw [zetaS_im] at him
    rw [zetaS_re] at hre
    have hsim : 0 < s.im := by
      rcases lt_trichotomy s.im 0 with h | h | h
      · have := (arg_mem_Ioo_of_im_neg h).2; linarith
      · have : 0 < s.re := by
          rcases mem_slitPlane_iff.mp hs with h' | h'
          · exact h'
          · exact absurd h h'
        rw [h, arg_eq_zero_iff.mpr ⟨this.le, h⟩] at him; linarith
      · exact h
    have := key s hsim him hn
    linarith

/-- For `ℜs < −1`, `0 < ±ℑs < π/2`: `π < ±ℑζ(s) < 2π`. -/
theorem im_zetaS_bounds {s : ℂ} (hre : s.re < -1) (hpos : 0 < s.im) (hsmall : s.im < π / 2)
    (lam : ℝ) : π < (zetaS lam s).im ∧ (zetaS lam s).im < 2 * π := by
  rw [zetaS_im]
  have hpi := Real.pi_pos
  have ha := arg_mem_Ioo_of_im_pos hpos
  refine ⟨?_, by linarith [ha.2]⟩
  -- `s` is outside the `W₀` region (`ℜs < −1 < −η cot η`)
  have hcurve : -(s.im * Real.cos s.im / Real.sin s.im) > -1 := by
    have hs := Real.sin_pos_of_pos_of_lt_pi hpos (by linarith)
    have := mul_cos_lt_sin hpos (by linarith)
    have : s.im * Real.cos s.im / Real.sin s.im < 1 := by rw [div_lt_one hs]; exact this
    linarith
  have hnot : ¬|s.im + arg s| < π := fun h => by
    have := ((abs_im_add_arg_lt_pi_iff hpos.ne').mp h).2
    linarith
  push Not at hnot
  rw [abs_of_pos (by linarith [ha.1])] at hnot
  rcases hnot.lt_or_eq with h | h
  · exact h
  · obtain ⟨-, -, -⟩ := green_facts hpos h.symm
    have h2 := norm_mul_cos_arg s
    obtain ⟨hη, hn, -⟩ := green_facts hpos h.symm
    rw [show arg s = π - s.im by linarith, Real.cos_pi_sub, hn] at h2
    have : s.re = -(s.im * Real.cos s.im / Real.sin s.im) := by rw [← h2]; ring
    linarith

theorem unwinding_eq_one {ζ : ℂ} (h1 : π < ζ.im) (h2 : ζ.im < 2 * π) : unwinding ζ = 1 := by
  rw [unwinding, Int.ceil_eq_iff]
  have hpi := Real.pi_pos
  constructor
  · push_cast; rw [lt_div_iff₀ (by positivity)]; linarith
  · push_cast; rw [div_le_iff₀ (by positivity)]; linarith

theorem unwinding_eq_neg_one {ζ : ℂ} (h1 : -(2 * π) < ζ.im) (h2 : ζ.im < -π) :
    unwinding ζ = -1 := by
  rw [unwinding, Int.ceil_eq_iff]
  have hpi := Real.pi_pos
  constructor
  · push_cast; rw [lt_div_iff₀ (by positivity)]; linarith
  · push_cast; rw [div_le_iff₀ (by positivity)]; linarith

theorem zZ_ne_zero (lam : ℝ) {s : ℂ} (hs : s ≠ 0) : zZ lam s ≠ 0 := by
  rw [← exp_zetaS lam hs]; exact exp_ne_zero _

theorem im_exp_eq (ζ : ℂ) : (exp ζ).im = Real.exp ζ.re * Real.sin ζ.im := exp_im ζ

/-- Just above the negative axis, `𝒲 = W₁ ∘ Z` with `ℑZ < 0`. -/
theorem bigW_eq_W1 (lam : ℝ) {s : ℂ} (hre : s.re < -1) (hpos : 0 < s.im)
    (hsmall : s.im < π / 2) :
    bigW lam s = lambertW 1 (zZ lam s) ∧ (zZ lam s).im < 0 := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
  obtain ⟨h1, h2⟩ := im_zetaS_bounds hre hpos hsmall lam
  have hZ := exp_zetaS lam hs0
  refine ⟨?_, ?_⟩
  · rw [bigW, ite_eq_right (fun h => by linarith [h.1]), lambertW_of_ne (zZ_ne_zero lam hs0), ← hZ,
      log_exp_eq_sub_unwinding, unwinding_eq_one h1 h2]
    congr 1; push_cast; ring
  · rw [← hZ, im_exp_eq]
    refine mul_neg_of_pos_of_neg (Real.exp_pos _) ?_
    have := Real.sin_pos_of_pos_of_lt_pi (x := (zetaS lam s).im - π) (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at this; linarith

/-- Just below the negative axis, `𝒲 = W_{−1} ∘ Z` with `ℑZ > 0`. -/
theorem bigW_eq_Wm1_below (lam : ℝ) {s : ℂ} (hre : s.re < -1) (hneg : s.im < 0)
    (hsmall : -(π / 2) < s.im) :
    bigW lam s = lambertW (-1) (zZ lam s) ∧ 0 < (zZ lam s).im := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hneg; simp at hneg
  have hne : arg s ≠ π := fun h => by have := (arg_eq_pi_iff.mp h).2; linarith
  obtain ⟨h1, h2⟩ := im_zetaS_bounds (s := conj s) (by simpa using hre) (by simpa using hneg)
    (by simp; linarith) lam
  have hconj : (zetaS lam (conj s)).im = -(zetaS lam s).im := by
    rw [zetaS_im, zetaS_im, conj_im]
    have : arg (conj s) = -arg s := by rw [arg_conj]; simp [hne]
    rw [this]; ring
  rw [hconj] at h1 h2
  have hZ := exp_zetaS lam hs0
  refine ⟨?_, ?_⟩
  · rw [bigW, ite_eq_right (fun h => by linarith [h.1]), lambertW_of_ne (zZ_ne_zero lam hs0), ← hZ,
      log_exp_eq_sub_unwinding, unwinding_eq_neg_one (by linarith) (by linarith)]
    congr 1; push_cast; ring
  · rw [← hZ, im_exp_eq]
    refine mul_pos (Real.exp_pos _) ?_
    have := Real.sin_pos_of_pos_of_lt_pi (x := (zetaS lam s).im + 2 * π) (by linarith)
      (by linarith)
    rwa [Real.sin_add_two_pi] at this

/-- On the negative axis, `𝒲 = W_{−1} ∘ Z` (and `Z` is real). -/
theorem bigW_eq_Wm1_axis (lam : ℝ) {s : ℂ} (him : s.im = 0) (hre : s.re < 0) :
    bigW lam s = lambertW (-1) (zZ lam s) ∧ (zZ lam s).im = 0 := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have hZ := exp_zetaS lam hs0
  have harg : arg s = π := arg_eq_pi_iff.mpr ⟨hre, him⟩
  have hzim : (zetaS lam s).im = π := by rw [zetaS_im, him, harg, zero_add]
  have hu : unwinding (zetaS lam s) = 0 := by
    rw [unwinding, hzim, sub_self, zero_div, Int.ceil_zero]
  refine ⟨?_, ?_⟩
  · rw [bigW, ite_eq_left ⟨him, hre⟩, lambertW_of_ne (zZ_ne_zero lam hs0), ← hZ,
      log_exp_eq_sub_unwinding, hu]
    congr 1; push_cast; ring
  · rw [← hZ, im_exp_eq, hzim, Real.sin_pi, mul_zero]

theorem tendsto_bigW_piece {f Z : ℂ → ℂ} {k : ℤ} {A S : Set ℂ} {p₀ x v : ℂ}
    (hZ : Tendsto Z (𝓝 p₀) (𝓝 x)) (hW : Tendsto (lambertW k) (𝓝[S] x) (𝓝 v))
    (hS : ∀ᶠ p in 𝓝[A] p₀, Z p ∈ S ∧ f p = lambertW k (Z p)) :
    Tendsto f (𝓝[A] p₀) (𝓝 v) :=
  (hW.comp (tendsto_nhdsWithin_iff.mpr ⟨hZ.mono_left nhdsWithin_le_nhds,
    hS.mono fun _ h => h.1⟩)).congr' (hS.mono fun _ h => h.2.symm)

theorem continuous_zZ (lam : ℝ) : Continuous (zZ lam) := by unfold zZ; fun_prop

theorem zZ_ofReal (lam r : ℝ) : zZ lam r = ((r * Real.exp r * Real.exp (-lam) : ℝ) : ℂ) := by
  simp [zZ, ofReal_exp]

theorem one_lt_norm_of_sStar {ξ₀ : ℝ} (hξ : 1 < ξ₀) {s : ℂ} (hs : ‖sStar ξ₀‖ < ‖s‖) :
    1 < ‖s‖ := (sStar_props hξ).2.2.2.2.1.trans hs

/-- Points of the negative axis outside `|s*|`: `ℜs < −1` and `Z(s) ∈ (−e⁻¹, 0)`. -/
theorem axis_facts {ξ₀ : ℝ} (hξ : 1 < ξ₀) {s : ℂ} (hs : ‖sStar ξ₀‖ < ‖s‖) (hsl : s ∉ slitPlane) :
    s.im = 0 ∧ s.re < -1 ∧
      -Real.exp (-1) < s.re * Real.exp s.re * Real.exp (-Real.log ξ₀) ∧
      s.re * Real.exp s.re * Real.exp (-Real.log ξ₀) < 0 := by
  rw [mem_slitPlane_iff] at hsl
  push Not at hsl
  obtain ⟨hre, him⟩ := hsl
  have h1 := one_lt_norm_of_sStar hξ hs
  have hn : ‖s‖ = |s.re| := by
    rw [show s = (s.re : ℂ) from Complex.ext rfl (by simp [him]), norm_real, Real.norm_eq_abs]
    simp
  have hre1 : s.re < -1 := by
    rw [hn, abs_of_nonpos hre] at h1; linarith
  have he : Real.exp (-Real.log ξ₀) = ξ₀⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (by linarith)]
  have hl := neg_exp_neg_one_le_mul_exp s.re
  have hneg : s.re * Real.exp s.re < 0 := mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos _)
  refine ⟨him, hre1, ?_, ?_⟩
  · rw [he]
    have hinv : ξ₀⁻¹ < 1 := inv_lt_one_of_one_lt₀ hξ
    have hinv0 : 0 < ξ₀⁻¹ := by positivity
    have he1 := Real.exp_pos (-1)
    nlinarith
  · rw [he]; exact mul_neg_of_neg_of_pos hneg (by positivity)

/-- **Continuity** of `𝒲` outside `|s| ≤ |s*|`. -/
theorem continuousAt_bigW {ξ₀ : ℝ} (hξ : 1 < ξ₀) {s₀ : ℂ} (hs : ‖sStar ξ₀‖ < ‖s₀‖) :
    ContinuousAt (bigW (Real.log ξ₀)) s₀ := by
  set lam := Real.log ξ₀
  by_cases hsl : s₀ ∈ slitPlane
  · have hL := not_omegaL_zetaS hξ hsl hs
    have hω : ContinuousAt wrightOmega (zetaS lam s₀) :=
      (hasDerivAt_wrightOmega hL.1 hL.2).continuousAt
    have hζ : ContinuousAt (zetaS lam) s₀ :=
      (continuousAt_id.add (continuousAt_clog hsl)).sub continuousAt_const
    refine (hω.comp hζ).congr ?_
    filter_upwards [isOpen_slitPlane.mem_nhds hsl] with s hs'
    have : ¬(s.im = 0 ∧ s.re < 0) := fun h => by
      rcases mem_slitPlane_iff.mp hs' with h' | h'
      · linarith [h.2]
      · exact h' h.1
    simp only [Function.comp_apply, bigW, ite_eq_right this]
  · obtain ⟨him, hre1, hx1, hx2⟩ := axis_facts hξ hs hsl
    set x := s₀.re * Real.exp s₀.re * Real.exp (-lam)
    have hs₀ : s₀ = (s₀.re : ℂ) := Complex.ext rfl (by simp [him])
    have hZx : zZ lam s₀ = (x : ℂ) := by rw [hs₀, zZ_ofReal]
    have hZt : Tendsto (zZ lam) (𝓝 s₀) (𝓝 (x : ℂ)) := by
      rw [← hZx]; exact (continuous_zZ lam).tendsto s₀
    have hval : bigW lam s₀ = (lambertWm1 x : ℂ) := by
      rw [(bigW_eq_Wm1_axis lam him (by linarith)).1, hZx,
        lambertW_neg_one_ofReal hx1.le hx2]
    -- eventually `ℜs < −1` and `|ℑs| < π/2`
    have hpi := Real.pi_pos
    have hev : ∀ᶠ s in 𝓝 s₀, s.re < -1 ∧ -(π / 2) < s.im ∧ s.im < π / 2 := by
      have h1 := (continuous_re.tendsto s₀).eventually (Iio_mem_nhds hre1)
      have h2 := (continuous_im.tendsto s₀).eventually
        (Ioo_mem_nhds (show -(π / 2) < s₀.im by rw [him]; linarith)
          (show s₀.im < π / 2 by rw [him]; linarith))
      filter_upwards [h1, h2] with s a b
      exact ⟨a, b.1, b.2⟩
    rw [ContinuousAt, hval]
    refine tendsto_split {s | 0 < s.im} ?_ ?_
    · refine tendsto_bigW_piece (k := 1) (S := {z | z.im < 0}) hZt
        (tendsto_lambertW_one_below hx1 hx2) ?_
      filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with s ⟨a, _, c⟩ (hp : 0 < s.im)
      obtain ⟨e1, e2⟩ := bigW_eq_W1 lam a hp c
      exact ⟨e2, e1⟩
    · rw [← lambertW_neg_one_ofReal hx1.le hx2]
      refine tendsto_bigW_piece (k := -1) (S := {z | 0 ≤ z.im}) hZt
        (continuousWithinAt_lambertW_neg_one hx1 hx2) ?_
      filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with s ⟨a, b, _⟩ hp
      have hp' : s.im ≤ 0 := not_lt.mp hp
      rcases hp'.lt_or_eq with h | h
      · obtain ⟨e1, e2⟩ := bigW_eq_Wm1_below lam a h b
        exact ⟨e2.le, e1⟩
      · obtain ⟨e1, e2⟩ := bigW_eq_Wm1_axis lam h (by linarith)
        exact ⟨e2.ge, e1⟩

theorem bigW_ne_neg_one {ξ₀ : ℝ} (hξ : 1 < ξ₀) {s : ℂ} (hs : ‖sStar ξ₀‖ < ‖s‖) :
    bigW (Real.log ξ₀) s ≠ -1 := by
  set lam := Real.log ξ₀
  by_cases hsl : s ∈ slitPlane
  · have hL := not_omegaL_zetaS hξ hsl hs
    have hns : ¬(s.im = 0 ∧ s.re < 0) := fun h => by
      rcases mem_slitPlane_iff.mp hsl with h' | h'
      · linarith [h.2]
      · exact h' h.1
    rw [bigW, ite_eq_right hns]
    intro h
    have h2 := dlmf_4_13_1_2 hL.1
    rw [h, log_neg_one] at h2
    apply hL.2
    rw [← h2]
    exact ⟨by simp, by simp⟩
  · obtain ⟨him, hre1, hx1, hx2⟩ := axis_facts hξ hs hsl
    have hs₀ : s = (s.re : ℂ) := Complex.ext rfl (by simp [him])
    rw [(bigW_eq_Wm1_axis lam him (by linarith)).1]
    conv_lhs => rw [hs₀]
    rw [zZ_ofReal, lambertW_neg_one_ofReal hx1.le hx2]
    intro h
    have : lambertWm1 (s.re * Real.exp s.re * Real.exp (-lam)) = -1 := by exact_mod_cast h
    linarith [lambertWm1_lt hx1 hx2]

/-- `𝒲` is analytic outside `|s| ≤ |s*|`. -/
theorem differentiableAt_bigW {ξ₀ : ℝ} (hξ : 1 < ξ₀) {s : ℂ} (hs : ‖sStar ξ₀‖ < ‖s‖) :
    DifferentiableAt ℂ (bigW (Real.log ξ₀)) s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, norm_zero] at hs; linarith [norm_nonneg (sStar ξ₀)]
  have hZd : DifferentiableAt ℂ (zZ (Real.log ξ₀)) s := by unfold zZ; fun_prop
  refine differentiableAt_of_mul_exp (continuousAt_bigW hξ hs) hZd ?_ (bigW_ne_neg_one hξ hs)
  · filter_upwards [eventually_ne_nhds hs0] with p hp
    exact bigW_mul_exp _ hp

/-! ### Power series in `σ` -/

theorem hasFPowerSeriesOnBall_ofScalars_of_hasSum {a : ℕ → ℂ} {f : ℂ → ℂ} {r : NNReal}
    (hr : 0 < r) (C : ℝ) (hC : ∀ n, ‖a n‖ * (r : ℝ) ^ n ≤ C)
    (h : ∀ σ ∈ Metric.eball (0 : ℂ) r, HasSum (fun n => a n * σ ^ n) (f σ)) :
    HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ a) 0 r where
  r_le := FormalMultilinearSeries.le_radius_of_bound _ C fun n => by
    rw [FormalMultilinearSeries.ofScalars_norm]; exact hC n
  r_pos := by exact_mod_cast hr
  hasSum := fun {y} hy => by
    rw [zero_add]
    convert h y hy using 1
    funext n
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm]

/-- Coefficients of a power series are determined by its sum on a disc. -/
theorem coeff_eq_of_hasSum {a b : ℕ → ℂ} {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (ha : ∀ σ ∈ Metric.ball (0 : ℂ) r, HasSum (fun n => a n * σ ^ n) (f σ))
    (hb : ∀ σ ∈ Metric.ball (0 : ℂ) r, HasSum (fun n => b n * σ ^ n) (f σ)) : a = b := by
  set r' : NNReal := ⟨r / 2, by positivity⟩
  have hr' : (0 : NNReal) < r' := by
    change (0 : ℝ) < r / 2; positivity
  have hmem : ((r / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hsub : ∀ σ ∈ Metric.eball (0 : ℂ) r', σ ∈ Metric.ball (0 : ℂ) r := by
    intro σ hσ
    rw [Metric.mem_eball, edist_zero_right] at hσ
    rw [Metric.mem_ball, dist_zero_right]
    have : ‖σ‖₊ < r' := by exact_mod_cast hσ
    have : ‖σ‖ < r / 2 := by exact_mod_cast this
    linarith
  have hbound : ∀ c : ℕ → ℂ, (∀ σ ∈ Metric.ball (0 : ℂ) r, HasSum (fun n => c n * σ ^ n) (f σ)) →
      ∃ C, ∀ n, ‖c n‖ * ((r' : NNReal) : ℝ) ^ n ≤ C := by
    intro c hc
    have ht := ((hc _ hmem).summable.tendsto_atTop_zero).norm
    obtain ⟨C, hC⟩ := ht.bddAbove_range
    refine ⟨C, fun n => ?_⟩
    have := hC ⟨n, rfl⟩
    have e : ((r' : NNReal) : ℝ) = r / 2 := rfl
    rw [e]
    simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs,
      abs_of_pos (show (0 : ℝ) < r / 2 by positivity)] at this
    exact this
  obtain ⟨Ca, hCa⟩ := hbound a ha
  obtain ⟨Cb, hCb⟩ := hbound b hb
  have h1 := (hasFPowerSeriesOnBall_ofScalars_of_hasSum hr' Ca hCa fun σ hσ => ha σ (hsub σ hσ))
  have h2 := (hasFPowerSeriesOnBall_ofScalars_of_hasSum hr' Cb hCb fun σ hσ => hb σ (hsub σ hσ))
  exact FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    (h1.hasFPowerSeriesAt.eq_formalMultilinearSeries h2.hasFPowerSeriesAt)

/-- `Qₙ(λ) = ∑_{m=1}^{n} (−1)^{n+m}[n, n − m + 1] λᵐ/m!`. -/
noncomputable def lambertQ (lam : ℝ) (n : ℕ) : ℂ := lambertInner 1 lam n

theorem lambertInner_scale (lam : ℝ) (σ : ℂ) (n : ℕ) :
    lambertInner σ (lam * σ) n = σ ^ n * lambertQ lam n := by
  rw [lambertQ, lambertInner, lambertInner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn := (Finset.mem_Icc.mp hm).2
  have hp : σ ^ n = σ ^ m * σ ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' hmn]
  rw [hp, mul_pow, one_pow]
  ring

theorem norm_lambertQ_le {lam : ℝ} (hlam : 0 ≤ lam) {M : ℝ} (hM1 : 1 ≤ M) (hM : lam ≤ M) (n : ℕ) :
    ‖lambertQ lam n‖ ≤ (n + 1) * (4 * M) ^ n := by
  refine (norm_lambertInner_le _ _ n).trans ?_
  gcongr
  rw [norm_one, norm_real, Real.norm_eq_abs, abs_of_nonneg hlam]
  exact max_le hM1 hM

/-- `P(σ) = ∑ Qₙ σⁿ`. -/
noncomputable def lambertPser (lam : ℝ) (σ : ℂ) : ℂ := ∑' n, lambertQ lam n * σ ^ n

theorem norm_lambertQ_mul_le {lam : ℝ} (hlam : 0 ≤ lam) {M : ℝ} (hM1 : 1 ≤ M) (hM : lam ≤ M)
    {σ : ℂ} (hσ : ‖σ‖ < 1 / (16 * M)) (n : ℕ) : ‖lambertQ lam n * σ ^ n‖ ≤ (1 / 2) ^ n := by
  rw [norm_mul, norm_pow]
  have hM0 : 0 < M := by linarith
  have h1 := norm_lambertQ_le hlam hM1 hM n
  have h2 : 4 * M * ‖σ‖ ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left hσ.le (by positivity : (0 : ℝ) ≤ 4 * M)
    calc 4 * M * ‖σ‖ ≤ 4 * M * (1 / (16 * M)) := this
      _ = 1 / 4 := by field_simp; ring
  calc ‖lambertQ lam n‖ * ‖σ‖ ^ n ≤ (n + 1) * (4 * M) ^ n * ‖σ‖ ^ n :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (n + 1) * (4 * M * ‖σ‖) ^ n := by rw [mul_pow]; ring
    _ ≤ (2 * (4 * M * ‖σ‖)) ^ n := two_mul_pow_le n (by positivity)
    _ ≤ (1 / 2) ^ n := by gcongr; linarith

theorem hasSum_lambertP {lam : ℝ} (hlam : 0 ≤ lam) {M : ℝ} (hM1 : 1 ≤ M) (hM : lam ≤ M)
    {σ : ℂ} (hσ : ‖σ‖ < 1 / (16 * M)) :
    HasSum (fun n => lambertQ lam n * σ ^ n) (lambertPser lam σ) :=
  (Summable.of_norm_bounded (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    (norm_lambertQ_mul_le hlam hM1 hM hσ)).hasSum

theorem differentiableOn_lambertP {lam : ℝ} (hlam : 0 ≤ lam) {M : ℝ} (hM1 : 1 ≤ M)
    (hM : lam ≤ M) : DifferentiableOn ℂ (lambertPser lam) (Metric.ball 0 (1 / (16 * M))) :=
  Complex.differentiableOn_tsum_of_summable_norm
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    (fun n => (differentiable_const _ |>.mul (differentiable_pow n)).differentiableOn)
    Metric.isOpen_ball fun n σ hσ => norm_lambertQ_mul_le hlam hM1 hM (by simpa using hσ) n

/-! ### The function `g̃(σ) = 𝒲(1/σ) − 1/σ + λ` -/

/-- `g̃(σ) = 𝒲(1/σ) − 1/σ + λ` (and `0` at `σ = 0`). -/
noncomputable def gTilde (ξ₀ : ℝ) (σ : ℂ) : ℂ :=
  if σ = 0 then 0 else bigW (Real.log ξ₀) (1 / σ) - 1 / σ + Real.log ξ₀

theorem bigW_ofReal_pos (lam : ℝ) {s : ℝ} (hs : 0 < s) :
    bigW lam s = (wrightOmegaReal (s + Real.log s - lam) : ℂ) := by
  have hns : ¬((s : ℂ).im = 0 ∧ (s : ℂ).re < 0) := fun h => by
    have := h.2; simp at this; linarith
  rw [bigW, ite_eq_right hns, ← wrightOmega_ofReal, zetaS]
  congr 1
  push_cast
  rw [ofReal_log hs.le]

/-- For small `σ > 0`, `g̃(σ) = P(σ)` (the core expansion with `u = 1 − σ𝒲(1/σ)`). -/
theorem gTilde_eq_lambertPser_real {ξ₀ : ℝ} (hξ : 1 < ξ₀) {σ : ℝ} (h0 : 0 < σ)
    (hσ : σ < 1 / (16 * ξ₀)) : gTilde ξ₀ σ = lambertPser (Real.log ξ₀) σ := by
  set lam := Real.log ξ₀
  have hlam : 0 < lam := Real.log_pos hξ
  have hlamξ : lam < ξ₀ := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < ξ₀); linarith
  set s := 1 / σ
  have hs : 0 < s := by positivity
  have hsσ : s * σ = 1 := by simp only [s]; field_simp
  set W := wrightOmegaReal (s + Real.log s - lam)
  have hW0 : 0 < W := wrightOmegaReal_pos _
  have hWeq : W + Real.log W = s + Real.log s - lam := dlmf_4_13_1_2_real _
  have hWs : W < s := by
    by_contra h; push Not at h
    have := Real.log_le_log hs h; linarith
  have hWs' : s - lam ≤ W := by
    have := Real.log_le_log hW0 hWs.le; linarith
  set u : ℝ := 1 - W / s
  have hu0 : 0 ≤ u := by simp only [u]; rw [sub_nonneg, div_le_one hs]; exact hWs.le
  have hu1 : u ≤ lam * σ := by
    simp only [u]
    rw [show lam * σ = lam / s by simp only [s]; field_simp]
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hs]; linarith
  have hlσ : lam * σ < 1 / 16 := by
    calc lam * σ < ξ₀ * (1 / (16 * ξ₀)) := mul_lt_mul hlamξ hσ.le h0 (by linarith)
      _ = 1 / 16 := by field_simp
  have hu1' : u < 1 := by linarith
  -- `L(u) = W − s + λ`
  have hL : -Real.log (1 - u) = W - s + lam := by
    have h1 : 1 - u = W / s := by simp only [u]; ring
    rw [h1, Real.log_div hW0.ne' hs.ne']; linarith
  have heq : (u : ℂ) = ((lam * σ : ℝ) : ℂ) - (σ : ℂ) * lambertLogL (u : ℂ) := by
    rw [lagL_ofReal hu1', hL]
    have hWs2 : W / s = W * σ := by simp only [s]; field_simp
    have : u = lam * σ - σ * (W - s + lam) := by
      simp only [u]; rw [hWs2]; linear_combination -hsσ
    exact_mod_cast this
  have hσ1 : ‖(σ : ℂ)‖ ≤ 1 / 4 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos h0]
    have : 1 / (16 * ξ₀) ≤ 1 / 16 := by
      rw [div_le_div_iff_of_pos_left (by norm_num) (by positivity) (by norm_num)]; linarith
    linarith
  have hτ1 : ‖((lam * σ : ℝ) : ℂ)‖ ≤ 1 / 8 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith
  have hu2 : ‖(u : ℂ)‖ ≤ 1 / 2 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]; linarith
  have h := hasSum_lambertInner hσ1 hτ1 hu2 heq
  rw [lagL_ofReal hu1', hL] at h
  have h' : HasSum (fun n => lambertQ lam n * (σ : ℂ) ^ n) ((W - s + lam : ℝ) : ℂ) := by
    convert h using 1; funext n
    rw [show ((lam * σ : ℝ) : ℂ) = (lam : ℂ) * (σ : ℂ) by push_cast; ring, lambertInner_scale,
      mul_comm]
  have hP := hasSum_lambertP hlam.le (M := ξ₀) hξ.le hlamξ.le
    (by rw [norm_real, Real.norm_eq_abs, abs_of_pos h0]; exact hσ)
  rw [hP.unique h', gTilde, ite_eq_right (by exact_mod_cast h0.ne'),
    show (1 / (σ : ℂ)) = ((1 / σ : ℝ) : ℂ) by push_cast; ring, bigW_ofReal_pos lam hs]
  simp only [W, s, lam]
  push_cast; ring

/-- The punctured disc is connected. -/
theorem isPreconnected_ball_diff_zero {r : ℝ} :
    IsPreconnected (Metric.ball (0 : ℂ) r \ {0}) := by
  have h : Metric.ball (0 : ℂ) r \ {0} =
      (fun p : ℝ × ℝ => (p.1 : ℂ) * exp (p.2 * I)) '' (Ioo 0 r ×ˢ univ) := by
    ext σ
    constructor
    · rintro ⟨hb, hne⟩
      refine ⟨(‖σ‖, arg σ), ⟨⟨norm_pos_iff.mpr hne, by simpa using hb⟩, trivial⟩, ?_⟩
      exact norm_mul_exp_arg_mul_I σ
    · rintro ⟨⟨t, θ⟩, ⟨⟨ht0, htr⟩, -⟩, rfl⟩
      dsimp only
      have hn : ‖(t : ℂ) * exp (θ * I)‖ = t := by
        rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_eq_abs,
          abs_of_pos ht0]
      refine ⟨by rw [Metric.mem_ball, dist_zero_right, hn]; exact htr, fun h => ?_⟩
      rw [Set.mem_singleton_iff] at h
      rw [h, norm_zero] at hn; linarith
  rw [h]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ (by fun_prop)

theorem differentiableAt_gTilde {ξ₀ : ℝ} (hξ : 1 < ξ₀) {σ : ℂ} (hσ0 : σ ≠ 0)
    (hσ : ‖σ‖ < 1 / ‖sStar ξ₀‖) : DifferentiableAt ℂ (gTilde ξ₀) σ := by
  have hs1 := (sStar_props hξ).2.2.2.2.1
  have hn : ‖sStar ξ₀‖ < ‖1 / σ‖ := by
    rw [norm_div, norm_one]
    rw [lt_div_iff₀ (norm_pos_iff.mpr hσ0)]
    rw [lt_div_iff₀ (by linarith)] at hσ
    linarith
  have hd : DifferentiableAt ℂ (fun σ => bigW (Real.log ξ₀) (1 / σ) - 1 / σ + Real.log ξ₀) σ := by
    have hinv : DifferentiableAt ℂ (fun σ : ℂ => 1 / σ) σ :=
      (differentiableAt_const _).div differentiableAt_id hσ0
    exact (((differentiableAt_bigW hξ hn).comp σ hinv).sub hinv).add_const _
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [eventually_ne_nhds hσ0] with p hp
  simp [gTilde, hp]

theorem lambertQ_zero (lam : ℝ) : lambertQ lam 0 = 0 := by simp [lambertQ, lambertInner]

theorem hasSum_lambertQ_zero (lam : ℝ) : HasSum (fun n => lambertQ lam n * (0 : ℂ) ^ n) 0 := by
  have : (fun n => lambertQ lam n * (0 : ℂ) ^ n) = fun _ => 0 := by
    funext n; rcases n with _ | n
    · simp [lambertQ_zero]
    · simp
  rw [this]; exact hasSum_zero

theorem gTilde_eqOn {ξ₀ : ℝ} (hξ : 1 < ξ₀) :
    EqOn (gTilde ξ₀) (lambertPser (Real.log ξ₀)) (Metric.ball 0 (1 / (16 * ξ₀)) \ {0}) := by
  set δ := 1 / (16 * ξ₀)
  have hδ : 0 < δ := by positivity
  have hlam : 0 < Real.log ξ₀ := Real.log_pos hξ
  have hlamξ : Real.log ξ₀ ≤ ξ₀ := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < ξ₀); linarith
  obtain ⟨-, -, -, -, hs1, hsξ⟩ := sStar_props hξ
  have hδs : δ < 1 / ‖sStar ξ₀‖ := by
    simp only [δ]
    rw [div_lt_div_iff_of_pos_left (by norm_num) (by positivity) (by linarith)]; linarith
  set U := Metric.ball (0 : ℂ) δ \ {0}
  have hUo : IsOpen U := Metric.isOpen_ball.sdiff isClosed_singleton
  have hf : AnalyticOnNhd ℂ (gTilde ξ₀) U := by
    refine DifferentiableOn.analyticOnNhd (fun σ hσ => ?_) hUo
    have hσ0 : σ ≠ 0 := hσ.2
    have : ‖σ‖ < δ := by simpa using hσ.1
    exact (differentiableAt_gTilde hξ hσ0 (by linarith)).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (lambertPser (Real.log ξ₀)) U :=
    ((differentiableOn_lambertP hlam.le hξ.le hlamξ).mono sdiff_subset).analyticOnNhd hUo
  have hz₀ : ((δ / 2 : ℝ) : ℂ) ∈ U := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    · simp only [Set.mem_singleton_iff, ofReal_eq_zero]; positivity
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] (δ / 2),
      gTilde ξ₀ (t : ℂ) = lambertPser (Real.log ξ₀) (t : ℂ) := by
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith : (0 : ℝ) < δ / 2)
      (by linarith : δ / 2 < δ))] with t ht
    exact gTilde_eq_lambertPser_real hξ ht.1 ht.2
  have hT : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (δ / 2)) (𝓝[≠] ((δ / 2 : ℝ) : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun t ht => by
        rw [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
        exact_mod_cast ht⟩
  exact hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_ball_diff_zero hz₀
    (hT.frequently hev.frequently)

/-- **DLMF §4.13** (after 4.13.10): for `k = 0` and real `z ≥ e` the series 4.13.10 converges
to `W₀(z)`: `W₀(z) = ξ − ln ξ + ∑_{n ≥ 1} (−1)ⁿ ξ^{−n} ∑_{m=1}^{n} [n, n − m + 1] (−ln ξ)ᵐ/m!`,
`ξ = ln z`. -/
theorem dlmf_4_13_10_real {z : ℝ} (hz : Real.exp 1 ≤ z) :
    HasSum (fun n => dlmfTerm10 (log (z : ℂ)) (n + 1))
      (lambertW 0 z - (log (z : ℂ) - log (log (z : ℂ)))) := by
  have hz0 : 0 < z := lt_of_lt_of_le (Real.exp_pos 1) hz
  rcases hz.lt_or_eq with hz' | hz'
  · set ξ₀ := Real.log z
    have hξ : 1 < ξ₀ := by rw [Real.lt_log_iff_exp_lt hz0]; exact hz'
    set lam := Real.log ξ₀
    have hlam : 0 < lam := Real.log_pos hξ
    have hlamξ : lam ≤ ξ₀ := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < ξ₀); linarith
    obtain ⟨-, -, -, -, hs1, hsξ⟩ := sStar_props hξ
    set r₀ := (‖sStar ξ₀‖ + ξ₀) / 2
    set R := 1 / r₀
    have hr₀ : ‖sStar ξ₀‖ < r₀ := by simp only [r₀]; linarith
    have hr₀ξ : r₀ < ξ₀ := by simp only [r₀]; linarith
    have hR : 0 < R := by simp only [R]; positivity
    set δ := 1 / (16 * ξ₀)
    have hδR : δ ≤ R := by
      simp only [δ, R]
      rw [div_le_div_iff_of_pos_left (by norm_num) (by positivity) (by linarith)]; linarith
    have hP0 : lambertPser lam 0 = 0 :=
      (hasSum_lambertP hlam.le hξ.le hlamξ (by simp; positivity)).unique (hasSum_lambertQ_zero lam)
    have heqon := gTilde_eqOn hξ
    -- continuity at `0`
    have hcont : ContinuousAt (gTilde ξ₀) 0 := by
      have hPc : ContinuousAt (lambertPser lam) 0 :=
        ((differentiableOn_lambertP hlam.le hξ.le hlamξ).differentiableAt
          (Metric.ball_mem_nhds 0 (by positivity))).continuousAt
      refine hPc.congr ?_
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < δ by positivity)] with σ hσ
      by_cases h0 : σ = 0
      · rw [h0, hP0]; simp [gTilde]
      · exact (heqon ⟨hσ, h0⟩).symm
    have hd : DifferentiableOn ℂ (gTilde ξ₀) (Metric.ball 0 R) := by
      rw [← Complex.differentiableOn_compl_singleton_and_continuousAt_iff
        (Metric.ball_mem_nhds 0 hR)]
      refine ⟨fun σ hσ => ?_, hcont⟩
      have h1 : ‖σ‖ < R := by simpa using hσ.1
      have h2 : R < 1 / ‖sStar ξ₀‖ := by
        simp only [R]
        rw [div_lt_div_iff_of_pos_left (by norm_num) (by linarith) (by linarith)]; exact hr₀
      exact (differentiableAt_gTilde hξ hσ.2 (by linarith)).differentiableWithinAt
    -- the Taylor coefficients at `0` are the `Qₙ`
    have hcoef : (fun n => (Nat.factorial n : ℂ)⁻¹ * iteratedDeriv n (gTilde ξ₀) 0) =
        lambertQ lam := by
      refine coeff_eq_of_hasSum (f := gTilde ξ₀) (r := δ) (by positivity) (fun σ hσ => ?_)
        (fun σ hσ => ?_)
      · have := Complex.hasSum_taylorSeries_on_ball (hd.mono (Metric.ball_subset_ball hδR))
          (by simpa using hσ)
        simp only [sub_zero, smul_eq_mul] at this
        convert this using 2 with n; ring
      · by_cases h0 : σ = 0
        · rw [h0]; simpa [gTilde] using hasSum_lambertQ_zero lam
        · rw [heqon ⟨hσ, h0⟩]
          have hσ' : ‖σ‖ < δ := by simpa using hσ
          exact hasSum_lambertP hlam.le hξ.le hlamξ hσ'
    set σ₀ : ℂ := ((ξ₀⁻¹ : ℝ) : ℂ)
    have hσ₀ : σ₀ ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      simp only [R]
      rw [one_div]; exact inv_strictAnti₀ (by linarith) hr₀ξ
    have hT := Complex.hasSum_taylorSeries_on_ball hd hσ₀
    simp only [sub_zero, smul_eq_mul] at hT
    have hT' : HasSum (fun n => lambertQ lam n * σ₀ ^ n) (gTilde ξ₀ σ₀) := by
      convert hT using 2 with n
      rw [← hcoef]; ring
    -- the value and the terms
    have hξ0 : (ξ₀ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : ξ₀ ≠ 0)
    have hlogz : log (z : ℂ) = (ξ₀ : ℂ) := (ofReal_log hz0.le).symm
    have hloglog : log (ξ₀ : ℂ) = (lam : ℂ) := (ofReal_log (by linarith)).symm
    have hval : gTilde ξ₀ σ₀ = lambertW 0 z - (log (z : ℂ) - log (log (z : ℂ))) := by
      have hσ₀0 : σ₀ ≠ 0 := by simp only [σ₀]; exact_mod_cast (inv_pos.mpr (by linarith)).ne'
      rw [gTilde, ite_eq_right hσ₀0, show 1 / σ₀ = (ξ₀ : ℂ) by simp [σ₀],
        bigW_ofReal_pos lam (by linarith), hlogz, hloglog,
        lambertW_zero_ofReal (by linarith [Real.exp_pos (-1)] : -Real.exp (-1) ≤ z)]
      have : wrightOmegaReal (ξ₀ + Real.log ξ₀ - lam) = lambertW0 z := by
        rw [show ξ₀ + Real.log ξ₀ - lam = ξ₀ by simp [lam], wrightOmegaReal,
          Real.exp_log hz0]
      rw [this]; ring
    have hterm : ∀ n, dlmfTerm10 (log (z : ℂ)) n = lambertQ lam n * σ₀ ^ n := by
      intro n
      rw [hlogz, ← lambertInner_eq_dlmfTerm10 hξ0, hloglog,
        show (lam : ℂ) / ξ₀ = (lam : ℂ) * σ₀ by simp [σ₀, div_eq_mul_inv],
        show ((ξ₀ : ℂ))⁻¹ = σ₀ by simp [σ₀], lambertInner_scale, mul_comm]
    rw [← hval]
    have := (hasSum_nat_add_iff' 1).mpr hT'
    simp only [Finset.range_one, Finset.sum_singleton, lambertQ_zero, zero_mul, sub_zero] at this
    simpa [hterm] using this
  · -- `z = e`: all terms vanish
    subst hz'
    have hl : log ((Real.exp 1 : ℝ) : ℂ) = 1 := by
      rw [← ofReal_log (Real.exp_pos 1).le, Real.log_exp]; simp
    rw [hl, log_one, dlmf_4_13_2.2.2.2]
    have : (fun n => dlmfTerm10 1 (n + 1)) = fun _ => 0 := by
      funext n
      rw [dlmfTerm10, log_one, neg_zero]
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun m hm => ?_)
      have hm1 : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
      simp [zero_pow hm1]
    rw [this]; simp

end Azurite.DLMF
