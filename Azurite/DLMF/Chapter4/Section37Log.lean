/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section35
import Azurite.DLMF.Chapter4.Section37

/-!
# DLMF §4.37(iv) Logarithmic Forms (inverse hyperbolic functions)

"Throughout this subsection all quantities assume their principal values." Values on the cuts
are the limits from the two sides (as in §4.23(iv)).

* 4.37.16–4.37.18 (`arcsinh`): `dlmf_4_37_16`, `dlmf_4_37_17`, `dlmf_4_37_18`, from 4.23.19–4.23.21
  at `iz`.
* 4.37.19–4.37.23 (`arccosh`): `dlmf_4_37_19` (the sign by `ℜz ≷ 0`: `coshRoot_eq_sqrt`, via
  `branch_eq_of_sq` on the right half-plane, star-shaped about `2`), `dlmf_4_37_20`,
  `dlmf_4_37_21` (Kahan), `dlmf_4_37_22`, `dlmf_4_37_23` (one-sided limits of the principal square
  root, `tendsto_sqrt_upper_nonpos`, `tendsto_sqrt_lower_nonpos`).
* 4.37.24–4.37.25 (`arctanh`): `dlmf_4_37_24`, `dlmf_4_37_25`, from 4.23.26–4.23.27 at `iz`.
* "Other Inverse Functions" (`arccsch`, `arcsech`, `arccoth`, via 4.37.7–4.37.9): logarithmic forms
  `dlmf_4_37_iv_arccsch`, `dlmf_4_37_iv_arcsech`, `dlmf_4_37_iv_arcsech_kahan`,
  `dlmf_4_37_iv_arccoth`, and values on their cuts `dlmf_4_37_iv_arccsch_cut`,
  `dlmf_4_37_iv_arcsech_cut`, `dlmf_4_37_iv_arccoth_cut` (with `1/(x ± i0) = 1/x ∓ i0`).
-/

open Set Filter Topology Complex
open scoped Real

namespace Azurite.DLMF

/-! ### Tools -/

/-- The principal square root lies in the closed right half-plane. -/
theorem zero_le_re_cpow_half (w : ℂ) : 0 ≤ (w ^ (1 / 2 : ℂ)).re := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  rw [cpow_def_of_ne_zero hw, exp_re]
  apply mul_nonneg (Real.exp_pos _).le
  apply Real.cos_nonneg_of_mem_Icc
  have h1 := neg_pi_lt_arg w
  have h2 := arg_le_pi w
  have : (log w * (1 / 2 : ℂ)).im = arg w / 2 := by simp [log_im, div_eq_mul_inv]
  rw [this]
  constructor <;> linarith

/-- `log v = −log u` when `u v = 1` and `u + v = 2S` with `ℜS ≥ 0`. -/
theorem log_eq_neg_log_of_mul_eq_one {u v S : ℂ} (h : u * v = 1) (hs : u + v = 2 * S)
    (hS : 0 ≤ S.re) : log v = -log u := by
  have hu : u ≠ 0 := left_ne_zero_of_mul_eq_one h
  have hv : v = u⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [hv, log_inv u fun harg => ?_]
  obtain ⟨hre, him⟩ := arg_eq_pi_iff.mp harg
  have hvre : v.re < 0 := by
    rw [hv, inv_re]; exact div_neg_of_neg_of_pos hre (normSq_pos.mpr hu)
  have := congrArg re hs
  simp only [add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero] at this
  linarith

theorem log_mul_I_of_pos {r : ℝ} (hr : 0 < r) : log ((r : ℂ) * I) = Real.log r + π / 2 * I := by
  apply Complex.ext
  · simp [log_re, abs_of_pos hr]
  · simp [log_im, arg_real_mul _ hr]

theorem log_mul_neg_I_of_pos {r : ℝ} (hr : 0 < r) :
    log ((r : ℂ) * -I) = Real.log r - π / 2 * I := by
  apply Complex.ext
  · simp [log_re, abs_of_pos hr]
  · rw [log_im, arg_real_mul _ hr, arg_neg_I]; simp

/-! ### Inverse hyperbolic sine -/

/-- **DLMF 4.37.16**: `arcsinh z = ln((z² + 1)^{1/2} + z)`, `z/i ∈ ℂ ∖ ((−∞, −1) ∪ (1, ∞))` (off
the cuts, or `z = ±i`). -/
theorem dlmf_4_37_16 {z : ℂ} (hz : z ∈ arcsinhCut ∨ z = I ∨ z = -I) :
    arcsinhD z = log ((z ^ 2 + 1) ^ (1 / 2 : ℂ) + z) := by
  have hw : I * z ∈ arcsinCut ∨ I * z = 1 ∨ I * z = -1 := by
    rcases hz with hz | rfl | rfl
    · exact Or.inl (I_mul_mem_arcsinCut.mpr hz)
    · right; right; rw [I_mul_I]
    · right; left; rw [mul_neg, I_mul_I, neg_neg]
  set S := (z ^ 2 + 1) ^ (1 / 2 : ℂ) with hS
  have h := dlmf_4_23_19 hw
  rw [show (1 : ℂ) - (I * z) ^ 2 = z ^ 2 + 1 by ring_nf; rw [I_sq]; ring,
    show I * (I * z) = -z by rw [← mul_assoc, I_mul_I]; ring, ← hS] at h
  rw [arcsinhD_eq, h, show -I * (-I * log (S + -z)) = -log (S + -z) by
    ring_nf; rw [I_sq]; ring]
  have hS2 : S ^ 2 = z ^ 2 + 1 := sqrt_half_sq _
  exact (log_eq_neg_log_of_mul_eq_one (by linear_combination hS2) (by ring)
    (zero_le_re_cpow_half _)).symm

/-- **DLMF 4.37.17** (on the cut `[i, i∞)`): `arcsinh(iy) = ½πi ± ln((y² − 1)^{1/2} + y)`,
`y ∈ [1, ∞)`, the upper/lower sign for the right/left side. -/
theorem dlmf_4_37_17 {y : ℝ} :
    (1 < y → Tendsto arcsinhD (𝓝[{z | 0 < z.re}] (y * I))
        (𝓝 (π / 2 * I + (Real.log (√(y ^ 2 - 1) + y) : ℂ))) ∧
      Tendsto arcsinhD (𝓝[{z | z.re < 0}] (y * I))
        (𝓝 (π / 2 * I - (Real.log (√(y ^ 2 - 1) + y) : ℂ)))) ∧
    arcsinhD I = π / 2 * I := by
  have he : arcsinhD = fun z => -I * arcsinD (I * z) := funext arcsinhD_eq
  refine ⟨fun hy => ?_, ?_⟩
  · obtain ⟨-, h2, -⟩ := dlmf_4_23_20_21 (x := -y)
    obtain ⟨e1, e2⟩ := h2 (by linarith)
    obtain ⟨t1, t2⟩ := tendsto_I_mul_re_side y
    rw [neg_sq, sub_neg_eq_add] at e1 e2
    rw [he]
    constructor
    · have h := (e1.comp t1).const_mul (-I)
      rw [show -I * (-(π / 2 : ℂ) + I * (Real.log (√(y ^ 2 - 1) + y) : ℂ)) =
        π / 2 * I + (Real.log (√(y ^ 2 - 1) + y) : ℂ) by
          linear_combination -(Real.log (√(y ^ 2 - 1) + y) : ℂ) * I_sq] at h
      exact h
    · have h := (e2.comp t2).const_mul (-I)
      rw [show -I * (-(π / 2 : ℂ) - I * (Real.log (√(y ^ 2 - 1) + y) : ℂ)) =
        π / 2 * I - (Real.log (√(y ^ 2 - 1) + y) : ℂ) by
          linear_combination (Real.log (√(y ^ 2 - 1) + y) : ℂ) * I_sq] at h
      exact h
  · rw [arcsinhD_eq, I_mul_I, (dlmf_4_23_20_21 (x := 0)).2.2.2]; ring

/-- **DLMF 4.37.18** (on the cut `(−i∞, −i]`): `arcsinh(iy) = −½πi ± ln((y² − 1)^{1/2} − y)`,
`y ∈ (−∞, −1]`, the upper/lower sign for the right/left side. -/
theorem dlmf_4_37_18 {y : ℝ} :
    (y < -1 → Tendsto arcsinhD (𝓝[{z | 0 < z.re}] (y * I))
        (𝓝 (-(π / 2 * I) + (Real.log (√(y ^ 2 - 1) - y) : ℂ))) ∧
      Tendsto arcsinhD (𝓝[{z | z.re < 0}] (y * I))
        (𝓝 (-(π / 2 * I) - (Real.log (√(y ^ 2 - 1) - y) : ℂ)))) ∧
    arcsinhD (-I) = -(π / 2 * I) := by
  have he : arcsinhD = fun z => -I * arcsinD (I * z) := funext arcsinhD_eq
  refine ⟨fun hy => ?_, ?_⟩
  · obtain ⟨h1, -, -⟩ := dlmf_4_23_20_21 (x := -y)
    obtain ⟨e1, e2⟩ := h1 (by linarith)
    obtain ⟨t1, t2⟩ := tendsto_I_mul_re_side y
    rw [neg_sq, ← sub_eq_add_neg] at e1 e2
    rw [he]
    constructor
    · have h := (e1.comp t1).const_mul (-I)
      rw [show -I * ((π / 2 : ℂ) + I * (Real.log (√(y ^ 2 - 1) - y) : ℂ)) =
        -(π / 2 * I) + (Real.log (√(y ^ 2 - 1) - y) : ℂ) by
          linear_combination -(Real.log (√(y ^ 2 - 1) - y) : ℂ) * I_sq] at h
      exact h
    · have h := (e2.comp t2).const_mul (-I)
      rw [show -I * ((π / 2 : ℂ) - I * (Real.log (√(y ^ 2 - 1) - y) : ℂ)) =
        -(π / 2 * I) - (Real.log (√(y ^ 2 - 1) - y) : ℂ) by
          linear_combination (Real.log (√(y ^ 2 - 1) - y) : ℂ) * I_sq] at h
      exact h
  · rw [arcsinhD_eq, mul_neg, I_mul_I, neg_neg, (dlmf_4_23_20_21 (x := 0)).2.2.1]; ring

/-! ### Inverse hyperbolic tangent -/

/-- **DLMF 4.37.24**: `arctanh z = ½ ln((1 + z)/(1 − z))`, `z ∈ ℂ ∖ ((−∞, −1] ∪ [1, ∞))`. -/
theorem dlmf_4_37_24 {z : ℂ} (hz : z ∈ arctanhCut) :
    arctanhD z = 1 / 2 * log ((1 + z) / (1 - z)) := by
  rw [arctanhD_eq, dlmf_4_23_26 (I_mul_mem_arctanCut.mpr hz),
    show (I + I * z) / (I - I * z) = (1 + z) / (1 - z) by
      rw [show I + I * z = I * (1 + z) by ring, show I - I * z = I * (1 - z) by ring,
        mul_div_mul_left _ _ I_ne_zero]]
  ring_nf; rw [I_sq]; ring

/-- **DLMF 4.37.25** (on the cuts): `arctanh x = ±½πi + ½ ln((x + 1)/(x − 1))`,
`x ∈ (−∞, −1) ∪ (1, ∞)`, the upper/lower sign for the upper/lower side. -/
theorem dlmf_4_37_25 {x : ℝ} (hx : 1 < |x|) :
    Tendsto arctanhD (𝓝[{w | 0 < w.im}] (x : ℂ))
        (𝓝 (π / 2 * I + 1 / 2 * (Real.log ((x + 1) / (x - 1)) : ℂ))) ∧
      Tendsto arctanhD (𝓝[{w | w.im < 0}] (x : ℂ))
        (𝓝 (-(π / 2 * I) + 1 / 2 * (Real.log ((x + 1) / (x - 1)) : ℂ))) := by
  obtain ⟨e1, e2⟩ := dlmf_4_23_27 hx
  obtain ⟨t1, t2⟩ := tendsto_I_mul_side x
  have he : arctanhD = fun z => -I * arctanD (I * z) := funext arctanhD_eq
  rw [he]
  set L : ℂ := (Real.log ((x + 1) / (x - 1)) : ℂ)
  constructor
  · have h := (e2.comp t1).const_mul (-I)
    rw [show -I * (-(π / 2 : ℂ) + I / 2 * L) = π / 2 * I + 1 / 2 * L by
      linear_combination -(L / 2) * I_sq] at h
    exact h
  · have h := (e1.comp t2).const_mul (-I)
    rw [show -I * ((π / 2 : ℂ) + I / 2 * L) = -(π / 2 * I) + 1 / 2 * L by
      linear_combination -(L / 2) * I_sq] at h
    exact h

/-! ### Inverse hyperbolic cosine -/

theorem sq_sub_one_mem_slitPlane {z : ℂ} (hz : z ∈ arccoshCut) (hre : 0 < z.re) :
    z ^ 2 - 1 ∈ slitPlane := by
  have e1 : (z ^ 2 - 1).re = z.re ^ 2 - z.im ^ 2 - 1 := by simp [sq]
  have e2 : (z ^ 2 - 1).im = 2 * z.re * z.im := by simp [sq]; ring
  rw [mem_slitPlane_iff]
  by_cases him : z.im = 0
  · left
    have h1 : 1 < z.re := hz.resolve_left (not_not.mpr him)
    rw [e1, him]; nlinarith
  · right
    rw [e2]; exact mul_ne_zero (mul_ne_zero two_ne_zero hre.ne') him

theorem smul_combo_re (a b : ℝ) (w : ℂ) :
    (a • ((2 : ℝ) : ℂ) + b • w).re = 2 * a + b * w.re := by
  simp [Complex.real_smul]; ring

theorem smul_combo_im (a b : ℝ) (w : ℂ) : (a • ((2 : ℝ) : ℂ) + b • w).im = b * w.im := by
  simp [Complex.real_smul]

/-- `{ℜz > 0} ∖ (0, 1]` is star-shaped about `2`. -/
theorem starConvex_right_cut :
    StarConvex ℝ ((2 : ℝ) : ℂ) ({w : ℂ | 0 < w.re} ∩ arccoshCut) := by
  intro w hw a b ha hb hab
  obtain ⟨hw1, hw2⟩ := hw
  have hw1' : 0 < w.re := hw1
  refine ⟨?_, ?_⟩
  · show 0 < (a • ((2 : ℝ) : ℂ) + b • w).re
    rw [smul_combo_re]
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · rw [← hb0] at hab ⊢; linarith
    · nlinarith [mul_pos hb0 hw1']
  · show (a • ((2 : ℝ) : ℂ) + b • w) ∈ arccoshCut
    rcases hw2 with h | h
    · rcases eq_or_lt_of_le hb with hb0 | hb0
      · right; rw [smul_combo_re, ← hb0]; rw [← hb0, add_zero] at hab; rw [hab]; norm_num
      · left; rw [smul_combo_im]; exact mul_ne_zero hb0.ne' h
    · right; rw [smul_combo_re]
      rcases eq_or_lt_of_le ha with ha0 | ha0
      · rw [← ha0] at hab ⊢; rw [zero_add] at hab; rw [hab]; linarith
      · nlinarith [mul_nonneg hb (sub_nonneg.2 h.le)]

/-- On the right half-plane (off the cut), the branch `coshRoot` of 4.37.2 is the principal
`(z² − 1)^{1/2}`. -/
theorem coshRoot_eq_sqrt {z : ℂ} (hz : z ∈ arccoshCut) (hre : 0 < z.re) :
    coshRoot z = (z ^ 2 - 1) ^ (1 / 2 : ℂ) := by
  set R : Set ℂ := {w | 0 < w.re} ∩ arccoshCut with hR
  have h2 : ((2 : ℝ) : ℂ) ∈ R := ⟨by simp, Or.inr (by norm_num)⟩
  have hpre : IsPreconnected R :=
    (starConvex_right_cut.isPathConnected h2).isConnected.isPreconnected
  have hsl : ∀ w ∈ R, w ^ 2 - 1 ∈ slitPlane := fun w hw => sq_sub_one_mem_slitPlane hw.2 hw.1
  have hc1 : ContinuousOn coshRoot R := fun w hw =>
    (hasDerivAt_coshRoot hw.2).continuousAt.continuousWithinAt
  have hc2 : ContinuousOn (fun w : ℂ => (w ^ 2 - 1) ^ (1 / 2 : ℂ)) R := fun w hw =>
    (ContinuousAt.comp (g := fun x : ℂ => x ^ (1 / 2 : ℂ)) (f := fun w : ℂ => w ^ 2 - 1)
      (continuousAt_cpow_const (hsl w hw)) (by fun_prop)).continuousWithinAt
  have hne : ∀ w ∈ R, (w ^ 2 - 1) ^ (1 / 2 : ℂ) ≠ 0 := fun w hw =>
    cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero (hsl w hw)))
  have hsq : ∀ w ∈ R, coshRoot w ^ 2 = ((w ^ 2 - 1) ^ (1 / 2 : ℂ)) ^ 2 := fun w _ => by
    rw [coshRoot_sq, sqrt_half_sq]
  have h0 : coshRoot ((2 : ℝ) : ℂ) = (((2 : ℝ) : ℂ) ^ 2 - 1) ^ (1 / 2 : ℂ) := by
    rw [(coshRoot_ofReal (by norm_num : (1 : ℝ) ≤ 2)).1,
      (coshRoot_ofReal (by norm_num : (1 : ℝ) ≤ 2)).2]
  exact branch_eq_of_sq hpre hc1 hc2 hne hsq h2 h0 z ⟨hre, hz⟩

theorem arccoshD_one : arccoshD 1 = 0 := by
  have := arccoshD_ofReal (x := 1) le_rfl
  simp only [ofReal_one] at this
  rw [this]; simp [Real.arcosh]

/-- **DLMF 4.37.19**: `arccosh z = ln(±(z² − 1)^{1/2} + z)`, `z ∈ ℂ ∖ (−∞, 1)`, the upper or lower
sign according as `ℜz ≷ 0`. -/
theorem dlmf_4_37_19 {z : ℂ} (hz : z ∈ arccoshCut ∨ z = 1) :
    (0 < z.re → arccoshD z = log ((z ^ 2 - 1) ^ (1 / 2 : ℂ) + z)) ∧
      (z.re < 0 → arccoshD z = log (-(z ^ 2 - 1) ^ (1 / 2 : ℂ) + z)) := by
  refine ⟨fun hre => ?_, fun hre => ?_⟩
  · rcases hz with hz | rfl
    · rw [arccoshD_eq_log hz, coshRoot_eq_sqrt hz hre, add_comm]
    · rw [arccoshD_one]; simp
  · have hz' : z ∈ arccoshCut := hz.resolve_right fun h => by rw [h] at hre; norm_num at hre
    have him : z.im ≠ 0 := hz'.resolve_right fun h => by linarith
    have hneg : -z ∈ arccoshCut := Or.inl (by simpa using him)
    have h := coshRoot_eq_sqrt hneg (by simp; linarith)
    rw [coshRoot_neg him, neg_sq] at h
    rw [arccoshD_eq_log hz', show coshRoot z = -(z ^ 2 - 1) ^ (1 / 2 : ℂ) by
      linear_combination -h, add_comm]

theorem eq_of_sq_eq_of_im {a b : ℂ} (h : a ^ 2 = b ^ 2) (hb : 0 < b.im) (ha : 0 ≤ a.im) :
    a = b := by
  have : (a - b) * (a + b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h' | h'
  · linear_combination h'
  · have := congrArg im h'
    simp at this
    linarith

/-- **DLMF 4.37.20**: `arccosh(iy) = ±½πi + ln((y² + 1)^{1/2} ± y)`, `y ≷ 0`. -/
theorem dlmf_4_37_20 {y : ℝ} :
    (0 < y → arccoshD (y * I) = π / 2 * I + (Real.log (√(y ^ 2 + 1) + y) : ℂ)) ∧
      (y < 0 → arccoshD (y * I) = -(π / 2 * I) + (Real.log (√(y ^ 2 + 1) - y) : ℂ)) := by
  have hs : 0 < √(y ^ 2 + 1) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : (√(y ^ 2 + 1) : ℂ) ^ 2 = y ^ 2 + 1 := by
    rw [← ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hsq : coshRoot ((y : ℂ) * I) ^ 2 = (I * (√(y ^ 2 + 1) : ℂ)) ^ 2 := by
    rw [coshRoot_sq, mul_pow, mul_pow, hs2, I_sq]; ring
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · have him : 0 < ((y : ℂ) * I).im := by simpa using hy
    have hq : coshRoot ((y : ℂ) * I) = I * (√(y ^ 2 + 1) : ℂ) :=
      eq_of_sq_eq_of_im hsq (by simpa using hs) (im_coshRoot_nonneg him)
    have hpos : 0 < √(y ^ 2 + 1) + y := by linarith
    rw [arccoshD_eq_log (Or.inl him.ne'), hq, show (y : ℂ) * I + I * (√(y ^ 2 + 1) : ℂ) =
      ((√(y ^ 2 + 1) + y : ℝ) : ℂ) * I by push_cast; ring, log_mul_I_of_pos hpos]
    ring
  · have him : ((y : ℂ) * I).im < 0 := by simpa using hy
    have hq : coshRoot ((y : ℂ) * I) = -(I * (√(y ^ 2 + 1) : ℂ)) := by
      have hsq' : (-coshRoot ((y : ℂ) * I)) ^ 2 = (I * (√(y ^ 2 + 1) : ℂ)) ^ 2 := by
        rw [neg_sq]; exact hsq
      have hneg : 0 ≤ (-coshRoot ((y : ℂ) * I)).im := by
        rw [neg_im]; linarith [im_coshRoot_nonpos him]
      have := eq_of_sq_eq_of_im hsq' (by simpa using hs) hneg
      linear_combination -this
    have hpos : 0 < √(y ^ 2 + 1) - y := by linarith
    rw [arccoshD_eq_log (Or.inl him.ne), hq, show (y : ℂ) * I + -(I * (√(y ^ 2 + 1) : ℂ)) =
      ((√(y ^ 2 + 1) - y : ℝ) : ℂ) * -I by push_cast; ring, log_mul_neg_I_of_pos hpos]
    ring

theorem cpow_half_two_mul {u : ℂ} (hu : u ≠ 0) :
    (2 * u) ^ (1 / 2 : ℂ) = (2 : ℂ) ^ (1 / 2 : ℂ) * u ^ (1 / 2 : ℂ) := by
  have hlog : log (2 * u) = log 2 + log u := by
    have := log_ofReal_mul (r := 2) (by norm_num) hu
    rw [show ((2 : ℝ) : ℂ) = 2 by norm_num] at this
    rw [this, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← ofReal_log (by norm_num)]
  rw [cpow_def_of_ne_zero (mul_ne_zero two_ne_zero hu), cpow_def_of_ne_zero two_ne_zero,
    cpow_def_of_ne_zero hu, ← exp_add, hlog, add_mul]

/-- **DLMF 4.37.21** (Kahan): `arccosh z = 2 ln(((z + 1)/2)^{1/2} + ((z − 1)/2)^{1/2})`,
`z ∈ ℂ ∖ (−∞, 1)`. -/
theorem dlmf_4_37_21 {z : ℂ} (hz : z ∈ arccoshCut ∨ z = 1) :
    arccoshD z = 2 * log (((z + 1) / 2) ^ (1 / 2 : ℂ) + ((z - 1) / 2) ^ (1 / 2 : ℂ)) := by
  rcases hz with hz | rfl
  · set p := ((z + 1) / 2) ^ (1 / 2 : ℂ) with hp
    set q := ((z - 1) / 2) ^ (1 / 2 : ℂ) with hq
    have hp2 : p ^ 2 = (z + 1) / 2 := sqrt_half_sq _
    have hq2 : q ^ 2 = (z - 1) / 2 := sqrt_half_sq _
    have h1 := slitPlane_ne_zero (add_one_mem_slitPlane hz)
    have h2 := slitPlane_ne_zero (sub_one_mem_slitPlane hz)
    have hroot : coshRoot z = 2 * p * q := by
      rw [coshRoot, show z - 1 = 2 * ((z - 1) / 2) by ring, show z + 1 = 2 * ((z + 1) / 2) by ring,
        cpow_half_two_mul (div_ne_zero h2 two_ne_zero), cpow_half_two_mul
        (div_ne_zero h1 two_ne_zero), ← hp, ← hq]
      have := sqrt_half_sq (2 : ℂ)
      linear_combination p * q * this
    have hsum : z + coshRoot z = (p + q) ^ 2 := by
      rw [hroot]; linear_combination -hp2 - hq2
    have hslp : (z + 1) / 2 ∈ slitPlane := by
      have := add_one_mem_slitPlane hz
      rw [mem_slitPlane_iff] at this ⊢
      rcases this with h | h
      · left; rw [Complex.div_ofNat_re]; exact half_pos h
      · right; rw [Complex.div_ofNat_im]; exact div_ne_zero h two_ne_zero
    have hre : 0 < (p + q).re := by
      rw [add_re]
      linarith [re_cpow_half_pos_of_mem_slitPlane hslp, zero_le_re_cpow_half ((z - 1) / 2)]
    have hw0 : p + q ≠ 0 := fun h0 => by rw [h0, zero_re] at hre; exact lt_irrefl _ hre
    have harg := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre))
    rw [arccoshD_eq_log hz, hsum, show (p + q) ^ 2 = exp (2 * log (p + q)) by
      rw [show (2 : ℂ) * log (p + q) = ((2 : ℕ) : ℂ) * log (p + q) by norm_num, exp_nat_mul,
        exp_log hw0], log_exp]
    · simp [log_im]; linarith
    · simp [log_im]; linarith
  · rw [arccoshD_one]
    norm_num

/-! ### `arccosh` on its cut: one-sided limits of the principal square root -/

theorem exp_pi_half_I : exp (π * I * (1 / 2 : ℂ)) = I := by
  rw [show (π : ℂ) * I * (1 / 2) = (π / 2 : ℂ) * I by ring, exp_mul_I, cos_pi_div_two,
    sin_pi_div_two]; ring

/-- For real `a ≤ 0`, `a^{1/2} = i√(−a)` (principal). -/
theorem ofReal_cpow_half_of_nonpos {a : ℝ} (ha : a ≤ 0) :
    (a : ℂ) ^ (1 / 2 : ℂ) = I * (√(-a) : ℝ) := by
  rw [ofReal_cpow_of_nonpos ha, exp_pi_half_I, ← ofReal_neg, ofReal_cpow_half (by linarith)]
  ring

/-- The principal square root is continuous at every `a ≥ 0`. -/
theorem tendsto_sqrt_nonneg {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun w : ℂ => w ^ (1 / 2 : ℂ)) (𝓝 (a : ℂ)) (𝓝 ((√a : ℝ) : ℂ)) := by
  rw [← ofReal_cpow_half ha]
  rcases ha.eq_or_lt with h | h
  · subst h
    exact (continuousAt_cpow_const_of_re_pos (Or.inl (by simp)) (by norm_num)).tendsto
  · exact (continuousAt_cpow_const (by simpa using h)).tendsto

/-- From above, at real `a ≤ 0`: `w^{1/2} → i√(−a)`. -/
theorem tendsto_sqrt_upper_nonpos {a : ℝ} (ha : a ≤ 0) :
    Tendsto (fun w : ℂ => w ^ (1 / 2 : ℂ)) (𝓝[{w | 0 < w.im}] (a : ℂ))
      (𝓝 (I * ((√(-a) : ℝ) : ℂ))) := by
  rcases ha.eq_or_lt with h | h
  · subst h
    have := (tendsto_sqrt_nonneg le_rfl).mono_left (nhdsWithin_le_nhds (s := {w : ℂ | 0 < w.im}))
    simpa using this
  have hre : (a : ℂ).re < 0 := by simpa using h
  have hsub : {w : ℂ | 0 < w.im} ⊆ {w : ℂ | 0 ≤ w.im} := fun w (hw : 0 < w.im) => hw.le
  have hlog := ((continuousWithinAt_log_of_re_neg_of_im_zero hre (by simp)).mono hsub).tendsto
  rw [← ofReal_cpow_half_of_nonpos h.le, cpow_def_of_ne_zero (by exact_mod_cast h.ne)]
  refine ((continuous_exp.tendsto _).comp (hlog.mul_const _)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw0 : w ≠ 0 := fun h0 => by rw [h0] at hw; simp at hw
  exact (cpow_def_of_ne_zero hw0 _).symm

/-- From below, at real `a ≤ 0`: `w^{1/2} → −i√(−a)`. -/
theorem tendsto_sqrt_lower_nonpos {a : ℝ} (ha : a ≤ 0) :
    Tendsto (fun w : ℂ => w ^ (1 / 2 : ℂ)) (𝓝[{w | w.im < 0}] (a : ℂ))
      (𝓝 (-I * ((√(-a) : ℝ) : ℂ))) := by
  rcases ha.eq_or_lt with h | h
  · subst h
    have := (tendsto_sqrt_nonneg le_rfl).mono_left (nhdsWithin_le_nhds (s := {w : ℂ | w.im < 0}))
    simpa using this
  have hre : (a : ℂ).re < 0 := by simpa using h
  have hlog := tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hre (by simp)
  have hval : exp ((Real.log ‖(a : ℂ)‖ - π * I) * (1 / 2)) = -I * ((√(-a) : ℝ) : ℂ) := by
    have hpos : 0 < -a := by linarith
    rw [show ((Real.log ‖(a : ℂ)‖ : ℂ) - π * I) * (1 / 2) =
      ((Real.log (-a) / 2 : ℝ) : ℂ) + (-(π / 2) : ℂ) * I by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg h]; push_cast; ring,
      exp_add, exp_mul_I, cos_neg, sin_neg, cos_pi_div_two, sin_pi_div_two, ← ofReal_exp,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]
    push_cast; ring_nf
  rw [← hval]
  refine ((continuous_exp.tendsto _).comp (hlog.mul_const _)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw0 : w ≠ 0 := fun h0 => by rw [h0] at hw; simp at hw
  exact (cpow_def_of_ne_zero hw0 _).symm

theorem coshRoot_eq_shift (z : ℂ) :
    coshRoot z = (z + ((-1 : ℝ) : ℂ)) ^ (1 / 2 : ℂ) * (z + ((1 : ℝ) : ℂ)) ^ (1 / 2 : ℂ) := by
  rw [coshRoot]; push_cast; ring_nf

/-- The two factors of `coshRoot` near a real point `x ≤ 1`, from above and below. -/
theorem tendsto_coshRoot_factors {x : ℝ} (hx : x ≤ 1) :
    Tendsto (fun z : ℂ => (z + ((-1 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) (𝓝[{w | 0 < w.im}] (x : ℂ))
        (𝓝 (I * ((√(1 - x) : ℝ) : ℂ))) ∧
      Tendsto (fun z : ℂ => (z + ((-1 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) (𝓝[{w | w.im < 0}] (x : ℂ))
        (𝓝 (-I * ((√(1 - x) : ℝ) : ℂ))) := by
  obtain ⟨s1, s2⟩ := tendsto_add_real_side x (-1)
  have e : -(x + -1) = 1 - x := by ring
  have h1 := (tendsto_sqrt_upper_nonpos (a := x + -1) (by linarith)).comp s1
  have h2 := (tendsto_sqrt_lower_nonpos (a := x + -1) (by linarith)).comp s2
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

/-- **DLMF 4.37.22** (on the cut from `−1` to `1`): `arccosh x = ±ln(i(1 − x²)^{1/2} + x)`,
`x ∈ (−1, 1]`, the upper/lower sign for the upper/lower side. -/
theorem dlmf_4_37_22 {x : ℝ} (hx : x ∈ Ioc (-1 : ℝ) 1) :
    Tendsto arccoshD (𝓝[{w | 0 < w.im}] (x : ℂ))
        (𝓝 (log (I * ((√(1 - x ^ 2) : ℝ) : ℂ) + x))) ∧
      Tendsto arccoshD (𝓝[{w | w.im < 0}] (x : ℂ))
        (𝓝 (-log (I * ((√(1 - x ^ 2) : ℝ) : ℂ) + x))) := by
  obtain ⟨f1, f2⟩ := tendsto_coshRoot_factors hx.2
  obtain ⟨s1, s2⟩ := tendsto_add_real_side x 1
  have hp : 0 ≤ x + 1 := by linarith [hx.1]
  have g1 := (tendsto_sqrt_nonneg hp).comp (s1.mono_right nhdsWithin_le_nhds)
  have g2 := (tendsto_sqrt_nonneg hp).comp (s2.mono_right nhdsWithin_le_nhds)
  have hsq : √(1 - x) * √(x + 1) = √(1 - x ^ 2) := by
    rw [← Real.sqrt_mul (by linarith [hx.2])]; congr 1; ring
  set r := √(1 - x ^ 2) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hq1 : Tendsto coshRoot (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝 (I * (r : ℂ))) := by
    have := f1.mul g1
    rw [show I * ((√(1 - x) : ℝ) : ℂ) * ((√(x + 1) : ℝ) : ℂ) = I * (r : ℂ) by
      rw [← hsq]; push_cast; ring] at this
    exact this.congr fun z => (coshRoot_eq_shift z).symm
  have hq2 : Tendsto coshRoot (𝓝[{w | w.im < 0}] (x : ℂ)) (𝓝 (-I * (r : ℂ))) := by
    have := f2.mul g2
    rw [show -I * ((√(1 - x) : ℝ) : ℂ) * ((√(x + 1) : ℝ) : ℂ) = -I * (r : ℂ) by
      rw [← hsq]; push_cast; ring] at this
    exact this.congr fun z => (coshRoot_eq_shift z).symm
  have hid : ∀ S : Set ℂ, Tendsto (fun z : ℂ => z) (𝓝[S] (x : ℂ)) (𝓝 (x : ℂ)) :=
    fun S => tendsto_id.mono_left nhdsWithin_le_nhds
  -- `w₀ = x + ir` lies off the cut of `ln`
  have hw0 : I * (r : ℂ) + x ∈ slitPlane := by
    rcases hr0.eq_or_lt with h | h
    · rw [← h]; simp
      have : r = 0 := h.symm
      have hx1 : x ^ 2 = 1 := by
        have := Real.sqrt_eq_zero'.mp this; nlinarith [hx.1, hx.2]
      have : x = 1 := by nlinarith [hx.1, hx.2]
      rw [this]; norm_num
    · exact mem_slitPlane_of_im_ne (by simp; exact h.ne')
  have hr2 : (r : ℂ) ^ 2 = 1 - x ^ 2 := by
    rw [← ofReal_pow, hr, Real.sq_sqrt (by nlinarith [hx.1, hx.2])]; push_cast; ring
  have hlogEv : ∀ S : Set ℂ, (∀ z ∈ S, z.im ≠ 0) →
      (fun z => log (z + coshRoot z)) =ᶠ[𝓝[S] (x : ℂ)] arccoshD := fun S hS => by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (arccoshD_eq_log (Or.inl (hS z hz))).symm
  constructor
  · have hs := (hid _).add hq1
    rw [show (x : ℂ) + I * (r : ℂ) = I * (r : ℂ) + x by ring] at hs
    have h := (continuousAt_clog hw0).tendsto.comp hs
    exact h.congr' (hlogEv _ fun z hz => ne_of_gt hz)
  · have hinv : (x : ℂ) + -I * (r : ℂ) = (I * (r : ℂ) + x)⁻¹ := by
      refine (eq_inv_of_mul_eq_one_left ?_)
      linear_combination hr2 - (r : ℂ) ^ 2 * I_sq
    have hw1 : (x : ℂ) + -I * (r : ℂ) ∈ slitPlane := by
      rcases hr0.eq_or_lt with h | h
      · have hx1 : x ^ 2 = 1 := by
          have h0 : r = 0 := h.symm
          have := Real.sqrt_eq_zero'.mp h0
          nlinarith [hx.1, hx.2]
        have : x = 1 := by nlinarith [hx.1, hx.2]
        rw [← h, this]; norm_num
      · exact mem_slitPlane_of_im_ne (by simp; exact h.ne')
    have h := ((continuousAt_clog hw1).tendsto.comp ((hid _).add hq2))
    rw [hinv, log_inv _ (mem_slitPlane_iff_arg.mp hw0).1] at h
    exact h.congr' (hlogEv _ fun z hz => ne_of_lt hz)

/-- **DLMF 4.37.23** (on the cut left of `−1`): `arccosh x = ±πi + ln((x² − 1)^{1/2} − x)`,
`x ≤ −1`, the upper/lower sign for the upper/lower side. -/
theorem dlmf_4_37_23 {x : ℝ} (hx : x ≤ -1) :
    Tendsto arccoshD (𝓝[{w | 0 < w.im}] (x : ℂ))
        (𝓝 (π * I + ((Real.log (√(x ^ 2 - 1) - x) : ℝ) : ℂ))) ∧
      Tendsto arccoshD (𝓝[{w | w.im < 0}] (x : ℂ))
        (𝓝 (-(π * I) + ((Real.log (√(x ^ 2 - 1) - x) : ℝ) : ℂ))) := by
  obtain ⟨f1, f2⟩ := tendsto_coshRoot_factors (x := x) (by linarith)
  obtain ⟨s1, s2⟩ := tendsto_add_real_side x 1
  have g1 := (tendsto_sqrt_upper_nonpos (a := x + 1) (by linarith)).comp s1
  have g2 := (tendsto_sqrt_lower_nonpos (a := x + 1) (by linarith)).comp s2
  have hsq : √(1 - x) * √(-(x + 1)) = √(x ^ 2 - 1) := by
    rw [← Real.sqrt_mul (by linarith)]; congr 1; ring
  set r := √(x ^ 2 - 1) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hq1 : Tendsto coshRoot (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝 (-(r : ℂ))) := by
    have := f1.mul g1
    rw [show I * ((√(1 - x) : ℝ) : ℂ) * (I * ((√(-(x + 1)) : ℝ) : ℂ)) = -(r : ℂ) by
      rw [← hsq]; push_cast; linear_combination (↑√(1 - x) * ↑√(-(x + 1)) : ℂ) * I_sq] at this
    exact this.congr fun z => (coshRoot_eq_shift z).symm
  have hq2 : Tendsto coshRoot (𝓝[{w | w.im < 0}] (x : ℂ)) (𝓝 (-(r : ℂ))) := by
    have := f2.mul g2
    rw [show -I * ((√(1 - x) : ℝ) : ℂ) * (-I * ((√(-(x + 1)) : ℝ) : ℂ)) = -(r : ℂ) by
      rw [← hsq]; push_cast; linear_combination (↑√(1 - x) * ↑√(-(x + 1)) : ℂ) * I_sq] at this
    exact this.congr fun z => (coshRoot_eq_shift z).symm
  have hid : ∀ S : Set ℂ, Tendsto (fun z : ℂ => z) (𝓝[S] (x : ℂ)) (𝓝 (x : ℂ)) :=
    fun S => tendsto_id.mono_left nhdsWithin_le_nhds
  -- `w₀ = x − r` is a negative real
  have hneg : x - r < 0 := by linarith
  have hw : ((x - r : ℝ) : ℂ) = (x : ℂ) + -(r : ℂ) := by push_cast; ring
  have hnorm : Real.log ‖((x - r : ℝ) : ℂ)‖ = Real.log (r - x) := by
    rw [norm_real, Real.norm_of_nonpos hneg.le]; ring_nf
  have hlogEv : ∀ S : Set ℂ, (∀ z ∈ S, z.im ≠ 0) →
      (fun z => log (z + coshRoot z)) =ᶠ[𝓝[S] (x : ℂ)] arccoshD := fun S hS => by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (arccoshD_eq_log (Or.inl (hS z hz))).symm
  constructor
  · have hs := (hid _).add hq1
    rw [← hw] at hs
    have hs' : Tendsto (fun z => z + coshRoot z) (𝓝[{w | 0 < w.im}] (x : ℂ))
        (𝓝[{w | 0 ≤ w.im}] ((x - r : ℝ) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hs, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z (hz : 0 < z.im)
      show 0 ≤ (z + coshRoot z).im
      rw [add_im]; linarith [im_coshRoot_nonneg hz]
    have h := ((continuousWithinAt_log_of_re_neg_of_im_zero (by simpa using hneg)
      (by simp)).tendsto).comp hs'
    rw [show log ((x - r : ℝ) : ℂ) = π * I + ((Real.log (r - x) : ℝ) : ℂ) by
      rw [← hnorm, Complex.log, arg_ofReal_of_neg hneg]; ring] at h
    exact h.congr' (hlogEv _ fun z hz => ne_of_gt hz)
  · have hs := (hid _).add hq2
    rw [← hw] at hs
    have hs' : Tendsto (fun z => z + coshRoot z) (𝓝[{w | w.im < 0}] (x : ℂ))
        (𝓝[{w | w.im < 0}] ((x - r : ℝ) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hs, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z (hz : z.im < 0)
      show (z + coshRoot z).im < 0
      rw [add_im]; linarith [im_coshRoot_nonpos hz]
    have h := (tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero (by simpa using hneg)
      (by simp)).comp hs'
    rw [hnorm, show ((Real.log (r - x) : ℝ) : ℂ) - π * I =
      -(π * I) + ((Real.log (r - x) : ℝ) : ℂ) by ring] at h
    exact h.congr' (hlogEv _ fun z hz => ne_of_lt hz)

/-! ### Other inverse functions (via 4.37.7–4.37.9) -/

/-- `arccsch z = ln((1/z² + 1)^{1/2} + 1/z)`, off the cut `[−i, i]` and at `±i` (4.37.16 at
`1/z`). -/
theorem dlmf_4_37_iv_arccsch {z : ℂ} (hz : z.re ≠ 0 ∨ 1 < |z.im| ∨ z = I ∨ z = -I) :
    arccschD z = log ((1 / z ^ 2 + 1) ^ (1 / 2 : ℂ) + 1 / z) := by
  have hw : 1 / z ∈ arcsinhCut ∨ 1 / z = I ∨ 1 / z = -I := by
    rcases hz with h | h | rfl | rfl
    · exact Or.inl (one_div_mem_arctanCut (Or.inl h)).2
    · exact Or.inl (one_div_mem_arctanCut (Or.inr h)).2
    · right; right; rw [one_div, inv_I]
    · right; left; rw [one_div, inv_neg, inv_I, neg_neg]
  rw [arccschD, dlmf_4_37_16 hw, one_div_pow]

/-- `arcsech z = ln(±((1/z)² − 1)^{1/2} + 1/z)`, the sign that of `ℜz`, off the cut
`(−∞, 0] ∪ [1, ∞)` and at `1` (4.37.19 at `1/z`; `ℜ(1/z)` has the sign of `ℜz`). -/
theorem dlmf_4_37_iv_arcsech {z : ℂ} (hz : z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) ∨ z = 1) :
    (0 < z.re → arcsechD z = log (((1 / z) ^ 2 - 1) ^ (1 / 2 : ℂ) + 1 / z)) ∧
      (z.re < 0 → arcsechD z = log (-((1 / z) ^ 2 - 1) ^ (1 / 2 : ℂ) + 1 / z)) := by
  have hw : 1 / z ∈ arccoshCut ∨ 1 / z = 1 := by
    rcases hz with h | h | rfl
    · exact Or.inl (one_div_mem_arccoshCut (Or.inl h)).2
    · exact Or.inl (one_div_mem_arccoshCut (Or.inr h)).2
    · right; simp
  have hz0 : z ≠ 0 := by rintro rfl; rcases hz with h | h | h <;> simp at h
  have hre : (1 / z).re = z.re / normSq z := by rw [one_div, inv_re]
  have hn := normSq_pos.mpr hz0
  obtain ⟨h1, h2⟩ := dlmf_4_37_19 hw
  exact ⟨fun h => h1 (by rw [hre]; exact div_pos h hn),
    fun h => h2 (by rw [hre]; exact div_neg_of_neg_of_pos h hn)⟩

/-- Kahan's form `arcsech z = 2 ln(((1/z + 1)/2)^{1/2} + ((1/z − 1)/2)^{1/2})` (4.37.21 at
`1/z`). -/
theorem dlmf_4_37_iv_arcsech_kahan {z : ℂ} (hz : z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) ∨ z = 1) :
    arcsechD z = 2 * log (((1 / z + 1) / 2) ^ (1 / 2 : ℂ) + ((1 / z - 1) / 2) ^ (1 / 2 : ℂ)) := by
  have hw : 1 / z ∈ arccoshCut ∨ 1 / z = 1 := by
    rcases hz with h | h | rfl
    · exact Or.inl (one_div_mem_arccoshCut (Or.inl h)).2
    · exact Or.inl (one_div_mem_arccoshCut (Or.inr h)).2
    · right; simp
  exact dlmf_4_37_21 hw

/-- `arccoth z = ½ ln((z + 1)/(z − 1))`, off the cut `[−1, 1]` (4.37.24 at `1/z`). -/
theorem dlmf_4_37_iv_arccoth {z : ℂ} (hz : z.im ≠ 0 ∨ 1 < |z.re|) :
    arccothD z = 1 / 2 * log ((z + 1) / (z - 1)) := by
  obtain ⟨hz0, hc⟩ := one_div_mem_arcsinCut hz
  rw [arccothD, dlmf_4_37_24 hc, show 1 + 1 / z = (z + 1) / z by field_simp,
    show 1 - 1 / z = (z - 1) / z by field_simp, div_div_div_cancel_right₀ hz0]

/-- `z ↦ 1/z` keeps the sides `ℜz ≷ 0` near a point `iy`, `y ≠ 0`, of the imaginary axis. -/
theorem tendsto_one_div_re_side {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun z : ℂ => 1 / z) (𝓝[{z | 0 < z.re}] ((y : ℂ) * I))
        (𝓝[{z | 0 < z.re}] (((-1 / y : ℝ) : ℂ) * I)) ∧
      Tendsto (fun z : ℂ => 1 / z) (𝓝[{z | z.re < 0}] ((y : ℂ) * I))
        (𝓝[{z | z.re < 0}] (((-1 / y : ℝ) : ℂ) * I)) := by
  have hy' : (y : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hy) I_ne_zero
  have hv : (((-1 / y : ℝ) : ℂ) * I) = 1 / ((y : ℂ) * I) := by
    refine eq_one_div_of_mul_eq_one_right ?_
    push_cast
    rw [show (y : ℂ) * I * (-1 / (y : ℂ) * I) = -((y : ℂ) / y) * (I * I) by ring,
      div_self (ofReal_ne_zero.mpr hy), I_mul_I]; ring
  have hc : Tendsto (fun z : ℂ => 1 / z) (𝓝 ((y : ℂ) * I)) (𝓝 (((-1 / y : ℝ) : ℂ) * I)) := by
    rw [hv]
    exact ((continuousAt_const (y := (1 : ℂ))).div continuousAt_id hy').tendsto
  have hre : ∀ z : ℂ, (1 / z).re = z.re / normSq z := fun z => by rw [one_div, inv_re]
  constructor
  · refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z (hz : 0 < z.re)
    have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
    show 0 < (1 / z).re
    rw [hre]; exact div_pos hz (normSq_pos.mpr hz0)
  · refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z (hz : z.re < 0)
    have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
    show (1 / z).re < 0
    rw [hre]; exact div_neg_of_neg_of_pos hz (normSq_pos.mpr hz0)

/-- `arccsch` on its cut `iy`, `0 < |y| < 1`, from the right (`ℜz > 0`) and the left
(4.37.17–4.37.18 at `1/(iy) = −i/y`): `∓½πi ± ln((1/y² − 1)^{1/2} ± 1/y)`, the first sign that
of `y`. -/
theorem dlmf_4_37_iv_arccsch_cut {y : ℝ} :
    (0 < y → y < 1 →
      Tendsto arccschD (𝓝[{z | 0 < z.re}] ((y : ℂ) * I))
          (𝓝 (-(π / 2 * I) + (Real.log (√(1 / y ^ 2 - 1) + 1 / y) : ℂ))) ∧
        Tendsto arccschD (𝓝[{z | z.re < 0}] ((y : ℂ) * I))
          (𝓝 (-(π / 2 * I) - (Real.log (√(1 / y ^ 2 - 1) + 1 / y) : ℂ)))) ∧
    (y < 0 → -1 < y →
      Tendsto arccschD (𝓝[{z | 0 < z.re}] ((y : ℂ) * I))
          (𝓝 (π / 2 * I + (Real.log (√(1 / y ^ 2 - 1) - 1 / y) : ℂ))) ∧
        Tendsto arccschD (𝓝[{z | z.re < 0}] ((y : ℂ) * I))
          (𝓝 (π / 2 * I - (Real.log (√(1 / y ^ 2 - 1) - 1 / y) : ℂ)))) := by
  have hsq : ∀ y : ℝ, (-1 / y) ^ 2 - 1 = 1 / y ^ 2 - 1 := fun y => by ring
  refine ⟨fun h0 h1 => ?_, fun h0 h1 => ?_⟩
  · obtain ⟨t1, t2⟩ := tendsto_one_div_re_side h0.ne'
    have hY : -1 / y < -1 := by
      rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ h0]; linarith
    obtain ⟨e1, e2⟩ := (dlmf_4_37_18 (y := -1 / y)).1 hY
    rw [hsq, show √(1 / y ^ 2 - 1) - -1 / y = √(1 / y ^ 2 - 1) + 1 / y by ring] at e1 e2
    exact ⟨e1.comp t1, e2.comp t2⟩
  · obtain ⟨t1, t2⟩ := tendsto_one_div_re_side h0.ne
    have hY : 1 < -1 / y := by
      rw [lt_div_iff_of_neg h0]; linarith
    obtain ⟨e1, e2⟩ := (dlmf_4_37_17 (y := -1 / y)).1 hY
    rw [hsq, show √(1 / y ^ 2 - 1) + -1 / y = √(1 / y ^ 2 - 1) - 1 / y by ring] at e1 e2
    exact ⟨e1.comp t1, e2.comp t2⟩

/-- `arcsech` on its cut `(−∞, 0) ∪ [1, ∞)` (4.37.22–4.37.23 at `1/x`, the sides exchanged):
for `x ≥ 1` or `x < −1`, `arcsech(x ± i0) = ∓ln(i(1 − 1/x²)^{1/2} + 1/x)`; for `−1 ≤ x < 0`,
`arcsech(x ± i0) = ∓πi + ln((1/x² − 1)^{1/2} − 1/x)`. -/
theorem dlmf_4_37_iv_arcsech_cut {x : ℝ} :
    (1 ≤ x ∨ x < -1 →
      Tendsto arcsechD (𝓝[{w | 0 < w.im}] (x : ℂ))
          (𝓝 (-log (I * ((√(1 - 1 / x ^ 2) : ℝ) : ℂ) + ((1 / x : ℝ) : ℂ)))) ∧
        Tendsto arcsechD (𝓝[{w | w.im < 0}] (x : ℂ))
          (𝓝 (log (I * ((√(1 - 1 / x ^ 2) : ℝ) : ℂ) + ((1 / x : ℝ) : ℂ))))) ∧
    (-1 ≤ x → x < 0 →
      Tendsto arcsechD (𝓝[{w | 0 < w.im}] (x : ℂ))
          (𝓝 (-(π * I) + ((Real.log (√(1 / x ^ 2 - 1) - 1 / x) : ℝ) : ℂ))) ∧
        Tendsto arcsechD (𝓝[{w | w.im < 0}] (x : ℂ))
          (𝓝 (π * I + ((Real.log (√(1 / x ^ 2 - 1) - 1 / x) : ℝ) : ℂ)))) := by
  refine ⟨fun hx => ?_, fun h1 h0 => ?_⟩
  · have hx0 : x ≠ 0 := by rcases hx with h | h <;> intro e <;> rw [e] at h <;> norm_num at h
    have hm : 1 / x ∈ Ioc (-1 : ℝ) 1 := by
      rcases hx with h | h
      · exact ⟨by have := one_div_pos.mpr (by linarith : (0 : ℝ) < x); linarith,
          div_le_one_of_le₀ h (by linarith)⟩
      · refine ⟨?_, by have := one_div_neg.mpr (by linarith : x < 0); linarith⟩
        rw [lt_div_iff_of_neg (by linarith)]; linarith
    obtain ⟨t1, t2⟩ := tendsto_one_div_nhdsWithin hx0
    obtain ⟨e1, e2⟩ := dlmf_4_37_22 hm
    rw [one_div_pow] at e1 e2
    exact ⟨e2.comp t1, e1.comp t2⟩
  · obtain ⟨t1, t2⟩ := tendsto_one_div_nhdsWithin h0.ne
    have hm : 1 / x ≤ -1 := by
      rw [div_le_iff_of_neg h0]; linarith
    obtain ⟨e1, e2⟩ := dlmf_4_37_23 hm
    rw [one_div_pow] at e1 e2
    exact ⟨e2.comp t1, e1.comp t2⟩

/-- `arccoth` on its cut, `0 < |x| < 1` (4.37.25 at `1/x`, the sides exchanged):
`arccoth(x ± i0) = ∓½πi + ½ ln((1 + x)/(1 − x))`. -/
theorem dlmf_4_37_iv_arccoth_cut {x : ℝ} (hx0 : x ≠ 0) (hx1 : |x| < 1) :
    Tendsto arccothD (𝓝[{w | 0 < w.im}] (x : ℂ))
        (𝓝 (-(π / 2 * I) + 1 / 2 * (Real.log ((1 + x) / (1 - x)) : ℂ))) ∧
      Tendsto arccothD (𝓝[{w | w.im < 0}] (x : ℂ))
        (𝓝 (π / 2 * I + 1 / 2 * (Real.log ((1 + x) / (1 - x)) : ℂ))) := by
  obtain ⟨t1, t2⟩ := tendsto_one_div_nhdsWithin hx0
  obtain ⟨e1, e2⟩ := dlmf_4_37_25 (one_lt_abs_one_div hx0 hx1)
  have hx1' : 1 - x ≠ 0 := by
    intro h; have : x = 1 := by linarith
    rw [this] at hx1; norm_num at hx1
  rw [show (1 / x + 1) / (1 / x - 1) = (1 + x) / (1 - x) by field_simp] at e1 e2
  exact ⟨e2.comp t1, e1.comp t2⟩

end Azurite.DLMF
