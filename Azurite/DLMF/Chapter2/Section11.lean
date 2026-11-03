/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14TableSinArctan
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# DLMF §2.11(i): Numerical Use of Asymptotic Expansions, 2.11.1–2.11.3

The example of §2.11(i):

* 2.11.1 (`cosIntI`): `I(m) = ∫_0^π cos(mt)/(t² + 1) dt`.
* The derivatives of `φ(t) = 1/(t² + 1)` (`cauchyD k = φ^{(k)}`, written as
  `(−1)^k k! ℑ((t − i)^{−k−1})`), with `|φ^{(k)}(t)| ≤ k!/|t − i|^{k+1}`.
* 2.11.2 (`dlmf_2_11_2`): `I(m) ∼ (−1)^m ∑_{s≥1} q_s(π)/m^{2s}` as `m → ∞` through the
  integers, with the explicit remainder `|q_{n+1}(π)| + ∫_0^π |φ^{(2n+2)}|` over `m^{2n+2}`, from
  the exact form `dlmf_2_11_2_exact` (repeated integration by parts, §2.3(i)); the coefficients
  are `q_s = (−1)^{s−1} φ^{(2s−1)}` (`cosIntQ`), since the odd derivatives vanish at `t = 0`.
* 2.11.3 (`dlmf_2_11_3`): `q₁`, `q₂`, `q₃` in closed form.
* The explanation of the failure of 2.11.4: with the tail `T(m) = ∫_π^∞ cos(mt)/(t² + 1) dt`
  (`cosIntTail`), `I(m) + T(m) = ½πe^{−m}` (`cosIntI_add_tail`, from §1.14), and the same
  series is the expansion of `I(m) − ½πe^{−m} = −T(m)` with a remainder that only involves
  `[π, ∞)` (`dlmf_2_11_i_shifted`, at most `((2n+1)!/(π² + 1)^{n+1} + (2n+1)!/π^{2n+2})/m^{2n+2}`),
  while `I(m)` itself carries the extra `½πe^{−m}`. Both functions have the same asymptotic
  expansion (`dlmf_2_11_i_same_expansion`): "the asymptotic series represents an infinite class
  of functions".

The numerical claims (`q_s(π)` to 5D, 2.11.4, `I(10)` to 7D, "approximately 700 times") are in
`Section11Numerics.lean`, computed by `AzFloat`. The remaining text of §2.11(i) (judging accuracy
from the size of terms, comparison with a nonasymptotic method, sectors of validity and Stokes
lines) is advice, not mathematics, and is not formalized.
-/

open Filter Topology Set MeasureTheory Complex
open scoped Real Interval

namespace Azurite.DLMF

/-! ### The derivatives of `1/(t² + 1)` -/

/-- `φ^{(k)}(t)` for `φ(t) = 1/(t² + 1)`, as `(−1)^k k! ℑ((t − i)^{−k−1})`. -/
noncomputable def cauchyD (k : ℕ) (t : ℝ) : ℝ :=
  (-1) ^ k * k.factorial * (((t : ℂ) - I) ^ (-((k : ℤ) + 1))).im

theorem ofReal_sub_I_ne_zero (t : ℝ) : (t : ℂ) - I ≠ 0 := fun h => by
  have := congrArg Complex.im h
  simp at this

theorem norm_ofReal_sub_I_sq (t : ℝ) : ‖(t : ℂ) - I‖ ^ 2 = t ^ 2 + 1 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem one_le_norm_ofReal_sub_I (t : ℝ) : 1 ≤ ‖(t : ℂ) - I‖ := by
  have h := norm_ofReal_sub_I_sq t
  nlinarith [norm_nonneg ((t : ℂ) - I), sq_nonneg t]

theorem abs_le_norm_ofReal_sub_I (t : ℝ) : |t| ≤ ‖(t : ℂ) - I‖ := by
  have := Complex.abs_re_le_norm ((t : ℂ) - I)
  simpa using this

theorem cauchyD_zero (t : ℝ) : cauchyD 0 t = 1 / (t ^ 2 + 1) := by
  have h : ((t : ℂ) - I) ^ (-((0 : ℤ) + 1)) = ((t : ℂ) - I)⁻¹ := by simp
  rw [cauchyD, Nat.cast_zero, h, Complex.inv_im, Complex.normSq_apply]
  simp
  ring

theorem hasDerivAt_cauchyD (k : ℕ) (t : ℝ) :
    HasDerivAt (cauchyD k) (cauchyD (k + 1) t) t := by
  have h1 : HasDerivAt (fun z : ℂ => (z - I) ^ (-((k : ℤ) + 1)))
      ((-((k : ℤ) + 1) : ℤ) * ((t : ℂ) - I) ^ (-((k : ℤ) + 1) - 1)) (t : ℂ) :=
    (hasDerivAt_zpow _ _ (Or.inl (ofReal_sub_I_ne_zero t))).comp_sub_const _ _
  have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h1.comp_ofReal
  have h3 := h2.const_mul ((-1) ^ k * (k.factorial : ℝ))
  convert h3 using 1
  · rfl
  rw [cauchyD, show -(((k + 1 : ℕ) : ℤ) + 1) = -((k : ℤ) + 1) - 1 by push_cast; ring]
  simp only [Complex.imCLM_apply, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, zero_mul, add_zero, Nat.factorial_succ]
  push_cast
  ring

theorem continuous_cauchyD (k : ℕ) : Continuous (cauchyD k) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_cauchyD k t).continuousAt

theorem abs_cauchyD_le (k : ℕ) (t : ℝ) :
    |cauchyD k t| ≤ k.factorial / ‖(t : ℂ) - I‖ ^ (k + 1) := by
  have hn : 0 < ‖(t : ℂ) - I‖ := norm_pos_iff.mpr (ofReal_sub_I_ne_zero t)
  have him := Complex.abs_im_le_norm (((t : ℂ) - I) ^ (-((k : ℤ) + 1)))
  rw [norm_zpow, show -((k : ℤ) + 1) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
    zpow_natCast] at him
  rw [cauchyD, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    Nat.abs_cast, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left him (by positivity)

/-- `|φ^{(2j+1)}(t)| ≤ (2j+1)!/(t² + 1)^{j+1}`. -/
theorem abs_cauchyD_odd_le (j : ℕ) (t : ℝ) :
    |cauchyD (2 * j + 1) t| ≤ (2 * j + 1).factorial / (t ^ 2 + 1) ^ (j + 1) := by
  have h := abs_cauchyD_le (2 * j + 1) t
  rwa [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, pow_mul, norm_ofReal_sub_I_sq] at h

/-- `|φ^{(k)}(t)| ≤ k!/t^{k+1}` for `t > 0`. -/
theorem abs_cauchyD_le_pow {k : ℕ} {t : ℝ} (ht : 0 < t) :
    |cauchyD k t| ≤ k.factorial / t ^ (k + 1) := by
  refine (abs_cauchyD_le k t).trans (div_le_div_of_nonneg_left (by positivity) (by positivity) ?_)
  have := abs_le_norm_ofReal_sub_I t
  rw [abs_of_pos ht] at this
  exact pow_le_pow_left₀ ht.le this _

/-- `|φ^{(k)}(t)| ≤ k!/(t² + 1)`. -/
theorem abs_cauchyD_le_inv (k : ℕ) (t : ℝ) : |cauchyD k t| ≤ k.factorial / (t ^ 2 + 1) := by
  rcases k with _ | k
  · rw [cauchyD_zero, abs_of_pos (by positivity)]
    simp
  · refine (abs_cauchyD_le _ t).trans (div_le_div_of_nonneg_left (by positivity) (by positivity) ?_)
    rw [← norm_ofReal_sub_I_sq]
    exact pow_le_pow_right₀ (one_le_norm_ofReal_sub_I t) (by omega)

theorem integrable_cauchyD (k : ℕ) : Integrable (cauchyD k) := by
  refine ((integrable_inv_one_add_sq.const_mul (k.factorial : ℝ))).mono'
    (continuous_cauchyD k).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_cauchyD_le_inv k t).trans (le_of_eq ?_)
  rw [div_eq_mul_inv, add_comm]

/-- The odd derivatives vanish at `0` (`φ` is even). -/
theorem cauchyD_odd_zero (j : ℕ) : cauchyD (2 * j + 1) 0 = 0 := by
  have h : ((0 : ℝ) : ℂ) - I = -I := by simp
  have e : (-I) ^ (-(((2 * j + 1 : ℕ) : ℤ) + 1)) = (((-1) ^ (j + 1) : ℝ) : ℂ)⁻¹ := by
    rw [show -(((2 * j + 1 : ℕ) : ℤ) + 1) = -((2 * (j + 1) : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, pow_mul, neg_sq, Complex.I_sq]
    push_cast
    ring
  rw [cauchyD, h, e, Complex.inv_im, Complex.ofReal_im]
  simp

/-- `(t − i)^{−k−1} = (t + i)^{k+1}/(t² + 1)^{k+1}`, so
`φ^{(k)}(t) = (−1)^k k! ℑ((t + i)^{k+1})/(t² + 1)^{k+1}`. -/
theorem cauchyD_eq (k : ℕ) (t : ℝ) :
    cauchyD k t =
      (-1) ^ k * k.factorial * (((t : ℂ) + I) ^ (k + 1)).im / (t ^ 2 + 1) ^ (k + 1) := by
  have hne := ofReal_sub_I_ne_zero t
  have hprod : ((t : ℂ) - I) * ((t : ℂ) + I) = ((t ^ 2 + 1 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have e : ((t : ℂ) - I) ^ (-((k : ℤ) + 1)) =
      ((t : ℂ) + I) ^ (k + 1) / (((t ^ 2 + 1) ^ (k + 1) : ℝ) : ℂ) := by
    rw [show -((k : ℤ) + 1) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
      Complex.ofReal_pow, ← hprod, mul_pow]
    have : ((t : ℂ) + I) ^ (k + 1) ≠ 0 := pow_ne_zero _ fun h => by
      have := congrArg Complex.im h; simp at this
    field_simp
  rw [cauchyD, e, Complex.div_ofReal_im]
  ring

/-! ### 2.11.1–2.11.3 -/

/-- **DLMF 2.11.1**: `I(m) = ∫_0^π cos(mt)/(t² + 1) dt`. -/
noncomputable def cosIntI (m : ℝ) : ℝ := ∫ t in (0 : ℝ)..π, Real.cos (m * t) / (t ^ 2 + 1)

/-- The coefficients `q_s(t) = (−1)^{s−1} φ^{(2s−1)}(t)` of 2.11.2 (`s ≥ 1`). -/
noncomputable def cosIntQ (s : ℕ) (t : ℝ) : ℝ := (-1) ^ (s + 1) * cauchyD (2 * s - 1) t

theorem cosIntQ_succ (s : ℕ) (t : ℝ) : cosIntQ (s + 1) t = (-1) ^ s * cauchyD (2 * s + 1) t := by
  rw [cosIntQ, show 2 * (s + 1) - 1 = 2 * s + 1 by omega, pow_add]
  ring

theorem im_I_add_pow_two (t : ℝ) : (((t : ℂ) + I) ^ 2).im = 2 * t := by
  simp [pow_succ, Complex.mul_im]; ring

theorem im_I_add_pow_four (t : ℝ) : (((t : ℂ) + I) ^ 4).im = 4 * t ^ 3 - 4 * t := by
  simp [pow_succ, Complex.mul_im, Complex.mul_re]; ring

theorem im_I_add_pow_six (t : ℝ) :
    (((t : ℂ) + I) ^ 6).im = 6 * t ^ 5 - 20 * t ^ 3 + 6 * t := by
  simp [pow_succ, Complex.mul_im, Complex.mul_re]; ring

/-- **DLMF 2.11.3**. -/
theorem dlmf_2_11_3 (t : ℝ) :
    cosIntQ 1 t = -(2 * t / (t ^ 2 + 1) ^ 2) ∧
      cosIntQ 2 t = 24 * (t ^ 3 - t) / (t ^ 2 + 1) ^ 4 ∧
      cosIntQ 3 t = -(240 * (3 * t ^ 5 - 10 * t ^ 3 + 3 * t) / (t ^ 2 + 1) ^ 6) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cosIntQ, show 2 * 1 - 1 = 1 by rfl, cauchyD_eq, im_I_add_pow_two]
    simp only [Nat.factorial]
    push_cast
    ring
  · rw [cosIntQ, show 2 * 2 - 1 = 3 by rfl, cauchyD_eq, im_I_add_pow_four]
    simp only [Nat.factorial]
    push_cast
    ring
  · rw [cosIntQ, show 2 * 3 - 1 = 5 by rfl, cauchyD_eq, im_I_add_pow_six]
    simp only [Nat.factorial]
    push_cast
    ring

/-! ### Integration by parts -/

theorem integrable_cauchyD_mul (k : ℕ) {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ}
    (hb : ∀ t, |g t| ≤ B) : Integrable fun t => cauchyD k t * g t := by
  refine ((integrable_inv_one_add_sq.const_mul ((k.factorial : ℝ) * B))).mono'
    ((continuous_cauchyD k).mul hg).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb 0)
  rw [Real.norm_eq_abs, abs_mul]
  calc |cauchyD k t| * |g t| ≤ k.factorial / (t ^ 2 + 1) * B :=
        mul_le_mul (abs_cauchyD_le_inv k t) (hb t) (abs_nonneg _) (by positivity)
    _ = _ := by rw [add_comm]; ring

theorem tendsto_cauchyD_mul_atTop (k : ℕ) {g : ℝ → ℝ} {B : ℝ} (hb : ∀ t, |g t| ≤ B) :
    Tendsto (fun t => cauchyD k t * g t) atTop (𝓝 0) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb 0)
  refine squeeze_zero_norm (a := fun t => (k.factorial : ℝ) * B / (t ^ 2 + 1)) (fun t => ?_)
    (tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 1 (tendsto_pow_atTop two_ne_zero)))
  rw [Real.norm_eq_abs, abs_mul]
  calc |cauchyD k t| * |g t| ≤ k.factorial / (t ^ 2 + 1) * B :=
        mul_le_mul (abs_cauchyD_le_inv k t) (hb t) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem hasDerivAt_sin_div (m t : ℝ) (hm : m ≠ 0) :
    HasDerivAt (fun t => Real.sin (m * t) / m) (Real.cos (m * t)) t := by
  have := (((hasDerivAt_id t).const_mul m).sin).div_const m
  convert this using 1
  · rfl
  · simp only [id, mul_one]; field_simp

theorem hasDerivAt_neg_cos_div (m t : ℝ) (hm : m ≠ 0) :
    HasDerivAt (fun t => -Real.cos (m * t) / m ^ 2) (Real.sin (m * t) / m) t := by
  have := ((((hasDerivAt_id t).const_mul m).cos).neg).div_const (m ^ 2)
  convert this using 1
  · funext x; simp only [id, Pi.neg_apply]
  · simp only [id, mul_one]; field_simp

/-- Two integrations by parts on `[0, π]`. -/
theorem ibp_two (k : ℕ) {m : ℕ} (hm : 0 < m) :
    ∫ t in (0 : ℝ)..π, cauchyD k t * Real.cos (m * t) =
      ((-1) ^ m * cauchyD (k + 1) π - cauchyD (k + 1) 0) / (m : ℝ) ^ 2 -
        (∫ t in (0 : ℝ)..π, cauchyD (k + 2) t * Real.cos (m * t)) / (m : ℝ) ^ 2 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := π)
    (u := cauchyD k) (u' := cauchyD (k + 1)) (v := fun t => Real.sin (m * t) / m)
    (v' := fun t => Real.cos (m * t)) (fun t _ => hasDerivAt_cauchyD k t)
    (fun t _ => hasDerivAt_sin_div m t hm') ((continuous_cauchyD _).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ => Real.cos (m * t)).intervalIntegrable _ _)
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := π)
    (u := cauchyD (k + 1)) (u' := cauchyD (k + 2)) (v := fun t => -Real.cos (m * t) / m ^ 2)
    (v' := fun t => Real.sin (m * t) / m) (fun t _ => hasDerivAt_cauchyD (k + 1) t)
    (fun t _ => hasDerivAt_neg_cos_div m t hm') ((continuous_cauchyD _).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ => Real.sin (m * t) / m).intervalIntegrable _ _)
  have e : (fun t => cauchyD (k + 2) t * (-Real.cos (m * t) / (m : ℝ) ^ 2)) =
      fun t => (-1 / (m : ℝ) ^ 2) * (cauchyD (k + 2) t * Real.cos (m * t)) := by
    funext t; ring
  rw [e, intervalIntegral.integral_const_mul] at h2
  rw [h1, h2, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, mul_zero, Real.sin_zero,
    Real.cos_zero]
  field_simp
  ring

/-- Two integrations by parts on `[π, ∞)`. -/
theorem ibp_two_tail (k : ℕ) {m : ℕ} (hm : 0 < m) :
    ∫ t in Ioi π, cauchyD k t * Real.cos (m * t) =
      -((-1) ^ m * cauchyD (k + 1) π) / (m : ℝ) ^ 2 -
        (∫ t in Ioi π, cauchyD (k + 2) t * Real.cos (m * t)) / (m : ℝ) ^ 2 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hc : Continuous fun t : ℝ => Real.cos (m * t) := by fun_prop
  have hs : Continuous fun t : ℝ => Real.sin (m * t) / m := by fun_prop
  have hc' : Continuous fun t : ℝ => -Real.cos (m * t) / m ^ 2 := by fun_prop
  have bc : ∀ t, |Real.cos (m * t)| ≤ 1 := fun t => Real.abs_cos_le_one _
  have bs : ∀ t, |Real.sin (m * t) / m| ≤ 1 / |(m : ℝ)| := fun t => by
    rw [abs_div]; exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
  have bc' : ∀ t, |-Real.cos (m * t) / m ^ 2| ≤ 1 / |(m : ℝ) ^ 2| := fun t => by
    rw [abs_div, abs_neg]; exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
  have h1 := integral_Ioi_mul_deriv_eq_deriv_mul (a := π)
    (u := cauchyD k) (u' := cauchyD (k + 1)) (v := fun t => Real.sin (m * t) / m)
    (v' := fun t => Real.cos (m * t)) (fun t _ => hasDerivAt_cauchyD k t)
    (fun t _ => hasDerivAt_sin_div m t hm') (integrable_cauchyD_mul k hc bc).integrableOn
    (integrable_cauchyD_mul (k + 1) hs bs).integrableOn
    (((continuous_cauchyD k).mul hs).tendsto π |>.mono_left nhdsWithin_le_nhds)
    (tendsto_cauchyD_mul_atTop k bs)
  have h2 := integral_Ioi_mul_deriv_eq_deriv_mul (a := π)
    (u := cauchyD (k + 1)) (u' := cauchyD (k + 2)) (v := fun t => -Real.cos (m * t) / m ^ 2)
    (v' := fun t => Real.sin (m * t) / m) (fun t _ => hasDerivAt_cauchyD (k + 1) t)
    (fun t _ => hasDerivAt_neg_cos_div m t hm') (integrable_cauchyD_mul (k + 1) hs bs).integrableOn
    (integrable_cauchyD_mul (k + 2) hc' bc').integrableOn
    (((continuous_cauchyD (k + 1)).mul hc').tendsto π |>.mono_left nhdsWithin_le_nhds)
    (tendsto_cauchyD_mul_atTop (k + 1) bc')
  have e : (fun t => cauchyD (k + 2) t * (-Real.cos (m * t) / (m : ℝ) ^ 2)) =
      fun t => (-1 / (m : ℝ) ^ 2) * (cauchyD (k + 2) t * Real.cos (m * t)) := by
    funext t; ring
  rw [e, MeasureTheory.integral_const_mul] at h2
  simp only [Pi.mul_apply] at h1 h2
  rw [h1, h2, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  field_simp
  ring

/-! ### 2.11.2 -/

theorem cosIntI_eq (m : ℝ) :
    cosIntI m = ∫ t in (0 : ℝ)..π, cauchyD 0 t * Real.cos (m * t) := by
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [cauchyD_zero]
  ring

/-- **2.11.2, exact form**: `n` steps of integration by parts give
`I(m) = (−1)^m ∑_{s=1}^{n} q_s(π)/m^{2s} + (−1)^n m^{−2n} ∫_0^π φ^{(2n)}(t) cos(mt) dt`. -/
theorem dlmf_2_11_2_exact (n : ℕ) {m : ℕ} (hm : 0 < m) :
    cosIntI m = (-1) ^ m * ∑ s ∈ Finset.range n, cosIntQ (s + 1) π / (m : ℝ) ^ (2 * (s + 1)) +
      (-1) ^ n / (m : ℝ) ^ (2 * n) * ∫ t in (0 : ℝ)..π, cauchyD (2 * n) t * Real.cos (m * t) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  induction n with
  | zero => simp [cosIntI_eq]
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, ibp_two (2 * n) hm, cauchyD_odd_zero, cosIntQ_succ,
      show 2 * (n + 1) = 2 * n + 2 by ring]
    field_simp
    ring

/-- **DLMF 2.11.2**: `I(m) ∼ (−1)^m ∑_{s≥1} q_s(π)/m^{2s}`, with the remainder after `n` terms
at most `(|q_{n+1}(π)| + ∫_0^π |φ^{(2n+2)}|)/m^{2n+2}` for every positive integer `m`. -/
theorem dlmf_2_11_2 (n : ℕ) {m : ℕ} (hm : 0 < m) :
    |cosIntI m - (-1) ^ m * ∑ s ∈ Finset.range n, cosIntQ (s + 1) π / (m : ℝ) ^ (2 * (s + 1))| ≤
      (|cosIntQ (n + 1) π| + ∫ t in (0 : ℝ)..π, |cauchyD (2 * n + 2) t|) /
        (m : ℝ) ^ (2 * n + 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hJ : |∫ t in (0 : ℝ)..π, cauchyD (2 * n + 2) t * Real.cos (m * t)| ≤
      ∫ t in (0 : ℝ)..π, |cauchyD (2 * n + 2) t| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le Real.pi_pos.le
      (Eventually.of_forall fun t _ => ?_) ((continuous_cauchyD _).abs.intervalIntegrable _ _)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  rw [dlmf_2_11_2_exact (n + 1) hm, Finset.sum_range_succ,
    show 2 * (n + 1) = 2 * n + 2 by ring]
  set J := ∫ t in (0 : ℝ)..π, cauchyD (2 * n + 2) t * Real.cos (m * t)
  have hp : (0 : ℝ) < (m : ℝ) ^ (2 * n + 2) := by positivity
  rw [show (-1 : ℝ) ^ m * (∑ s ∈ Finset.range n, cosIntQ (s + 1) π / (m : ℝ) ^ (2 * (s + 1)) +
      cosIntQ (n + 1) π / (m : ℝ) ^ (2 * n + 2)) + (-1) ^ (n + 1) / (m : ℝ) ^ (2 * n + 2) * J -
      (-1) ^ m * ∑ s ∈ Finset.range n, cosIntQ (s + 1) π / (m : ℝ) ^ (2 * (s + 1)) =
      ((-1) ^ m * cosIntQ (n + 1) π + (-1) ^ (n + 1) * J) / (m : ℝ) ^ (2 * n + 2) by ring,
    abs_div, abs_of_pos hp]
  gcongr
  refine (abs_add_le _ _).trans ?_
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  gcongr

/-! ### The tail and `½πe^{−m}` -/

/-- `T(m) = ∫_π^∞ cos(mt)/(t² + 1) dt`. -/
noncomputable def cosIntTail (m : ℝ) : ℝ := ∫ t in Ioi π, Real.cos (m * t) / (t ^ 2 + 1)

theorem integrable_cos_div (m : ℝ) : Integrable fun t : ℝ => Real.cos (m * t) / (t ^ 2 + 1) := by
  refine (integrable_cauchyD_mul 0 (g := fun t => Real.cos (m * t)) (by fun_prop)
    (fun t => Real.abs_cos_le_one _)).congr (Eventually.of_forall fun t => ?_)
  simp only [cauchyD_zero]
  ring

/-- `I(m) + T(m) = ∫_0^∞ cos(mt)/(t² + 1) dt = ½πe^{−m}` (§1.14). -/
theorem cosIntI_add_tail {m : ℝ} (hm : 0 < m) :
    cosIntI m + cosIntTail m = π / 2 * Real.exp (-m) := by
  have h := integral_poisson_kernel_cos (a := 1) one_pos hm
  have e : (fun t : ℝ => 1 / (1 ^ 2 + t ^ 2) * Real.cos (m * t)) =
      fun t => Real.cos (m * t) / (t ^ 2 + 1) := by funext t; ring
  rw [e, one_mul, ← Ioc_union_Ioi_eq_Ioi Real.pi_pos.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (integrable_cos_div m).integrableOn (integrable_cos_div m).integrableOn] at h
  rw [cosIntI, cosIntTail, intervalIntegral.integral_of_le Real.pi_pos.le, h]

theorem cosIntTail_eq (m : ℝ) :
    cosIntTail m = ∫ t in Ioi π, cauchyD 0 t * Real.cos (m * t) := by
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [cauchyD_zero]
  ring

/-- The tail expansion: `T(m) = −(−1)^m ∑_{s=1}^{n} q_s(π)/m^{2s}
+ (−1)^n m^{−2n} ∫_π^∞ φ^{(2n)}(t) cos(mt) dt`. -/
theorem cosIntTail_exact (n : ℕ) {m : ℕ} (hm : 0 < m) :
    cosIntTail m =
      -((-1) ^ m * ∑ s ∈ Finset.range n, cosIntQ (s + 1) π / (m : ℝ) ^ (2 * (s + 1))) +
      (-1) ^ n / (m : ℝ) ^ (2 * n) * ∫ t in Ioi π, cauchyD (2 * n) t * Real.cos (m * t) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  induction n with
  | zero => simp [cosIntTail_eq]
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, ibp_two_tail (2 * n) hm, cosIntQ_succ,
      show 2 * (n + 1) = 2 * n + 2 by ring]
    field_simp
    ring

/-- `∫_π^∞ |φ^{(j+1)}| ≤ j!/π^{j+1}`. -/
theorem integral_abs_cauchyD_tail_le (j : ℕ) :
    ∫ t in Ioi π, |cauchyD (j + 1) t| ≤ j.factorial / π ^ (j + 1) := by
  have ha : (-((j : ℝ) + 2)) < -1 := by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
  have hint := integrableOn_Ioi_rpow_of_lt ha Real.pi_pos
  have hval := integral_Ioi_rpow_of_lt ha Real.pi_pos
  calc ∫ t in Ioi π, |cauchyD (j + 1) t|
      ≤ ∫ t in Ioi π, ((j + 1).factorial : ℝ) * t ^ (-((j : ℝ) + 2)) := by
        refine setIntegral_mono_on (integrable_cauchyD _).abs.integrableOn
          (hint.const_mul _) measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := Real.pi_pos.trans ht
        refine (abs_cauchyD_le_pow ht0).trans (le_of_eq ?_)
        rw [Real.rpow_neg ht0.le, show (j : ℝ) + 2 = ((j + 1 + 1 : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast, div_eq_mul_inv]
    _ = j.factorial / π ^ (j + 1) := by
        rw [MeasureTheory.integral_const_mul, hval,
          show -((j : ℝ) + 2) + 1 = -((j + 1 : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_neg Real.pi_pos.le, Real.rpow_natCast, Nat.factorial_succ]
        push_cast
        field_simp

/-- **The explanation of §2.11(i)**: the same series expands `I(m) − ½πe^{−m}` with a remainder
that only involves `[π, ∞)`:
`|I(m) − ½πe^{−m} − (−1)^m ∑_{s=1}^{n} q_s(π)/m^{2s}|
≤ (|q_{n+1}(π)| + ∫_π^∞ |φ^{(2n+2)}|)/m^{2n+2}
≤ ((2n+1)!/(π² + 1)^{n+1} + (2n+1)!/π^{2n+2})/m^{2n+2}`. -/
theorem dlmf_2_11_i_shifted (n : ℕ) {m : ℕ} (hm : 0 < m) :
    |cosIntI m - π / 2 * Real.exp (-m) -
        (-1) ^ m * ∑ s ∈ Finset.range n, cosIntQ (s + 1) π / (m : ℝ) ^ (2 * (s + 1))| ≤
      (|cosIntQ (n + 1) π| + ∫ t in Ioi π, |cauchyD (2 * n + 2) t|) / (m : ℝ) ^ (2 * n + 2) ∧
    (|cosIntQ (n + 1) π| + ∫ t in Ioi π, |cauchyD (2 * n + 2) t|) / (m : ℝ) ^ (2 * n + 2) ≤
      ((2 * n + 1).factorial / (π ^ 2 + 1) ^ (n + 1) + (2 * n + 1).factorial / π ^ (2 * n + 2)) /
        (m : ℝ) ^ (2 * n + 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : (0 : ℝ) < (m : ℝ) ^ (2 * n + 2) := by positivity
  refine ⟨?_, ?_⟩
  · have hJ : |∫ t in Ioi π, cauchyD (2 * n + 2) t * Real.cos (m * t)| ≤
        ∫ t in Ioi π, |cauchyD (2 * n + 2) t| := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (integrable_cauchyD _).abs.integrableOn
        (Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    have hI : cosIntI m - π / 2 * Real.exp (-m) = -cosIntTail m := by
      linarith [cosIntI_add_tail hm0]
    rw [hI, cosIntTail_exact (n + 1) hm, Finset.sum_range_succ,
      show 2 * (n + 1) = 2 * n + 2 by ring]
    set J := ∫ t in Ioi π, cauchyD (2 * n + 2) t * Real.cos (m * t)
    rw [show -(-((-1 : ℝ) ^ m * (∑ s ∈ Finset.range n,
        cosIntQ (s + 1) π / (m : ℝ) ^ (2 * (s + 1)) +
        cosIntQ (n + 1) π / (m : ℝ) ^ (2 * n + 2))) + (-1) ^ (n + 1) / (m : ℝ) ^ (2 * n + 2) * J) -
        (-1) ^ m * ∑ s ∈ Finset.range n, cosIntQ (s + 1) π / (m : ℝ) ^ (2 * (s + 1)) =
        ((-1) ^ m * cosIntQ (n + 1) π - (-1) ^ (n + 1) * J) / (m : ℝ) ^ (2 * n + 2) by ring,
      abs_div, abs_of_pos hp]
    gcongr
    refine (abs_sub _ _).trans ?_
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    gcongr
  · gcongr
    · rw [cosIntQ_succ, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact abs_cauchyD_odd_le n π
    · have := integral_abs_cauchyD_tail_le (2 * n + 1)
      rwa [show 2 * n + 1 + 1 = 2 * n + 2 by ring] at this

/-- **"The asymptotic series represents an infinite class of functions"**: `I(m)` and
`I(m) − ½πe^{−m}` (which differ for every `m`) have the same expansion 2.11.2. -/
theorem dlmf_2_11_i_same_expansion (n : ℕ) :
    ∃ C₁ C₂ : ℝ, ∀ m : ℕ, 0 < m →
      |cosIntI m - (-1) ^ m * ∑ s ∈ Finset.range n,
          cosIntQ (s + 1) π / (m : ℝ) ^ (2 * (s + 1))| ≤ C₁ / (m : ℝ) ^ (2 * n + 2) ∧
      |cosIntI m - π / 2 * Real.exp (-m) - (-1) ^ m * ∑ s ∈ Finset.range n,
          cosIntQ (s + 1) π / (m : ℝ) ^ (2 * (s + 1))| ≤ C₂ / (m : ℝ) ^ (2 * n + 2) ∧
      cosIntI m ≠ cosIntI m - π / 2 * Real.exp (-m) :=
  ⟨|cosIntQ (n + 1) π| + ∫ t in (0 : ℝ)..π, |cauchyD (2 * n + 2) t|,
    |cosIntQ (n + 1) π| + ∫ t in Ioi π, |cauchyD (2 * n + 2) t|, fun m hm =>
    ⟨dlmf_2_11_2 n hm, (dlmf_2_11_i_shifted n hm).1, by
      have : 0 < π / 2 * Real.exp (-(m : ℝ)) := mul_pos (by positivity) (Real.exp_pos _)
      linarith⟩⟩

end Azurite.DLMF
