/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13Real
import Azurite.Transcendental.Exp
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The real Lambert `W` function: enclosures, Lipschitz bounds, irrationality

The analytic facts behind `AzFloat.lambertW0PrecRound`/`lambertWm1PrecRound`
(`AzFloat/LambertW.lean`), for `W₀` and `W₋₁` of `DLMF/Chapter4/Section13Real.lean`:

* **A priori enclosures.**  `W₀`: `x/(1+x) ≤ W₀ x ≤ x` for `x ≥ 0`;
  `ln x − ln ln x ≤ W₀ x ≤ ln x` for `x ≥ e`; near the branch point, with `q = 1 + e x ∈ (0, 1)`,
  `−1 + √(2q/e) ≤ W₀ x ≤ −1 + √(2q)` (from `s²/2 ≤ (s − 1)eˢ + 1 ≤ e s²/2` on `[0, 1]`).
  `W₋₁` (`−e⁻¹ < x < 0`, `y = −x`): `L − 1 ≤ W₋₁ x ≤ L` with `L = ln y − ln(−ln y)`;
  `W₋₁ x ≤ −1 − √(2q)`, and `−1 − √(2eq) ≤ W₋₁ x` for `q ≤ 1/4` (from
  `e⁻ᵗ t²/2 ≤ 1 − (1 + t)e⁻ᵗ ≤ t²/2`).
* **Inverse Lipschitz bounds** (`mul_abs_sub_le_abs_sub_mul_exp_W0/_Wm1`): on an interval
  avoiding `−1`, `|W − m| ≤ |x − m eᵐ| / D` for any `D` below the derivative `(1 + t)eᵗ` of
  `t eᵗ` on the interval — how a verified enclosure of `W` is obtained from an unverified
  approximation `m` and a rigorous enclosure of `m eᵐ`.
* **Irrationality** of `W₀ x`, `W₋₁ x` for rational `x ≠ 0` (`e^W = x/W` would be a rational
  power of `e`), and `−e⁻¹` is irrational, so a float is never on the domain boundary.
-/

open Real Set Azurite.DLMF

namespace Azurite.LambertW

/-! ### The functions `(s − 1)eˢ + 1` and `1 − (1 + t)e⁻ᵗ` -/

theorem hasDerivAt_sub_one_mul_exp (s : ℝ) :
    HasDerivAt (fun s => (s - 1) * exp s + 1) (s * exp s) s := by
  have h : HasDerivAt (fun s => (s - 1) * exp s + 1) (1 * exp s + (s - 1) * exp s) s :=
    (((hasDerivAt_id s).sub_const 1).mul (hasDerivAt_exp s)).add_const 1
  exact h.congr_deriv (by ring)

/-- `s²/2 ≤ (s − 1)eˢ + 1` for `s ≥ 0`. -/
theorem sq_div_two_le_sub_one_mul_exp {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 / 2 ≤ (s - 1) * exp s + 1 := by
  let φ : ℝ → ℝ := fun s => (s - 1) * exp s + 1 - s ^ 2 / 2
  have hφ : ∀ s, HasDerivAt φ (s * exp s - s) s := fun s => by
    have h := (hasDerivAt_sub_one_mul_exp s).sub ((hasDerivAt_pow 2 s).div_const 2)
    convert h using 1
    push_cast
    ring
  have hmono : MonotoneOn φ (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun s _ => (hφ s).continuousAt.continuousWithinAt)
      (fun s _ => (hφ s).differentiableAt.differentiableWithinAt) fun s hs => ?_
    rw [interior_Ici, mem_Ioi] at hs
    rw [(hφ s).deriv]
    have : 1 ≤ exp s := by rw [← exp_zero]; exact exp_le_exp.mpr hs.le
    nlinarith
  have h0 : φ 0 = 0 := by simp [φ]
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs) hs
  rw [h0] at this
  simp only [φ] at this
  linarith

/-- `(s − 1)eˢ + 1 ≤ e s²/2` for `0 ≤ s ≤ 1`. -/
theorem sub_one_mul_exp_le_exp_mul_sq {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (s - 1) * exp s + 1 ≤ exp 1 * s ^ 2 / 2 := by
  let χ : ℝ → ℝ := fun s => exp 1 * s ^ 2 / 2 - ((s - 1) * exp s + 1)
  have hχ : ∀ s, HasDerivAt χ (exp 1 * s - s * exp s) s := fun s => by
    have h := (((hasDerivAt_pow 2 s).const_mul (exp 1)).div_const 2).sub
      (hasDerivAt_sub_one_mul_exp s)
    convert h using 1
    push_cast
    ring
  have hmono : MonotoneOn χ (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun s _ => (hχ s).continuousAt.continuousWithinAt)
      (fun s _ => (hχ s).differentiableAt.differentiableWithinAt) fun s hs => ?_
    rw [interior_Icc, mem_Ioo] at hs
    rw [(hχ s).deriv]
    have : exp s ≤ exp 1 := exp_le_exp.mpr hs.2.le
    nlinarith
  have h0 : χ 0 = 0 := by simp [χ]
  have := hmono (mem_Icc.mpr ⟨le_rfl, zero_le_one⟩) (mem_Icc.mpr ⟨hs, hs1⟩) hs
  rw [h0] at this
  simp only [χ] at this
  linarith

theorem hasDerivAt_one_sub_mul_exp_neg (t : ℝ) :
    HasDerivAt (fun t => 1 - (1 + t) * exp (-t)) (t * exp (-t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => exp (-t)) (-exp (-t)) t := by
    have := (hasDerivAt_neg t).exp
    simpa using this
  have h : HasDerivAt (fun t => 1 - (1 + t) * exp (-t))
      (-(1 * exp (-t) + (1 + t) * -exp (-t))) t :=
    (((hasDerivAt_id t).const_add 1).mul h1).const_sub 1
  exact h.congr_deriv (by ring)

/-- `1 − (1 + t)e⁻ᵗ ≤ t²/2` for `t ≥ 0`. -/
theorem one_sub_mul_exp_neg_le_sq_div_two {t : ℝ} (ht : 0 ≤ t) :
    1 - (1 + t) * exp (-t) ≤ t ^ 2 / 2 := by
  let ψ : ℝ → ℝ := fun t => t ^ 2 / 2 - (1 - (1 + t) * exp (-t))
  have hψ : ∀ t, HasDerivAt ψ (t - t * exp (-t)) t := fun t => by
    have h := ((hasDerivAt_pow 2 t).div_const 2).sub (hasDerivAt_one_sub_mul_exp_neg t)
    convert h using 1
    push_cast
    ring
  have hmono : MonotoneOn ψ (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun t _ => (hψ t).continuousAt.continuousWithinAt)
      (fun t _ => (hψ t).differentiableAt.differentiableWithinAt) fun t ht => ?_
    rw [interior_Ici, mem_Ioi] at ht
    rw [(hψ t).deriv]
    have : exp (-t) ≤ 1 := by rw [← exp_zero]; exact exp_le_exp.mpr (by linarith)
    nlinarith
  have h0 : ψ 0 = 0 := by simp [ψ]
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  rw [h0] at this
  simp only [ψ] at this
  linarith

/-- `e⁻ᵗ t²/2 ≤ 1 − (1 + t)e⁻ᵗ` for `t ≥ 0`. -/
theorem exp_neg_mul_sq_div_two_le {t : ℝ} (ht : 0 ≤ t) :
    exp (-t) * t ^ 2 / 2 ≤ 1 - (1 + t) * exp (-t) := by
  let ω : ℝ → ℝ := fun t => 1 - (1 + t) * exp (-t) - exp (-t) * t ^ 2 / 2
  have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => exp (-t)) (-exp (-t)) t := fun t => by
    have := (hasDerivAt_neg t).exp
    simpa using this
  have hω : ∀ t, HasDerivAt ω (exp (-t) * t ^ 2 / 2) t := fun t => by
    have h := (hasDerivAt_one_sub_mul_exp_neg t).sub
      (((h1 t).mul (hasDerivAt_pow 2 t)).div_const 2)
    convert h using 1
    push_cast
    ring
  have hmono : MonotoneOn ω (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun t _ => (hω t).continuousAt.continuousWithinAt)
      (fun t _ => (hω t).differentiableAt.differentiableWithinAt) fun t _ => ?_
    rw [(hω t).deriv]
    positivity
  have h0 : ω 0 = 0 := by simp [ω]
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  rw [h0] at this
  simp only [ω] at this
  linarith

/-- `t ↦ 1 − (1 + t)e⁻ᵗ` is increasing on `[0, ∞)`. -/
theorem monotoneOn_one_sub_mul_exp_neg : MonotoneOn (fun t => 1 - (1 + t) * exp (-t)) (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun t _ => (hasDerivAt_one_sub_mul_exp_neg t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_one_sub_mul_exp_neg t).differentiableAt.differentiableWithinAt)
    fun t ht => ?_
  rw [interior_Ici, mem_Ioi] at ht
  rw [(hasDerivAt_one_sub_mul_exp_neg t).deriv]
  positivity

/-! ### A priori enclosures of `W₀` -/

theorem lambertW0_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ lambertW0 x := (dlmf_4_13_1_nonneg hx).2

theorem neg_exp_neg_one_le_of_nonneg {x : ℝ} (hx : 0 ≤ x) : -exp (-1) ≤ x := by
  linarith [exp_pos (-1)]

/-- `W₀ x ≤ x` for `x ≥ 0`. -/
theorem lambertW0_le_self {x : ℝ} (hx : 0 ≤ x) : lambertW0 x ≤ x := by
  have h := lambertW0_spec (neg_exp_neg_one_le_of_nonneg hx)
  have hW := lambertW0_nonneg hx
  by_contra hlt
  push Not at hlt
  have := strictMonoOn_mul_exp (by simp; linarith) (by simp; linarith) hlt
  simp only at this
  rw [h.2] at this
  have : x ≤ x * exp x := le_mul_of_one_le_right hx (one_le_exp hx)
  linarith

/-- `x/(1 + x) ≤ W₀ x` for `x ≥ 0`. -/
theorem div_one_add_le_lambertW0 {x : ℝ} (hx : 0 ≤ x) : x / (1 + x) ≤ lambertW0 x := by
  have h := lambertW0_spec (neg_exp_neg_one_le_of_nonneg hx)
  have hW := lambertW0_nonneg hx
  have h1x : 0 < 1 + x := by linarith
  set u := x / (1 + x) with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : 1 - u = 1 / (1 + x) := by rw [hu]; field_simp; ring
  -- `e^u ≤ 1/(1 − u) = 1 + x`
  have hexp : exp u ≤ 1 + x := by
    have h2 : 1 - u ≤ exp (-u) := by have := add_one_le_exp (-u); linarith
    have h3 : 0 < 1 - u := by rw [hu1]; positivity
    rw [exp_neg] at h2
    have h4 : (1 - u) * exp u ≤ 1 := by
      have := mul_le_mul_of_nonneg_right h2 (exp_pos u).le
      rwa [inv_mul_cancel₀ (exp_pos u).ne'] at this
    rw [hu1] at h4
    have := (div_mul_eq_mul_div _ _ _).symm.trans_le h4
    rwa [div_le_one h1x, one_mul] at this
  have hg : u * exp u ≤ x := by
    calc u * exp u ≤ u * (1 + x) := mul_le_mul_of_nonneg_left hexp hu0
      _ = x := by rw [hu]; field_simp
  by_contra hlt
  push Not at hlt
  have := strictMonoOn_mul_exp (by simp; linarith) (by simp; linarith) hlt
  simp only at this
  rw [h.2] at this
  linarith

/-- `W₀ x ≤ ln x` for `x ≥ e`. -/
theorem lambertW0_le_log {x : ℝ} (hx : exp 1 ≤ x) : lambertW0 x ≤ log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos 1) hx
  have h := lambertW0_spec (neg_exp_neg_one_le_of_nonneg hx0.le)
  have hl1 : 1 ≤ log x := by rw [← log_exp 1]; exact log_le_log (exp_pos 1) hx
  by_contra hlt
  push Not at hlt
  have := strictMonoOn_mul_exp (by simp; linarith) (by simp; linarith [lambertW0_nonneg hx0.le]) hlt
  simp only at this
  rw [h.2, exp_log hx0] at this
  have : x ≤ log x * x := le_mul_of_one_le_left hx0.le hl1
  linarith

/-- `ln x − ln ln x ≤ W₀ x` for `x ≥ e`. -/
theorem log_sub_log_log_le_lambertW0 {x : ℝ} (hx : exp 1 ≤ x) :
    log x - log (log x) ≤ lambertW0 x := by
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos 1) hx
  have h := lambertW0_spec (neg_exp_neg_one_le_of_nonneg hx0.le)
  have hl1 : 1 ≤ log x := by rw [← log_exp 1]; exact log_le_log (exp_pos 1) hx
  have hl0 : 0 < log x := by linarith
  have hll : 0 ≤ log (log x) := log_nonneg hl1
  have hllle : log (log x) ≤ log x - 1 := log_le_sub_one_of_pos hl0
  set L := log x - log (log x) with hL
  have hL1 : 1 ≤ L := by rw [hL]; linarith
  have heL : exp L = x / log x := by
    rw [hL, exp_sub, exp_log hx0, exp_log hl0]
  have hg : L * exp L ≤ x := by
    rw [heL, hL, sub_mul, mul_div_assoc', mul_comm (log x) x, mul_div_assoc, div_self hl0.ne',
      mul_one]
    have : 0 ≤ log (log x) * (x / log x) := by positivity
    linarith
  by_contra hlt
  push Not at hlt
  have := strictMonoOn_mul_exp (by simp; linarith) (by simp; linarith) hlt
  simp only at this
  rw [h.2] at this
  linarith

/-- `W₀ x < 0` for `−e⁻¹ ≤ x < 0`. -/
theorem lambertW0_neg {x : ℝ} (hx1 : -exp (-1) ≤ x) (hx0 : x < 0) : lambertW0 x < 0 := by
  have h := lambertW0_spec hx1
  by_contra hle
  push Not at hle
  have : 0 ≤ lambertW0 x * exp (lambertW0 x) := mul_nonneg hle (exp_pos _).le
  linarith

/-- The branch-point enclosure of `W₀`: with `q = 1 + e x ∈ (0, 1)`,
`−1 + √(2q/e) ≤ W₀ x ≤ −1 + √(2q)`. -/
theorem lambertW0_branch_bounds {x : ℝ} (hx1 : -exp (-1) < x) (hx0 : x < 0) :
    -1 + √(2 * (1 + exp 1 * x) / exp 1) ≤ lambertW0 x ∧
      lambertW0 x ≤ -1 + √(2 * (1 + exp 1 * x)) := by
  have h := lambertW0_spec hx1.le
  have hgt := lambertW0_gt hx1
  have hlt := lambertW0_neg hx1.le hx0
  set W := lambertW0 x with hW
  set s := 1 + W with hs
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hs1 : s ≤ 1 := by rw [hs]; linarith
  -- `q = (s − 1)eˢ + 1`
  have hq : 1 + exp 1 * x = (s - 1) * exp s + 1 := by
    rw [← h.2, hs, exp_add, show 1 + W - 1 = W by ring]
    ring
  have hlo := sq_div_two_le_sub_one_mul_exp hs0
  have hhi := sub_one_mul_exp_le_exp_mul_sq hs0 hs1
  have he0 : 0 < exp 1 := exp_pos 1
  constructor
  · have h1 : 2 * (1 + exp 1 * x) / exp 1 ≤ s ^ 2 := by
      rw [hq, div_le_iff₀ he0]; linarith
    have := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq hs0] at this
    rw [hs] at this
    linarith
  · have h1 : s ^ 2 ≤ 2 * (1 + exp 1 * x) := by rw [hq]; linarith
    have := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq hs0] at this
    rw [hs] at this
    linarith

/-! ### A priori enclosures of `W₋₁` -/

/-- `W₋₁ x ≤ −1 − √(2q)` with `q = 1 + e x`, for `−e⁻¹ < x < 0`. -/
theorem lambertWm1_le_branch {x : ℝ} (hx1 : -exp (-1) < x) (hx0 : x < 0) :
    lambertWm1 x ≤ -1 - √(2 * (1 + exp 1 * x)) := by
  have h := lambertWm1_spec hx1.le hx0
  set W := lambertWm1 x with hW
  set t := -1 - W with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith [h.1]
  have hq : 1 + exp 1 * x = 1 - (1 + t) * exp (-t) := by
    rw [← h.2, ht, show -(-1 - W) = 1 + W by ring, exp_add]
    ring
  have h1 : 2 * (1 + exp 1 * x) ≤ t ^ 2 := by
    rw [hq]; linarith [one_sub_mul_exp_neg_le_sq_div_two ht0]
  have := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq ht0] at this
  rw [ht] at this
  linarith

/-- `−1 − √(2eq) ≤ W₋₁ x` with `q = 1 + e x ≤ 1/4`, for `−e⁻¹ < x < 0`. -/
theorem branch_le_lambertWm1 {x : ℝ} (hx1 : -exp (-1) < x) (hx0 : x < 0)
    (hq : 1 + exp 1 * x ≤ 1 / 4) :
    -1 - √(2 * exp 1 * (1 + exp 1 * x)) ≤ lambertWm1 x := by
  have h := lambertWm1_spec hx1.le hx0
  set W := lambertWm1 x with hW
  set t := -1 - W with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith [h.1]
  have hqt : 1 + exp 1 * x = 1 - (1 + t) * exp (-t) := by
    rw [← h.2, ht, show -(-1 - W) = 1 + W by ring, exp_add]
    ring
  -- `t ≤ 1`, since the function is increasing and its value at `1` exceeds `1/4`
  have ht1 : t ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have hmono := monotoneOn_one_sub_mul_exp_neg (mem_Ici.mpr zero_le_one) (mem_Ici.mpr ht0) hgt.le
    simp only at hmono
    have he : exp (-1) < 3 / 8 := by
      rw [exp_neg]
      have := exp_one_gt_d9
      rw [inv_lt_comm₀ (exp_pos 1) (by norm_num)]
      linarith
    have : 1 - (1 + 1) * exp (-1) > 1 / 4 := by linarith
    linarith
  have he1 : exp (-1) ≤ exp (-t) := exp_le_exp.mpr (by linarith)
  have hlow := exp_neg_mul_sq_div_two_le ht0
  have h1 : t ^ 2 ≤ 2 * exp 1 * (1 + exp 1 * x) := by
    rw [hqt]
    have he0 : 0 < exp 1 := exp_pos 1
    have hinv : exp (-1) * exp 1 = 1 := by rw [← exp_add]; simp
    have h2 : exp (-1) * t ^ 2 / 2 ≤ exp (-t) * t ^ 2 / 2 := by
      have : 0 ≤ t ^ 2 := sq_nonneg t
      nlinarith
    have h3 : exp (-1) * t ^ 2 / 2 ≤ 1 - (1 + t) * exp (-t) := h2.trans hlow
    have h4 := mul_le_mul_of_nonneg_left h3 he0.le
    have hinv' : exp 1 * exp (-1) = 1 := by rw [mul_comm]; exact hinv
    calc t ^ 2 = exp 1 * (exp (-1) * t ^ 2 / 2) * 2 := by
          rw [show exp 1 * (exp (-1) * t ^ 2 / 2) * 2 = (exp 1 * exp (-1)) * t ^ 2 by ring, hinv',
            one_mul]
      _ ≤ exp 1 * (1 - (1 + t) * exp (-t)) * 2 := by linarith
      _ = 2 * exp 1 * (1 - (1 + t) * exp (-t)) := by ring
  have := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq ht0] at this
  rw [ht] at this
  linarith

/-- `W₋₁ x ≤ ln y − ln(−ln y)` with `y = −x`, for `−e⁻¹ < x < 0`. -/
theorem lambertWm1_le_log_sub_log {x : ℝ} (hx1 : -exp (-1) < x) (hx0 : x < 0) :
    lambertWm1 x ≤ log (-x) - log (-log (-x)) := by
  have h := lambertWm1_spec hx1.le hx0
  set y := -x with hy
  have hy0 : 0 < y := by rw [hy]; linarith
  have hy1 : y < exp (-1) := by rw [hy]; linarith
  have hly : log y < -1 := by
    have := log_lt_log hy0 hy1
    rwa [log_exp] at this
  set v := -log y with hv
  have hv0 : 0 < v := by rw [hv]; linarith
  have hv1 : 1 ≤ v := by rw [hv]; linarith
  have hlv : 0 ≤ log v := log_nonneg hv1
  set L := log y - log v with hL
  have heL : exp L = y / v := by rw [hL, exp_sub, exp_log hy0, exp_log hv0]
  have hL1 : L ≤ -1 := by rw [hL, hv]; linarith
  -- `L e^L = −y − (ln v) y/v ≤ −y = x`
  have hg : L * exp L ≤ x := by
    have hvy : v * (y / v) = y := by rw [mul_div_assoc', mul_div_cancel_left₀ y hv0.ne']
    have hlogy : log y = -v := by rw [hv]; ring
    rw [heL, hL, hlogy, sub_mul, neg_mul, hvy]
    have : 0 ≤ log v * (y / v) := by positivity
    rw [hy]
    linarith
  by_contra hlt
  push Not at hlt
  have := strictAntiOn_mul_exp (by simp; linarith [h.1, hL1]) (by simp; linarith [h.1, hL1]) hlt
  simp only at this
  rw [h.2] at this
  linarith

/-- `ln y − ln(−ln y) − 1 ≤ W₋₁ x` with `y = −x`, for `−e⁻¹ < x < 0`. -/
theorem log_sub_log_sub_one_le_lambertWm1 {x : ℝ} (hx1 : -exp (-1) < x) (hx0 : x < 0) :
    log (-x) - log (-log (-x)) - 1 ≤ lambertWm1 x := by
  have h := lambertWm1_spec hx1.le hx0
  set y := -x with hy
  have hy0 : 0 < y := by rw [hy]; linarith
  have hy1 : y < exp (-1) := by rw [hy]; linarith
  have hly : log y < -1 := by
    have := log_lt_log hy0 hy1
    rwa [log_exp] at this
  set v := -log y with hv
  have hv0 : 0 < v := by rw [hv]; linarith
  have hv1 : 1 ≤ v := by rw [hv]; linarith
  have hlv : log v ≤ v - 1 := log_le_sub_one_of_pos hv0
  set L := log y - log v with hL
  have heL : exp (L - 1) = y / (exp 1 * v) := by
    rw [exp_sub, hL, exp_sub, exp_log hy0, exp_log hv0]
    field_simp
  have hL1 : L - 1 ≤ -1 := by
    rw [hL]
    have : 0 ≤ log v := log_nonneg hv1
    linarith
  -- `(L − 1) e^(L−1) ≥ −y`, i.e. `1 − L ≤ e v`
  have hkey : 1 - L ≤ exp 1 * v := by
    have hlogy : log y = -v := by rw [hv]; ring
    have h1L : 1 - L = 1 + v + log v := by rw [hL, hlogy]; ring
    have he2 : (2 : ℝ) < exp 1 := by have := add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
    rw [h1L]
    nlinarith
  have hg : x ≤ (L - 1) * exp (L - 1) := by
    rw [heL]
    have hev : 0 < exp 1 * v := by positivity
    have hcancel : exp 1 * v * (y / (exp 1 * v)) = y := by
      rw [mul_div_assoc', mul_div_cancel_left₀ y hev.ne']
    have e1 : (L - 1) * (y / (exp 1 * v)) = -y + (L - 1 + exp 1 * v) * (y / (exp 1 * v)) := by
      rw [add_mul, hcancel]; ring
    rw [e1]
    have : 0 ≤ (L - 1 + exp 1 * v) * (y / (exp 1 * v)) := by
      apply mul_nonneg (by linarith) (by positivity)
    rw [hy]
    linarith
  by_contra hlt
  push Not at hlt
  have := strictAntiOn_mul_exp (by simp; linarith [h.1, hL1]) (by simp; linarith [h.1, hL1]) hlt
  simp only at this
  rw [h.2] at this
  linarith

/-! ### Inverse Lipschitz bounds -/

theorem hasDerivAt_mul_exp' (t : ℝ) : HasDerivAt (fun t => t * exp t) ((1 + t) * exp t) t :=
  hasDerivAt_mul_exp t

/-- On `[a, ∞)` with `a > −1`: `D |W − m| ≤ |x − m eᵐ|` for the root `W` of `W e^W = x` and any
`D ≤ (1 + a) eᵃ`. -/
theorem mul_abs_sub_le_abs_sub_mul_exp_W0 {a m W x D : ℝ} (ha : -1 < a) (hm : a ≤ m)
    (hW : a ≤ W) (hWx : W * exp W = x) (hD0 : 0 ≤ D) (hD : D ≤ (1 + a) * exp a) :
    D * |W - m| ≤ |x - m * exp m| := by
  have hconv : Convex ℝ (Ici a) := convex_Ici a
  have hcont : ContinuousOn (fun t => t * exp t) (Ici a) :=
    (continuous_id.mul continuous_exp).continuousOn
  have hdiff : DifferentiableOn ℝ (fun t => t * exp t) (interior (Ici a)) := fun t _ =>
    (hasDerivAt_mul_exp' t).differentiableAt.differentiableWithinAt
  have hderiv : ∀ t ∈ interior (Ici a), D ≤ deriv (fun t => t * exp t) t := fun t ht => by
    rw [interior_Ici, mem_Ioi] at ht
    rw [(hasDerivAt_mul_exp' t).deriv]
    calc D ≤ (1 + a) * exp a := hD
      _ ≤ (1 + t) * exp t := by
        have h1 : 1 + a ≤ 1 + t := by linarith
        have h2 : exp a ≤ exp t := exp_le_exp.mpr ht.le
        have h3 : 0 ≤ 1 + a := by linarith
        exact mul_le_mul h1 h2 (exp_pos a).le (by linarith)
  have key := hconv.mul_sub_le_image_sub_of_le_deriv hcont hdiff hderiv
  rcases le_total m W with hmW | hWm
  · have := key m (mem_Ici.mpr hm) W (mem_Ici.mpr hW) hmW
    rw [hWx] at this
    have hprod := mul_nonneg hD0 (sub_nonneg.mpr hmW)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · have := key W (mem_Ici.mpr hW) m (mem_Ici.mpr hm) hWm
    rw [hWx] at this
    have hprod := mul_nonneg hD0 (sub_nonneg.mpr hWm)
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-- On `[a, b]` with `b < −1`: `D |W − m| ≤ |x − m eᵐ|` for the root `W` of `W e^W = x` and
any `D ≤ (−1 − b) eᵃ`. -/
theorem mul_abs_sub_le_abs_sub_mul_exp_Wm1 {a b m W x D : ℝ} (hb : b < -1) (ham : a ≤ m)
    (hmb : m ≤ b) (haW : a ≤ W) (hWb : W ≤ b) (hWx : W * exp W = x) (hD0 : 0 ≤ D)
    (hD : D ≤ (-1 - b) * exp a) :
    D * |W - m| ≤ |x - m * exp m| := by
  have hconv : Convex ℝ (Icc a b) := convex_Icc a b
  have hcont : ContinuousOn (fun t => -(t * exp t)) (Icc a b) :=
    (continuous_id.mul continuous_exp).neg.continuousOn
  have hd : ∀ t, HasDerivAt (fun t => -(t * exp t)) (-((1 + t) * exp t)) t := fun t =>
    (hasDerivAt_mul_exp' t).neg
  have hdiff : DifferentiableOn ℝ (fun t => -(t * exp t)) (interior (Icc a b)) := fun t _ =>
    (hd t).differentiableAt.differentiableWithinAt
  have hderiv : ∀ t ∈ interior (Icc a b), D ≤ deriv (fun t => -(t * exp t)) t := fun t ht => by
    rw [interior_Icc, mem_Ioo] at ht
    rw [(hd t).deriv]
    calc D ≤ (-1 - b) * exp a := hD
      _ ≤ (-1 - t) * exp t := by
        have h1 : -1 - b ≤ -1 - t := by linarith
        have h2 : exp a ≤ exp t := exp_le_exp.mpr ht.1.le
        have h3 : 0 ≤ -1 - b := by linarith
        exact mul_le_mul h1 h2 (exp_pos a).le (by linarith)
      _ = -((1 + t) * exp t) := by ring
  have key := hconv.mul_sub_le_image_sub_of_le_deriv hcont hdiff hderiv
  rcases le_total m W with hmW | hWm
  · have := key m (mem_Icc.mpr ⟨ham, hmb⟩) W (mem_Icc.mpr ⟨haW, hWb⟩) hmW
    rw [hWx] at this
    have hprod := mul_nonneg hD0 (sub_nonneg.mpr hmW)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have := key W (mem_Icc.mpr ⟨haW, hWb⟩) m (mem_Icc.mpr ⟨ham, hmb⟩) hWm
    rw [hWx] at this
    have hprod := mul_nonneg hD0 (sub_nonneg.mpr hWm)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-! ### Irrationality -/

/-- `−e⁻¹` is irrational. -/
theorem irrational_neg_exp_neg_one : Irrational (-exp (-1)) := by
  rw [exp_neg]
  exact irrational_exp_one.inv.neg

/-- A root `W ≠ 0` of `W e^W = x` with `x` rational is irrational. -/
theorem irrational_of_mul_exp_eq {W : ℝ} {x : ℚ} (hx : x ≠ 0) (h : W * exp W = (x : ℝ)) :
    Irrational W := by
  rintro ⟨r, hr⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Rat.cast_zero] at hr
    rw [← hr, zero_mul] at h
    exact hx (by exact_mod_cast h.symm)
  have hr0' : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
  have : exp W = ((x / r : ℚ) : ℝ) := by
    rw [Rat.cast_div, ← hr, eq_div_iff hr0', hr, mul_comm]; exact h
  have hirr := irrational_exp_rat hr0
  rw [← hr] at this
  exact hirr ⟨x / r, this.symm⟩

theorem irrational_lambertW0 {x : ℚ} (hx : x ≠ 0) (hx1 : -exp (-1) ≤ (x : ℝ)) :
    Irrational (lambertW0 x) :=
  irrational_of_mul_exp_eq hx (lambertW0_spec hx1).2

theorem irrational_lambertWm1 {x : ℚ} (hx1 : -exp (-1) ≤ (x : ℝ)) (hx0 : (x : ℝ) < 0) :
    Irrational (lambertWm1 x) :=
  irrational_of_mul_exp_eq (by exact_mod_cast hx0.ne) (lambertWm1_spec hx1 hx0).2

end Azurite.LambertW
