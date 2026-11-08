/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# DLMF §4.45 Methods of Computation

The section describes algorithms; what is formalized is the mathematics they rest on: the
range reductions, identities and series, and (§4.45(iii)) the convergence of Newton's rule. The
numerical example 4.45.12–4.45.14 and the constants `½ ln 10 = 1.15…`, `½π = 1.57…` are computed
by `AzFloat` in `Section45Numerics.lean`.

## §4.45(i) Real variables

* Logarithms: 4.45.1–4.45.2 `dlmf_4_45_1_2` (`ln x = 2^m ln(1 + y)`, `y = x^{2^{−m}} − 1`) and
  `dlmf_4_45_1_tendsto` (`y → 0`, so the series 4.6.1 applies); 4.45.3 `dlmf_4_45_3`, with the
  existence of the scaling `x = 10^m ξ`, `1/10 ≤ ξ ≤ 10` (`dlmf_4_45_3_exists`).
* Exponentials: 4.45.4–4.45.5 `dlmf_4_45_4_5` (`eˣ = 10^m e^y`, `|y| ≤ ½ ln 10`).
* Trigonometric functions: 4.45.6–4.45.7 `dlmf_4_45_6_7` (`|θ| ≤ ½π`).
* Inverse trigonometric functions: 4.45.8 `dlmf_4_45_8` (for all real `x`, not only `x > 0`);
  4.45.9–4.45.10 `dlmf_4_45_9_10` (the sequence `arctanSeq`, `arctan x = 2ⁿ arctan xₙ`,
  `|xₙ| ≤ |x|/2ⁿ → 0`); 4.45.11 `dlmf_4_45_11` (`x > 1`, via 4.24.4's real form); the example
  `arcsin x = arctan(x(1 − x²)^{−1/2})` `dlmf_4_45_arcsin`. DLMF's erratum V1.0.7 replaced
  4.45.8–4.45.9 by the forms formalized here (the old `((1 + x²)^{1/2} − 1)/x` is the same number
  for `x ≠ 0`, but loses accuracy when `x` is small).
* The hyperbolic and inverse hyperbolic functions are referred to §4.28 and §4.37(iv) (no new
  statements).

## §4.45(ii) Complex variables

* 4.45.15 `dlmf_4_45_15` (principal `ph z ∈ (−π, π]`; DLMF's `−π ≤ ph z ≤ π` also allows the value
  from below on the negative axis, `dlmf_4_45_15_cut`; **imprecision**), 4.45.16 `dlmf_4_45_16`.

## §4.45(iii) Lambert `W`-function

"`W₀(x)` can be computed by solving the defining equation `W e^W = x` numerically, for example,
by Newton's rule". With the Newton step `lambertNewton` (iterates `lambertNewtonSeq`):

* `dlmf_4_45_iii_W0`: for `x > −1/e` and any start `w₀ ≥ W₀(x)`, the iterates decrease
  monotonically to `W₀(x)` (`w eʷ` is increasing and convex on `[−1, ∞)`, `convexOn_mul_exp`).
* `dlmf_4_45_iii_Wm1` ("similarly for `W₋₁`"): for `−1/e < x ≤ −2e⁻²` (`W₋₁(x) ∈ [−2, −1)`, where
  `w eʷ` is decreasing and convex) and any start `−2 ≤ w₀ ≤ W₋₁(x)`, the iterates increase to
  `W₋₁(x)`.

The initial approximations (4.13.6, 4.13.10, 4.13.4) are referred to §4.13.
-/

open Set Filter Topology
open scoped Real

namespace Azurite.DLMF

/-! ### §4.45(i) Logarithms -/

/-- **DLMF 4.45.1–4.45.2**: with `y = x^{2^{−m}} − 1`, `ln x = 2^m ln(1 + y)` (`x > 0`). -/
theorem dlmf_4_45_1_2 {x : ℝ} (hx : 0 < x) (m : ℕ) :
    Real.log x = 2 ^ m * Real.log (1 + (x ^ ((2 : ℝ) ^ (-(m : ℝ))) - 1)) := by
  rw [add_sub_cancel, Real.log_rpow hx, ← mul_assoc, ← Real.rpow_natCast,
    ← Real.rpow_add two_pos]
  simp

/-- "We take square roots repeatedly until `|y|` is sufficiently small": `y → 0` as `m → ∞`. -/
theorem dlmf_4_45_1_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun m : ℕ => x ^ ((2 : ℝ) ^ (-(m : ℝ))) - 1) atTop (𝓝 0) := by
  have he : Tendsto (fun m : ℕ => (2 : ℝ) ^ (-(m : ℝ))) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    refine h.congr fun m => ?_
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
  have hc := ((Real.continuousAt_const_rpow hx.ne').tendsto.comp he).sub_const 1
  simpa using hc

/-- **DLMF 4.45.3**: if `x = 10^m ξ` (`m ∈ ℤ`, `ξ > 0`) then `ln x = ln ξ + m ln 10`. -/
theorem dlmf_4_45_3 {x ξ : ℝ} {m : ℤ} (hξ : 0 < ξ) (h : x = 10 ^ m * ξ) :
    Real.log x = Real.log ξ + m * Real.log 10 := by
  rw [h, Real.log_mul (by positivity) hξ.ne', Real.log_zpow]; ring

/-- Every `x > 0` is `10^m ξ` with `m ∈ ℤ`, `1/10 ≤ ξ ≤ 10`. -/
theorem dlmf_4_45_3_exists {x : ℝ} (hx : 0 < x) :
    ∃ m : ℤ, ∃ ξ ∈ Icc (1 / 10 : ℝ) 10, x = 10 ^ m * ξ := by
  set t := Real.logb 10 x
  set m := ⌊t⌋
  have ht : (10 : ℝ) ^ t = x := Real.rpow_logb (by norm_num) (by norm_num) hx
  have h1 := Int.floor_le t
  have h2 := Int.lt_floor_add_one t
  refine ⟨m, (10 : ℝ) ^ (t - m), ⟨?_, ?_⟩, ?_⟩
  · have : (1 : ℝ) ≤ 10 ^ (t - m) := Real.one_le_rpow (by norm_num) (by linarith)
    linarith
  · calc (10 : ℝ) ^ (t - m) ≤ 10 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 10 := Real.rpow_one 10
  · rw [← Real.rpow_intCast, ← Real.rpow_add (by norm_num), add_sub_cancel, ht]

/-! ### §4.45(i) Exponentials -/

/-- **DLMF 4.45.4–4.45.5**: with `m = ⌊x/ln 10 + ½⌋`, `y = x − m ln 10`: `eˣ = 10^m e^y` and
`|y| ≤ ½ ln 10`. -/
theorem dlmf_4_45_4_5 (x : ℝ) :
    Real.exp x = 10 ^ ⌊x / Real.log 10 + 1 / 2⌋ *
        Real.exp (x - ⌊x / Real.log 10 + 1 / 2⌋ * Real.log 10) ∧
      |x - ⌊x / Real.log 10 + 1 / 2⌋ * Real.log 10| ≤ 1 / 2 * Real.log 10 := by
  set m := ⌊x / Real.log 10 + 1 / 2⌋
  have hL : 0 < Real.log 10 := Real.log_pos (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num), ← Real.exp_add]
    ring_nf
  · have h1 := Int.floor_le (x / Real.log 10 + 1 / 2)
    have h2 := Int.lt_floor_add_one (x / Real.log 10 + 1 / 2)
    have e : x - m * Real.log 10 = Real.log 10 * (x / Real.log 10 - m) := by field_simp
    rw [e, abs_mul, abs_of_pos hL, mul_comm (1 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ hL.le
    rw [abs_le]; constructor <;> linarith

/-! ### §4.45(i) Trigonometric functions -/

/-- **DLMF 4.45.6–4.45.7**: with `ξ = x/π`, `m = ⌊ξ + ½⌋`, `θ = π(ξ − m)`:
`sin x = (−1)^m sin θ`, `cos x = (−1)^m cos θ`, and `|θ| ≤ ½π`. -/
theorem dlmf_4_45_6_7 (x : ℝ) :
    Real.sin x = (-1) ^ ⌊x / π + 1 / 2⌋ * Real.sin (π * (x / π - ⌊x / π + 1 / 2⌋)) ∧
      Real.cos x = (-1) ^ ⌊x / π + 1 / 2⌋ * Real.cos (π * (x / π - ⌊x / π + 1 / 2⌋)) ∧
      |π * (x / π - ⌊x / π + 1 / 2⌋)| ≤ π / 2 := by
  set m := ⌊x / π + 1 / 2⌋
  have hx : x = π * (x / π - m) + m * π := by field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · conv_lhs => rw [hx]
    rw [Real.sin_add_int_mul_pi]
  · conv_lhs => rw [hx]
    rw [Real.cos_add_int_mul_pi]
  · have h1 := Int.floor_le (x / π + 1 / 2)
    have h2 := Int.lt_floor_add_one (x / π + 1 / 2)
    rw [abs_mul, abs_of_pos Real.pi_pos, show π / 2 = π * (1 / 2) by ring]
    refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
    rw [abs_le]; constructor <;> linarith

/-! ### §4.45(i) Inverse trigonometric functions -/

/-- **DLMF 4.45.8**: `2 arctan(x/(1 + (1 + x²)^{1/2})) = arctan x` (DLMF: `0 < x < ∞`; in fact
for all real `x`). -/
theorem dlmf_4_45_8 (x : ℝ) : 2 * Real.arctan (x / (1 + √(1 + x ^ 2))) = Real.arctan x := by
  set t := Real.arctan x
  set h := t / 2
  have ht := Real.arctan_mem_Ioo x
  have hh : h ∈ Ioo (-(π / 2)) (π / 2) := ⟨by simp only [h]; linarith [ht.1, Real.pi_pos],
    by simp only [h]; linarith [ht.2, Real.pi_pos]⟩
  have hS : 0 < √(1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hc : 0 < Real.cos h := Real.cos_pos_of_mem_Ioo hh
  have hsin : Real.sin t = x / √(1 + x ^ 2) := Real.sin_arctan x
  have hcos : Real.cos t = 1 / √(1 + x ^ 2) := Real.cos_arctan x
  have key : x / (1 + √(1 + x ^ 2)) = Real.sin t / (1 + Real.cos t) := by
    rw [hsin, hcos]; field_simp; ring
  have key2 : Real.sin t / (1 + Real.cos t) = Real.tan h := by
    rw [show t = 2 * h by simp only [h]; ring, Real.sin_two_mul, Real.cos_two_mul,
      Real.tan_eq_sin_div_cos]
    field_simp; ring
  have htan : x / (1 + √(1 + x ^ 2)) = Real.tan h := key.trans key2
  rw [htan, Real.arctan_tan hh.1 hh.2]
  simp only [h]; ring

/-- The sequence of 4.45.9: `x₀ = x`, `xₙ = xₙ₋₁/(1 + (1 + xₙ₋₁²)^{1/2})`. -/
noncomputable def arctanSeq (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => arctanSeq x n / (1 + √(1 + arctanSeq x n ^ 2))

/-- **DLMF 4.45.9–4.45.10**: `arctan x = 2ⁿ arctan xₙ`, and `|xₙ| ≤ |x|/2ⁿ`, so `xₙ → 0`
("until `xₙ` is sufficiently small"). -/
theorem dlmf_4_45_9_10 (x : ℝ) :
    (∀ n : ℕ, Real.arctan x = 2 ^ n * Real.arctan (arctanSeq x n)) ∧
      (∀ n : ℕ, |arctanSeq x n| ≤ |x| / 2 ^ n) ∧ Tendsto (arctanSeq x) atTop (𝓝 0) := by
  have hstep : ∀ n, |arctanSeq x (n + 1)| ≤ |arctanSeq x n| / 2 := fun n => by
    simp only [arctanSeq]
    have hS : 1 ≤ √(1 + arctanSeq x n ^ 2) :=
      Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg (arctanSeq x n)])
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + √(1 + arctanSeq x n ^ 2))]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by linarith)
  have hb : ∀ n : ℕ, |arctanSeq x n| ≤ |x| / 2 ^ n := fun n => by
    induction n with
    | zero => simp [arctanSeq]
    | succ n ih =>
      calc |arctanSeq x (n + 1)| ≤ |arctanSeq x n| / 2 := hstep n
        _ ≤ |x| / 2 ^ n / 2 := by gcongr
        _ = |x| / 2 ^ (n + 1) := by rw [pow_succ, div_div]
  refine ⟨fun n => ?_, hb, ?_⟩
  · induction n with
    | zero => simp [arctanSeq]
    | succ n ih =>
      rw [ih, ← dlmf_4_45_8 (arctanSeq x n), pow_succ (2 : ℝ) n]
      show _ = _ * Real.arctan (arctanSeq x n / (1 + √(1 + arctanSeq x n ^ 2)))
      ring
  · have h0 : Tendsto (fun n : ℕ => |x| / 2 ^ n) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)).const_mul |x|
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      rw [one_div, inv_pow, div_eq_mul_inv]
    exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hb n) h0

/-- **DLMF 4.45.11** (compare 4.24.4): `arctan x = ½π − 1/x + 1/(3x³) − 1/(5x⁵) + ⋯`, `x > 1`. -/
theorem dlmf_4_45_11 {x : ℝ} (hx : 1 < x) :
    HasSum (fun k : ℕ => (-1) ^ (k + 1) / ((2 * k + 1) * x ^ (2 * k + 1)))
      (Real.arctan x - π / 2) := by
  have hx0 : 0 < x := by linarith
  have hz : ‖((x⁻¹ : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0)]
    exact inv_lt_one_of_one_lt₀ hx
  have h := Complex.hasSum_arctan hz
  rw [← Complex.ofReal_arctan] at h
  have h' : HasSum (fun k : ℕ => (((-1) ^ k * (x⁻¹) ^ (2 * k + 1) / (2 * k + 1) : ℝ) : ℂ))
      ((Real.arctan x⁻¹ : ℝ) : ℂ) := by
    convert h using 1; funext k; push_cast; ring
  have h'' := (Complex.hasSum_ofReal.mp h').neg
  rw [Real.arctan_inv_of_pos hx0, neg_sub] at h''
  refine h''.congr_fun fun k => ?_
  have hx1 : x ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ hx0.ne'
  have hk : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  rw [inv_pow, pow_succ]
  field_simp

/-- **§4.45(i)**, the example from the fourth row of Table 4.16.3:
`arcsin x = arctan(x(1 − x²)^{−1/2})`, `−1 < x < 1`. -/
theorem dlmf_4_45_arcsin {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Real.arcsin x = Real.arctan (x * (1 - x ^ 2) ^ (-1 / 2 : ℝ)) := by
  have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  rw [Real.arcsin_eq_arctan hx, show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hp.le,
    ← Real.sqrt_eq_rpow, div_eq_mul_inv]

/-! ### §4.45(ii) Complex variables -/

/-- **DLMF 4.45.15**: `ln z = ln|z| + i ph z`, with the principal `ph z ∈ (−π, π]`. DLMF writes
`−π ≤ ph z ≤ π`: on the negative real axis the value `ph z = −π` is the limit from below
(`dlmf_4_45_15_cut`). -/
theorem dlmf_4_45_15 (z : ℂ) :
    Complex.log z = Real.log ‖z‖ + Complex.arg z * Complex.I ∧
      -π < Complex.arg z ∧ Complex.arg z ≤ π :=
  ⟨rfl, Complex.neg_pi_lt_arg z, Complex.arg_le_pi z⟩

/-- 4.45.15 with `ph z = −π` on the negative real axis, as a limit from below. -/
theorem dlmf_4_45_15_cut {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    Tendsto Complex.log (𝓝[{w : ℂ | w.im < 0}] z) (𝓝 (Real.log ‖z‖ + (-π : ℝ) * Complex.I)) := by
  have h := Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him
  convert h using 2; push_cast; ring

/-- **DLMF 4.45.16**: `e^z = e^{ℜz}(cos(ℑz) + i sin(ℑz))`. -/
theorem dlmf_4_45_16 (z : ℂ) :
    Complex.exp z = Real.exp z.re * (Real.cos z.im + Complex.I * Real.sin z.im) := by
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  ring

/-! ### §4.45(iii) Lambert `W`-function: Newton's rule -/

/-- The Newton step for `w eʷ = x`: `N(w) = w − (w eʷ − x)/((1 + w) eʷ)`. -/
noncomputable def lambertNewton (x w : ℝ) : ℝ :=
  w - (w * Real.exp w - x) / ((1 + w) * Real.exp w)

/-- The Newton iterates `w₀, N(w₀), N(N(w₀)), …`. -/
noncomputable def lambertNewtonSeq (x w₀ : ℝ) : ℕ → ℝ
  | 0 => w₀
  | n + 1 => lambertNewton x (lambertNewtonSeq x w₀ n)

theorem convexOn_mul_exp : ConvexOn ℝ (Ici (-2)) (fun w : ℝ => w * Real.exp w) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici _)
    (show Continuous fun w : ℝ => w * Real.exp w by fun_prop).continuousOn
    (f' := fun w => (1 + w) * Real.exp w) (f'' := fun w => (2 + w) * Real.exp w)
    (fun w _ => (hasDerivAt_mul_exp w).hasDerivWithinAt) (fun w _ => ?_) (fun w hw => ?_)
  · have h := ((hasDerivAt_id w).const_add 1).mul (Real.hasDerivAt_exp w)
    exact (h.congr_deriv (by simp only [id]; ring)).hasDerivWithinAt
  · rw [interior_Ici] at hw
    have : (-2 : ℝ) < w := hw
    exact mul_nonneg (by linarith) (Real.exp_pos w).le

theorem continuousAt_lambertNewton {x w : ℝ} (hw : w ≠ -1) :
    ContinuousAt (lambertNewton x) w := by
  unfold lambertNewton
  have h : (1 + w) * Real.exp w ≠ 0 :=
    mul_ne_zero (fun h => hw (by linarith)) (Real.exp_pos w).ne'
  fun_prop (disch := exact h)

/-- A fixed point of the Newton step (away from `w = −1`) solves `w eʷ = x`. -/
theorem mul_exp_eq_of_lambertNewton_eq {x w : ℝ} (hw : w ≠ -1) (h : lambertNewton x w = w) :
    w * Real.exp w = x := by
  unfold lambertNewton at h
  have hd : (1 + w) * Real.exp w ≠ 0 :=
    mul_ne_zero (fun h => hw (by linarith)) (Real.exp_pos w).ne'
  have : (w * Real.exp w - x) / ((1 + w) * Real.exp w) = 0 := by linarith
  rcases div_eq_zero_iff.mp this with h | h
  · linarith
  · exact absurd h hd

/-- **§4.45(iii)**, `W₀` by Newton's rule: for `x > −1/e` and any start `w₀ ≥ W₀(x)`, the Newton
iterates decrease monotonically to `W₀(x)` (`w eʷ` is convex and increasing on `[−1, ∞)`). -/
theorem dlmf_4_45_iii_W0 {x w₀ : ℝ} (hx : -Real.exp (-1) < x) (hw : lambertW0 x ≤ w₀) :
    Antitone (lambertNewtonSeq x w₀) ∧ (∀ n, lambertW0 x ≤ lambertNewtonSeq x w₀ n) ∧
      Tendsto (lambertNewtonSeq x w₀) atTop (𝓝 (lambertW0 x)) := by
  set W := lambertW0 x
  have hW1 : -1 < W := lambertW0_gt hx
  have hWx : W * Real.exp W = x := (lambertW0_spec hx.le).2
  -- one step: `W ≤ w ⇒ W ≤ N w ≤ w`
  have step : ∀ w, W ≤ w → W ≤ lambertNewton x w ∧ lambertNewton x w ≤ w := fun w hw => by
    have hw1 : -1 < w := by linarith
    have hd : 0 < (1 + w) * Real.exp w := mul_pos (by linarith) (Real.exp_pos w)
    have hf : 0 ≤ w * Real.exp w - x := by
      rw [← hWx]; linarith [strictMonoOn_mul_exp.monotoneOn (mem_Ici.mpr hW1.le)
        (mem_Ici.mpr hw1.le) hw]
    refine ⟨?_, ?_⟩
    · rcases hw.eq_or_lt with h | h
      · rw [← h]; unfold lambertNewton; rw [hWx]; simp
      · have hs := convexOn_mul_exp.slope_le_of_hasDerivAt (mem_Ici.mpr (by linarith))
          (mem_Ici.mpr (by linarith)) h (hasDerivAt_mul_exp w)
        rw [slope_def_field, hWx, div_le_iff₀ (by linarith)] at hs
        unfold lambertNewton
        rw [le_sub_comm, div_le_iff₀ hd]
        linarith
    · unfold lambertNewton
      have : 0 ≤ (w * Real.exp w - x) / ((1 + w) * Real.exp w) := div_nonneg hf hd.le
      linarith
  have hlow : ∀ n, W ≤ lambertNewtonSeq x w₀ n := fun n => by
    induction n with
    | zero => exact hw
    | succ n ih => exact (step _ ih).1
  have hanti : Antitone (lambertNewtonSeq x w₀) :=
    antitone_nat_of_succ_le fun n => (step _ (hlow n)).2
  refine ⟨hanti, hlow, ?_⟩
  obtain ⟨L, hL⟩ : ∃ L, Tendsto (lambertNewtonSeq x w₀) atTop (𝓝 L) :=
    ⟨_, tendsto_atTop_ciInf hanti ⟨W, fun _ ⟨n, hn⟩ => hn ▸ hlow n⟩⟩
  have hLW : W ≤ L := ge_of_tendsto' hL hlow
  have hL1 : L ≠ -1 := by linarith
  have hfix : lambertNewton x L = L := by
    have h1 : Tendsto (fun n => lambertNewtonSeq x w₀ (n + 1)) atTop (𝓝 L) :=
      hL.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => lambertNewton x (lambertNewtonSeq x w₀ n)) atTop
        (𝓝 (lambertNewton x L)) := (continuousAt_lambertNewton hL1).tendsto.comp hL
    exact tendsto_nhds_unique h2 h1
  have hLx := mul_exp_eq_of_lambertNewton_eq hL1 hfix
  have hWL : W = L := by
    show lambertW0 x = L
    rw [← hLx]; exact dlmf_4_13_3_1 (by linarith)
  rw [hWL]; exact hL

/-- **§4.45(iii)**, "similarly for `W₋₁`": for `−1/e < x ≤ −2e⁻²` (so that `W₋₁(x) ∈ [−2, −1)`,
where `w eʷ` is convex and decreasing) and any start `−2 ≤ w₀ ≤ W₋₁(x)`, the Newton iterates
increase monotonically to `W₋₁(x)`. -/
theorem dlmf_4_45_iii_Wm1 {x w₀ : ℝ} (hx : -Real.exp (-1) < x) (hx2 : x ≤ -2 * Real.exp (-2))
    (hw2 : -2 ≤ w₀) (hw : w₀ ≤ lambertWm1 x) :
    Monotone (lambertNewtonSeq x w₀) ∧ (∀ n, lambertNewtonSeq x w₀ n ≤ lambertWm1 x) ∧
      Tendsto (lambertNewtonSeq x w₀) atTop (𝓝 (lambertWm1 x)) := by
  set W := lambertWm1 x
  have hx0 : x < 0 := by nlinarith [Real.exp_pos (-2)]
  obtain ⟨hW1', hWx⟩ := lambertWm1_spec hx.le hx0
  have hW1 : W < -1 := by
    rcases hW1'.lt_or_eq with h | h
    · exact h
    · rw [h] at hWx; linarith [neg_one_mul_exp]
  have hW2 : -2 ≤ W := by
    by_contra h
    push Not at h
    have := strictAntiOn_mul_exp (a := W) (b := -2) (mem_Iic.mpr (by linarith))
      (mem_Iic.mpr (by norm_num)) h
    simp only at this
    have hWx' : W * Real.exp W = x := hWx
    linarith
  -- one step: `−2 ≤ w ≤ W ⇒ w ≤ N w ≤ W`
  have step : ∀ w, -2 ≤ w → w ≤ W → w ≤ lambertNewton x w ∧ lambertNewton x w ≤ W :=
    fun w hw2 hw => by
      have hd : (1 + w) * Real.exp w < 0 := mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos w)
      have hf : 0 ≤ w * Real.exp w - x := by
        rw [← hWx]; linarith [strictAntiOn_mul_exp.antitoneOn (mem_Iic.mpr (by linarith))
          (mem_Iic.mpr hW1.le) hw]
      refine ⟨?_, ?_⟩
      · unfold lambertNewton
        have : (w * Real.exp w - x) / ((1 + w) * Real.exp w) ≤ 0 :=
          div_nonpos_of_nonneg_of_nonpos hf hd.le
        linarith
      · rcases hw.eq_or_lt with h | h
        · rw [h]; unfold lambertNewton; rw [hWx]; simp
        · have hs := convexOn_mul_exp.le_slope_of_hasDerivAt (mem_Ici.mpr hw2)
            (mem_Ici.mpr hW2) h (hasDerivAt_mul_exp w)
          rw [slope_def_field, hWx, le_div_iff₀ (by linarith)] at hs
          unfold lambertNewton
          rw [sub_le_comm, le_div_iff_of_neg hd]
          linarith
  have hbd : ∀ n, -2 ≤ lambertNewtonSeq x w₀ n ∧ lambertNewtonSeq x w₀ n ≤ W := fun n => by
    induction n with
    | zero => exact ⟨hw2, hw⟩
    | succ n ih =>
      obtain ⟨h1, h2⟩ := step _ ih.1 ih.2
      show -2 ≤ lambertNewton x (lambertNewtonSeq x w₀ n) ∧ lambertNewton x _ ≤ W
      exact ⟨by linarith [ih.1], h2⟩
  have hmono : Monotone (lambertNewtonSeq x w₀) :=
    monotone_nat_of_le_succ fun n => (step _ (hbd n).1 (hbd n).2).1
  refine ⟨hmono, fun n => (hbd n).2, ?_⟩
  obtain ⟨L, hL⟩ : ∃ L, Tendsto (lambertNewtonSeq x w₀) atTop (𝓝 L) :=
    ⟨_, tendsto_atTop_ciSup hmono ⟨W, fun _ ⟨n, hn⟩ => hn ▸ (hbd n).2⟩⟩
  have hLW : L ≤ W := le_of_tendsto' hL fun n => (hbd n).2
  have hL1 : L ≠ -1 := by linarith
  have hfix : lambertNewton x L = L := by
    have h1 : Tendsto (fun n => lambertNewtonSeq x w₀ (n + 1)) atTop (𝓝 L) :=
      hL.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => lambertNewton x (lambertNewtonSeq x w₀ n)) atTop
        (𝓝 (lambertNewton x L)) := (continuousAt_lambertNewton hL1).tendsto.comp hL
    exact tendsto_nhds_unique h2 h1
  have hLx := mul_exp_eq_of_lambertNewton_eq hL1 hfix
  have hWL : W = L := by
    show lambertWm1 x = L
    rw [← hLx]; exact dlmf_4_13_3_2 (by linarith)
  rw [hWL]; exact hL

end Azurite.DLMF
