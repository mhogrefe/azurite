/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.AGMLog
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Brent–Zimmermann §4.8.2 (continued): the error bound (4.73)

The rigorous error bound of §4.8.2: for `0 < k ≤ 1`,

  `|(π/2)/AGM(1, k) − ln(4/k)| ≤ 4k² (8 − ln k)`,                                        (4.73)

and the asymptotic (4.71) `(π/2)/AGM(1, k) = ln(4/k)(1 + O(k²))`.

The proof is elementary and goes through Gauss's theorem (4.68) in the form
`(π/2)/AGM(1, k) = J(1, k) = ∫_0^∞ dt/√((1 + t²)(k² + t²))` (`agmIntegral_eq_pi_div_AGM`).
Split the integral at `t = 1`:

* on `[1, ∞)`, `1/√((1+t²)(k²+t²)) = 1/(t√(1+t²)) − r₁(t)` with `0 ≤ r₁(t) ≤ k²/(2t³)`, and
  `∫_1^∞ dt/(t√(1+t²)) = arsinh 1 = ln(1 + √2)` (`integral_inv_mul_sqrt_Ioi`);
* on `[0, 1]`, `1/√((1+t²)(k²+t²)) = 1/√(k²+t²) − φ(t) + r₂(t)` where
  `φ(t) = t/(√(1+t²)(1 + √(1+t²))) = (1 − 1/√(1+t²))/t` (`agmLogPhi`), with
  `∫_0^1 dt/√(k²+t²) = arsinh(1/k)` (`integral_inv_sqrt_sq_add`), `∫_0^1 φ = ln(1+√2) − ln 2`
  (`integral_agmLogPhi`), and `r₂(t) = (1 − 1/√(1+t²))(1/t − 1/√(k²+t²)) ≥ 0` (`agmLogRem`),
  bounded by `t/2` on `[0, k]` and by `k²/(4t)` on `[k, 1]`, so `0 ≤ ∫_0^1 r₂ ≤ (k²/4)(1 − ln k)`.

Adding up, `(π/2)/AGM(1, k) = arsinh(1/k) + ln 2 − R₁ + R₂ = ln(4/k) + R₀ − R₁ + R₂` with
`R₀ = ln((1 + √(1+k²))/2) ∈ [0, k²/4]`, `R₁ ∈ [0, k²/4]`, `R₂ ∈ [0, (k²/4)(1 − ln k)]`, which gives

  `|(π/2)/AGM(1, k) − ln(4/k)| ≤ (k²/4)(2 − ln k)`      (`abs_pi_div_AGM_sub_log_le`),

sixteen times sharper than (4.73) (`abs_pi_div_AGM_sub_log_le_bz`).  For `agmLog` this reads
`|agmLog x − ln x| ≤ (4/x²)(2 + ln(x/4))` for `x ≥ 4` (`abs_agmLog_sub_log_le`), and (4.71) holds
in the explicit form `(π/2)/AGM(1, k) = ln(4/k)(1 + ε)` with `|ε| ≤ k²/2` (`pi_div_AGM_eq_log_mul`).
-/

namespace Azurite

namespace BZ

open Real Set MeasureTheory

variable {k t : ℝ}

/-! ### Pointwise estimates -/

theorem one_le_sqrt_one_add_sq (t : ℝ) : 1 ≤ Real.sqrt (1 + t ^ 2) := by
  rw [Real.le_sqrt zero_le_one (by positivity)]
  nlinarith [sq_nonneg t]

/-- `√(1 + t²) ≤ 1 + t²/2`. -/
theorem sqrt_one_add_sq_le (t : ℝ) : Real.sqrt (1 + t ^ 2) ≤ 1 + t ^ 2 / 2 := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_nonneg (t ^ 2)]

/-- `1 − 1/√(1 + t²) ≤ t²/2`. -/
theorem one_sub_inv_sqrt_le (t : ℝ) : 1 - (Real.sqrt (1 + t ^ 2))⁻¹ ≤ t ^ 2 / 2 := by
  set s := Real.sqrt (1 + t ^ 2) with hs_def
  have hs2 : s ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  have h1 : 1 ≤ s := one_le_sqrt_one_add_sq t
  have hs : 0 < s := by linarith
  have ht2 : t ^ 2 = s ^ 2 - 1 := by linarith
  rw [sub_le_iff_le_add, inv_eq_one_div, div_add_div _ _ two_ne_zero hs.ne',
    le_div_iff₀ (by positivity), ht2]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h1))
    (by linarith : (0 : ℝ) ≤ s + 2)]

theorem one_sub_inv_sqrt_nonneg (t : ℝ) : 0 ≤ 1 - (Real.sqrt (1 + t ^ 2))⁻¹ :=
  sub_nonneg.mpr (inv_le_one_of_one_le₀ (one_le_sqrt_one_add_sq t))

/-- `t ≤ √(k² + t²)`. -/
theorem le_sqrt_sq_add_sq (ht : 0 ≤ t) : t ≤ Real.sqrt (k ^ 2 + t ^ 2) := by
  rw [Real.le_sqrt ht (by positivity)]
  nlinarith

theorem inv_sub_inv_sqrt_nonneg (ht : 0 < t) :
    0 ≤ t⁻¹ - (Real.sqrt (k ^ 2 + t ^ 2))⁻¹ :=
  sub_nonneg.mpr (inv_anti₀ ht (le_sqrt_sq_add_sq ht.le))

/-- `1/t − 1/√(k² + t²) ≤ k²/(2t³)` for `t > 0`. -/
theorem inv_sub_inv_sqrt_le (hk : 0 < k) (ht : 0 < t) :
    t⁻¹ - (Real.sqrt (k ^ 2 + t ^ 2))⁻¹ ≤ k ^ 2 / (2 * t ^ 3) := by
  set u := Real.sqrt (k ^ 2 + t ^ 2) with hu_def
  have hu2 : u ^ 2 = k ^ 2 + t ^ 2 := Real.sq_sqrt (by positivity)
  have htu : t ≤ u := le_sqrt_sq_add_sq ht.le
  have hu : 0 < u := lt_of_lt_of_le ht htu
  have hk2 : k ^ 2 = u ^ 2 - t ^ 2 := by linarith
  rw [inv_eq_one_div, inv_eq_one_div, div_sub_div _ _ ht.ne' hu.ne',
    div_le_div_iff₀ (by positivity : (0 : ℝ) < t * u) (by positivity : (0 : ℝ) < 2 * t ^ 3), hk2]
  nlinarith [mul_nonneg (mul_nonneg (mul_self_nonneg (u - t)) ht.le)
    (by linarith : (0 : ℝ) ≤ u + 2 * t)]

/-- The kernel `1/√((t² + 1)(t² + k²))` factored. -/
theorem agmKernel_one_eq (k t : ℝ) :
    agmKernel 1 k t = (Real.sqrt (1 + t ^ 2))⁻¹ * (Real.sqrt (k ^ 2 + t ^ 2))⁻¹ := by
  unfold agmKernel
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ t ^ 2 + 1 ^ 2) (t ^ 2 + k ^ 2), mul_inv, one_pow,
    add_comm (t ^ 2) 1, add_comm (t ^ 2) (k ^ 2)]

theorem continuous_inv_sqrt_sq_add (hk : 0 < k) :
    Continuous fun t : ℝ => (Real.sqrt (k ^ 2 + t ^ 2))⁻¹ :=
  (continuous_const.add (continuous_id.pow 2)).sqrt.inv₀ fun t =>
    (Real.sqrt_pos.mpr (by show (0 : ℝ) < k ^ 2 + t ^ 2; positivity)).ne'

/-! ### The auxiliary function `φ` and the remainder `r₂` on `[0, 1]` -/

/-- `φ(t) = t/(√(1+t²)(1 + √(1+t²)))`, which equals `(1 − 1/√(1+t²))/t` for `t ≠ 0`; its
antiderivative is `ln(1 + √(1+t²))`. -/
noncomputable def agmLogPhi (t : ℝ) : ℝ :=
  t / (Real.sqrt (1 + t ^ 2) * (1 + Real.sqrt (1 + t ^ 2)))

theorem continuous_agmLogPhi : Continuous agmLogPhi := by
  have hs : Continuous fun t : ℝ => Real.sqrt (1 + t ^ 2) :=
    (continuous_const.add (continuous_id.pow 2)).sqrt
  exact continuous_id.div (hs.mul (continuous_const.add hs)) fun t => by positivity

theorem agmLogPhi_eq (ht : 0 < t) :
    agmLogPhi t = (1 - (Real.sqrt (1 + t ^ 2))⁻¹) * t⁻¹ := by
  set s := Real.sqrt (1 + t ^ 2) with hs_def
  have hs2 : s ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  rw [agmLogPhi, ← hs_def, div_eq_iff (by positivity)]
  field_simp
  linear_combination -hs2

/-- The remainder on `[0, 1]`: `r₂(t) = 1/√((1+t²)(k²+t²)) − 1/√(k²+t²) + φ(t)`. -/
noncomputable def agmLogRem (k t : ℝ) : ℝ :=
  agmKernel 1 k t - (Real.sqrt (k ^ 2 + t ^ 2))⁻¹ + agmLogPhi t

theorem continuous_agmLogRem (hk : 0 < k) : Continuous (agmLogRem k) :=
  ((continuous_agmKernel one_pos hk).sub (continuous_inv_sqrt_sq_add hk)).add continuous_agmLogPhi

theorem agmLogRem_eq (ht : 0 < t) :
    agmLogRem k t = (1 - (Real.sqrt (1 + t ^ 2))⁻¹) * (t⁻¹ - (Real.sqrt (k ^ 2 + t ^ 2))⁻¹) := by
  rw [agmLogRem, agmKernel_one_eq, agmLogPhi_eq ht]
  ring

theorem agmLogRem_zero (k : ℝ) : agmLogRem k 0 = 0 := by
  simp [agmLogRem, agmKernel, agmLogPhi]

theorem agmLogRem_nonneg (ht : 0 ≤ t) : 0 ≤ agmLogRem k t := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [agmLogRem_zero]
  · rw [agmLogRem_eq ht]
    exact mul_nonneg (one_sub_inv_sqrt_nonneg t) (inv_sub_inv_sqrt_nonneg ht)

/-- `r₂(t) ≤ t/2`. -/
theorem agmLogRem_le_half (ht : 0 ≤ t) : agmLogRem k t ≤ t / 2 := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [agmLogRem_zero]; simp
  · rw [agmLogRem_eq ht]
    have h2 : t⁻¹ - (Real.sqrt (k ^ 2 + t ^ 2))⁻¹ ≤ t⁻¹ := by
      linarith [inv_nonneg.mpr (Real.sqrt_nonneg (k ^ 2 + t ^ 2))]
    calc _ ≤ t ^ 2 / 2 * t⁻¹ :=
          mul_le_mul (one_sub_inv_sqrt_le t) h2 (inv_sub_inv_sqrt_nonneg ht) (by positivity)
      _ = t / 2 := by field_simp

/-- `r₂(t) ≤ k²/(4t)` for `t > 0`. -/
theorem agmLogRem_le_div (hk : 0 < k) (ht : 0 < t) : agmLogRem k t ≤ k ^ 2 / (4 * t) := by
  rw [agmLogRem_eq ht]
  calc _ ≤ t ^ 2 / 2 * (k ^ 2 / (2 * t ^ 3)) :=
        mul_le_mul (one_sub_inv_sqrt_le t) (inv_sub_inv_sqrt_le hk ht)
          (inv_sub_inv_sqrt_nonneg ht) (by positivity)
    _ = k ^ 2 / (4 * t) := by field_simp; ring

/-! ### The exact integrals -/

/-- `∫_0^1 dt/√(k² + t²) = arsinh(1/k)`. -/
theorem integral_inv_sqrt_sq_add (hk : 0 < k) :
    ∫ t in (0 : ℝ)..1, (Real.sqrt (k ^ 2 + t ^ 2))⁻¹ = arsinh (1 / k) := by
  have hk0 : k ≠ 0 := hk.ne'
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun y => arsinh (y / k)) ((Real.sqrt (k ^ 2 + x ^ 2))⁻¹) x := by
    intro x _
    refine ((hasDerivAt_id' (x := x)).div_const k).arsinh.congr_deriv ?_
    have : Real.sqrt (k ^ 2 + x ^ 2) = k * Real.sqrt (1 + (x / k) ^ 2) := by
      rw [show k ^ 2 + x ^ 2 = k ^ 2 * (1 + (x / k) ^ 2) by field_simp,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ k ^ 2) (1 + (x / k) ^ 2), Real.sqrt_sq hk.le]
    rw [this, smul_eq_mul, mul_inv]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_inv_sqrt_sq_add hk).intervalIntegrable 0 1)]
  simp

/-- `∫_0^1 φ = ln(1 + √2) − ln 2`. -/
theorem integral_agmLogPhi :
    ∫ t in (0 : ℝ)..1, agmLogPhi t = Real.log (1 + Real.sqrt 2) - Real.log 2 := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun y => Real.log (1 + Real.sqrt (1 + y ^ 2))) (agmLogPhi x) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).const_add 1
    have hs : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have h2 := (h1.sqrt (by positivity)).const_add 1
    refine (h2.log (by positivity)).congr_deriv ?_
    unfold agmLogPhi
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (continuous_agmLogPhi.intervalIntegrable 0 1)]
  norm_num

theorem hasDerivAt_neg_arsinh_inv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -arsinh y⁻¹) ((x * Real.sqrt (1 + x ^ 2))⁻¹) x := by
  have hx0 : x ≠ 0 := hx.ne'
  refine ((hasDerivAt_inv hx0).arsinh.neg).congr_deriv ?_
  have : Real.sqrt (1 + (x⁻¹) ^ 2) = Real.sqrt (1 + x ^ 2) / x := by
    rw [show 1 + (x⁻¹) ^ 2 = (1 + x ^ 2) / x ^ 2 by field_simp; ring,
      Real.sqrt_div (by positivity : (0 : ℝ) ≤ 1 + x ^ 2) (x ^ 2), Real.sqrt_sq hx.le]
  have hs : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [this, smul_eq_mul]
  field_simp

theorem tendsto_neg_arsinh_inv :
    Filter.Tendsto (fun y : ℝ => -arsinh y⁻¹) Filter.atTop (nhds 0) := by
  simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).arsinh.neg

theorem integrableOn_inv_mul_sqrt_Ioi :
    IntegrableOn (fun t : ℝ => (t * Real.sqrt (1 + t ^ 2))⁻¹) (Ioi 1) :=
  integrableOn_Ioi_deriv_of_nonneg' (g := fun y : ℝ => -arsinh y⁻¹) (l := 0)
    (fun x hx => hasDerivAt_neg_arsinh_inv (by linarith [mem_Ici.mp hx]))
    (fun x hx => by
      have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
      positivity)
    tendsto_neg_arsinh_inv

/-- `∫_1^∞ dt/(t√(1 + t²)) = arsinh 1 = ln(1 + √2)`. -/
theorem integral_inv_mul_sqrt_Ioi :
    ∫ t in Ioi (1 : ℝ), (t * Real.sqrt (1 + t ^ 2))⁻¹ = arsinh 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 1) (g := fun y : ℝ => -arsinh y⁻¹)
    (g' := fun t => (t * Real.sqrt (1 + t ^ 2))⁻¹) (l := 0)
    (fun x hx => hasDerivAt_neg_arsinh_inv (by linarith [mem_Ici.mp hx]))
    (fun x hx => by
      have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
      positivity)
    tendsto_neg_arsinh_inv
  simpa using h

/-! ### The two remainders -/

/-- On `[1, ∞)`: `∫_1^∞ dt/√((1+t²)(k²+t²)) = arsinh 1 − R₁` with `0 ≤ R₁ ≤ k²/4`. -/
theorem integral_agmKernel_Ioi (hk : 0 < k) :
    ∃ R₁, 0 ≤ R₁ ∧ R₁ ≤ k ^ 2 / 4 ∧ ∫ t in Ioi (1 : ℝ), agmKernel 1 k t = arsinh 1 - R₁ := by
  have hint : IntegrableOn (agmKernel 1 k) (Ioi 1) := (integrable_agmKernel one_pos hk).integrableOn
  have hint1 := integrableOn_inv_mul_sqrt_Ioi
  refine ⟨∫ t in Ioi (1 : ℝ), ((t * Real.sqrt (1 + t ^ 2))⁻¹ - agmKernel 1 k t), ?_, ?_, ?_⟩
  · refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := by linarith [mem_Ioi.mp ht]
    rw [mul_comm t, mul_inv, agmKernel_one_eq, sub_nonneg]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ ht0 (le_sqrt_sq_add_sq ht0.le))
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
  · have hbound : ∀ t ∈ Ioi (1 : ℝ),
        (t * Real.sqrt (1 + t ^ 2))⁻¹ - agmKernel 1 k t ≤ k ^ 2 / 2 * t ^ (-3 : ℝ) := by
      intro t ht
      have ht0 : 0 < t := by linarith [mem_Ioi.mp ht]
      rw [mul_comm t, mul_inv, agmKernel_one_eq, ← mul_sub, Real.rpow_neg ht0.le,
        show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc (Real.sqrt (1 + t ^ 2))⁻¹ * (t⁻¹ - (Real.sqrt (k ^ 2 + t ^ 2))⁻¹)
          ≤ 1 * (k ^ 2 / (2 * t ^ 3)) :=
            mul_le_mul (inv_le_one_of_one_le₀ (one_le_sqrt_one_add_sq t))
              (inv_sub_inv_sqrt_le hk ht0) (inv_sub_inv_sqrt_nonneg ht0) zero_le_one
        _ = k ^ 2 / 2 * (t ^ 3)⁻¹ := by ring
    have hint2 : IntegrableOn (fun t : ℝ => k ^ 2 / 2 * t ^ (-3 : ℝ)) (Ioi 1) :=
      Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos) _
    calc _ ≤ ∫ t in Ioi (1 : ℝ), k ^ 2 / 2 * t ^ (-3 : ℝ) :=
          setIntegral_mono_on (hint1.sub hint) hint2 measurableSet_Ioi hbound
      _ = k ^ 2 / 4 := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
          norm_num
          ring
  · rw [integral_sub hint1 hint, integral_inv_mul_sqrt_Ioi]
    ring

/-- On `[0, 1]`: `∫_0^1 dt/√((1+t²)(k²+t²)) = arsinh(1/k) − (ln(1+√2) − ln 2) + R₂` with
`0 ≤ R₂ ≤ (k²/4)(1 − ln k)`. -/
theorem integral_agmKernel_Ioc (hk : 0 < k) (hk1 : k ≤ 1) :
    ∃ R₂, 0 ≤ R₂ ∧ R₂ ≤ k ^ 2 / 4 * (1 - Real.log k) ∧
      ∫ t in (0 : ℝ)..1, agmKernel 1 k t
        = arsinh (1 / k) - (Real.log (1 + Real.sqrt 2) - Real.log 2) + R₂ := by
  have hK : IntervalIntegrable (agmKernel 1 k) volume 0 1 :=
    (continuous_agmKernel one_pos hk).intervalIntegrable 0 1
  have hU : IntervalIntegrable (fun t : ℝ => (Real.sqrt (k ^ 2 + t ^ 2))⁻¹) volume 0 1 :=
    (continuous_inv_sqrt_sq_add hk).intervalIntegrable 0 1
  have hP : IntervalIntegrable agmLogPhi volume 0 1 := continuous_agmLogPhi.intervalIntegrable 0 1
  have hR : Continuous (agmLogRem k) := continuous_agmLogRem hk
  refine ⟨∫ t in (0 : ℝ)..1, agmLogRem k t, ?_, ?_, ?_⟩
  · exact intervalIntegral.integral_nonneg zero_le_one fun t ht => agmLogRem_nonneg ht.1
  · rw [← intervalIntegral.integral_add_adjacent_intervals (hR.intervalIntegrable 0 k)
      (hR.intervalIntegrable k 1)]
    have h1 : ∫ t in (0 : ℝ)..k, agmLogRem k t ≤ k ^ 2 / 4 := by
      calc _ ≤ ∫ t in (0 : ℝ)..k, t / 2 :=
            intervalIntegral.integral_mono_on hk.le (hR.intervalIntegrable 0 k)
              ((continuous_id'.div_const 2).intervalIntegrable 0 k)
              fun t ht => agmLogRem_le_half ht.1
        _ = k ^ 2 / 4 := by rw [intervalIntegral.integral_div, integral_id]; ring
    have h2 : ∫ t in k..1, agmLogRem k t ≤ k ^ 2 / 4 * (-Real.log k) := by
      have hc : ContinuousOn (fun t : ℝ => k ^ 2 / 4 * t⁻¹) (uIcc k 1) := by
        refine continuousOn_const.mul (continuousOn_inv₀.mono ?_)
        intro t ht
        rw [uIcc_of_le hk1] at ht
        exact mem_compl_singleton_iff.mpr (ne_of_gt (lt_of_lt_of_le hk ht.1))
      calc _ ≤ ∫ t in k..1, k ^ 2 / 4 * t⁻¹ :=
            intervalIntegral.integral_mono_on hk1 (hR.intervalIntegrable k 1) hc.intervalIntegrable
              fun t ht => (agmLogRem_le_div hk (lt_of_lt_of_le hk ht.1)).trans_eq (by ring)
        _ = k ^ 2 / 4 * (-Real.log k) := by
            rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hk one_pos, one_div,
              Real.log_inv]
    linarith
  · simp only [agmLogRem]
    rw [intervalIntegral.integral_add
      (f := fun t => agmKernel 1 k t - (Real.sqrt (k ^ 2 + t ^ 2))⁻¹) (g := agmLogPhi)
      (hK.sub hU) hP,
      intervalIntegral.integral_sub (f := agmKernel 1 k)
      (g := fun t => (Real.sqrt (k ^ 2 + t ^ 2))⁻¹) hK hU,
      integral_inv_sqrt_sq_add hk, integral_agmLogPhi]
    ring

/-! ### The bound (4.73) -/

/-- The error of the AGM approximation to the logarithm: for `0 < k ≤ 1`,
`|(π/2)/AGM(1, k) − ln(4/k)| ≤ (k²/4)(2 − ln k)`. -/
theorem abs_pi_div_AGM_sub_log_le (hk : 0 < k) (hk1 : k ≤ 1) :
    |(π / 2) / AGM 1 k - Real.log (4 / k)| ≤ k ^ 2 / 4 * (2 - Real.log k) := by
  obtain ⟨R₁, hR₁0, hR₁, h1⟩ := integral_agmKernel_Ioi hk
  obtain ⟨R₂, hR₂0, hR₂, h2⟩ := integral_agmKernel_Ioc hk hk1
  have hsplit : (π / 2) / AGM 1 k
      = (∫ t in (0 : ℝ)..1, agmKernel 1 k t) + ∫ t in Ioi (1 : ℝ), agmKernel 1 k t := by
    rw [div_div, ← agmIntegral_eq_pi_div_AGM one_pos hk, agmIntegral,
      ← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1),
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (integrable_agmKernel one_pos hk).integrableOn
        (integrable_agmKernel one_pos hk).integrableOn,
      intervalIntegral.integral_of_le zero_le_one]
  have hmain : arsinh (1 / k) + Real.log 2 - Real.log (4 / k)
      = Real.log ((1 + Real.sqrt (1 + k ^ 2)) / 2) := by
    have hk0 : k ≠ 0 := hk.ne'
    have hs : Real.sqrt (1 + (1 / k) ^ 2) = Real.sqrt (1 + k ^ 2) / k := by
      rw [show 1 + (1 / k) ^ 2 = (1 + k ^ 2) / k ^ 2 by field_simp; ring,
        Real.sqrt_div (by positivity : (0 : ℝ) ≤ 1 + k ^ 2) (k ^ 2), Real.sqrt_sq hk.le]
    have hpos : 0 < 1 + Real.sqrt (1 + k ^ 2) := by positivity
    rw [Real.arsinh, hs,
      show 1 / k + Real.sqrt (1 + k ^ 2) / k = (1 + Real.sqrt (1 + k ^ 2)) / k by ring,
      Real.log_div hpos.ne' hk0, Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hk0,
      Real.log_div hpos.ne' two_ne_zero, show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul two_ne_zero two_ne_zero]
    ring
  have hR₀0 : 0 ≤ Real.log ((1 + Real.sqrt (1 + k ^ 2)) / 2) :=
    Real.log_nonneg (by linarith [one_le_sqrt_one_add_sq k])
  have hR₀ : Real.log ((1 + Real.sqrt (1 + k ^ 2)) / 2) ≤ k ^ 2 / 4 := by
    have := Real.log_le_sub_one_of_pos (x := (1 + Real.sqrt (1 + k ^ 2)) / 2) (by positivity)
    linarith [sqrt_one_add_sq_le k]
  have harsinh1 : arsinh 1 = Real.log (1 + Real.sqrt 2) := by rw [Real.arsinh]; norm_num
  have hlog : Real.log k ≤ 0 := Real.log_nonpos hk.le hk1
  have hk2log : 0 ≤ k ^ 2 / 4 * (-Real.log k) := mul_nonneg (by positivity) (by linarith)
  have hk2 : 0 ≤ k ^ 2 := sq_nonneg k
  rw [hsplit, h1, h2, harsinh1, abs_le]
  constructor <;> linarith

/-- (4.73) in the textbook's form: `|(π/2)/AGM(1, k) − ln(4/k)| ≤ 4k² (8 − ln k)` on `(0, 1]`. -/
theorem abs_pi_div_AGM_sub_log_le_bz (hk : 0 < k) (hk1 : k ≤ 1) :
    |(π / 2) / AGM 1 k - Real.log (4 / k)| ≤ 4 * k ^ 2 * (8 - Real.log k) := by
  refine (abs_pi_div_AGM_sub_log_le hk hk1).trans ?_
  have hlog : Real.log k ≤ 0 := Real.log_nonpos hk.le hk1
  have := mul_nonneg (sq_nonneg k) (neg_nonneg.mpr hlog)
  nlinarith [sq_nonneg k]

/-- The error of `agmLog`: `|agmLog x − ln x| ≤ (4/x²)(2 + ln(x/4))` for `x ≥ 4`. -/
theorem abs_agmLog_sub_log_le {x : ℝ} (hx : 4 ≤ x) :
    |agmLog x - Real.log x| ≤ 4 / x ^ 2 * (2 + Real.log (x / 4)) := by
  have hx0 : 0 < x := by linarith
  have hk : 0 < 4 / x := by positivity
  have hk1 : 4 / x ≤ 1 := by rw [div_le_one hx0]; exact hx
  have h := abs_pi_div_AGM_sub_log_le hk hk1
  rw [show (4 : ℝ) / (4 / x) = x by field_simp, Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hx0.ne']
    at h
  rw [agmLog, Real.log_div hx0.ne' (by norm_num : (4 : ℝ) ≠ 0)]
  convert h using 1
  ring

/-- (4.71) in explicit form: `(π/2)/AGM(1, k) = ln(4/k)(1 + ε)` with `|ε| ≤ k²/2`, for
`0 < k ≤ 1`. -/
theorem pi_div_AGM_eq_log_mul (hk : 0 < k) (hk1 : k ≤ 1) :
    ∃ ε : ℝ, |ε| ≤ k ^ 2 / 2 ∧ (π / 2) / AGM 1 k = Real.log (4 / k) * (1 + ε) := by
  have hL : 0 < Real.log (4 / k) := Real.log_pos (by rw [lt_div_iff₀ hk]; linarith)
  have hlog4 : 1 ≤ Real.log 4 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    exact Real.exp_one_lt_three.le.trans (by norm_num)
  have hlogk : Real.log k ≤ 0 := Real.log_nonpos hk.le hk1
  have hdiv : Real.log (4 / k) = Real.log 4 - Real.log k :=
    Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hk.ne'
  refine ⟨((π / 2) / AGM 1 k - Real.log (4 / k)) / Real.log (4 / k), ?_, ?_⟩
  · rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]
    refine (abs_pi_div_AGM_sub_log_le hk hk1).trans ?_
    rw [hdiv]
    nlinarith [mul_nonneg (sq_nonneg k) (neg_nonneg.mpr hlogk),
      mul_nonneg (sq_nonneg k) (sub_nonneg.mpr hlog4)]
  · field_simp
    ring

/-- (4.70) to first order: with `k' = √(1 − k²)`, `|K(k') − ln(4/k)| ≤ (k²/4)(2 − ln k)` for
`0 < k ≤ 1`, i.e. `K'(k) = ln(4/k) + O(k² ln(1/k))` as `k → 0` (Gauss's theorem turns
`abs_pi_div_AGM_sub_log_le` into a statement about `K`). -/
theorem abs_ellipticK_sqrt_sub_log_le (hk : 0 < k) (hk1 : k ≤ 1) :
    |ellipticK (Real.sqrt (1 - k ^ 2)) - Real.log (4 / k)| ≤ k ^ 2 / 4 * (2 - Real.log k) := by
  have h : (π / 2) / AGM 1 k = ellipticK (Real.sqrt (1 - k ^ 2)) := by
    rw [div_eq_mul_one_div, one_div_AGM_one hk hk1]
    field_simp
  rw [← h]
  exact abs_pi_div_AGM_sub_log_le hk hk1

end BZ

end Azurite
