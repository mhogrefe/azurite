/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.AGMLogBound

/-!
# Brent–Zimmermann §4.8.2 (continued): the Legendre relation (4.72)

  `E(k) K'(k) + E'(k) K(k) − K(k) K'(k) = π/2`,   `k' = √(1 − k²)`, `0 < k < 1`,     (4.72)

the identity behind the Brent–Salamin algorithm for `π`.  The proof is the classical one:

* differentiation under the integral sign (`hasDerivAt_ellipticK`, `hasDerivAt_ellipticE`, via
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` on a small interval of
  moduli, where the derivatives of the integrands are uniformly bounded);
* the two classical identities `k E'(k) = E − K` (`mul_ellipticE_deriv`, pointwise) and
  `k k'² K'(k) = E − k'² K` (`ellipticK_deriv_identity`, by integrating the derivative of
  `sin θ cos θ/√(1 − k² sin²θ)`, which vanishes at both ends);
* hence `L(k) = E K' + E' K − K K'` has derivative zero on `(0, 1)` (`hasDerivAt_legendreL`,
  an algebraic consequence of the four identities), so it is constant there
  (`legendreL_eq_of_lt`, mean value theorem);
* the constant is the limit at `k → 0⁺`: `K(k) → π/2`, `E(k') → E(1) = 1`
  (`abs_ellipticE_sqrt_sub_one_le`: `|E(k') − 1| ≤ (π/2) k`), and
  `K'(k)(E(k) − K(k)) → 0` since `|E − K| ≤ k² K` and `K'(k) = ln(4/k) + O(k² ln k)`
  (`abs_ellipticK_sqrt_sub_log_le`) — `tendsto_legendreL_nhdsGT_zero`.

`legendre_relation` is (4.72); `legendre_relation_sqrt_half` is the symmetric case
`2 E K − K² = π/2` at `k = k' = 1/√2`.
-/

namespace Azurite

namespace BZ

open Real MeasureTheory Set Filter Topology
open scoped Interval

variable {k : ℝ}

/-! ### Derivatives of the integrands with respect to the modulus -/

theorem hasDerivAt_one_sub_sq_mul (x c : ℝ) :
    HasDerivAt (fun x : ℝ => 1 - x ^ 2 * c) (-(2 * x * c)) x := by
  have := ((hasDerivAt_pow 2 x).mul_const c).const_sub 1
  refine this.congr_deriv ?_
  push_cast
  ring

/-- `∂/∂x (1 − x² sin²θ)^(−1/2) = x sin²θ (1 − x² sin²θ)^(−3/2)`. -/
theorem hasDerivAt_ellipticK_integrand {x : ℝ} (hx : x ^ 2 < 1) (θ : ℝ) :
    HasDerivAt (fun x : ℝ => (Real.sqrt (1 - x ^ 2 * Real.sin θ ^ 2))⁻¹)
      (x * Real.sin θ ^ 2 / Real.sqrt (1 - x ^ 2 * Real.sin θ ^ 2) ^ 3) x := by
  have hΔ : 0 < 1 - x ^ 2 * Real.sin θ ^ 2 := one_sub_mul_sin_sq_pos hx θ
  have hs : 0 < Real.sqrt (1 - x ^ 2 * Real.sin θ ^ 2) := Real.sqrt_pos.mpr hΔ
  have h := ((hasDerivAt_one_sub_sq_mul x (Real.sin θ ^ 2)).sqrt hΔ.ne').inv hs.ne'
  refine h.congr_deriv ?_
  field_simp

/-- `∂/∂x (1 − x² sin²θ)^(1/2) = −x sin²θ (1 − x² sin²θ)^(−1/2)`. -/
theorem hasDerivAt_ellipticE_integrand {x : ℝ} (hx : x ^ 2 < 1) (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2 * Real.sin θ ^ 2))
      (-(x * Real.sin θ ^ 2) / Real.sqrt (1 - x ^ 2 * Real.sin θ ^ 2)) x := by
  have hΔ : 0 < 1 - x ^ 2 * Real.sin θ ^ 2 := one_sub_mul_sin_sq_pos hx θ
  have hs : 0 < Real.sqrt (1 - x ^ 2 * Real.sin θ ^ 2) := Real.sqrt_pos.mpr hΔ
  refine ((hasDerivAt_one_sub_sq_mul x (Real.sin θ ^ 2)).sqrt hΔ.ne').congr_deriv ?_
  field_simp

theorem continuous_ellipticK_deriv_integrand (hk : k ^ 2 < 1) :
    Continuous fun θ : ℝ => k * Real.sin θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ^ 3 :=
  Continuous.div (by fun_prop) ((Real.continuous_sqrt.comp (by fun_prop)).pow 3) fun θ =>
    pow_ne_zero 3 (Real.sqrt_pos.mpr (one_sub_mul_sin_sq_pos hk θ)).ne'

theorem continuous_ellipticE_deriv_integrand (hk : k ^ 2 < 1) :
    Continuous fun θ : ℝ => -(k * Real.sin θ ^ 2) / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) :=
  Continuous.div (by fun_prop) (Real.continuous_sqrt.comp (by fun_prop)) fun θ =>
    (Real.sqrt_pos.mpr (one_sub_mul_sin_sq_pos hk θ)).ne'

/-- A uniform lower bound for `1 − x² sin²θ` when `|x| ≤ m`. -/
theorem one_sub_sq_mul_sin_sq_ge {x m : ℝ} (hxm : |x| ≤ m) (θ : ℝ) :
    1 - m ^ 2 ≤ 1 - x ^ 2 * Real.sin θ ^ 2 := by
  have h1 := Real.sin_sq_le_one θ
  have h2 : x ^ 2 ≤ m ^ 2 := by
    rw [← sq_abs x]
    exact pow_le_pow_left₀ (abs_nonneg x) hxm 2
  nlinarith [sq_nonneg (Real.sin θ), sq_nonneg x]

/-- `∂K/∂k = ∫_0^{π/2} k sin²θ (1 − k² sin²θ)^(−3/2) dθ` for `k² < 1`. -/
theorem hasDerivAt_ellipticK (hk : k ^ 2 < 1) :
    HasDerivAt ellipticK
      (∫ θ in (0 : ℝ)..(π / 2),
        k * Real.sin θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ^ 3) k := by
  have hk1 : |k| < 1 := by rwa [← sq_lt_one_iff_abs_lt_one]
  set m : ℝ := (|k| + 1) / 2 with hm
  have hm1 : m < 1 := by rw [hm]; linarith
  have hm0 : 0 ≤ m := by positivity
  have hkm : |k| < m := by rw [hm]; linarith
  obtain ⟨hk_lo, hk_hi⟩ := abs_lt.mp hkm
  have hmem : Ioo (-m) m ∈ 𝓝 k := Ioo_mem_nhds hk_lo hk_hi
  have hsq : ∀ x ∈ Ioo (-m) m, x ^ 2 < 1 := fun x hx => by
    have : |x| < m := abs_lt.mpr ⟨hx.1, hx.2⟩
    rw [← sq_abs x]
    exact pow_lt_one₀ (abs_nonneg x) (this.trans hm1) two_ne_zero
  have hΔm : 0 < 1 - m ^ 2 := by nlinarith
  have hsm : 0 < Real.sqrt (1 - m ^ 2) := Real.sqrt_pos.mpr hΔm
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := π / 2)
    (F := fun x θ => (Real.sqrt (1 - x ^ 2 * Real.sin θ ^ 2))⁻¹)
    (F' := fun x θ => x * Real.sin θ ^ 2 / Real.sqrt (1 - x ^ 2 * Real.sin θ ^ 2) ^ 3)
    (bound := fun _ => m / Real.sqrt (1 - m ^ 2) ^ 3) hmem
    (Filter.eventually_of_mem hmem fun x hx =>
      (continuous_ellipticK_integrand (hsq x hx)).aestronglyMeasurable)
    ((continuous_ellipticK_integrand hk).intervalIntegrable _ _)
    (continuous_ellipticK_deriv_integrand hk).aestronglyMeasurable
    (Eventually.of_forall fun θ _ x hx => ?_) intervalIntegrable_const
    (Eventually.of_forall fun θ _ x hx => hasDerivAt_ellipticK_integrand (hsq x hx) θ)
  · exact key.2
  · have hx2 := hsq x hx
    have hxm : |x| ≤ m := (abs_lt.mpr ⟨hx.1, hx.2⟩).le
    have hΔ := one_sub_mul_sin_sq_pos hx2 θ
    have hΔge := one_sub_sq_mul_sin_sq_ge hxm θ
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos (Real.sqrt_pos.mpr hΔ) 3), abs_mul,
      abs_of_nonneg (sq_nonneg (Real.sin θ))]
    refine div_le_div₀ hm0 ?_ (by positivity) ?_
    · calc |x| * Real.sin θ ^ 2 ≤ m * 1 := mul_le_mul hxm (Real.sin_sq_le_one θ) (sq_nonneg _) hm0
        _ = m := mul_one m
    · exact pow_le_pow_left₀ hsm.le (Real.sqrt_le_sqrt hΔge) 3

/-- `∂E/∂k = −∫_0^{π/2} k sin²θ (1 − k² sin²θ)^(−1/2) dθ` for `k² < 1`. -/
theorem hasDerivAt_ellipticE (hk : k ^ 2 < 1) :
    HasDerivAt ellipticE
      (∫ θ in (0 : ℝ)..(π / 2),
        -(k * Real.sin θ ^ 2) / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)) k := by
  have hk1 : |k| < 1 := by rwa [← sq_lt_one_iff_abs_lt_one]
  set m : ℝ := (|k| + 1) / 2 with hm
  have hm1 : m < 1 := by rw [hm]; linarith
  have hm0 : 0 ≤ m := by positivity
  have hkm : |k| < m := by rw [hm]; linarith
  obtain ⟨hk_lo, hk_hi⟩ := abs_lt.mp hkm
  have hmem : Ioo (-m) m ∈ 𝓝 k := Ioo_mem_nhds hk_lo hk_hi
  have hsq : ∀ x ∈ Ioo (-m) m, x ^ 2 < 1 := fun x hx => by
    have : |x| < m := abs_lt.mpr ⟨hx.1, hx.2⟩
    rw [← sq_abs x]
    exact pow_lt_one₀ (abs_nonneg x) (this.trans hm1) two_ne_zero
  have hΔm : 0 < 1 - m ^ 2 := by nlinarith
  have hsm : 0 < Real.sqrt (1 - m ^ 2) := Real.sqrt_pos.mpr hΔm
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := π / 2)
    (F := fun x θ => Real.sqrt (1 - x ^ 2 * Real.sin θ ^ 2))
    (F' := fun x θ => -(x * Real.sin θ ^ 2) / Real.sqrt (1 - x ^ 2 * Real.sin θ ^ 2))
    (bound := fun _ => m / Real.sqrt (1 - m ^ 2)) hmem
    (Eventually.of_forall fun x => (continuous_ellipticE_integrand x).aestronglyMeasurable)
    ((continuous_ellipticE_integrand k).intervalIntegrable _ _)
    (continuous_ellipticE_deriv_integrand hk).aestronglyMeasurable
    (Eventually.of_forall fun θ _ x hx => ?_) intervalIntegrable_const
    (Eventually.of_forall fun θ _ x hx => hasDerivAt_ellipticE_integrand (hsq x hx) θ)
  · exact key.2
  · have hx2 := hsq x hx
    have hxm : |x| ≤ m := (abs_lt.mpr ⟨hx.1, hx.2⟩).le
    have hΔ := one_sub_mul_sin_sq_pos hx2 θ
    have hΔge := one_sub_sq_mul_sin_sq_ge hxm θ
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.sqrt_pos.mpr hΔ), abs_neg, abs_mul,
      abs_of_nonneg (sq_nonneg (Real.sin θ))]
    refine div_le_div₀ hm0 ?_ hsm (Real.sqrt_le_sqrt hΔge)
    calc |x| * Real.sin θ ^ 2 ≤ m * 1 := mul_le_mul hxm (Real.sin_sq_le_one θ) (sq_nonneg _) hm0
      _ = m := mul_one m

/-! ### The two classical identities -/

/-- `k ∂E/∂k = E − K`. -/
theorem mul_ellipticE_deriv (hk : k ^ 2 < 1) :
    k * ∫ θ in (0 : ℝ)..(π / 2), -(k * Real.sin θ ^ 2) / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
      = ellipticE k - ellipticK k := by
  unfold ellipticE ellipticK
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
    ((continuous_ellipticE_integrand k).intervalIntegrable _ _)
    ((continuous_ellipticK_integrand hk).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hΔ := one_sub_mul_sin_sq_pos hk θ
  have hs : 0 < Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) := Real.sqrt_pos.mpr hΔ
  have hs2 := Real.sq_sqrt hΔ.le
  field_simp
  linear_combination -hs2

/-- The derivative of `sin θ cos θ/√(1 − k² sin²θ)`. -/
theorem hasDerivAt_sin_mul_cos_div_sqrt (hk : k ^ 2 < 1) (θ : ℝ) :
    HasDerivAt (fun θ => Real.sin θ * Real.cos θ / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))
      ((1 - 2 * Real.sin θ ^ 2 + k ^ 2 * Real.sin θ ^ 4)
        / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ^ 3) θ := by
  have hΔ := one_sub_mul_sin_sq_pos hk θ
  have hs : 0 < Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) := Real.sqrt_pos.mpr hΔ
  have hs2 := Real.sq_sqrt hΔ.le
  have hcos : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := Real.cos_sq' θ
  have hnum : HasDerivAt (fun θ => Real.sin θ * Real.cos θ)
      (Real.cos θ * Real.cos θ + Real.sin θ * -Real.sin θ) θ :=
    (Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_cos θ)
  have hΔ' : HasDerivAt (fun θ => 1 - k ^ 2 * Real.sin θ ^ 2)
      (-(k ^ 2 * (2 * Real.sin θ * Real.cos θ))) θ := by
    have := (((Real.hasDerivAt_sin θ).pow 2).const_mul (k ^ 2)).const_sub 1
    refine this.congr_deriv ?_
    push_cast
    ring
  have hden : HasDerivAt (fun θ => Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))
      (-(k ^ 2 * Real.sin θ * Real.cos θ) / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)) θ := by
    refine (hΔ'.sqrt hΔ.ne').congr_deriv ?_
    field_simp
  refine (hnum.div hden hs.ne').congr_deriv ?_
  set D := Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) with hD
  field_simp
  linear_combination (1 - 2 * Real.sin θ ^ 2) * hs2 + (Real.sin θ ^ 2 * k ^ 2 + D ^ 2) * hcos

theorem continuous_sin_cos_deriv (hk : k ^ 2 < 1) :
    Continuous fun θ : ℝ => (1 - 2 * Real.sin θ ^ 2 + k ^ 2 * Real.sin θ ^ 4)
      / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ^ 3 :=
  Continuous.div (by fun_prop) ((Real.continuous_sqrt.comp (by fun_prop)).pow 3) fun θ =>
    pow_ne_zero 3 (Real.sqrt_pos.mpr (one_sub_mul_sin_sq_pos hk θ)).ne'

/-- `k (1 − k²) ∂K/∂k = E − (1 − k²) K`. -/
theorem ellipticK_deriv_identity (hk : k ^ 2 < 1) :
    k * (1 - k ^ 2) * ∫ θ in (0 : ℝ)..(π / 2),
        k * Real.sin θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ^ 3
      = ellipticE k - (1 - k ^ 2) * ellipticK k := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hasDerivAt_sin_mul_cos_div_sqrt hk θ)
    ((continuous_sin_cos_deriv hk).intervalIntegrable 0 (π / 2))
  have h0 : Real.sin (π / 2) * Real.cos (π / 2) / Real.sqrt (1 - k ^ 2 * Real.sin (π / 2) ^ 2)
      - Real.sin 0 * Real.cos 0 / Real.sqrt (1 - k ^ 2 * Real.sin 0 ^ 2) = 0 := by
    simp
  rw [h0] at hFTC
  have hE : IntervalIntegrable (fun θ : ℝ => Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)) volume 0
      (π / 2) := (continuous_ellipticE_integrand k).intervalIntegrable _ _
  have hK : IntervalIntegrable
      (fun θ : ℝ => (1 - k ^ 2) * (Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹) volume 0 (π / 2) := ((continuous_ellipticK_integrand hk).const_mul _).intervalIntegrable _ _
  have hD : IntervalIntegrable
      (fun θ : ℝ => k ^ 2 * ((1 - 2 * Real.sin θ ^ 2 + k ^ 2 * Real.sin θ ^ 4)
        / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ^ 3)) volume 0 (π / 2) :=
    ((continuous_sin_cos_deriv hk).const_mul _).intervalIntegrable _ _
  have hpt : ∀ θ : ℝ,
      k * (1 - k ^ 2) * (k * Real.sin θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ^ 3)
      = Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
        - (1 - k ^ 2) * (Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹
        - k ^ 2 * ((1 - 2 * Real.sin θ ^ 2 + k ^ 2 * Real.sin θ ^ 4)
          / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ^ 3) := by
    intro θ
    have hΔ := one_sub_mul_sin_sq_pos hk θ
    have hs : 0 < Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) := Real.sqrt_pos.mpr hΔ
    have hs2 := Real.sq_sqrt hΔ.le
    field_simp
    linear_combination (-(Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)) ^ 2
      - k ^ 2 * (1 - Real.sin θ ^ 2)) * hs2
  unfold ellipticE ellipticK
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_congr fun θ _ => hpt θ,
    intervalIntegral.integral_sub (hE.sub hK) hD, intervalIntegral.integral_sub hE hK,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hFTC]
  ring

/-! ### The Legendre function and its derivative -/

/-- `L(k) = E(k) K(k') + E(k') K(k) − K(k) K(k')` with `k' = √(1 − k²)`. -/
noncomputable def legendreL (k : ℝ) : ℝ :=
  ellipticE k * ellipticK (Real.sqrt (1 - k ^ 2)) + ellipticE (Real.sqrt (1 - k ^ 2)) * ellipticK k
    - ellipticK k * ellipticK (Real.sqrt (1 - k ^ 2))

theorem hasDerivAt_legendreL (hk0 : 0 < k) (hk1 : k < 1) : HasDerivAt legendreL 0 k := by
  have hk2 : k ^ 2 < 1 := by nlinarith
  set b := Real.sqrt (1 - k ^ 2) with hb
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by nlinarith)
  have hb2 : b ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by nlinarith)
  have hb1 : b ^ 2 < 1 := by rw [hb2]; nlinarith
  have hb' : HasDerivAt (fun k : ℝ => Real.sqrt (1 - k ^ 2)) (-k / b) k := by
    have h1 : HasDerivAt (fun k : ℝ => 1 - k ^ 2) (-(2 * k)) k := by
      have := (hasDerivAt_pow 2 k).const_sub 1
      refine this.congr_deriv ?_
      push_cast
      ring
    refine (h1.sqrt (by nlinarith : (1 : ℝ) - k ^ 2 ≠ 0)).congr_deriv ?_
    rw [← hb]
    field_simp
  have hE := hasDerivAt_ellipticE hk2
  have hK := hasDerivAt_ellipticK hk2
  have hE' := (hasDerivAt_ellipticE hb1).comp k hb'
  have hK' := (hasDerivAt_ellipticK hb1).comp k hb'
  have h := ((hE.mul hK').add (hE'.mul hK)).sub (hK.mul hK')
  refine h.congr_deriv ?_
  have r1 := mul_ellipticE_deriv hk2
  have r2 := ellipticK_deriv_identity hk2
  have r3 := mul_ellipticE_deriv hb1
  have r4 := ellipticK_deriv_identity hb1
  have hc : -k / b * b = -k := by field_simp
  set c := -k / b with hc_def
  set E₁ := ∫ θ in (0 : ℝ)..(π / 2),
    -(k * Real.sin θ ^ 2) / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) with hE₁
  set K₁ := ∫ θ in (0 : ℝ)..(π / 2),
    k * Real.sin θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ^ 3 with hK₁
  set E₂ := ∫ θ in (0 : ℝ)..(π / 2),
    -(b * Real.sin θ ^ 2) / Real.sqrt (1 - b ^ 2 * Real.sin θ ^ 2) with hE₂
  set K₂ := ∫ θ in (0 : ℝ)..(π / 2),
    b * Real.sin θ ^ 2 / Real.sqrt (1 - b ^ 2 * Real.sin θ ^ 2) ^ 3 with hK₂
  rw [show (1 : ℝ) - k ^ 2 = b ^ 2 from hb2.symm] at r2
  rw [show (1 : ℝ) - b ^ 2 = k ^ 2 by rw [hb2]; ring] at r4
  simp only [Function.comp_apply]
  rw [← hb]
  have key : k * b ^ 2 * (E₁ * ellipticK b + ellipticE k * (K₂ * c) + (E₂ * c * ellipticK k
      + ellipticE b * K₁) - (K₁ * ellipticK b + ellipticK k * (K₂ * c))) = 0 := by
    linear_combination (b ^ 2 * ellipticK b) * r1 + (ellipticE b - ellipticK b) * r2
      - (k ^ 2 * ellipticK k) * r3 + (ellipticK k - ellipticE k) * r4
      + (ellipticE k * ellipticK b - ellipticK k * ellipticE b) * hb2
      + (k * b * (ellipticE k * K₂ + ellipticK k * E₂ - ellipticK k * K₂)) * hc
  exact (mul_eq_zero.mp key).resolve_left (mul_ne_zero hk0.ne' (pow_ne_zero 2 hb0.ne'))

/-- `L` is constant on `(0, 1)`. -/
theorem legendreL_eq_of_lt {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    legendreL a = legendreL b := by
  have hcont : ContinuousOn legendreL (Icc a b) := fun x hx =>
    (hasDerivAt_legendreL (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
  obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope legendreL (fun _ => 0) hab hcont
    fun x hx => hasDerivAt_legendreL (by linarith [hx.1]) (by linarith [hx.2])
  have h := hc.symm
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · linarith
  · linarith

/-! ### The limit `k → 0⁺` -/

theorem ellipticE_one : ellipticE 1 = 1 := by
  unfold ellipticE
  have : ∫ θ in (0 : ℝ)..(π / 2), Real.sqrt (1 - 1 ^ 2 * Real.sin θ ^ 2)
      = ∫ θ in (0 : ℝ)..(π / 2), Real.cos θ := by
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le Real.pi_div_two_pos.le] at hθ
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_div_two_pos], hθ.2⟩
    simp only [one_pow, one_mul]
    rw [← Real.cos_sq', Real.sqrt_sq hcos]
  rw [this, integral_cos, Real.sin_pi_div_two, Real.sin_zero, sub_zero]

/-- `0 ≤ E(√(1 − k²)) − 1 ≤ (π/2) k` for `0 ≤ k ≤ 1`. -/
theorem ellipticE_sqrt_sub_one_bounds (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    0 ≤ ellipticE (Real.sqrt (1 - k ^ 2)) - 1
      ∧ ellipticE (Real.sqrt (1 - k ^ 2)) - 1 ≤ π / 2 * k := by
  have hb2 : Real.sqrt (1 - k ^ 2) ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by nlinarith)
  set b := Real.sqrt (1 - k ^ 2) with hb
  have hcosInt : ∫ θ in (0 : ℝ)..(π / 2), Real.cos θ = 1 := by
    rw [integral_cos, Real.sin_pi_div_two, Real.sin_zero, sub_zero]
  have hE : IntervalIntegrable (fun θ : ℝ => Real.sqrt (1 - b ^ 2 * Real.sin θ ^ 2)) volume 0
      (π / 2) := (continuous_ellipticE_integrand b).intervalIntegrable _ _
  have hC : IntervalIntegrable Real.cos volume 0 (π / 2) :=
    Real.continuous_cos.intervalIntegrable _ _
  have hsplit : ellipticE b - 1
      = ∫ θ in (0 : ℝ)..(π / 2), (Real.sqrt (1 - b ^ 2 * Real.sin θ ^ 2) - Real.cos θ) := by
    rw [intervalIntegral.integral_sub hE hC, hcosInt, ellipticE]
  have hpt : ∀ θ ∈ Icc (0 : ℝ) (π / 2),
      0 ≤ Real.sqrt (1 - b ^ 2 * Real.sin θ ^ 2) - Real.cos θ
        ∧ Real.sqrt (1 - b ^ 2 * Real.sin θ ^ 2) - Real.cos θ ≤ k := by
    intro θ hθ
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_div_two_pos], hθ.2⟩
    have hs1 := Real.sin_sq_le_one θ
    have hs0 := sq_nonneg (Real.sin θ)
    set A := 1 - b ^ 2 * Real.sin θ ^ 2 with hA
    set B := 1 - Real.sin θ ^ 2 with hB
    have hB0 : 0 ≤ B := by rw [hB]; linarith
    have hBA : B ≤ A := by rw [hA, hB]; nlinarith [sq_nonneg b]
    have hA0 : 0 ≤ A := hB0.trans hBA
    have hcosB : Real.cos θ = Real.sqrt B := by
      rw [hB, ← Real.cos_sq', Real.sqrt_sq hcos]
    rw [hcosB]
    refine ⟨sub_nonneg.mpr (Real.sqrt_le_sqrt hBA), ?_⟩
    have hsq : (Real.sqrt A - Real.sqrt B) ^ 2 ≤ A - B := by
      nlinarith [Real.sqrt_le_sqrt hBA, Real.mul_self_sqrt hB0, Real.sqrt_nonneg B,
        Real.sq_sqrt hA0, Real.sq_sqrt hB0, Real.sqrt_nonneg A]
    have h1 := Real.abs_le_sqrt hsq
    have hAB : A - B = k ^ 2 * Real.sin θ ^ 2 := by rw [hA, hB, hb2]; ring
    have h2 : Real.sqrt (A - B) ≤ k := by
      rw [hAB]
      calc Real.sqrt (k ^ 2 * Real.sin θ ^ 2) ≤ Real.sqrt (k ^ 2) :=
            Real.sqrt_le_sqrt (mul_le_of_le_one_right (sq_nonneg k) hs1)
        _ = k := Real.sqrt_sq hk0
    exact (le_abs_self _).trans (h1.trans h2)
  have hint : IntervalIntegrable (fun θ : ℝ => Real.sqrt (1 - b ^ 2 * Real.sin θ ^ 2) - Real.cos θ)
      volume 0 (π / 2) := hE.sub hC
  rw [hsplit]
  constructor
  · exact intervalIntegral.integral_nonneg Real.pi_div_two_pos.le fun θ hθ => (hpt θ hθ).1
  · calc _ ≤ ∫ _ in (0 : ℝ)..(π / 2), k :=
          intervalIntegral.integral_mono_on Real.pi_div_two_pos.le hint
            intervalIntegrable_const fun θ hθ => (hpt θ hθ).2
      _ = π / 2 * k := by simp [mul_comm]

/-- `0 ≤ K − E ≤ k² K` for `k² < 1`. -/
theorem ellipticK_sub_ellipticE_bounds (hk : k ^ 2 < 1) :
    0 ≤ ellipticK k - ellipticE k ∧ ellipticK k - ellipticE k ≤ k ^ 2 * ellipticK k := by
  have hE : IntervalIntegrable (fun θ : ℝ => Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)) volume 0
      (π / 2) := (continuous_ellipticE_integrand k).intervalIntegrable _ _
  have hK : IntervalIntegrable (fun θ : ℝ => (Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹) volume 0
      (π / 2) := (continuous_ellipticK_integrand hk).intervalIntegrable _ _
  have hsplit : ellipticK k - ellipticE k = ∫ θ in (0 : ℝ)..(π / 2),
      ((Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹ - Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)) := by
    rw [intervalIntegral.integral_sub hK hE, ellipticK, ellipticE]
  have hpt : ∀ θ : ℝ, 0 ≤ (Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹
        - Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
      ∧ (Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹ - Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
        ≤ k ^ 2 * (Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹ := by
    intro θ
    have hΔ := one_sub_mul_sin_sq_pos hk θ
    have hs : 0 < Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) := Real.sqrt_pos.mpr hΔ
    have hs2 := Real.sq_sqrt hΔ.le
    have hs1 := Real.sin_sq_le_one θ
    have heq : (Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹ - Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
        = k ^ 2 * Real.sin θ ^ 2 * (Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹ := by
      field_simp
      linear_combination -hs2
    rw [heq]
    constructor
    · positivity
    · exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (sq_nonneg k) hs1)
        (inv_nonneg.mpr hs.le)
  rw [hsplit]
  constructor
  · exact intervalIntegral.integral_nonneg Real.pi_div_two_pos.le fun θ _ => (hpt θ).1
  · calc _ ≤ ∫ θ in (0 : ℝ)..(π / 2), k ^ 2 * (Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹ :=
          intervalIntegral.integral_mono_on Real.pi_div_two_pos.le (hK.sub hE)
            (hK.const_mul _) fun θ _ => (hpt θ).2
      _ = k ^ 2 * ellipticK k := by rw [intervalIntegral.integral_const_mul, ellipticK]

/-- `K(k) → π/2` as `k → 0⁺`. -/
theorem tendsto_ellipticK_nhdsGT_zero : Tendsto ellipticK (𝓝[>] 0) (𝓝 (π / 2)) := by
  have hmem : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  have hlo : Tendsto (fun k : ℝ => π / 2 * (1 + k ^ 2 / 4)) (𝓝[>] 0) (𝓝 (π / 2)) := by
    have := tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ))
      ((by fun_prop : Continuous fun k : ℝ => π / 2 * (1 + k ^ 2 / 4)).tendsto 0)
    simpa using this
  have hhi : Tendsto (fun k : ℝ => π / 2 * (1 + k ^ 2 / 4 + 3 / 8 * k ^ 4)) (𝓝[>] 0)
      (𝓝 (π / 2)) := by
    have := tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ))
      ((by fun_prop : Continuous fun k : ℝ => π / 2 * (1 + k ^ 2 / 4 + 3 / 8 * k ^ 4)).tendsto 0)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [hmem] with k hk
    exact (ellipticK_bounds (by nlinarith [hk.1, hk.2])).1
  · filter_upwards [hmem] with k hk
    exact (ellipticK_bounds (by nlinarith [hk.1, hk.2])).2

/-- `E(√(1 − k²)) → 1` as `k → 0⁺`. -/
theorem tendsto_ellipticE_sqrt_nhdsGT_zero :
    Tendsto (fun k : ℝ => ellipticE (Real.sqrt (1 - k ^ 2))) (𝓝[>] 0) (𝓝 1) := by
  have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT one_pos
  have hhi : Tendsto (fun k : ℝ => 1 + π / 2 * k) (𝓝[>] 0) (𝓝 1) := by
    have := tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ))
      ((by fun_prop : Continuous fun k : ℝ => 1 + π / 2 * k).tendsto 0)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hhi ?_ ?_
  · filter_upwards [hmem] with k hk
    linarith [(ellipticE_sqrt_sub_one_bounds hk.1.le hk.2.le).1]
  · filter_upwards [hmem] with k hk
    linarith [(ellipticE_sqrt_sub_one_bounds hk.1.le hk.2.le).2]

/-- `K(√(1 − k²)) (E(k) − K(k)) → 0` as `k → 0⁺`. -/
theorem tendsto_ellipticK_sqrt_mul_sub_nhdsGT_zero :
    Tendsto (fun k : ℝ => ellipticK (Real.sqrt (1 - k ^ 2)) * (ellipticE k - ellipticK k))
      (𝓝[>] 0) (𝓝 0) := by
  have hmem : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  have h1 : Tendsto (fun k : ℝ => k ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ))
      ((continuous_pow 2).tendsto (0 : ℝ))
    simpa using this
  have h2 : Tendsto (fun k : ℝ => Real.log k * k ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_log_mul_rpow_nhdsGT_zero (r := 2) (by norm_num)
    refine this.congr fun k => ?_
    rw [Real.rpow_two]
  have hg : Tendsto (fun k : ℝ => π * Real.log 4 * k ^ 2 - π * (Real.log k * k ^ 2)
      + π / 2 * (k ^ 2 * k ^ 2) - π / 4 * (k ^ 2 * (Real.log k * k ^ 2))) (𝓝[>] 0) (𝓝 0) := by
    have := (((h1.const_mul (π * Real.log 4)).sub (h2.const_mul π)).add
      ((h1.mul h1).const_mul (π / 2))).sub ((h1.mul h2).const_mul (π / 4))
    simpa using this
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [hmem] with k hk
  obtain ⟨hk0, hk12⟩ := hk
  have hk1 : k ≤ 1 := by linarith
  have hk2 : k ^ 2 ≤ 1 / 2 := by nlinarith
  have hk2' : k ^ 2 < 1 := by linarith
  have hKb := abs_ellipticK_sqrt_sub_log_le hk0 hk1
  have hKpos : 0 < ellipticK (Real.sqrt (1 - k ^ 2)) :=
    lt_of_lt_of_le Real.pi_div_two_pos
      (pi_div_two_le_ellipticK (by rw [Real.sq_sqrt (by linarith)]; nlinarith))
  have hKk := ellipticK_bounds hk2
  have hKle : ellipticK k ≤ π := by nlinarith [hKk.2, Real.pi_pos]
  have hsub := ellipticK_sub_ellipticE_bounds hk2'
  have hlogk : Real.log k ≤ 0 := Real.log_nonpos hk0.le hk1
  have hlog4 : Real.log (4 / k) = Real.log 4 - Real.log k :=
    Real.log_div (by norm_num) hk0.ne'
  have hKb' : ellipticK (Real.sqrt (1 - k ^ 2))
      ≤ Real.log 4 - Real.log k + k ^ 2 / 4 * (2 - Real.log k) := by
    have := (abs_le.mp hKb).2
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hKpos, abs_sub_comm, abs_of_nonneg hsub.1]
  calc ellipticK (Real.sqrt (1 - k ^ 2)) * (ellipticK k - ellipticE k)
      ≤ (Real.log 4 - Real.log k + k ^ 2 / 4 * (2 - Real.log k)) * (k ^ 2 * π) := by
        refine mul_le_mul hKb' (hsub.2.trans ?_) hsub.1 ?_
        · exact mul_le_mul_of_nonneg_left hKle (sq_nonneg k)
        · linarith
    _ = π * Real.log 4 * k ^ 2 - π * (Real.log k * k ^ 2)
      + π / 2 * (k ^ 2 * k ^ 2) - π / 4 * (k ^ 2 * (Real.log k * k ^ 2)) := by ring

/-- `L(k) → π/2` as `k → 0⁺`. -/
theorem tendsto_legendreL_nhdsGT_zero : Tendsto legendreL (𝓝[>] 0) (𝓝 (π / 2)) := by
  have h := tendsto_ellipticK_sqrt_mul_sub_nhdsGT_zero.add
    (tendsto_ellipticE_sqrt_nhdsGT_zero.mul tendsto_ellipticK_nhdsGT_zero)
  rw [zero_add, one_mul] at h
  refine h.congr fun k => ?_
  unfold legendreL
  ring

/-- `L` equals `π/2` on `(0, 1)`. -/
theorem legendreL_eq (hk0 : 0 < k) (hk1 : k < 1) : legendreL k = π / 2 := by
  have hconst : Tendsto legendreL (𝓝[>] 0) (𝓝 (legendreL k)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hk0] with a ha
    exact (legendreL_eq_of_lt ha.1 ha.2 hk1).symm
  exact tendsto_nhds_unique hconst tendsto_legendreL_nhdsGT_zero

/-- **The Legendre relation** (4.72): `E(k) K(k') + E(k') K(k) − K(k) K(k') = π/2` for
`0 < k < 1`, `k' = √(1 − k²)`. -/
theorem legendre_relation (hk0 : 0 < k) (hk1 : k < 1) :
    ellipticE k * ellipticK (Real.sqrt (1 - k ^ 2))
      + ellipticE (Real.sqrt (1 - k ^ 2)) * ellipticK k
      - ellipticK k * ellipticK (Real.sqrt (1 - k ^ 2)) = π / 2 :=
  legendreL_eq hk0 hk1

/-- The symmetric case `k = k' = 1/√2` (the modulus of the Brent–Salamin algorithm):
`2 E(1/√2) K(1/√2) − K(1/√2)² = π/2`. -/
theorem legendre_relation_sqrt_half :
    2 * ellipticE (1 / Real.sqrt 2) * ellipticK (1 / Real.sqrt 2)
      - ellipticK (1 / Real.sqrt 2) ^ 2 = π / 2 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hk : Real.sqrt (1 - (1 / Real.sqrt 2) ^ 2) = 1 / Real.sqrt 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt zero_le_two, show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num,
      Real.sqrt_inv, one_div]
  have hk0 : 0 < 1 / Real.sqrt 2 := by positivity
  have hk1 : 1 / Real.sqrt 2 < 1 := by
    rw [div_lt_one h2, Real.lt_sqrt zero_le_one]
    norm_num
  have h := legendre_relation hk0 hk1
  rw [hk] at h
  linear_combination h

end BZ

end Azurite
