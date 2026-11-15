/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section7Aux

/-!
# DLMF §6.8: inequalities

Formalizations of <https://dlmf.nist.gov/6.8>, equations 6.8.1–6.8.3 (`x > 0`; `E₁(x)` is the
real `expIntE₁R x`, equal to `expIntE₁ x` by `dlmf_6_3_F1_real`).

Method (`lt_exp_mul_E1_of_defect_pos`, `exp_mul_E1_lt_of_defect_neg`): `F(x) = eˣ E₁(x)`
satisfies `F′ = F − 1/x`, so for a bounded smooth `φ` the function `E₁(x) − e^{−x} φ(x)` has
derivative `−e^{−x}(φ′ − φ + 1/x)` and tends to `0`; hence `φ < F` when the defect
`φ′ − φ + 1/x` is positive and `φ > F` when it is negative.  The six bounds have defects
`(1/x + 1/(x+2))/2 − ½ ln(1 + 2/x) > 0`, `1/(x+1) − ln(1 + 1/x) < 0`, `1/(x(x+1)²)`,
`−2/(x(x+2))²`, `4/(x(x²+4x+2)²)`, `−12/(x²(x²+6x+6)²)`.
-/

open Filter Topology Set

namespace Azurite.DLMF

/-- The comparison function `k(t) = E₁(t) − e^{−t} φ(t)`. -/
theorem hasDerivAt_comparison {φ φ' : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (hφ : HasDerivAt φ (φ' t) t) :
    HasDerivAt (fun t => expIntE₁R t - Real.exp (-t) * φ t)
      (-(Real.exp (-t) * (φ' t - φ t + 1 / t))) t := by
  have h1 := hasDerivAt_expIntE₁R ht
  have h2 := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).mul hφ
  refine (h1.sub h2).congr_deriv ?_
  simp only [Function.comp]
  field_simp
  ring

theorem tendsto_comparison {φ : ℝ → ℝ} (hb : ∃ C, ∀ x, 1 ≤ x → |φ x| ≤ C) :
    Tendsto (fun t => expIntE₁R t - Real.exp (-t) * φ t) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hb
  have h2 : Tendsto (fun t => Real.exp (-t) * φ t) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (Real.tendsto_exp_neg_atTop_nhds_zero.mul_const C |>.congr'
      (Eventually.of_forall fun _ => rfl) |> fun h => by simpa using h)
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hC t ht) (Real.exp_pos _).le
  simpa using tendsto_expIntE₁R_atTop.sub h2

/-- A positive defect `φ′ − φ + 1/x` gives the lower bound `φ(x) < eˣ E₁(x)`. -/
theorem lt_exp_mul_E1_of_defect_pos {φ φ' : ℝ → ℝ} (hφ : ∀ x, 0 < x → HasDerivAt φ (φ' x) x)
    (hD : ∀ x, 0 < x → 0 < φ' x - φ x + 1 / x) (hb : ∃ C, ∀ x, 1 ≤ x → |φ x| ≤ C)
    {x : ℝ} (hx : 0 < x) : φ x < Real.exp x * expIntE₁R x := by
  set k := fun t => expIntE₁R t - Real.exp (-t) * φ t
  have hanti : StrictAntiOn k (Ioi 0) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioi 0) (fun t ht =>
      (hasDerivAt_comparison ht (hφ t ht)).continuousAt.continuousWithinAt) fun t ht => ?_
    rw [interior_Ioi] at ht
    rw [(hasDerivAt_comparison ht (hφ t ht)).deriv]
    exact neg_neg_of_pos (mul_pos (Real.exp_pos _) (hD t ht))
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have h0 : 0 ≤ k (x + 1) := by
    refine le_of_tendsto (tendsto_comparison hb) ?_
    filter_upwards [eventually_ge_atTop (x + 1)] with y hy
    rcases hy.eq_or_lt with rfl | hy
    · exact le_rfl
    · exact (hanti hx1 (hx1.trans hy) hy).le
  have hk : 0 < k x := h0.trans_lt (hanti hx hx1 (by linarith))
  have := mul_lt_mul_of_pos_left hk (Real.exp_pos x)
  simp only [k, mul_zero] at this
  rw [mul_sub, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at this
  linarith

/-- A negative defect `φ′ − φ + 1/x` gives the upper bound `eˣ E₁(x) < φ(x)`. -/
theorem exp_mul_E1_lt_of_defect_neg {φ φ' : ℝ → ℝ} (hφ : ∀ x, 0 < x → HasDerivAt φ (φ' x) x)
    (hD : ∀ x, 0 < x → φ' x - φ x + 1 / x < 0) (hb : ∃ C, ∀ x, 1 ≤ x → |φ x| ≤ C)
    {x : ℝ} (hx : 0 < x) : Real.exp x * expIntE₁R x < φ x := by
  set k := fun t => expIntE₁R t - Real.exp (-t) * φ t
  have hmono : StrictMonoOn k (Ioi 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi 0) (fun t ht =>
      (hasDerivAt_comparison ht (hφ t ht)).continuousAt.continuousWithinAt) fun t ht => ?_
    rw [interior_Ioi] at ht
    rw [(hasDerivAt_comparison ht (hφ t ht)).deriv]
    exact neg_pos_of_neg (mul_neg_of_pos_of_neg (Real.exp_pos _) (hD t ht))
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have h0 : k (x + 1) ≤ 0 := by
    refine ge_of_tendsto (tendsto_comparison hb) ?_
    filter_upwards [eventually_ge_atTop (x + 1)] with y hy
    rcases hy.eq_or_lt with rfl | hy
    · exact le_rfl
    · exact (hmono hx1 (hx1.trans hy) hy).le
  have hk : k x < 0 := (hmono hx hx1 (by linarith)).trans_le h0
  have := mul_lt_mul_of_pos_left hk (Real.exp_pos x)
  simp only [k, mul_zero] at this
  rw [mul_sub, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at this
  linarith

/-! ### 6.8.1 -/

/-- `ln(1 + 2/x) < 1/x + 1/(x + 2)` for `x > 0` (the function `1/x + 1/(x+2) − ln(1 + 2/x)`
decreases to `0`). -/
theorem log_one_add_two_div_lt {x : ℝ} (hx : 0 < x) :
    Real.log (x + 2) - Real.log x < 1 / x + 1 / (x + 2) := by
  set ψ := fun t : ℝ => 1 / t + 1 / (t + 2) - (Real.log (t + 2) - Real.log t)
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt ψ (-(1 / t - 1 / (t + 2)) ^ 2) t := by
    intro t ht
    have h1 := (hasDerivAt_inv ht.ne').add (((hasDerivAt_id t).add_const 2).inv (by
      simp only [id]; linarith))
    have h2 := ((((hasDerivAt_id t).add_const 2).log (by simp only [id]; linarith))).sub
      (Real.hasDerivAt_log ht.ne')
    refine ((h1.sub h2).congr_deriv ?_).congr_of_eventuallyEq
      (Eventually.of_forall fun s => by simp [ψ, one_div])
    have : t + 2 ≠ 0 := by linarith
    simp only [id]
    field_simp
    ring
  have hanti : StrictAntiOn ψ (Ioi 0) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt) fun t ht => ?_
    rw [interior_Ioi] at ht
    rw [(hd t ht).deriv]
    have ht' : (0 : ℝ) < t := ht
    have : 1 / t - 1 / (t + 2) ≠ 0 := by
      have h := ht'.ne'
      rw [sub_ne_zero]
      intro h'
      field_simp at h'
      linarith
    exact neg_neg_of_pos (by positivity)
  have hlim : Tendsto ψ atTop (𝓝 0) := by
    have e : ∀ t : ℝ, 0 < t → Real.log (t + 2) - Real.log t = Real.log (1 + 2 * t⁻¹) :=
        fun t ht => by
      rw [← Real.log_div (by linarith) ht.ne']
      congr 1
      field_simp
    have h1 : Tendsto (fun t : ℝ => Real.log (1 + 2 * t⁻¹)) atTop (𝓝 0) := by
      have := ((Real.continuousAt_log (by norm_num : (1 : ℝ) + 2 * 0 ≠ 0)).tendsto.comp
        ((tendsto_inv_atTop_zero.const_mul 2).const_add 1))
      rw [mul_zero, add_zero, Real.log_one] at this
      exact this
    have h2 : Tendsto (fun t : ℝ => 1 / t + 1 / (t + 2)) atTop (𝓝 0) := by
      have ha : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have hb : Tendsto (fun t : ℝ => 1 / (t + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_id)
      simpa using ha.add hb
    have h3 := h2.sub h1
    rw [sub_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [ψ, e t ht]
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have h0 : 0 ≤ ψ (x + 1) := by
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (x + 1)] with y hy
    rcases hy.eq_or_lt with rfl | hy
    · exact le_rfl
    · exact (hanti hx1 (hx1.trans hy) hy).le
  have := h0.trans_lt (hanti hx hx1 (by linarith))
  simp only [ψ] at this
  linarith

/-- **DLMF 6.8.1**: `½ ln(1 + 2/x) < eˣ E₁(x) < ln(1 + 1/x)`, `x > 0`. -/
theorem dlmf_6_8_1 {x : ℝ} (hx : 0 < x) :
    1 / 2 * Real.log (1 + 2 / x) < Real.exp x * expIntE₁R x ∧
      Real.exp x * expIntE₁R x < Real.log (1 + 1 / x) := by
  have e2 : ∀ t : ℝ, 0 < t → Real.log (1 + 2 / t) = Real.log (t + 2) - Real.log t := fun t ht => by
    rw [← Real.log_div (by linarith) ht.ne']
    congr 1
    field_simp
  have e1 : ∀ t : ℝ, 0 < t → Real.log (1 + 1 / t) = Real.log (t + 1) - Real.log t := fun t ht => by
    rw [← Real.log_div (by linarith) ht.ne']
    congr 1
    field_simp
  have hlog_nonneg : ∀ t : ℝ, 0 < t → ∀ c : ℝ, 0 ≤ c → 0 ≤ Real.log (1 + c / t) := fun t ht c hc =>
    Real.log_nonneg (by have := div_nonneg hc ht.le; linarith)
  have hlog_le : ∀ t : ℝ, 0 < t → ∀ c : ℝ, 0 ≤ c → Real.log (1 + c / t) ≤ c / t :=
      fun t ht c hc => by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + c / t by positivity)
    linarith
  constructor
  · refine lt_exp_mul_E1_of_defect_pos (φ := fun t => 1 / 2 * (Real.log (t + 2) - Real.log t))
      (φ' := fun t => 1 / 2 * (1 / (t + 2) - 1 / t)) (fun t ht => ?_) (fun t ht => ?_)
      ⟨1, fun t ht => ?_⟩ hx |> fun h => by rwa [e2 x hx]
    · have := ((((hasDerivAt_id t).add_const 2).log (by simp only [id]; linarith)).sub
        (Real.hasDerivAt_log ht.ne')).const_mul (1 / 2)
      exact this.congr_deriv (by simp [one_div])
    · have := log_one_add_two_div_lt ht
      linarith
    · have ht0 : (0 : ℝ) < t := by linarith
      rw [← e2 t ht0, abs_of_nonneg (by have := hlog_nonneg t ht0 2 (by norm_num); positivity)]
      have := hlog_le t ht0 2 (by norm_num)
      have : 2 / t ≤ 2 := by rw [div_le_iff₀ ht0]; linarith
      linarith
  · refine exp_mul_E1_lt_of_defect_neg (φ := fun t => Real.log (t + 1) - Real.log t)
      (φ' := fun t => 1 / (t + 1) - 1 / t) (fun t ht => ?_) (fun t ht => ?_)
      ⟨1, fun t ht => ?_⟩ hx |> fun h => by rwa [e1 x hx]
    · have := (((hasDerivAt_id t).add_const 1).log (by simp only [id]; linarith)).sub
        (Real.hasDerivAt_log ht.ne')
      exact this.congr_deriv (by simp [one_div])
    · -- `ln(1 + 1/t) > 1/(t + 1)`: `ln y < y − 1` at `y = t/(t + 1)`
      have h := Real.log_lt_sub_one_of_pos (show 0 < t / (t + 1) by positivity)
        (by intro h; field_simp at h; linarith)
      rw [Real.log_div ht.ne' (by linarith)] at h
      have : t / (t + 1) - 1 = -(1 / (t + 1)) := by field_simp; ring
      rw [this] at h
      have : 1 / (t + 1) - 1 / t - (Real.log (t + 1) - Real.log t) + 1 / t =
          1 / (t + 1) - (Real.log (t + 1) - Real.log t) := by ring
      linarith
    · have ht0 : (0 : ℝ) < t := by linarith
      rw [← e1 t ht0, abs_of_nonneg (hlog_nonneg t ht0 1 zero_le_one)]
      have := hlog_le t ht0 1 zero_le_one
      have : 1 / t ≤ 1 := by rw [div_le_one ht0]; exact ht
      linarith

/-! ### 6.8.2, 6.8.3 -/

/-- A rational bound `N/M` with `0 < N ≤ M` on `[1, ∞)` is bounded by `1` there. -/
theorem abs_div_le_one_of {N M : ℝ} (hN : 0 ≤ N) (hM : 0 < M) (hNM : N ≤ M) : |N / M| ≤ 1 := by
  rw [abs_of_nonneg (div_nonneg hN hM.le)]
  exact (div_le_one hM).mpr hNM

/-- **DLMF 6.8.2**: `x/(x + 1) < x eˣ E₁(x) < (x + 1)/(x + 2)`, `x > 0`. -/
theorem dlmf_6_8_2 {x : ℝ} (hx : 0 < x) :
    x / (x + 1) < x * (Real.exp x * expIntE₁R x) ∧
      x * (Real.exp x * expIntE₁R x) < (x + 1) / (x + 2) := by
  have hl := lt_exp_mul_E1_of_defect_pos (φ := fun t => 1 / (t + 1))
    (φ' := fun t => -1 / (t + 1) ^ 2) (fun t ht => by
      have := ((hasDerivAt_id t).add_const 1).inv (by simp only [id]; linarith)
      refine (this.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s => by simp)
      simp only [id])
    (fun t ht => by
      have h1 : -1 / (t + 1) ^ 2 - 1 / (t + 1) + 1 / t = 1 / (t * (t + 1) ^ 2) := by
        field_simp; ring
      rw [h1]; positivity)
    ⟨1, fun t ht => abs_div_le_one_of zero_le_one (by linarith) (by linarith)⟩ hx
  have hu := exp_mul_E1_lt_of_defect_neg (φ := fun t => (t + 1) / (t * (t + 2)))
    (φ' := fun t => (t * (t + 2) - (t + 1) * (2 * t + 2)) / (t * (t + 2)) ^ 2) (fun t ht => by
      have hM : t * (t + 2) ≠ 0 := by positivity
      have := ((hasDerivAt_id t).add_const 1).div ((hasDerivAt_id t).mul
        ((hasDerivAt_id t).add_const 2)) hM
      refine this.congr_deriv ?_
      simp only [Pi.mul_apply, id]
      ring)
    (fun t ht => by
      have h1 : (t * (t + 2) - (t + 1) * (2 * t + 2)) / (t * (t + 2)) ^ 2 -
          (t + 1) / (t * (t + 2)) + 1 / t = -2 / (t * (t + 2)) ^ 2 := by
        field_simp; ring
      rw [h1]
      exact div_neg_of_neg_of_pos (by norm_num) (by positivity))
    ⟨1, fun t ht => abs_div_le_one_of (by linarith) (by nlinarith) (by nlinarith)⟩ hx
  constructor
  · have := mul_lt_mul_of_pos_left hl hx
    rwa [show x * (1 / (x + 1)) = x / (x + 1) by ring] at this
  · have := mul_lt_mul_of_pos_left hu hx
    rwa [show x * ((x + 1) / (x * (x + 2))) = (x + 1) / (x + 2) by field_simp] at this

/-- **DLMF 6.8.3**: `x(x + 3)/(x² + 4x + 2) < x eˣ E₁(x) < (x² + 5x + 2)/(x² + 6x + 6)`, `x > 0`. -/
theorem dlmf_6_8_3 {x : ℝ} (hx : 0 < x) :
    x * (x + 3) / (x ^ 2 + 4 * x + 2) < x * (Real.exp x * expIntE₁R x) ∧
      x * (Real.exp x * expIntE₁R x) < (x ^ 2 + 5 * x + 2) / (x ^ 2 + 6 * x + 6) := by
  have hl := lt_exp_mul_E1_of_defect_pos (φ := fun t => (t + 3) / (t ^ 2 + 4 * t + 2))
    (φ' := fun t => ((t ^ 2 + 4 * t + 2) - (t + 3) * (2 * t + 4)) / (t ^ 2 + 4 * t + 2) ^ 2)
    (fun t ht => by
      have hM : t ^ 2 + 4 * t + 2 ≠ 0 := by positivity
      have := ((hasDerivAt_id t).add_const 3).div
        ((((hasDerivAt_id t).pow 2).add ((hasDerivAt_id t).const_mul 4)).add_const 2) hM
      refine this.congr_deriv ?_
      simp only [Pi.add_apply, Pi.pow_apply, id]
      ring)
    (fun t ht => by
      have hM : t ^ 2 + 4 * t + 2 ≠ 0 := by positivity
      have h1 : ((t ^ 2 + 4 * t + 2) - (t + 3) * (2 * t + 4)) / (t ^ 2 + 4 * t + 2) ^ 2 -
          (t + 3) / (t ^ 2 + 4 * t + 2) + 1 / t = 4 / (t * (t ^ 2 + 4 * t + 2) ^ 2) := by
        field_simp; ring
      rw [h1]; positivity)
    ⟨1, fun t ht => abs_div_le_one_of (by linarith) (by positivity) (by nlinarith)⟩ hx
  have hu := exp_mul_E1_lt_of_defect_neg
    (φ := fun t => (t ^ 2 + 5 * t + 2) / (t ^ 3 + 6 * t ^ 2 + 6 * t))
    (φ' := fun t => ((2 * t + 5) * (t ^ 3 + 6 * t ^ 2 + 6 * t) -
      (t ^ 2 + 5 * t + 2) * (3 * t ^ 2 + 12 * t + 6)) / (t ^ 3 + 6 * t ^ 2 + 6 * t) ^ 2)
    (fun t ht => by
      have hM : t ^ 3 + 6 * t ^ 2 + 6 * t ≠ 0 := by positivity
      have := ((((hasDerivAt_id t).pow 2).add ((hasDerivAt_id t).const_mul 5)).add_const 2).div
        ((((hasDerivAt_id t).pow 3).add (((hasDerivAt_id t).pow 2).const_mul 6)).add
          ((hasDerivAt_id t).const_mul 6)) hM
      refine this.congr_deriv ?_
      simp only [Pi.add_apply, Pi.pow_apply, id]
      push_cast
      ring)
    (fun t ht => by
      have hM : t ^ 3 + 6 * t ^ 2 + 6 * t ≠ 0 := by positivity
      have h1 : ((2 * t + 5) * (t ^ 3 + 6 * t ^ 2 + 6 * t) -
          (t ^ 2 + 5 * t + 2) * (3 * t ^ 2 + 12 * t + 6)) / (t ^ 3 + 6 * t ^ 2 + 6 * t) ^ 2 -
          (t ^ 2 + 5 * t + 2) / (t ^ 3 + 6 * t ^ 2 + 6 * t) + 1 / t =
          -12 / (t ^ 3 + 6 * t ^ 2 + 6 * t) ^ 2 := by
        field_simp; ring
      rw [h1]
      exact div_neg_of_neg_of_pos (by norm_num) (by positivity))
    ⟨1, fun t ht => abs_div_le_one_of (by positivity) (by positivity) (by nlinarith)⟩ hx
  constructor
  · have := mul_lt_mul_of_pos_left hl hx
    rwa [show x * ((x + 3) / (x ^ 2 + 4 * x + 2)) = x * (x + 3) / (x ^ 2 + 4 * x + 2) by ring]
      at this
  · have := mul_lt_mul_of_pos_left hu hx
    rwa [show x * ((x ^ 2 + 5 * x + 2) / (x ^ 3 + 6 * x ^ 2 + 6 * x)) =
      (x ^ 2 + 5 * x + 2) / (x ^ 2 + 6 * x + 6) by
        rw [show x ^ 3 + 6 * x ^ 2 + 6 * x = x * (x ^ 2 + 6 * x + 6) by ring]
        field_simp] at this

end Azurite.DLMF
