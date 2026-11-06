/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13Taylor
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Bounds

/-!
# DLMF §4.13: the Stirling generating function and a Lagrange reversion

Groundwork for the asymptotic expansions 4.13.10–4.13.11.

* `lambertLogL w = −ln(1 − w)`, analytic on `|w| < 1`.
* `hasSum_stirlingFirst`: `(−ln(1 − x))ᵏ/k! = ∑ₙ [n, k] xⁿ/n!` (`[n, k] = Nat.stirlingFirst n k`,
  the Stirling cycle numbers of DLMF 26.13), from `(1 − x) f′ₖ = f_{k−1}` and the Leibniz rule.
-/

open Set Filter Topology Complex Finset
open scoped Real Nat

namespace Azurite.DLMF

/-- `L(w) = −ln(1 − w)`. -/
noncomputable def lambertLogL (w : ℂ) : ℂ := -log (1 - w)

theorem one_sub_mem_slitPlane_of_norm_lt {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left
  have := (re_le_norm w).trans_lt hw
  simp only [sub_re, one_re]; linarith

theorem hasDerivAt_lagL {w : ℂ} (hw : ‖w‖ < 1) : HasDerivAt lambertLogL (1 - w)⁻¹ w := by
  have h1 : HasDerivAt (fun t : ℂ => 1 - t) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub (1 : ℂ)
  have h3 := (h1.clog (one_sub_mem_slitPlane_of_norm_lt hw)).neg
  unfold lambertLogL
  convert h3 using 1
  rw [neg_div, neg_neg, one_div]

theorem differentiableOn_lagL : DifferentiableOn ℂ lambertLogL (Metric.ball 0 1) := fun _ hw =>
  (hasDerivAt_lagL (by simpa using hw)).differentiableAt.differentiableWithinAt

theorem lagL_zero : lambertLogL 0 = 0 := by rw [lambertLogL, sub_zero, log_one, neg_zero]

/-! ### The Stirling generating function -/

/-- `fₖ = Lᵏ/k!`. -/
noncomputable def stirF (k : ℕ) (w : ℂ) : ℂ := lambertLogL w ^ k / k !

theorem analyticAt_stirF (k : ℕ) {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ (stirF k) w := by
  have hL : AnalyticAt ℂ lambertLogL w :=
    differentiableOn_lagL.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hw))
  exact (hL.pow k).div_const

theorem hasDerivAt_stirF_succ (k : ℕ) {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (stirF (k + 1)) (stirF k w * (1 - w)⁻¹) w := by
  have h := ((hasDerivAt_lagL hw).pow (k + 1)).div_const (((k + 1)! : ℕ) : ℂ)
  refine h.congr_deriv ?_
  unfold stirF
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

/-- `(1 − w) f′_{k+1} = fₖ` near `0`. -/
theorem stirF_ode (k : ℕ) :
    (fun w => deriv (stirF (k + 1)) w - w * deriv (stirF (k + 1)) w) =ᶠ[𝓝 0] stirF k := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with w hw
  have hw' : ‖w‖ < 1 := by simpa using hw
  rw [(hasDerivAt_stirF_succ k hw').deriv]
  have hne : (1 : ℂ) - w ≠ 0 := slitPlane_ne_zero (one_sub_mem_slitPlane_of_norm_lt hw')
  field_simp

theorem contDiffAt_deriv_stirF (k n : ℕ) : ContDiffAt ℂ n (deriv (stirF k)) 0 :=
  (analyticAt_stirF k (by simp)).deriv.contDiffAt

/-- `fₖ^{(n)}(0) = [n, k]`. -/
theorem iteratedDeriv_stirF (n k : ℕ) : iteratedDeriv n (stirF k) 0 = Nat.stirlingFirst n k := by
  induction n generalizing k with
  | zero =>
    rcases k with _ | k
    · simp [stirF]
    · simp [stirF, lagL_zero]
  | succ n ih =>
    rcases k with _ | k
    · have : stirF 0 = fun _ => 1 := by funext w; simp [stirF]
      rw [this, iteratedDeriv_const]
      simp
    · rw [iteratedDeriv_succ', Nat.stirlingFirst_succ_succ]
      have h := (stirF_ode k).iteratedDeriv_eq n
      rw [iteratedDeriv_fun_sub (f := deriv (stirF (k + 1)))
        (g := fun w => w * deriv (stirF (k + 1)) w) (contDiffAt_deriv_stirF _ n)
        (contDiffAt_id.mul (contDiffAt_deriv_stirF _ n)),
        iteratedDeriv_id_mul_zero (contDiffAt_deriv_stirF _ n), ih k] at h
      rcases n with _ | n
      · simp at h ⊢; exact h
      · rw [show n + 1 - 1 = n by omega, ← iteratedDeriv_succ', ← iteratedDeriv_succ',
          ih (k + 1)] at h
        rw [← iteratedDeriv_succ']
        push_cast at h ⊢
        linear_combination h

/-- **The Stirling generating function**: `(−ln(1 − x))ᵏ/k! = ∑ₙ [n, k] xⁿ/n!`, `|x| < 1`. -/
theorem hasSum_stirlingFirst (k : ℕ) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n => (Nat.stirlingFirst n k : ℂ) * x ^ n / n !) (lambertLogL x ^ k / k !) := by
  have hd : DifferentiableOn ℂ (stirF k) (Metric.ball 0 1) := fun w hw =>
    (analyticAt_stirF k (by simpa using hw)).differentiableAt.differentiableWithinAt
  have h := Complex.hasSum_taylorSeries_on_ball hd (by simpa using hx)
  simp only [sub_zero, smul_eq_mul, iteratedDeriv_stirF] at h
  rw [show lambertLogL x ^ k / k ! = stirF k x from rfl]
  convert h using 2 with n
  ring

theorem lagL_ofReal {r : ℝ} (hr : r < 1) : lambertLogL r = ((-Real.log (1 - r) : ℝ) : ℂ) := by
  rw [lambertLogL, ofReal_neg, ofReal_log (by linarith)]; push_cast; rfl

/-- The real Stirling generating function, `0 ≤ r < 1`. -/
theorem hasSum_stirlingFirst_real (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    HasSum (fun n => (Nat.stirlingFirst n k : ℝ) * r ^ n / n !)
      ((-Real.log (1 - r)) ^ k / k !) := by
  have h := hasSum_stirlingFirst k (x := (r : ℂ)) (by rwa [norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0])
  rw [lagL_ofReal hr] at h
  rw [← hasSum_ofReal]
  convert h using 1
  · funext n; push_cast; rfl
  · push_cast; rfl

/-- `|L(w)ᵏ/k!| ≤ (−ln(1 − r))ᵏ/k!` for `|w| ≤ r < 1`. -/
theorem norm_stirF_le (k : ℕ) {w : ℂ} {r : ℝ} (hw : ‖w‖ ≤ r) (hr : r < 1) :
    ‖lambertLogL w ^ k / (k ! : ℂ)‖ ≤ (-Real.log (1 - r)) ^ k / k ! := by
  have hr0 : 0 ≤ r := (norm_nonneg w).trans hw
  refine (hasSum_stirlingFirst k (hw.trans_lt hr)).norm_le_of_bounded
    (hasSum_stirlingFirst_real k hr0 hr) fun n => ?_
  rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
  gcongr

theorem log_two_lt_one : Real.log 2 < 1 := by
  have := Real.log_two_lt_d9; linarith

/-- `|L(w)| ≤ ln 2` on `|w| ≤ 1/2`. -/
theorem norm_lagL_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) : ‖lambertLogL w‖ ≤ Real.log 2 := by
  have := norm_stirF_le 1 hw (by norm_num)
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at this
  rwa [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv, neg_neg] at this

theorem norm_inv_one_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) : ‖(1 - w)⁻¹‖ ≤ 2 := by
  have h1 : 1 / 2 ≤ ‖1 - w‖ := by
    have := norm_sub_norm_le (1 : ℂ) w
    rw [norm_one] at this; linarith
  rw [norm_inv]
  calc ‖1 - w‖⁻¹ ≤ (1 / 2)⁻¹ := inv_anti₀ (by norm_num) h1
    _ = 2 := by norm_num

/-- `|L(w) − L(u)| ≤ 2|w − u|` on `|w|, |u| ≤ 1/2`. -/
theorem norm_lagL_sub_le {w u : ℂ} (hw : ‖w‖ ≤ 1 / 2) (hu : ‖u‖ ≤ 1 / 2) :
    ‖lambertLogL w - lambertLogL u‖ ≤ 2 * ‖w - u‖ := by
  have hmem : ∀ {x : ℂ}, ‖x‖ ≤ 1 / 2 → x ∈ Metric.closedBall (0 : ℂ) (1 / 2) := fun h => by
    simpa using h
  refine (convex_closedBall (0 : ℂ) (1 / 2)).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hasDerivAt_lagL (by simp at hx; linarith)).differentiableAt) (fun x hx => ?_)
    (hmem hu) (hmem hw)
  rw [(hasDerivAt_lagL (by simp at hx; linarith)).deriv]
  exact norm_inv_one_sub_le (by simpa using hx)

/-! ### The argument principle for `w − τ + σ L(w)` -/

theorem norm_le_half_of_mem_closedBall {τ w : ℂ} (hτ : ‖τ‖ ≤ 1 / 8)
    (hw : w ∈ Metric.closedBall τ (3 / 8)) : ‖w‖ ≤ 1 / 2 := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have := norm_le_norm_add_norm_sub' w τ
  linarith

theorem closedBall_subset_ball_one {τ : ℂ} (hτ : ‖τ‖ ≤ 1 / 8) :
    Metric.closedBall τ (3 / 8) ⊆ Metric.ball 0 1 := fun w hw => by
  have := norm_le_half_of_mem_closedBall hτ hw
  rw [Metric.mem_ball, dist_zero_right]; linarith

/-- If `u = τ − σ L(u)` (with `|τ| ≤ 1/8`, `|σ| ≤ 1/4`, `|u| ≤ 1/2`), then
`L(u) = (2πi)⁻¹ ∮_{|w − τ| = 3/8} L(w) (1 + σ L′(w))/(w − τ + σ L(w)) dw`. -/
theorem lagL_eq_circleIntegral {σ τ u : ℂ} (hσ : ‖σ‖ ≤ 1 / 4) (hτ : ‖τ‖ ≤ 1 / 8)
    (hu : ‖u‖ ≤ 1 / 2) (heq : u = τ - σ * lambertLogL u) :
    (2 * π * I)⁻¹ * ∮ w in C(τ, 3 / 8),
      lambertLogL w * (1 + σ * (1 - w)⁻¹) / (w - τ + σ * lambertLogL w) = lambertLogL u := by
  have hl2 := log_two_lt_one
  have hl0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  -- `u` is inside the circle
  have huτ : u ∈ Metric.ball τ (3 / 8) := by
    rw [Metric.mem_ball, dist_eq_norm,
      show u - τ = -(σ * lambertLogL u) by linear_combination heq, norm_neg,
      norm_mul]
    calc ‖σ‖ * ‖lambertLogL u‖ ≤ 1 / 4 * Real.log 2 :=
          mul_le_mul hσ (norm_lagL_le hu) (norm_nonneg _) (by norm_num)
      _ < 3 / 8 := by linarith
  set D := Metric.ball (0 : ℂ) 1
  have hDu : D ∈ 𝓝 u := Metric.isOpen_ball.mem_nhds (by
    rw [Metric.mem_ball, dist_zero_right]; linarith)
  set q : ℂ → ℂ := fun w => 1 + σ * dslope lambertLogL u w
  have hqd : DifferentiableOn ℂ q D :=
    (differentiableOn_const _).add
      (((differentiableOn_dslope hDu).mpr differentiableOn_lagL).const_mul σ)
  -- `h = (w − u) q`
  have hfac : ∀ w, w - τ + σ * lambertLogL w = (w - u) * q w := by
    intro w
    have := sub_smul_dslope lambertLogL u w
    simp only [smul_eq_mul] at this
    simp only [q]
    linear_combination -σ * this + heq
  -- `|dslope L u w| ≤ 2`, hence `q ≠ 0`
  have hds : ∀ w, ‖w‖ ≤ 1 / 2 → ‖dslope lambertLogL u w‖ ≤ 2 := by
    intro w hw
    by_cases hwu : w = u
    · rw [hwu, dslope_same, (hasDerivAt_lagL (by linarith)).deriv]
      exact norm_inv_one_sub_le hu
    · rw [dslope_of_ne _ hwu, slope_def_field, norm_div]
      rw [div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hwu))]
      exact norm_lagL_sub_le hw hu
  have hq0 : ∀ w, ‖w‖ ≤ 1 / 2 → q w ≠ 0 := by
    intro w hw h
    have h1 : ‖σ * dslope lambertLogL u w‖ ≤ 1 / 2 := by
      rw [norm_mul]
      calc ‖σ‖ * ‖dslope lambertLogL u w‖ ≤ 1 / 4 * 2 := mul_le_mul hσ (hds w hw) (norm_nonneg _)
            (by norm_num)
        _ = 1 / 2 := by norm_num
    have h2 : σ * dslope lambertLogL u w = -1 := by simp only [q] at h; linear_combination h
    rw [h2, norm_neg, norm_one] at h1; norm_num at h1
  -- the logarithmic derivative splits
  have hB := closedBall_subset_ball_one hτ
  have hsplit : ∀ w ∈ Metric.sphere τ (3 / 8),
      lambertLogL w * (1 + σ * (1 - w)⁻¹) / (w - τ + σ * lambertLogL w) =
        (w - u)⁻¹ • lambertLogL w + lambertLogL w * deriv q w / q w := by
    intro w hw
    have hwB : w ∈ Metric.closedBall τ (3 / 8) := Metric.sphere_subset_closedBall hw
    have hw2 := norm_le_half_of_mem_closedBall hτ hwB
    have hwD : w ∈ D := hB hwB
    have hwu : w - u ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rw [← h, Metric.mem_ball] at huτ
      rw [Metric.mem_sphere] at hw
      linarith
    have hqw := hq0 w hw2
    -- `h′ = q + (w − u) q′`
    have hh : HasDerivAt (fun w => w - τ + σ * lambertLogL w) (1 + σ * (1 - w)⁻¹) w := by
      exact ((hasDerivAt_id w).sub_const τ).add ((hasDerivAt_lagL (by linarith)).const_mul σ)
    have hq' : HasDerivAt q (deriv q w) w :=
      (hqd.differentiableAt (Metric.isOpen_ball.mem_nhds hwD)).hasDerivAt
    have hh2 : HasDerivAt (fun w => w - τ + σ * lambertLogL w)
        (1 * q w + (w - u) * deriv q w) w := by
      have := ((hasDerivAt_id w).sub_const u).mul hq'
      simp only [id] at this
      exact this.congr_of_eventuallyEq (Eventually.of_forall fun x => hfac x)
    have hder := hh.unique hh2
    rw [hder, hfac w, smul_eq_mul]
    field_simp
  rw [circleIntegral.integral_congr (by norm_num) hsplit]
  have hLd : DifferentiableOn ℂ lambertLogL (Metric.closedBall τ (3 / 8)) :=
    differentiableOn_lagL.mono hB
  have hqD : DifferentiableOn ℂ (deriv q) D :=
    (hqd.analyticOnNhd Metric.isOpen_ball).deriv.differentiableOn
  have hg : DifferentiableOn ℂ (fun w => lambertLogL w * deriv q w / q w)
      (Metric.closedBall τ (3 / 8)) :=
    ((differentiableOn_lagL.mul hqD).mono hB).div (hqd.mono hB) fun w hw =>
      hq0 w (norm_le_half_of_mem_closedBall hτ hw)
  have hc1 : CircleIntegrable (fun w => (w - u)⁻¹ • lambertLogL w) τ (3 / 8) := by
    refine ContinuousOn.circleIntegrable (by norm_num) ?_
    refine ((continuousOn_id.sub continuousOn_const).inv₀ fun w hw => ?_).smul
      (hLd.continuousOn.mono Metric.sphere_subset_closedBall)
    intro h
    have h' : w = u := sub_eq_zero.mp h
    rw [← h', Metric.mem_ball] at huτ
    rw [Metric.mem_sphere] at hw
    linarith
  have hc2 : CircleIntegrable (fun w => lambertLogL w * deriv q w / q w) τ (3 / 8) :=
    ContinuousOn.circleIntegrable (by norm_num)
      (hg.continuousOn.mono Metric.sphere_subset_closedBall)
  rw [circleIntegral.integral_add hc1 hc2, hLd.circleIntegral_sub_inv_smul huτ,
    (hg.diffContOnCl_ball subset_rfl).circleIntegral_eq_zero (by norm_num), add_zero, smul_eq_mul]
  have : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  field_simp

/-! ### Exchanging a series and a circle integral -/

theorem hasSum_circleIntegral_of_bound {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {c : ℂ} {R : ℝ} {b : ℕ → ℝ}
    (hR : 0 ≤ R) (hf : ∀ n, ContinuousOn (f n) (Metric.sphere c R))
    (hb : ∀ n, ∀ w ∈ Metric.sphere c R, ‖f n w‖ ≤ b n) (hbs : Summable b)
    (hsum : ∀ w ∈ Metric.sphere c R, HasSum (fun n => f n w) (F w)) :
    HasSum (fun n => ∮ w in C(c, R), f n w) (∮ w in C(c, R), F w) := by
  simp only [circleIntegral]
  have hmem : ∀ θ, circleMap c R θ ∈ Metric.sphere c R := circleMap_mem_sphere c hR
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => R * b n)
    (fun n => ?_) (fun n => Eventually.of_forall fun θ _ => ?_)
    (Eventually.of_forall fun _ _ => hbs.mul_left R) intervalIntegrable_const
    (Eventually.of_forall fun θ _ => ((hsum _ (hmem θ)).const_smul _))
  · refine (Continuous.aestronglyMeasurable ?_)
    rw [show (fun θ => deriv (circleMap c R) θ • f n (circleMap c R θ)) =
      fun θ => (circleMap 0 R θ * I) • f n (circleMap c R θ) from funext fun θ => by
        rw [deriv_circleMap]]
    exact ((continuous_circleMap 0 R).mul continuous_const).smul
      ((hf n).comp_continuous (continuous_circleMap c R) hmem)
  · rw [norm_smul, deriv_circleMap, norm_mul, norm_I, mul_one, norm_circleMap_zero,
      abs_of_nonneg hR]
    exact mul_le_mul_of_nonneg_left (hb n _ (hmem θ)) hR

/-! ### The Lagrange reversion series -/

/-- `Dʲ(L^{j+1})(τ)`. -/
noncomputable def lagD (j : ℕ) (τ : ℂ) : ℂ := iteratedDeriv j (fun w => lambertLogL w ^ (j + 1)) τ

theorem differentiableOn_lagL_pow (n : ℕ) :
    DifferentiableOn ℂ (fun w => lambertLogL w ^ n) (Metric.ball 0 1) :=
  differentiableOn_lagL.pow n

theorem analyticAt_lagL {τ : ℂ} (hτ : ‖τ‖ < 1) : AnalyticAt ℂ lambertLogL τ :=
  differentiableOn_lagL.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hτ))

/-- `Dᵏ(L^{k+1}(1 + σL′))(τ) = Dᵏ(L^{k+1})(τ) + σ D^{k+1}(L^{k+2})(τ)/(k + 2)`. -/
theorem iteratedDeriv_lagL_pow_mul (k : ℕ) (σ : ℂ) {τ : ℂ} (hτ : ‖τ‖ < 1) :
    iteratedDeriv k (fun w => lambertLogL w ^ (k + 1) * (1 + σ * (1 - w)⁻¹)) τ =
      lagD k τ + σ * lagD (k + 1) τ / (k + 2) := by
  have hev : (fun w => lambertLogL w ^ (k + 1) * (1 + σ * (1 - w)⁻¹)) =ᶠ[𝓝 τ]
      fun w => lambertLogL w ^ (k + 1) +
        σ / (k + 2) * deriv (fun w => lambertLogL w ^ (k + 2)) w := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show τ ∈ Metric.ball (0 : ℂ) 1 by simpa using hτ)]
      with w hw
    have hw' : ‖w‖ < 1 := by simpa using hw
    rw [((hasDerivAt_lagL hw').fun_pow (k + 2)).deriv]
    have : ((k : ℂ) + 2) ≠ 0 := by exact_mod_cast (by omega : k + 2 ≠ 0)
    push_cast
    field_simp
  rw [hev.iteratedDeriv_eq]
  have hA := analyticAt_lagL hτ
  have h1 : ContDiffAt ℂ k (fun w => lambertLogL w ^ (k + 1)) τ := (hA.pow _).contDiffAt
  have h2 : ContDiffAt ℂ k (fun w => σ / (k + 2) * deriv (fun w => lambertLogL w ^ (k + 2)) w) τ :=
    contDiffAt_const.mul ((hA.pow _).deriv.contDiffAt)
  rw [iteratedDeriv_fun_add h1 h2, iteratedDeriv_const_mul_field, ← iteratedDeriv_succ']
  simp only [lagD]
  ring

theorem lagL_pow_differentiableOn_closedBall (n : ℕ) {τ : ℂ} (hτ : ‖τ‖ ≤ 1 / 8) :
    DifferentiableOn ℂ (fun w => lambertLogL w ^ n) (Metric.closedBall τ (3 / 8)) :=
  (differentiableOn_lagL_pow n).mono (closedBall_subset_ball_one hτ)

theorem continuousOn_inv_one_sub {τ : ℂ} (hτ : ‖τ‖ ≤ 1 / 8) :
    ContinuousOn (fun w : ℂ => (1 - w)⁻¹) (Metric.closedBall τ (3 / 8)) :=
  (continuousOn_const.sub continuousOn_id).inv₀ fun w hw h => by
    have := norm_le_half_of_mem_closedBall hτ hw
    have h' : (1 : ℂ) - w = 0 := h
    rw [sub_eq_zero] at h'; rw [← h', norm_one] at this; norm_num at this

/-- The Cauchy formula: `(2πi)⁻¹ ∮ L^{j+1}/(w − τ)^{j+1} = Dʲ(L^{j+1})(τ)/j!`. -/
theorem lagD_eq_circleIntegral (j : ℕ) {τ : ℂ} (hτ : ‖τ‖ ≤ 1 / 8) :
    (2 * π * I)⁻¹ * ∮ w in C(τ, 3 / 8), (1 / (w - τ) ^ (j + 1)) • lambertLogL w ^ (j + 1) =
      lagD j τ / j ! := by
  rw [(lagL_pow_differentiableOn_closedBall (j + 1) hτ).circleIntegral_one_div_sub_center_pow_smul
    (by norm_num) j, smul_eq_mul, lagD]
  have : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  field_simp

/-- `|Dʲ(L^{j+1})(τ)/j!| ≤ (ln 2)^{j+1}/(3/8)ʲ`. -/
theorem norm_lagD_div_le (j : ℕ) {τ : ℂ} (hτ : ‖τ‖ ≤ 1 / 8) :
    ‖lagD j τ / (j ! : ℂ)‖ ≤ Real.log 2 ^ (j + 1) / (3 / 8) ^ j := by
  rw [← lagD_eq_circleIntegral j hτ]
  have hb : ∀ w ∈ Metric.sphere τ (3 / 8),
      ‖(1 / (w - τ) ^ (j + 1)) • lambertLogL w ^ (j + 1)‖ ≤
        Real.log 2 ^ (j + 1) / (3 / 8) ^ (j + 1) := by
    intro w hw
    have hw2 := norm_le_half_of_mem_closedBall hτ (Metric.sphere_subset_closedBall hw)
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    rw [smul_eq_mul, norm_mul, norm_div, norm_one, norm_pow, hw, norm_pow, one_div_mul_eq_div]
    gcongr
    exact norm_lagL_le hw2
  have h := circleIntegral.norm_integral_le_of_norm_le_const (by norm_num) hb
  rw [norm_mul, norm_inv]
  have hn : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    rw [norm_mul, norm_I, mul_one, norm_mul, Complex.norm_ofNat, norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hn]
  have hπ := Real.pi_pos
  calc (2 * π)⁻¹ * ‖∮ w in C(τ, 3 / 8), (1 / (w - τ) ^ (j + 1)) • lambertLogL w ^ (j + 1)‖
      ≤ (2 * π)⁻¹ * (2 * π * (3 / 8) * (Real.log 2 ^ (j + 1) / (3 / 8) ^ (j + 1))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = Real.log 2 ^ (j + 1) / (3 / 8) ^ j := by field_simp; ring

theorem geom_term_eq (k : ℕ) {a b c d : ℂ} (hd : d ≠ 0) :
    (1 / d ^ (k + 1)) * (a ^ k * (b ^ (k + 1) * c)) = b * c / d * (a * b / d) ^ k := by
  rw [div_pow, mul_pow, pow_succ, pow_succ]
  field_simp

/-- **Lagrange reversion** for `u = τ − σ L(u)`:
`L(u) = ∑ⱼ (−σ)ʲ Dʲ(L^{j+1})(τ)/(j + 1)!` (`|σ| ≤ 1/4`, `|τ| ≤ 1/8`, `|u| ≤ 1/2`). -/
theorem hasSum_lambert_lagrange {σ τ u : ℂ} (hσ : ‖σ‖ ≤ 1 / 4) (hτ : ‖τ‖ ≤ 1 / 8)
    (hu : ‖u‖ ≤ 1 / 2) (heq : u = τ - σ * lambertLogL u) :
    HasSum (fun j => (-σ) ^ j * lagD j τ / (j + 1)!) (lambertLogL u) := by
  have hl2 := log_two_lt_one
  have hl0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hτ1 : ‖τ‖ < 1 := by linarith
  set ρ0 : ℝ := 1 / 4 * Real.log 2 / (3 / 8)
  have hρ0 : ρ0 < 1 := by simp only [ρ0]; linarith
  have hρ00 : 0 ≤ ρ0 := by positivity
  set G : ℂ → ℂ := fun w => lambertLogL w * (1 + σ * (1 - w)⁻¹) / (w - τ + σ * lambertLogL w)
  set f : ℕ → ℂ → ℂ := fun k w =>
    (1 / (w - τ) ^ (k + 1)) • ((-σ) ^ k * (lambertLogL w ^ (k + 1) * (1 + σ * (1 - w)⁻¹)))
  -- pointwise expansion on the circle
  have hpt : ∀ w ∈ Metric.sphere τ (3 / 8), HasSum (fun k => f k w) (G w) := by
    intro w hw
    have hw2 := norm_le_half_of_mem_closedBall hτ (Metric.sphere_subset_closedBall hw)
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    have hwτ : w - τ ≠ 0 := fun h => by rw [h, norm_zero] at hw; norm_num at hw
    set r := -σ * lambertLogL w / (w - τ)
    have hr : ‖r‖ ≤ ρ0 := by
      simp only [r, ρ0, norm_div, norm_mul, norm_neg, hw]
      gcongr
      exact norm_lagL_le hw2
    have hg := (hasSum_geometric_of_norm_lt_one (hr.trans_lt hρ0)).mul_left
      (lambertLogL w * (1 + σ * (1 - w)⁻¹) / (w - τ))
    have h1r : 1 - r ≠ 0 := fun h => by
      have : r = 1 := by linear_combination -h
      rw [this, norm_one] at hr; linarith
    convert hg using 1
    · funext k
      simp only [f, r, smul_eq_mul]
      exact geom_term_eq k hwτ
    · simp only [G, r]
      have hh : w - τ + σ * lambertLogL w = (w - τ) * (1 - -σ * lambertLogL w / (w - τ)) := by
        field_simp; ring
      rw [hh]
      field_simp
  -- bound
  set b : ℕ → ℝ := fun k => 3 / 2 * Real.log 2 / (3 / 8) * ρ0 ^ k
  have hbound : ∀ k, ∀ w ∈ Metric.sphere τ (3 / 8), ‖f k w‖ ≤ b k := by
    intro k w hw
    have hw2 := norm_le_half_of_mem_closedBall hτ (Metric.sphere_subset_closedBall hw)
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    have h1 : ‖1 + σ * (1 - w)⁻¹‖ ≤ 3 / 2 := by
      calc ‖1 + σ * (1 - w)⁻¹‖ ≤ 1 + ‖σ‖ * ‖(1 - w)⁻¹‖ := by
            rw [← norm_mul]; simpa using norm_add_le (1 : ℂ) (σ * (1 - w)⁻¹)
        _ ≤ 1 + 1 / 4 * 2 := by
            gcongr
            exact norm_inv_one_sub_le hw2
        _ = 3 / 2 := by norm_num
    have hL := norm_lagL_le hw2
    simp only [f, b, ρ0, smul_eq_mul, norm_mul, norm_div, norm_one, norm_pow, norm_neg, hw]
    calc 1 / (3 / 8) ^ (k + 1) * (‖σ‖ ^ k * (‖lambertLogL w‖ ^ (k + 1) * ‖1 + σ * (1 - w)⁻¹‖))
        ≤ 1 / (3 / 8) ^ (k + 1) * ((1 / 4) ^ k * (Real.log 2 ^ (k + 1) * (3 / 2))) := by
          gcongr
      _ = 3 / 2 * Real.log 2 / (3 / 8) * (1 / 4 * Real.log 2 / (3 / 8)) ^ k := by
          rw [show (1 / 4 * Real.log 2 / (3 / 8)) ^ k = (1 / 4) ^ k * Real.log 2 ^ k / (3 / 8) ^ k
            by rw [div_pow, mul_pow], pow_succ, pow_succ]
          field_simp
  have hbs : Summable b := (summable_geometric_of_lt_one hρ00 hρ0).mul_left _
  have hcont : ∀ k, ContinuousOn (f k) (Metric.sphere τ (3 / 8)) := by
    intro k
    have hS := Metric.sphere_subset_closedBall (x := τ) (ε := 3 / 8)
    show ContinuousOn (fun w => (1 / (w - τ) ^ (k + 1)) •
      ((-σ) ^ k * (lambertLogL w ^ (k + 1) * (1 + σ * (1 - w)⁻¹)))) _
    refine ContinuousOn.smul (f := fun w => 1 / (w - τ) ^ (k + 1))
      (g := fun w => (-σ) ^ k * (lambertLogL w ^ (k + 1) * (1 + σ * (1 - w)⁻¹))) ?_ ?_
    · refine continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow _) fun w hw => ?_
      rw [Metric.mem_sphere, dist_eq_norm] at hw
      exact pow_ne_zero _ fun h => by rw [h, norm_zero] at hw; norm_num at hw
    · exact continuousOn_const.mul (((lagL_pow_differentiableOn_closedBall (k + 1)
        hτ).continuousOn.mono hS).mul (continuousOn_const.add (continuousOn_const.mul
          ((continuousOn_inv_one_sub hτ).mono hS))))
  have hint := hasSum_circleIntegral_of_bound (by norm_num) hcont hbound hbs hpt
  have hint2 := hint.mul_left (2 * π * I)⁻¹
  rw [lagL_eq_circleIntegral hσ hτ hu heq] at hint2
  -- each coefficient
  have hcoef : ∀ k, (2 * π * I)⁻¹ * ∮ w in C(τ, 3 / 8), f k w =
      (-σ) ^ k * (lagD k τ + σ * lagD (k + 1) τ / (k + 2)) / k ! := by
    intro k
    have hd : DifferentiableOn ℂ (fun w => lambertLogL w ^ (k + 1) * (1 + σ * (1 - w)⁻¹))
        (Metric.closedBall τ (3 / 8)) := by
      refine (lagL_pow_differentiableOn_closedBall (k + 1) hτ).mul ?_
      refine (differentiableOn_const _).add ((differentiableOn_const _).mul ?_)
      refine ((differentiableOn_const _).sub differentiableOn_id).inv fun w hw h => ?_
      have := norm_le_half_of_mem_closedBall hτ hw
      rw [sub_eq_zero] at h; rw [← h, norm_one] at this; norm_num at this
    have hc := hd.circleIntegral_one_div_sub_center_pow_smul (by norm_num : (0 : ℝ) < 3 / 8) k
    rw [iteratedDeriv_lagL_pow_mul k σ hτ1] at hc
    have hf : ∀ w, f k w = (-σ) ^ k * ((1 / (w - τ) ^ (k + 1)) •
        (lambertLogL w ^ (k + 1) * (1 + σ * (1 - w)⁻¹))) := fun w => by
      simp only [f, smul_eq_mul]; ring
    simp only [hf]
    rw [circleIntegral.integral_const_mul, hc, smul_eq_mul]
    have : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    field_simp
  simp only [hcoef] at hint2
  -- telescoping
  set A : ℕ → ℂ := fun j => (-σ) ^ j * lagD j τ / (j ! : ℂ)
  set B : ℕ → ℂ := fun j => (-σ) ^ j * lagD j τ / (j + 1)!
  have hAB : ∀ j, A j = (j + 1) * B j := fun j => by
    simp only [A, B, Nat.factorial_succ]; push_cast
    have : (j ! : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    field_simp
  have hterm : ∀ k, (-σ) ^ k * (lagD k τ + σ * lagD (k + 1) τ / (k + 2)) / k ! =
      (k + 1) * B k - (k + 1) * B (k + 1) := by
    intro k
    simp only [B, Nat.factorial_succ]; push_cast
    have : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have h2 : ((k : ℂ) + 2) ≠ 0 := by exact_mod_cast (by omega : k + 2 ≠ 0)
    have h1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast (by omega : k + 1 ≠ 0)
    have h3 : (k : ℂ) + 1 + 1 ≠ 0 := by rw [add_assoc, one_add_one_eq_two]; exact h2
    rw [pow_succ, show (k : ℂ) + 1 + 1 = k + 2 by ring]
    field_simp
    ring
  simp only [hterm] at hint2
  have hAn : ∀ j, ‖A j‖ ≤ Real.log 2 * ρ0 ^ j := by
    intro j
    simp only [A, mul_div_assoc, norm_mul, norm_pow, norm_neg]
    have := norm_lagD_div_le j hτ
    calc ‖σ‖ ^ j * ‖lagD j τ / (j ! : ℂ)‖ ≤ (1 / 4) ^ j * (Real.log 2 ^ (j + 1) / (3 / 8) ^ j) := by
          gcongr
      _ = Real.log 2 * ρ0 ^ j := by
          simp only [ρ0]
          rw [show (1 / 4 * Real.log 2 / (3 / 8)) ^ j = (1 / 4) ^ j * Real.log 2 ^ j / (3 / 8) ^ j
            by rw [div_pow, mul_pow], pow_succ]
          field_simp
  have hBn : ∀ j, ‖B j‖ ≤ ‖A j‖ := by
    intro j
    rw [hAB j, norm_mul]
    have : (1 : ℝ) ≤ ‖((j : ℂ) + 1)‖ := by
      rw [show ((j : ℂ) + 1) = ((j + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      exact_mod_cast Nat.le_add_left 1 j
    nlinarith [norm_nonneg (B j)]
  have hBs : Summable B := Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hρ00 hρ0).mul_left (Real.log 2))
    fun j => (hBn j).trans (hAn j)
  -- partial sums
  have hpartial : ∀ N, ∑ k ∈ range N, ((k + 1) * B k - (k + 1) * B (k + 1)) =
      ∑ k ∈ range N, B k - N * B N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [sum_range_succ, ih, sum_range_succ]; push_cast; ring
  rw [hBs.hasSum_iff_tendsto_nat]
  have h1 := hint2.tendsto_sum_nat
  simp only [hpartial] at h1
  have h2 : Tendsto (fun N : ℕ => (N : ℂ) * B N) atTop (𝓝 0) := by
    have hA0 : Tendsto (fun N => ‖A N‖) atTop (𝓝 0) := by
      refine squeeze_zero (fun _ => norm_nonneg _) hAn ?_
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ00 hρ0).const_mul (Real.log 2)
    refine squeeze_zero_norm (fun N => ?_) hA0
    rw [norm_mul, hAB N, norm_mul]
    have h3 : ‖(N : ℂ)‖ ≤ ‖((N : ℂ) + 1)‖ := by
      rw [Complex.norm_natCast, show ((N : ℂ) + 1) = ((N + 1 : ℕ) : ℂ) by push_cast; ring,
        Complex.norm_natCast]
      exact_mod_cast Nat.le_succ N
    exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
  have := h1.add h2
  simp only [sub_add_cancel, add_zero] at this
  exact this

/-! ### The coefficients in Stirling numbers -/

/-- `Dʲ(L^{j+1})(τ)/(j + 1)! = ∑ₘ [m + j, j + 1] τᵐ/m!`. -/
theorem hasSum_lagD_div (j : ℕ) {τ : ℂ} (hτ : ‖τ‖ ≤ 1 / 8) :
    HasSum (fun m => (Nat.stirlingFirst (m + j) (j + 1) : ℂ) * τ ^ m / m !)
      (lagD j τ / (j + 1)!) := by
  have hl0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  set f : ℕ → ℂ → ℂ := fun n w => (1 / (w - τ) ^ (j + 1)) •
    (((j + 1)! : ℂ) * ((Nat.stirlingFirst n (j + 1) : ℂ) * w ^ n / n !))
  have hpt : ∀ w ∈ Metric.sphere τ (3 / 8),
      HasSum (fun n => f n w) ((1 / (w - τ) ^ (j + 1)) • lambertLogL w ^ (j + 1)) := by
    intro w hw
    have hw2 := norm_le_half_of_mem_closedBall hτ (Metric.sphere_subset_closedBall hw)
    have h := ((hasSum_stirlingFirst (j + 1) (x := w) (by linarith)).mul_left
      ((j + 1)! : ℂ)).const_smul (1 / (w - τ) ^ (j + 1))
    convert h using 2
    have : ((j + 1)! : ℂ) ≠ 0 := by exact_mod_cast (j + 1).factorial_ne_zero
    field_simp
  set b : ℕ → ℝ := fun n => 1 / (3 / 8) ^ (j + 1) * ((j + 1)! *
    ((Nat.stirlingFirst n (j + 1) : ℝ) * (1 / 2) ^ n / n !))
  have hbound : ∀ n, ∀ w ∈ Metric.sphere τ (3 / 8), ‖f n w‖ ≤ b n := by
    intro n w hw
    have hw2 := norm_le_half_of_mem_closedBall hτ (Metric.sphere_subset_closedBall hw)
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    simp only [f, b, smul_eq_mul, norm_mul, norm_div, norm_one, norm_pow, hw, Complex.norm_natCast]
    gcongr
  have hbs : Summable b :=
    ((hasSum_stirlingFirst_real (j + 1) (r := 1 / 2) (by norm_num) (by norm_num)).summable.mul_left
      _).mul_left _
  have hcont : ∀ n, ContinuousOn (f n) (Metric.sphere τ (3 / 8)) := by
    intro n
    show ContinuousOn (fun w => (1 / (w - τ) ^ (j + 1)) •
      (((j + 1)! : ℂ) * ((Nat.stirlingFirst n (j + 1) : ℂ) * w ^ n / n !))) _
    refine ContinuousOn.smul (f := fun w => 1 / (w - τ) ^ (j + 1))
      (g := fun w => ((j + 1)! : ℂ) * ((Nat.stirlingFirst n (j + 1) : ℂ) * w ^ n / n !)) ?_
      (by fun_prop)
    refine continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow _) fun w hw => ?_
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    exact pow_ne_zero _ fun h => by rw [h, norm_zero] at hw; norm_num at hw
  have hint := (hasSum_circleIntegral_of_bound (by norm_num) hcont hbound hbs hpt).mul_left
    (2 * π * I)⁻¹
  rw [lagD_eq_circleIntegral j hτ] at hint
  -- the coefficient integrals
  have hcoef : ∀ n, (2 * π * I)⁻¹ * ∮ w in C(τ, 3 / 8), f n w =
      ((j + 1)! : ℂ) * ((Nat.stirlingFirst n (j + 1) : ℂ) / n !) *
        ((n.descFactorial j : ℂ) * τ ^ (n - j)) / j ! := by
    intro n
    have hd : DifferentiableOn ℂ (fun w : ℂ => w ^ n) (Metric.closedBall τ (3 / 8)) :=
      (differentiable_pow n).differentiableOn
    have hc := hd.circleIntegral_one_div_sub_center_pow_smul (by norm_num : (0 : ℝ) < 3 / 8) j
    rw [iteratedDeriv_pow] at hc
    have hf : ∀ w, f n w = ((j + 1)! : ℂ) * ((Nat.stirlingFirst n (j + 1) : ℂ) / n !) *
        ((1 / (w - τ) ^ (j + 1)) • w ^ n) := fun w => by
      simp only [f, smul_eq_mul]; ring
    simp only [hf]
    rw [circleIntegral.integral_const_mul, hc, smul_eq_mul]
    have : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    field_simp
  simp only [hcoef] at hint
  have hj1 : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero j)
  have hint2 := hint.div_const ((j : ℂ) + 1)
  rw [show lagD j τ / (j ! : ℂ) / ((j : ℂ) + 1) = lagD j τ / (j + 1)! by
    rw [Nat.factorial_succ]; push_cast; field_simp] at hint2
  rw [← hasSum_nat_add_iff' j] at hint2
  have hz : ∑ i ∈ range j, ((j + 1)! : ℂ) * ((Nat.stirlingFirst i (j + 1) : ℂ) / i !) *
      ((i.descFactorial j : ℂ) * τ ^ (i - j)) / j ! / ((j : ℂ) + 1) = 0 := by
    refine sum_eq_zero fun i hi => ?_
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (mem_range.mp hi)]
    simp
  rw [hz, sub_zero] at hint2
  convert hint2 using 1
  funext m
  have hdesc : ((m + j).descFactorial j : ℂ) * (m ! : ℂ) = ((m + j)! : ℂ) := by
    have := Nat.factorial_mul_descFactorial (n := m + j) (k := j) (by omega)
    rw [show m + j - j = m by omega] at this
    exact_mod_cast (by rw [mul_comm]; exact this)
  rw [show m + j - j = m by omega, Nat.factorial_succ]
  push_cast
  have h1 : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have h2 : ((m + j)! : ℂ) ≠ 0 := by exact_mod_cast (m + j).factorial_ne_zero
  have h3 : (j ! : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  rw [← hdesc]
  field_simp

/-! ### The double series -/

/-- `[n, k] ≤ n! 2ⁿ (ln 2)ᵏ/k!`. -/
theorem stirlingFirst_le (n k : ℕ) :
    (Nat.stirlingFirst n k : ℝ) ≤ n ! * 2 ^ n * Real.log 2 ^ k / k ! := by
  have h := hasSum_stirlingFirst_real k (r := 1 / 2) (by norm_num) (by norm_num)
  rw [show -Real.log (1 - 1 / 2) = Real.log 2 by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv, neg_neg]] at h
  have hle := le_hasSum h n fun _ _ => by positivity
  have hn : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  rw [div_le_iff₀ hn] at hle
  calc (Nat.stirlingFirst n k : ℝ) = Nat.stirlingFirst n k * (1 / 2) ^ n * 2 ^ n := by
        rw [mul_assoc, ← mul_pow]; norm_num
    _ ≤ Real.log 2 ^ k / k ! * n ! * 2 ^ n := by gcongr
    _ = _ := by ring

/-- The terms `(−σ)ʲ [m + j, j + 1] τᵐ/m!` of the double series. -/
noncomputable def lambertT (σ τ : ℂ) (j m : ℕ) : ℂ :=
  (-σ) ^ j * Nat.stirlingFirst (m + j) (j + 1) * τ ^ m / m !

theorem norm_lambertT_le (σ τ : ℂ) (j m : ℕ) :
    ‖lambertT σ τ j m‖ ≤ Real.log 2 * (4 * Real.log 2 * ‖σ‖) ^ j * (4 * ‖τ‖) ^ m := by
  have hst := stirlingFirst_le (m + j) (j + 1)
  have hfac : ((m + j)! : ℝ) ≤ 2 ^ (m + j) * (j + 1)! * m ! := by
    have h1 := Nat.add_choose_mul_factorial_mul_factorial m j
    have h2 := Nat.choose_le_two_pow (m + j) j
    have h3 : (j ! : ℝ) ≤ (j + 1)! := by exact_mod_cast Nat.factorial_le (Nat.le_succ j)
    have h1' : ((m + j)! : ℝ) = ((m + j).choose j : ℝ) * m ! * j ! := by exact_mod_cast h1.symm
    rw [h1']
    have hc : ((m + j).choose j : ℝ) ≤ 2 ^ (m + j) := by exact_mod_cast h2
    have hm : (0 : ℝ) ≤ m ! := by positivity
    calc ((m + j).choose j : ℝ) * m ! * j ! ≤ 2 ^ (m + j) * m ! * (j + 1)! := by gcongr
      _ = _ := by ring
  have hm : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
  have hj : (0 : ℝ) < (j + 1)! := by exact_mod_cast (j + 1).factorial_pos
  rw [lambertT, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, Complex.norm_natCast,
    Complex.norm_natCast, div_le_iff₀ hm]
  have hl0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  calc ‖σ‖ ^ j * (Nat.stirlingFirst (m + j) (j + 1) : ℝ) * ‖τ‖ ^ m
      ≤ ‖σ‖ ^ j * ((m + j)! * 2 ^ (m + j) * Real.log 2 ^ (j + 1) / (j + 1)!) * ‖τ‖ ^ m := by
        gcongr
    _ ≤ ‖σ‖ ^ j * (2 ^ (m + j) * (j + 1)! * m ! * 2 ^ (m + j) * Real.log 2 ^ (j + 1) / (j + 1)!) *
        ‖τ‖ ^ m := by gcongr
    _ = Real.log 2 * (4 * Real.log 2 * ‖σ‖) ^ j * (4 * ‖τ‖) ^ m * m ! := by
        field_simp
        rw [mul_pow, mul_pow, mul_pow, ← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
          ← pow_mul]
        ring

theorem summable_lambertT {σ τ : ℂ} (hσ : ‖σ‖ ≤ 1 / 4) (hτ : ‖τ‖ ≤ 1 / 8) :
    Summable fun p : ℕ × ℕ => ‖lambertT σ τ p.1 p.2‖ := by
  have hl2 := log_two_lt_one
  have hl0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have ha : 4 * Real.log 2 * ‖σ‖ < 1 := by nlinarith [norm_nonneg σ]
  have hb : 4 * ‖τ‖ < 1 := by linarith
  have hs := summable_mul_of_summable_norm
    (f := fun j : ℕ => Real.log 2 * (4 * Real.log 2 * ‖σ‖) ^ j) (g := fun m : ℕ => (4 * ‖τ‖) ^ m)
    (by simpa [abs_of_nonneg hl0.le, abs_of_nonneg (norm_nonneg σ)] using
      (summable_geometric_of_lt_one (by positivity) ha).mul_left (Real.log 2))
    (by simpa [abs_of_nonneg (norm_nonneg τ)] using
      summable_geometric_of_lt_one (by positivity) hb)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => norm_lambertT_le σ τ p.1 p.2) hs

/-- The double series over `ℕ × ℕ` sums to `L(u)`. -/
theorem hasSum_lambertT {σ τ u : ℂ} (hσ : ‖σ‖ ≤ 1 / 4) (hτ : ‖τ‖ ≤ 1 / 8)
    (hu : ‖u‖ ≤ 1 / 2) (heq : u = τ - σ * lambertLogL u) :
    HasSum (fun p : ℕ × ℕ => lambertT σ τ p.1 p.2) (lambertLogL u) := by
  have hS := (summable_lambertT hσ hτ).of_norm
  have hfib : ∀ j, HasSum (fun m => lambertT σ τ j m) ((-σ) ^ j * lagD j τ / (j + 1)!) := by
    intro j
    have := (hasSum_lagD_div j hτ).mul_left ((-σ) ^ j)
    convert this using 1
    · funext m; simp only [lambertT]; ring
    · ring
  have h := hS.hasSum.prod_fiberwise hfib
  rw [← h.unique (hasSum_lambert_lagrange hσ hτ hu heq)]
  exact hS.hasSum

/-- DLMF's grouping: `∑_{m=1}^{n} (−1)^{n+m} [n, n − m + 1] τᵐ σ^{n−m}/m!`. -/
noncomputable def lambertInner (σ τ : ℂ) (n : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 n, (-1) ^ (n + m) * Nat.stirlingFirst n (n - m + 1) * τ ^ m * σ ^ (n - m) / m !

theorem sum_antidiagonal_lambertT (σ τ : ℂ) (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n, lambertT σ τ p.1 p.2 = lambertInner σ τ n := by
  rw [← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun m j => lambertT σ τ j m), sum_range_succ']
  have h0 : lambertT σ τ (n - 0) 0 = 0 := by
    simp [lambertT, Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self n)]
  rw [h0, add_zero, lambertInner, ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  rw [show 1 + k = k + 1 by ring, lambertT, show k + 1 + (n - (k + 1)) = n by omega,
    show n - (k + 1) + 1 = n - (k + 1) + 1 from rfl]
  have hs : ((-1 : ℂ) ^ (n + (k + 1))) = (-1) ^ (n - (k + 1)) := by
    rw [show n + (k + 1) = n - (k + 1) + 2 * (k + 1) by omega, pow_add, pow_mul]; norm_num
  rw [hs, neg_pow σ]
  ring

/-- **The core expansion**: if `u = τ − σ L(u)` (`|σ| ≤ 1/4`, `|τ| ≤ 1/8`, `|u| ≤ 1/2`), then
`L(u) = ∑_{n ≥ 1} ∑_{m=1}^{n} (−1)^{n+m} [n, n − m + 1] τᵐ σ^{n−m}/m!`. -/
theorem hasSum_lambertInner {σ τ u : ℂ} (hσ : ‖σ‖ ≤ 1 / 4) (hτ : ‖τ‖ ≤ 1 / 8)
    (hu : ‖u‖ ≤ 1 / 2) (heq : u = τ - σ * lambertLogL u) :
    HasSum (lambertInner σ τ) (lambertLogL u) := by
  have h := hasSum_lambertT hσ hτ hu heq
  have h2 := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.mpr h).sigma
    (fun n => Finset.hasSum (Finset.antidiagonal n) (fun p => lambertT σ τ p.1 p.2))
  simp only [sum_antidiagonal_lambertT] at h2
  exact h2

/-- `|∑_m …| ≤ (n + 1)(4ρ)ⁿ`, `ρ = max(|σ|, |τ|)`. -/
theorem norm_lambertInner_le (σ τ : ℂ) (n : ℕ) :
    ‖lambertInner σ τ n‖ ≤ (n + 1) * (4 * max ‖σ‖ ‖τ‖) ^ n := by
  rw [← sum_antidiagonal_lambertT]
  have hl2 := log_two_lt_one
  have hl0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hterm : ∀ p ∈ Finset.antidiagonal n,
      ‖lambertT σ τ p.1 p.2‖ ≤ (4 * max ‖σ‖ ‖τ‖) ^ n := by
    intro p hp
    have hpn := Finset.mem_antidiagonal.mp hp
    refine (norm_lambertT_le σ τ p.1 p.2).trans ?_
    have h1 : 4 * Real.log 2 * ‖σ‖ ≤ 4 * max ‖σ‖ ‖τ‖ := by
      have := le_max_left ‖σ‖ ‖τ‖
      nlinarith [norm_nonneg σ]
    have h2 : 4 * ‖τ‖ ≤ 4 * max ‖σ‖ ‖τ‖ := by linarith [le_max_right ‖σ‖ ‖τ‖]
    calc Real.log 2 * (4 * Real.log 2 * ‖σ‖) ^ p.1 * (4 * ‖τ‖) ^ p.2
        ≤ 1 * (4 * max ‖σ‖ ‖τ‖) ^ p.1 * (4 * max ‖σ‖ ‖τ‖) ^ p.2 := by
          gcongr
      _ = (4 * max ‖σ‖ ‖τ‖) ^ n := by rw [one_mul, ← pow_add, hpn]
  calc ‖∑ p ∈ Finset.antidiagonal n, lambertT σ τ p.1 p.2‖
      ≤ ∑ p ∈ Finset.antidiagonal n, ‖lambertT σ τ p.1 p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ Finset.antidiagonal n, (4 * max ‖σ‖ ‖τ‖) ^ n := sum_le_sum hterm
    _ = (n + 1) * (4 * max ‖σ‖ ‖τ‖) ^ n := by
        rw [sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]; push_cast; ring

end Azurite.DLMF
