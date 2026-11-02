/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section10Darboux
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# DLMF §2.10(iv): the Example 2.10.33–2.10.36 (Legendre polynomials by Darboux's method)

For `α ∈ (0, π)` (DLMF: `(0, 2π)`; see `dlmf_2_10_36_false` and `docs/dlmf_errata.md`):

* Legendre polynomials `Pₙ` (`legendreP`) by the recurrence
  `(n+1)P_{n+1}(x) = (2n+1)xPₙ(x) − nP_{n−1}(x)`, `P₀ = 1`, `P₁ = x` (§18.9).
* 2.10.33 (`dlmf_2_10_33`): `f(z) = (1 − 2z cos α + z²)^{−1/2} = ∑ Pₙ(cos α) zⁿ`, `|z| < 1`, where
  `f = (1 − ze^{iα})^{−1/2}(1 − ze^{−iα})^{−1/2}` (principal powers) is the branch with `f(0) = 1`
  (`legendreGen`, `legendreGen_sq`). The Taylor coefficients are identified through the linear ODE
  `(1 − 2z cos α + z²) f′ = (cos α − z) f` (`laurentCoeff_ode`).
* 2.10.34 (`legendreCmp`): `g(z) = e^{−πi/4}(2 sin α)^{−1/2}(e^{−iα} − z)^{−1/2}
  + e^{πi/4}(2 sin α)^{−1/2}(e^{iα} − z)^{−1/2}` with the branches of DLMF
  (`(e^{∓iα} − z)^{−1/2} = e^{±iα/2}(1 − ze^{±iα})^{−1/2}`).
* 2.10.35 (`dlmf_2_10_35`): `gₙ = (2/(π sin α))^{1/2} Γ(n+½)/n! cos(nα + ½α − ¼π)`.
* (b´) with `m = 1` (`legendre_darbouxCond`): `f′ − g′ = O((z − e^{∓iα})^{−1/2})`.
* 2.10.36 (`dlmf_2_10_36`): `Pₙ(cos α) = (2/(πn sin α))^{1/2} cos(nα + ½α − ¼π) + o(n^{−1})`,
  from `dlmf_2_10_31` and the bounds `(n+½)^{−1/2} ≤ Γ(n+½)/n! ≤ n^{−1/2}` (log-convexity of `Γ`,
  in place of 5.11.7).
-/

open Filter Topology Set Metric Complex MeasureTheory Finset
open scoped Real

namespace Azurite.DLMF

/-! ### Coefficient calculus on the unit disk -/

section Coeff

variable {G : ℂ → ℂ} {ρ : ℝ}

theorem laurentCoeff_add' {G₁ G₂ : ℂ → ℂ} (hρ : 0 < ρ) (h₁ : ContinuousOn G₁ (sphere 0 ρ))
    (h₂ : ContinuousOn G₂ (sphere 0 ρ)) (n : ℤ) :
    laurentCoeff (fun z => G₁ z + G₂ z) 0 ρ n = laurentCoeff G₁ 0 ρ n + laurentCoeff G₂ 0 ρ n := by
  have hz : ∀ z ∈ sphere (0 : ℂ) ρ, z - 0 ≠ 0 := fun z hz h => by
    rw [sub_zero] at h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hz; linarith
  have hc : ∀ {H : ℂ → ℂ}, ContinuousOn H (sphere 0 ρ) →
      CircleIntegrable (fun z => H z / (z - 0) ^ (n + 1)) 0 ρ := fun {H} hH =>
    ContinuousOn.circleIntegrable hρ.le (hH.div ((continuous_sub_right (0 : ℂ)).continuousOn.zpow₀
      _ fun z hz' => Or.inl (hz z hz')) fun z hz' => zpow_ne_zero _ (hz z hz'))
  unfold laurentCoeff
  rw [← mul_add, ← circleIntegral.integral_add (hc h₁) (hc h₂)]
  congr 1
  refine circleIntegral.integral_congr hρ.le fun z _ => ?_
  simp only [add_div]

theorem laurentCoeff_const_mul (c : ℂ) (G : ℂ → ℂ) (ρ : ℝ) (n : ℤ) :
    laurentCoeff (fun z => c * G z) 0 ρ n = c * laurentCoeff G 0 ρ n := by
  simp only [laurentCoeff, mul_div_assoc, circleIntegral.integral_const_mul]
  ring

/-- `(zG)ₙ = G_{n−1}`. -/
theorem laurentCoeff_mul_id (G : ℂ → ℂ) (hρ : 0 < ρ) (n : ℤ) :
    laurentCoeff (fun z => z * G z) 0 ρ n = laurentCoeff G 0 ρ (n - 1) := by
  unfold laurentCoeff
  congr 1
  refine circleIntegral.integral_congr hρ.le fun z hz => ?_
  have hz0 : z ≠ 0 := fun h => by rw [h, mem_sphere_zero_iff_norm, norm_zero] at hz; linarith
  simp only [sub_zero, sub_add_cancel]
  rw [zpow_add_one₀ hz0]
  field_simp

theorem laurentCoeff_congr {G₁ G₂ : ℂ → ℂ} (hρ : 0 ≤ ρ) (h : EqOn G₁ G₂ (sphere 0 ρ)) (n : ℤ) :
    laurentCoeff G₁ 0 ρ n = laurentCoeff G₂ 0 ρ n := by
  unfold laurentCoeff
  congr 1
  exact circleIntegral.integral_congr hρ fun z hz => by simp only [h hz]

variable (hG : DifferentiableOn ℂ G (ball 0 1)) (hρ : ρ ∈ Set.Ioo 0 1)
include hG hρ

omit hG hρ in
theorem annulus_subset_ball : annulus 0 0 1 ⊆ ball (0 : ℂ) 1 := fun z hz => by
  rw [mem_ball_zero_iff]; simpa using hz.2

omit hG in
theorem sphere_subset_ball' : sphere (0 : ℂ) ρ ⊆ ball 0 1 := fun z hz => by
  rw [mem_sphere_zero_iff_norm] at hz; rw [mem_ball_zero_iff, hz]; exact hρ.2

/-- `G₀ = G(0)`. -/
theorem laurentCoeff_zero' : laurentCoeff G 0 ρ 0 = G 0 := by
  have hsub : closedBall (0 : ℂ) ρ ⊆ ball 0 1 := closedBall_subset_ball hρ.2
  have h := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    countable_empty (mem_ball_self hρ.1) (hG.continuousOn.mono hsub) fun z hz =>
      hG.differentiableAt (isOpen_ball.mem_nhds (hsub (ball_subset_closedBall hz.1)))
  rw [← h, laurentCoeff, smul_eq_mul]
  congr 1
  refine circleIntegral.integral_congr hρ.1.le fun z _ => ?_
  simp [div_eq_inv_mul]

/-- The Taylor series: `G(z) = ∑ Gₙ zⁿ` for `|z| < ρ`. -/
theorem hasSum_taylor {z : ℂ} (hz : ‖z‖ < ρ) :
    HasSum (fun n : ℕ => laurentCoeff G 0 ρ n * z ^ n) (G z) := by
  have hsub : closedBall (0 : ℂ) ρ ⊆ ball 0 1 := closedBall_subset_ball hρ.2
  set R : NNReal := ⟨ρ, hρ.1.le⟩
  have hps := (hG.mono hsub).hasFPowerSeriesOnBall (R := R) (by
    show (0 : ℝ) < ρ; exact hρ.1)
  have hzR : z ∈ Metric.eball (0 : ℂ) R := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_coe,
      ← NNReal.coe_lt_coe, coe_nnnorm]
    exact hz
  have h := hps.hasSum hzR
  rw [zero_add] at h
  refine h.congr_fun fun n => ?_
  rw [cauchyPowerSeries_apply, laurentCoeff, smul_eq_mul, mul_assoc, mul_comm _ (z ^ n),
    ← circleIntegral.integral_const_mul]
  congr 1
  refine circleIntegral.integral_congr hρ.1.le fun w hw => ?_
  have hw0 : w ≠ 0 := fun h => by
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hw; linarith [hρ.1]
  simp only [sub_zero, smul_eq_mul]
  rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, div_pow, pow_succ]
  field_simp

/-- **The coefficient recurrence of a linear ODE**: if
`(p₀ + p₁z + p₂z²) G′(z) = (q₀ + q₁z) G(z)` on `|z| < 1`, then
`p₀(n+1)a_{n+1} + p₁ n aₙ + p₂(n−1)a_{n−1} = q₀aₙ + q₁a_{n−1}` for the coefficients `aₙ = Gₙ`. -/
theorem laurentCoeff_ode {p₀ p₁ p₂ q₀ q₁ : ℂ}
    (hode : ∀ z ∈ ball (0 : ℂ) 1, (p₀ + p₁ * z + p₂ * z ^ 2) * deriv G z = (q₀ + q₁ * z) * G z)
    (n : ℤ) :
    p₀ * ((n + 1) * laurentCoeff G 0 ρ (n + 1)) + p₁ * (n * laurentCoeff G 0 ρ n) +
        p₂ * ((n - 1) * laurentCoeff G 0 ρ (n - 1)) =
      q₀ * laurentCoeff G 0 ρ n + q₁ * laurentCoeff G 0 ρ (n - 1) := by
  have hsph := sphere_subset_ball' hρ
  have hGa : DifferentiableOn ℂ G (annulus 0 0 1) := hG.mono annulus_subset_ball
  have hρ' : ρ ∈ Set.Ioo (0 : ℝ) 1 := hρ
  have hD : ContinuousOn (deriv G) (sphere 0 ρ) :=
    ((hG.deriv isOpen_ball).continuousOn).mono hsph
  have hGc : ContinuousOn G (sphere 0 ρ) := hG.continuousOn.mono hsph
  have hDz : ContinuousOn (fun z => z * deriv G z) (sphere 0 ρ) := continuousOn_id.mul hD
  have hDzz : ContinuousOn (fun z => z * (z * deriv G z)) (sphere 0 ρ) := continuousOn_id.mul hDz
  have hGz : ContinuousOn (fun z => z * G z) (sphere 0 ρ) := continuousOn_id.mul hGc
  have hA : ContinuousOn (fun z => p₀ * deriv G z) (sphere 0 ρ) := continuousOn_const.mul hD
  have hB : ContinuousOn (fun z => p₁ * (z * deriv G z)) (sphere 0 ρ) :=
    continuousOn_const.mul hDz
  have hC : ContinuousOn (fun z => p₂ * (z * (z * deriv G z))) (sphere 0 ρ) :=
    continuousOn_const.mul hDzz
  have hAB : ContinuousOn (fun z => p₀ * deriv G z + p₁ * (z * deriv G z)) (sphere 0 ρ) :=
    hA.add hB
  have hP : ContinuousOn (fun z => q₀ * G z) (sphere 0 ρ) := continuousOn_const.mul hGc
  have hQ : ContinuousOn (fun z => q₁ * (z * G z)) (sphere 0 ρ) := continuousOn_const.mul hGz
  have hEq := laurentCoeff_congr (G₁ := fun z => p₀ * deriv G z + p₁ * (z * deriv G z) +
      p₂ * (z * (z * deriv G z))) (G₂ := fun z => q₀ * G z + q₁ * (z * G z)) hρ.1.le
    (fun z hz => by
      have := hode z (hsph hz)
      simp only
      linear_combination this) n
  rw [laurentCoeff_add' hρ.1 hAB hC, laurentCoeff_add' hρ.1 hA hB,
    laurentCoeff_add' hρ.1 hP hQ,
    laurentCoeff_const_mul, laurentCoeff_const_mul, laurentCoeff_const_mul,
    laurentCoeff_const_mul, laurentCoeff_const_mul, laurentCoeff_mul_id _ hρ.1,
    laurentCoeff_mul_id _ hρ.1, laurentCoeff_mul_id _ hρ.1, laurentCoeff_mul_id _ hρ.1,
    laurentCoeff_deriv hGa hρ', laurentCoeff_deriv hGa hρ', laurentCoeff_deriv hGa hρ'] at hEq
  rw [show n - 1 - 1 + 1 = n - 1 by ring, show n - 1 + 1 = n by ring] at hEq
  push_cast at hEq
  linear_combination hEq

end Coeff

/-! ### The functions `(1 − βz)^{−1/2}` -/

/-- `(1 − βz)^{−1/2}`, principal branch. -/
noncomputable def hsq (β z : ℂ) : ℂ := (1 - β * z) ^ (-1 / 2 : ℂ)

/-- Its derivative `(β/2)(1 − βz)^{−3/2}`. -/
noncomputable def dhsq (β z : ℂ) : ℂ := β / 2 * (1 - β * z) ^ (-3 / 2 : ℂ)

theorem one_sub_mem_slitPlane {β z : ℂ} (hβ : ‖β‖ = 1) (hz : ‖z‖ ≤ 1) (hne : β * z ≠ 1) :
    1 - β * z ∈ slitPlane := by
  left
  have hn : ‖β * z‖ ≤ 1 := by rw [norm_mul, hβ, one_mul]; exact hz
  have hre : (β * z).re ≤ 1 := (Complex.re_le_norm _).trans hn
  rcases hre.lt_or_eq with h | h
  · simp only [sub_re, one_re]; linarith
  · exfalso
    apply hne
    have h2 := Complex.sq_norm (β * z)
    rw [Complex.normSq_apply, h] at h2
    have him : (β * z).im = 0 := by nlinarith [norm_nonneg (β * z)]
    exact Complex.ext (by simp [h]) (by simp [him])

theorem one_sub_mem_slitPlane_of_lt {β z : ℂ} (hβ : ‖β‖ = 1) (hz : ‖z‖ < 1) :
    1 - β * z ∈ slitPlane :=
  one_sub_mem_slitPlane hβ hz.le fun h => by
    have := congrArg norm h
    rw [norm_mul, hβ, one_mul, norm_one] at this
    linarith

theorem hasDerivAt_hsq {β z : ℂ} (h : 1 - β * z ∈ slitPlane) :
    HasDerivAt (hsq β) (dhsq β z) z := by
  have h1 : HasDerivAt (fun w => 1 - β * w) (-β) z := by
    simpa using ((hasDerivAt_id z).const_mul β).const_sub 1
  have h2 := h1.cpow_const (c := (-1 / 2 : ℂ)) h
  unfold hsq dhsq
  convert h2 using 1
  rw [show (-1 / 2 : ℂ) - 1 = -3 / 2 by norm_num]
  ring

/-- `(1 − βz) · d/dz (1 − βz)^{−1/2} = (β/2)(1 − βz)^{−1/2}`. -/
theorem one_sub_mul_dhsq {β z : ℂ} (h : 1 - β * z ∈ slitPlane) :
    (1 - β * z) * dhsq β z = β / 2 * hsq β z := by
  have h0 := slitPlane_ne_zero h
  unfold dhsq hsq
  have : (1 - β * z) ^ (-1 / 2 : ℂ) = (1 - β * z) ^ (1 : ℂ) * (1 - β * z) ^ (-3 / 2 : ℂ) := by
    rw [← Complex.cpow_add _ _ h0]; norm_num
  rw [this, Complex.cpow_one]
  ring

theorem hsq_zero (β : ℂ) : hsq β 0 = 1 := by simp [hsq]

theorem hsq_sq_mul {β z : ℂ} (h : 1 - β * z ≠ 0) : hsq β z ^ 2 * (1 - β * z) = 1 := by
  unfold hsq
  rw [← Complex.cpow_nat_mul]
  norm_num
  rw [Complex.cpow_neg_one, inv_mul_cancel₀ h]

theorem differentiableOn_hsq {β : ℂ} (hβ : ‖β‖ = 1) : DifferentiableOn ℂ (hsq β) (ball 0 1) :=
  fun _ hz => (hasDerivAt_hsq (one_sub_mem_slitPlane_of_lt hβ (mem_ball_zero_iff.mp hz))
    ).differentiableAt.differentiableWithinAt

/-- `cₙ = Γ(n + ½)/(√π n!)`, the coefficients of `(1 − w)^{−1/2}`. -/
noncomputable def halfCoeff (n : ℕ) : ℝ := Real.Gamma (n + 1 / 2) / (√π * (n.factorial : ℝ))

theorem halfCoeff_zero : halfCoeff 0 = 1 := by
  have : (√π : ℝ) ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  simp only [halfCoeff, Nat.cast_zero, zero_add, Real.Gamma_one_half_eq, Nat.factorial_zero,
    Nat.cast_one, mul_one, div_self this]

theorem halfCoeff_succ (n : ℕ) : (n + 1 : ℝ) * halfCoeff (n + 1) = (n + 1 / 2) * halfCoeff n := by
  unfold halfCoeff
  rw [show ((n + 1 : ℕ) : ℝ) + 1 / 2 = (n + 1 / 2) + 1 by push_cast; ring,
    Real.Gamma_add_one (by positivity), Nat.factorial_succ]
  have : (√π : ℝ) ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- The Taylor coefficients of `(1 − βz)^{−1/2}`: `βⁿ cₙ`. -/
theorem laurentCoeff_hsq {β : ℂ} (hβ : ‖β‖ = 1) {ρ : ℝ} (hρ : ρ ∈ Set.Ioo 0 1) (n : ℕ) :
    laurentCoeff (hsq β) 0 ρ n = β ^ n * halfCoeff n := by
  have hG := differentiableOn_hsq hβ
  have hode : ∀ z ∈ ball (0 : ℂ) 1, (1 + (-β) * z + 0 * z ^ 2) * deriv (hsq β) z =
      (β / 2 + 0 * z) * hsq β z := fun z hz => by
    have hs := one_sub_mem_slitPlane_of_lt hβ (mem_ball_zero_iff.mp hz)
    rw [(hasDerivAt_hsq hs).deriv]
    linear_combination one_sub_mul_dhsq hs
  induction n with
  | zero => simp [laurentCoeff_zero' hG hρ, hsq_zero, halfCoeff_zero]
  | succ n ih =>
    have h := laurentCoeff_ode hG hρ hode n
    push_cast at h ⊢
    rw [ih] at h
    have hc := halfCoeff_succ n
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hc' : ((n : ℂ) + 1) * (halfCoeff (n + 1) : ℂ) = ((n : ℂ) + 1 / 2) * halfCoeff n := by
      have := congrArg (fun t : ℝ => (t : ℂ)) hc
      push_cast at this
      linear_combination this
    apply mul_left_cancel₀ hn
    linear_combination h - β ^ (n + 1) * hc'

/-! ### 2.10.33: the generating function of the Legendre polynomials -/

/-- The Legendre polynomials `Pₙ(x)` by Bonnet's recurrence (DLMF 18.9.1 with Table 18.9.1). -/
noncomputable def legendreP : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => x
  | n + 2, x => ((2 * n + 3) * x * legendreP (n + 1) x - (n + 1) * legendreP n x) / (n + 2)

/-- `e^{iα}`. -/
noncomputable def eP (α : ℝ) : ℂ := cexp (α * I)

/-- `e^{−iα}`. -/
noncomputable def eM (α : ℝ) : ℂ := cexp (-α * I)

theorem norm_eP (α : ℝ) : ‖eP α‖ = 1 := Complex.norm_exp_ofReal_mul_I α

theorem norm_eM (α : ℝ) : ‖eM α‖ = 1 := by
  rw [eM, show -(α : ℂ) * I = ((-α : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem eP_mul_eM (α : ℝ) : eP α * eM α = 1 := by
  rw [eP, eM, ← Complex.exp_add, show (α : ℂ) * I + -α * I = 0 by ring, Complex.exp_zero]

theorem two_cos_eq (α : ℝ) : 2 * (Real.cos α : ℂ) = eP α + eM α := by
  rw [Complex.ofReal_cos, Complex.two_cos, eP, eM]

/-- The generating function `f(z) = (1 − 2z cos α + z²)^{−1/2}` of 2.10.33, as the branch
`(1 − ze^{iα})^{−1/2}(1 − ze^{−iα})^{−1/2}` that is holomorphic in `|z| < 1` with `f(0) = 1`. -/
noncomputable def legendreGen (α : ℝ) (z : ℂ) : ℂ := hsq (eP α) z * hsq (eM α) z

theorem legendreGen_zero (α : ℝ) : legendreGen α 0 = 1 := by
  simp [legendreGen, hsq_zero]

/-- `f` is a square root of `(1 − 2z cos α + z²)^{−1}`. -/
theorem legendreGen_sq (α : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    legendreGen α z ^ 2 * (1 - 2 * z * Real.cos α + z ^ 2) = 1 := by
  have h₁ := hsq_sq_mul (slitPlane_ne_zero (one_sub_mem_slitPlane_of_lt (norm_eP α) hz))
  have h₂ := hsq_sq_mul (slitPlane_ne_zero (one_sub_mem_slitPlane_of_lt (norm_eM α) hz))
  have hc := two_cos_eq α
  have hp := eP_mul_eM α
  rw [legendreGen, mul_pow, show 1 - 2 * z * (Real.cos α : ℂ) + z ^ 2 =
    (1 - eP α * z) * (1 - eM α * z) by linear_combination (-z) * hc - z ^ 2 * hp]
  linear_combination hsq (eM α) z ^ 2 * (1 - eM α * z) * h₁ + h₂

theorem differentiableOn_legendreGen (α : ℝ) : DifferentiableOn ℂ (legendreGen α) (ball 0 1) :=
  (differentiableOn_hsq (norm_eP α)).mul (differentiableOn_hsq (norm_eM α))

theorem hasDerivAt_legendreGen (α : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (legendreGen α)
      (dhsq (eP α) z * hsq (eM α) z + hsq (eP α) z * dhsq (eM α) z) z :=
  (hasDerivAt_hsq (one_sub_mem_slitPlane_of_lt (norm_eP α) hz)).mul
    (hasDerivAt_hsq (one_sub_mem_slitPlane_of_lt (norm_eM α) hz))

/-- The ODE `(1 − 2z cos α + z²) f′ = (cos α − z) f`. -/
theorem legendreGen_ode (α : ℝ) :
    ∀ z ∈ ball (0 : ℂ) 1, (1 + (-2 * Real.cos α : ℂ) * z + 1 * z ^ 2) * deriv (legendreGen α) z =
      ((Real.cos α : ℂ) + (-1) * z) * legendreGen α z := fun z hz => by
  have hz' := mem_ball_zero_iff.mp hz
  have hdP := one_sub_mul_dhsq (one_sub_mem_slitPlane_of_lt (norm_eP α) hz')
  have hdM := one_sub_mul_dhsq (one_sub_mem_slitPlane_of_lt (norm_eM α) hz')
  have hc := two_cos_eq α
  have hp := eP_mul_eM α
  rw [(hasDerivAt_legendreGen α hz').deriv, legendreGen]
  set D := dhsq (eP α) z * hsq (eM α) z + hsq (eP α) z * dhsq (eM α) z
  set P := hsq (eP α) z * hsq (eM α) z
  linear_combination (1 - eM α * z) * hsq (eM α) z * hdP + (1 - eP α * z) * hsq (eP α) z * hdM +
    (-z * D - P / 2) * hc + (-z ^ 2 * D - z * P) * hp

/-- The Taylor coefficients of `f` are `Pₙ(cos α)`. -/
theorem laurentCoeff_legendreGen (α : ℝ) {ρ : ℝ} (hρ : ρ ∈ Set.Ioo 0 1) (n : ℕ) :
    laurentCoeff (legendreGen α) 0 ρ n = legendreP n (Real.cos α) := by
  have hG := differentiableOn_legendreGen α
  have hrec := laurentCoeff_ode hG hρ (legendreGen_ode α)
  have h0 : laurentCoeff (legendreGen α) 0 ρ 0 = 1 := by
    rw [laurentCoeff_zero' hG hρ, legendreGen_zero]
  suffices H : ∀ n : ℕ, laurentCoeff (legendreGen α) 0 ρ n = legendreP n (Real.cos α) ∧
      laurentCoeff (legendreGen α) 0 ρ ((n : ℤ) + 1) = legendreP (n + 1) (Real.cos α) from
    (H n).1
  intro n
  induction n with
  | zero =>
    have h := hrec 0
    norm_num at h
    refine ⟨by simp [h0, legendreP], ?_⟩
    simp only [Nat.cast_zero, zero_add, legendreP]
    rw [h, h0, mul_one, Complex.ofReal_cos]
  | succ n ih =>
    refine ⟨by push_cast; exact ih.2, ?_⟩
    have h := hrec ((n : ℤ) + 1)
    rw [add_sub_cancel_right, ih.1, ih.2] at h
    push_cast at h ⊢
    rw [show n + 1 + 1 = n + 2 by ring, legendreP]
    have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
    push_cast
    field_simp
    linear_combination h

/-- **DLMF 2.10.33**: `(1 − 2z cos α + z²)^{−1/2} = ∑ₙ Pₙ(cos α) zⁿ`, `|z| < 1`. -/
theorem dlmf_2_10_33 (α : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (legendreP n (Real.cos α) : ℂ) * z ^ n) (legendreGen α z) := by
  have hρ : (‖z‖ + 1) / 2 ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨by positivity, by linarith⟩
  have h := hasSum_taylor (differentiableOn_legendreGen α) hρ (by linarith : ‖z‖ < (‖z‖ + 1) / 2)
  simpa only [laurentCoeff_legendreGen α hρ] using h

/-! ### 2.10.34–2.10.35: the comparison function -/

/-- `A₊ = e^{−πi/4}(2 sin α)^{−1/2} e^{iα/2}`, the coefficient of `(1 − ze^{iα})^{−1/2}` in `g`. -/
noncomputable def legendreAP (α : ℝ) : ℂ :=
  ((√(2 * Real.sin α))⁻¹ : ℝ) * cexp (((α / 2 - π / 4 : ℝ) : ℂ) * I)

/-- `A₋ = e^{πi/4}(2 sin α)^{−1/2} e^{−iα/2}`, the coefficient of `(1 − ze^{−iα})^{−1/2}`. -/
noncomputable def legendreAM (α : ℝ) : ℂ :=
  ((√(2 * Real.sin α))⁻¹ : ℝ) * cexp (-((α / 2 - π / 4 : ℝ) : ℂ) * I)

/-- **DLMF 2.10.34**: `g(z) = e^{−πi/4}(2 sin α)^{−1/2}(e^{−iα} − z)^{−1/2}
+ e^{πi/4}(2 sin α)^{−1/2}(e^{iα} − z)^{−1/2}`, with the branches
`(e^{∓iα} − z)^{−1/2} = e^{±iα/2}(1 − ze^{±iα})^{−1/2}` (continuous in the plane cut along the
outward rays from `e^{∓iα}`, equal to `e^{±iα/2}` at `z = 0`; `legendreBranch_sq`). -/
noncomputable def legendreCmp (α : ℝ) (z : ℂ) : ℂ :=
  legendreAP α * hsq (eP α) z + legendreAM α * hsq (eM α) z

/-- The branch of `(e^{−iα} − z)^{−1/2}` used in 2.10.34 squares correctly. -/
theorem legendreBranch_sq (α : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    (cexp ((α / 2 : ℝ) * I) * hsq (eP α) z) ^ 2 * (eM α - z) = 1 := by
  have h := hsq_sq_mul (slitPlane_ne_zero (one_sub_mem_slitPlane_of_lt (norm_eP α) hz))
  have he : cexp ((α / 2 : ℝ) * I) ^ 2 = eP α := by
    rw [← Complex.exp_nat_mul, eP]; push_cast; ring_nf
  have hp := eP_mul_eM α
  rw [mul_pow, he]
  linear_combination h + hsq (eP α) z ^ 2 * hp

theorem legendreCmp_comb (α : ℝ) (z : ℂ) :
    legendreCmp α z = cexp (-(π / 4 : ℝ) * I) * ((√(2 * Real.sin α))⁻¹ : ℝ) *
        (cexp ((α / 2 : ℝ) * I) * hsq (eP α) z) +
      cexp ((π / 4 : ℝ) * I) * ((√(2 * Real.sin α))⁻¹ : ℝ) *
        (cexp (-(α / 2 : ℝ) * I) * hsq (eM α) z) := by
  have h1 : cexp (((α / 2 - π / 4 : ℝ) : ℂ) * I) =
      cexp (-(π / 4 : ℝ) * I) * cexp ((α / 2 : ℝ) * I) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  have h2 : cexp (-((α / 2 - π / 4 : ℝ) : ℂ) * I) =
      cexp ((π / 4 : ℝ) * I) * cexp (-(α / 2 : ℝ) * I) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  rw [legendreCmp, legendreAP, legendreAM, h1, h2]
  ring

theorem differentiableOn_legendreCmp (α : ℝ) : DifferentiableOn ℂ (legendreCmp α) (ball 0 1) :=
  ((differentiableOn_hsq (norm_eP α)).const_mul _).add
    ((differentiableOn_hsq (norm_eM α)).const_mul _)

theorem sqrt_coeff_eq {x : ℝ} (hx : 0 < x) :
    (√(2 * x))⁻¹ * 2 / √π = √(2 / (π * x)) := by
  have h2x : 0 < √(2 * x) := Real.sqrt_pos.mpr (by positivity)
  have hπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  field_simp
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt Real.pi_pos.le]
  ring

/-- **DLMF 2.10.35**: `gₙ = (2/(π sin α))^{1/2} Γ(n + ½)/n! cos(nα + ½α − ¼π)`. -/
theorem dlmf_2_10_35 {α : ℝ} (hα : α ∈ Set.Ioo 0 π) {ρ : ℝ} (hρ : ρ ∈ Set.Ioo 0 1) (n : ℕ) :
    laurentCoeff (legendreCmp α) 0 ρ n = ((√(2 / (π * Real.sin α)) *
      (Real.Gamma (n + 1 / 2) / n.factorial) * Real.cos (n * α + α / 2 - π / 4) : ℝ) : ℂ) := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
  have hsph := sphere_subset_ball' hρ
  have hcP : ContinuousOn (fun z => legendreAP α * hsq (eP α) z) (sphere 0 ρ) :=
    (continuousOn_const.mul (differentiableOn_hsq (norm_eP α)).continuousOn).mono hsph
  have hcM : ContinuousOn (fun z => legendreAM α * hsq (eM α) z) (sphere 0 ρ) :=
    (continuousOn_const.mul (differentiableOn_hsq (norm_eM α)).continuousOn).mono hsph
  rw [show legendreCmp α = fun z =>
      legendreAP α * hsq (eP α) z + legendreAM α * hsq (eM α) z from rfl,
    laurentCoeff_add' hρ.1 hcP hcM,
    laurentCoeff_const_mul, laurentCoeff_const_mul, laurentCoeff_hsq (norm_eP α) hρ,
    laurentCoeff_hsq (norm_eM α) hρ]
  set θ : ℝ := n * α + α / 2 - π / 4
  have e1 : cexp (((α / 2 - π / 4 : ℝ) : ℂ) * I) * eP α ^ n = cexp (θ * I) := by
    rw [eP, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; simp only [θ]; push_cast; ring
  have e2 : cexp (-((α / 2 - π / 4 : ℝ) : ℂ) * I) * eM α ^ n = cexp (-θ * I) := by
    rw [eM, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; simp only [θ]; push_cast; ring
  have hcos : 2 * (Real.cos θ : ℂ) = cexp (θ * I) + cexp (-θ * I) := by
    rw [Complex.ofReal_cos, Complex.two_cos]
  have hk := sqrt_coeff_eq hs
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have hπ : √π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [legendreAP, legendreAM, ← hk]
  calc _ = (((√(2 * Real.sin α))⁻¹ : ℝ) : ℂ) * (halfCoeff n : ℂ) *
        (cexp (((α / 2 - π / 4 : ℝ) : ℂ) * I) * eP α ^ n +
          cexp (-((α / 2 - π / 4 : ℝ) : ℂ) * I) * eM α ^ n) := by ring
    _ = (((√(2 * Real.sin α))⁻¹ : ℝ) : ℂ) * (halfCoeff n : ℂ) * (2 * (Real.cos θ : ℂ)) := by
        rw [e1, e2, hcos]
    _ = _ := by
        rw [halfCoeff]
        push_cast
        field_simp

/-! ### Condition (b´) with `m = 1` -/

theorem continuousAt_dhsq {β z : ℂ} (h : 1 - β * z ∈ slitPlane) : ContinuousAt (dhsq β) z :=
  continuousAt_const.mul ((continuousAt_cpow_const h).comp (f := fun w => 1 - β * w)
    (by fun_prop))

theorem norm_one_sub_mul {β γ : ℂ} (hβ : ‖β‖ = 1) (hγ : β * γ = 1) (z : ℂ) :
    ‖1 - β * z‖ = ‖z - γ‖ := by
  rw [show 1 - β * z = β * (γ - z) by linear_combination (-1 : ℂ) * hγ, norm_mul, hβ, one_mul,
    norm_sub_rev]

theorem norm_hsq {β γ : ℂ} (hβ : ‖β‖ = 1) (hγ : β * γ = 1) (z : ℂ) :
    ‖hsq β z‖ = ‖z - γ‖ ^ (-1 / 2 : ℝ) := by
  rw [hsq, show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real,
    norm_one_sub_mul hβ hγ]

theorem norm_dhsq_le {β γ : ℂ} (hβ : ‖β‖ = 1) (hγ : β * γ = 1) (z : ℂ) :
    ‖dhsq β z‖ ≤ ‖z - γ‖ ^ (-3 / 2 : ℝ) := by
  rw [dhsq, norm_mul, norm_div, hβ, show (-3 / 2 : ℂ) = ((-3 / 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_real, norm_one_sub_mul hβ hγ, Complex.norm_two]
  have := Real.rpow_nonneg (norm_nonneg (z - γ)) (-3 / 2)
  linarith

/-- The local estimate at one singular point `s`: if `|f₁(z)| ≤ |z − s|^{−1/2}`,
`|g₁(z)| ≤ |z − s|^{−3/2}`, `f₂(z) − f₂(s) = O(z − s)` and `g₂` is continuous at `s`, then
`g₁(f₂ − f₂(s)) + f₁g₂ − cg₂ = O(|z − s|^{−1/2})`. -/
theorem sing_bound {s c : ℂ} {f₁ g₁ f₂ g₂ : ℂ → ℂ}
    (hf₁ : ∀ z, ‖f₁ z‖ ≤ ‖z - s‖ ^ (-1 / 2 : ℝ)) (hg₁ : ∀ z, ‖g₁ z‖ ≤ ‖z - s‖ ^ (-3 / 2 : ℝ))
    (hf₂ : (fun z => f₂ z - f₂ s) =O[𝓝 s] fun z => z - s) (hg₂ : ContinuousAt g₂ s) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ z, z ≠ s → ‖z - s‖ < δ →
      ‖g₁ z * (f₂ z - f₂ s) + f₁ z * g₂ z - c * g₂ z‖ ≤ C * ‖z - s‖ ^ ((1 / 2 : ℝ) - 1) := by
  obtain ⟨L, hLpos, hLw⟩ := hf₂.exists_pos
  have hc2 : ∀ᶠ z in 𝓝 s, ‖g₂ z‖ ≤ ‖g₂ s‖ + 1 :=
    (hg₂.norm.eventually (gt_mem_nhds (lt_add_one _))).mono fun _ h => h.le
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.mp (hLw.bound.and hc2)
  set M := ‖g₂ s‖ + 1
  have hM : 0 ≤ M := by positivity
  refine ⟨L + M + ‖c‖ * M, min ε 1, by positivity, fun z hzs hzδ => ?_⟩
  have ht : 0 < ‖z - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzs)
  have ht1 : ‖z - s‖ < 1 := hzδ.trans_le (min_le_right _ _)
  obtain ⟨hL', hM'⟩ := hεb (by rw [dist_eq_norm]; exact hzδ.trans_le (min_le_left _ _))
  have hu1 : 1 ≤ ‖z - s‖ ^ (-1 / 2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1.le (by norm_num)
  have h32 : ‖z - s‖ ^ (-3 / 2 : ℝ) * ‖z - s‖ = ‖z - s‖ ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_add_one ht.ne']; norm_num
  have hu0 : 0 ≤ ‖z - s‖ ^ (-3 / 2 : ℝ) := by positivity
  have e1 : ‖g₁ z * (f₂ z - f₂ s)‖ ≤ L * ‖z - s‖ ^ (-1 / 2 : ℝ) := by
    rw [norm_mul, ← h32]
    calc ‖g₁ z‖ * ‖f₂ z - f₂ s‖ ≤ ‖z - s‖ ^ (-3 / 2 : ℝ) * (L * ‖z - s‖) :=
          mul_le_mul (hg₁ z) hL' (norm_nonneg _) hu0
      _ = _ := by ring
  have e2 : ‖f₁ z * g₂ z‖ ≤ ‖z - s‖ ^ (-1 / 2 : ℝ) * M := by
    rw [norm_mul]; exact mul_le_mul (hf₁ z) hM' (norm_nonneg _) (by positivity)
  have e3 : ‖c * g₂ z‖ ≤ ‖c‖ * M * ‖z - s‖ ^ (-1 / 2 : ℝ) := by
    rw [norm_mul]
    calc ‖c‖ * ‖g₂ z‖ ≤ ‖c‖ * M := mul_le_mul_of_nonneg_left hM' (norm_nonneg _)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hu1
  calc _ ≤ ‖g₁ z * (f₂ z - f₂ s) + f₁ z * g₂ z‖ + ‖c * g₂ z‖ := norm_sub_le _ _
    _ ≤ ‖g₁ z * (f₂ z - f₂ s)‖ + ‖f₁ z * g₂ z‖ + ‖c * g₂ z‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ L * ‖z - s‖ ^ (-1 / 2 : ℝ) + ‖z - s‖ ^ (-1 / 2 : ℝ) * M +
        ‖c‖ * M * ‖z - s‖ ^ (-1 / 2 : ℝ) := by gcongr
    _ = _ := by rw [show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num]; ring

theorem cpow_exp_of_im {L : ℂ} (h₁ : -π < L.im) (h₂ : L.im ≤ π) (c : ℂ) :
    cexp L ^ c = cexp (L * c) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero L), Complex.log_exp h₁ h₂]

theorem exp_pi_div_two_I : cexp ((π / 2 : ℝ) * I) = I := by
  rw [Complex.exp_mul_I]; push_cast; rw [Complex.cos_pi_div_two, Complex.sin_pi_div_two]; ring

theorem inv_sqrt_eq_exp {x : ℝ} (hx : 0 < x) :
    (((√x)⁻¹ : ℝ) : ℂ) = cexp ((Real.log x : ℂ) * (-1 / 2)) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, ← Real.exp_neg, Complex.ofReal_exp]
  push_cast; ring_nf

/-- `A₊ = (1 − e^{−2iα})^{−1/2}`: `g` matches `f` to first order at `z = e^{−iα}`. -/
theorem legendreAP_eq {α : ℝ} (hα : α ∈ Set.Ioo 0 π) : legendreAP α = hsq (eM α) (eM α) := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
  have hL : 1 - eM α * eM α =
      cexp ((Real.log (2 * Real.sin α) : ℂ) + ((π / 2 - α : ℝ) : ℂ) * I) := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (by positivity),
      show ((π / 2 - α : ℝ) : ℂ) * I = (π / 2 : ℝ) * I + -α * I by push_cast; ring,
      Complex.exp_add, exp_pi_div_two_I]
    have h2 := Complex.two_sin (α : ℂ)
    have hp := eP_mul_eM α
    push_cast
    rw [h2, show cexp (-α * I) = eM α from rfl, show cexp (α * I) = eP α from rfl]
    linear_combination (-1 : ℂ) * hp - (eM α - eP α) * eM α * Complex.I_mul_I
  rw [hsq, hL, cpow_exp_of_im (by simp; linarith [hα.1, hα.2, Real.pi_pos])
    (by simp; linarith [hα.1, hα.2, Real.pi_pos]),
    legendreAP, inv_sqrt_eq_exp (by positivity), ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `A₋ = (1 − e^{2iα})^{−1/2}`. -/
theorem legendreAM_eq {α : ℝ} (hα : α ∈ Set.Ioo 0 π) : legendreAM α = hsq (eP α) (eP α) := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
  have hL : 1 - eP α * eP α =
      cexp ((Real.log (2 * Real.sin α) : ℂ) + ((α - π / 2 : ℝ) : ℂ) * I) := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (by positivity),
      show ((α - π / 2 : ℝ) : ℂ) * I = -((π / 2 : ℝ) * I) + α * I by push_cast; ring,
      Complex.exp_add, Complex.exp_neg, exp_pi_div_two_I]
    have h2 := Complex.two_sin (α : ℂ)
    have hp := eP_mul_eM α
    push_cast
    rw [h2, show cexp (-α * I) = eM α from rfl, show cexp (α * I) = eP α from rfl,
      Complex.inv_I]
    linear_combination (-1 : ℂ) * hp + (eM α - eP α) * eP α * Complex.I_mul_I
  rw [hsq, hL, cpow_exp_of_im (by simp; linarith [hα.1, hα.2, Real.pi_pos])
    (by simp; linarith [hα.1, hα.2, Real.pi_pos]),
    legendreAM, inv_sqrt_eq_exp (by positivity), ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `f′ − g′` (with `f′`, `g′` written out). -/
noncomputable def legendreH (α : ℝ) (z : ℂ) : ℂ :=
  dhsq (eP α) z * hsq (eM α) z + hsq (eP α) z * dhsq (eM α) z -
    (legendreAP α * dhsq (eP α) z + legendreAM α * dhsq (eM α) z)

theorem legendreH_eq {α : ℝ} {z : ℂ} (hz : ‖z‖ < 1) :
    legendreH α z = deriv^[1] (legendreGen α) z - deriv^[1] (legendreCmp α) z := by
  have hP := hasDerivAt_hsq (one_sub_mem_slitPlane_of_lt (norm_eP α) hz)
  have hM := hasDerivAt_hsq (one_sub_mem_slitPlane_of_lt (norm_eM α) hz)
  have hC : HasDerivAt (legendreCmp α)
      (legendreAP α * dhsq (eP α) z + legendreAM α * dhsq (eM α) z) z :=
    (hP.const_mul (legendreAP α)).add (hM.const_mul (legendreAM α))
  show legendreH α z = deriv (legendreGen α) z - deriv (legendreCmp α) z
  rw [(hasDerivAt_legendreGen α hz).deriv,
    hC.deriv, legendreH]

theorem mem_slitPlane_of_ne {β γ z : ℂ} (hβ : ‖β‖ = 1) (hγ : γ * β = 1) (hz : ‖z‖ ≤ 1)
    (hne : z ≠ γ) : 1 - β * z ∈ slitPlane :=
  one_sub_mem_slitPlane hβ hz fun h => hne (by linear_combination γ * h - z * hγ)

/-- **Condition (b´)** for `f′ − g′`, `r = 1`: singularities `e^{±iα}`, `σ = ½`. -/
theorem legendre_darbouxCond {α : ℝ} (hα : α ∈ Set.Ioo 0 π) : DarbouxCond (legendreH α) 1 := by
  have hp := eP_mul_eM α
  have hp' : eM α * eP α = 1 := by rw [mul_comm]; exact hp
  have hAP := legendreAP_eq hα
  have hAM := legendreAM_eq hα
  -- `1 − e^{∓iα}e^{∓iα} ≠ 0`
  have hMM : 1 - eM α * eM α ∈ slitPlane := by
    refine one_sub_mem_slitPlane (norm_eM α) (norm_eM α).le fun h => ?_
    have hs := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
    have : eM α = eP α := by linear_combination eP α * h - eM α * hp
    have h2 := Complex.two_sin (α : ℂ)
    rw [show cexp (α * I) = eP α from rfl, show cexp (-α * I) = eM α from rfl, this, sub_self,
      zero_mul, ← Complex.ofReal_sin] at h2
    have : Real.sin α = 0 := by exact_mod_cast (mul_eq_zero.mp h2).resolve_left two_ne_zero
    linarith
  have hPP : 1 - eP α * eP α ∈ slitPlane := by
    refine one_sub_mem_slitPlane (norm_eP α) (norm_eP α).le fun h => ?_
    have hs := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
    have : eM α = eP α := by linear_combination -(eM α * h) + eP α * hp
    have h2 := Complex.two_sin (α : ℂ)
    rw [show cexp (α * I) = eP α from rfl, show cexp (-α * I) = eM α from rfl, this, sub_self,
      zero_mul, ← Complex.ofReal_sin] at h2
    have : Real.sin α = 0 := by exact_mod_cast (mul_eq_zero.mp h2).resolve_left two_ne_zero
    linarith
  refine ⟨{eP α, eM α}, ?_, ?_, ?_⟩
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact norm_eP α
    · exact norm_eM α
  · intro z hz
    simp only [Set.mem_sdiff, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hz
    obtain ⟨⟨_, hz1⟩, hzP, hzM⟩ := hz
    have hsP := mem_slitPlane_of_ne (norm_eP α) hp' hz1 hzM
    have hsM := mem_slitPlane_of_ne (norm_eM α) hp hz1 hzP
    refine ContinuousAt.continuousWithinAt ?_
    unfold legendreH
    exact (((continuousAt_dhsq hsP).mul (hasDerivAt_hsq hsM).continuousAt).add
      ((hasDerivAt_hsq hsP).continuousAt.mul (continuousAt_dhsq hsM))).sub
      ((continuousAt_const.mul (continuousAt_dhsq hsP)).add
        (continuousAt_const.mul (continuousAt_dhsq hsM)))
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    refine ⟨1 / 2, by norm_num, ?_⟩
    rcases hs with rfl | rfl
    · -- at `e^{iα}`: the singular factor is `(1 − ze^{−iα})^{−1/2}`
      obtain ⟨C, δ, hδ, hb⟩ := sing_bound (c := legendreAP α)
        (f₁ := hsq (eM α)) (g₁ := dhsq (eM α)) (f₂ := hsq (eP α)) (g₂ := dhsq (eP α))
        (fun z => (norm_hsq (norm_eM α) hp' z).le) (norm_dhsq_le (norm_eM α) hp')
        (hasDerivAt_hsq hPP).isBigO_sub
        (continuousAt_dhsq hPP)
      refine ⟨C, δ, hδ, fun z _ hzs hzδ => ?_⟩
      convert hb z hzs hzδ using 2
      rw [legendreH, ← hAM]
      ring
    · obtain ⟨C, δ, hδ, hb⟩ := sing_bound (c := legendreAM α)
        (f₁ := hsq (eP α)) (g₁ := dhsq (eP α)) (f₂ := hsq (eM α)) (g₂ := dhsq (eM α))
        (fun z => (norm_hsq (norm_eP α) hp z).le) (norm_dhsq_le (norm_eP α) hp)
        (hasDerivAt_hsq hMM).isBigO_sub
        (continuousAt_dhsq hMM)
      refine ⟨C, δ, hδ, fun z _ hzs hzδ => ?_⟩
      convert hb z hzs hzδ using 2
      rw [legendreH, ← hAP]
      ring

/-! ### 2.10.36 -/

/-- Log-convexity of `Γ` at the midpoint: `Γ(s + ½)² ≤ Γ(s)Γ(s + 1)`. -/
theorem gamma_sq_le {s : ℝ} (hs : 0 < s) :
    Real.Gamma (s + 1 / 2) ^ 2 ≤ Real.Gamma s * Real.Gamma (s + 1) := by
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hs (by linarith : 0 < s + 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  rw [show 1 / 2 * s + 1 / 2 * (s + 1) = s + 1 / 2 by ring, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow] at h
  have h0 : 0 ≤ Real.Gamma (s + 1 / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
  calc _ ≤ (√(Real.Gamma s) * √(Real.Gamma (s + 1))) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (Real.Gamma_pos_of_pos hs).le,
        Real.sq_sqrt (Real.Gamma_pos_of_pos (by linarith)).le]

/-- `(n + ½)^{−1/2} ≤ Γ(n + ½)/n! ≤ n^{−1/2}` (a weak form of Gautschi's inequality 5.6.4). -/
theorem halfGamma_bounds {n : ℕ} (hn : 1 ≤ n) :
    1 / √(n + 1 / 2) ≤ Real.Gamma (n + 1 / 2) / n.factorial ∧
      Real.Gamma (n + 1 / 2) / n.factorial ≤ 1 / √n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hG : Real.Gamma (n + 1) = n.factorial := Real.Gamma_nat_eq_factorial n
  have hGn : Real.Gamma (n + 1) = n * Real.Gamma n := Real.Gamma_add_one hn0.ne'
  have hpos : 0 < Real.Gamma (n + 1 / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hF : (0 : ℝ) < n.factorial := by positivity
  have h1 := gamma_sq_le hn0
  have h2 := gamma_sq_le (s := n + 1 / 2) (by positivity)
  have h3 : Real.Gamma (n + 1 / 2 + 1) = (n + 1 / 2) * Real.Gamma (n + 1 / 2) :=
    Real.Gamma_add_one (by positivity)
  rw [show (n : ℝ) + 1 / 2 + 1 / 2 = n + 1 by ring, h3] at h2
  have hq : 0 < Real.Gamma (n + 1 / 2) / n.factorial := div_pos hpos hF
  have hq2 : (Real.Gamma (n + 1 / 2) / n.factorial) ^ 2 ≤ (n : ℝ)⁻¹ := by
    rw [div_pow, ← one_div, div_le_div_iff₀ (by positivity) hn0, ← hG]
    have h' : Real.Gamma n * Real.Gamma (n + 1) * n = Real.Gamma (n + 1) * Real.Gamma (n + 1) := by
      rw [hGn]; ring
    nlinarith [mul_le_mul_of_nonneg_right h1 hn0.le]
  have hq2' : ((n : ℝ) + 1 / 2)⁻¹ ≤ (Real.Gamma (n + 1 / 2) / n.factorial) ^ 2 := by
    rw [div_pow, ← one_div, div_le_div_iff₀ (by positivity) (by positivity), ← hG]
    nlinarith
  constructor
  · rw [one_div (√((n : ℝ) + 1 / 2)), ← Real.sqrt_inv, ← Real.sqrt_sq hq.le]
    exact Real.sqrt_le_sqrt hq2'
  · rw [one_div (√(n : ℝ)), ← Real.sqrt_inv, ← Real.sqrt_sq hq.le]
    exact Real.sqrt_le_sqrt hq2

/-- `n(n^{−1/2} − (n + ½)^{−1/2}) ≤ 1/(4n^{1/2})`. -/
theorem nat_mul_inv_sqrt_sub_le {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * (1 / √n - 1 / √(n + 1 / 2)) ≤ 1 / (4 * √n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set a := √(n : ℝ)
  set b := √((n : ℝ) + 1 / 2)
  have ha : 0 < a := Real.sqrt_pos.mpr hn0
  have hb : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have ha2 : a ^ 2 = n := Real.sq_sqrt hn0.le
  have hb2 : b ^ 2 = n + 1 / 2 := Real.sq_sqrt (by positivity)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  rw [← ha2, show a ^ 2 * (1 / a - 1 / b) = a * (b - a) / b by field_simp,
    div_le_div_iff₀ hb (by positivity)]
  have h3 : a * b ^ 2 - a * a ^ 2 = a * (1 / 2) := by rw [hb2, ha2]; ring
  nlinarith [mul_nonneg ha.le (sq_nonneg (b - a))]

/-- **DLMF 2.10.36**: `Pₙ(cos α) = (2/(πn sin α))^{1/2} cos(nα + ½α − ¼π) + o(n^{−1})`,
`0 < α < π`. -/
theorem dlmf_2_10_36 {α : ℝ} (hα : α ∈ Set.Ioo 0 π) :
    Tendsto (fun n : ℕ => (n : ℝ) * |legendreP n (Real.cos α) -
      √(2 / (π * n * Real.sin α)) * Real.cos (n * α + α / 2 - π / 4)|) atTop (𝓝 0) := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
  set K := √(2 / (π * Real.sin α))
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hρ : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := ⟨by norm_num, by norm_num⟩
  have hball : ∀ z ∈ annulus (0 : ℂ) 0 1, ‖z‖ < 1 := fun z hz =>
    mem_ball_zero_iff.mp (annulus_subset_ball hz)
  have h31 := (dlmf_2_10_31 one_pos
    ((differentiableOn_legendreGen α).mono annulus_subset_ball)
    ((differentiableOn_legendreCmp α).mono annulus_subset_ball) 1
    (fun z hz => legendreH_eq (hball z hz)) (legendre_darbouxCond hα) hρ).1
  -- `n |Pₙ(cos α) − gₙ| → 0`
  have he : Tendsto (fun n : ℕ => (n : ℝ) * |legendreP n (Real.cos α) -
      K * (Real.Gamma (n + 1 / 2) / n.factorial) * Real.cos (n * α + α / 2 - π / 4)|)
      atTop (𝓝 0) := by
    refine (h31.comp tendsto_natCast_atTop_atTop).congr fun n => ?_
    simp only [Function.comp_apply, laurentCoeff_legendreGen α hρ, dlmf_2_10_35 hα hρ,
      one_zpow, one_mul, pow_one, Int.cast_natCast, Nat.abs_cast, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    rfl
  have hsq : Tendsto (fun n : ℕ => K / (4 * √(n : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
        (by norm_num : (0 : ℝ) < 4))
  have hu := he.add hsq
  rw [zero_add] at hu
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (Eventually.of_forall fun n => by positivity) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hlo, hhi⟩ := halfGamma_bounds hn
  have hroot : √(2 / (π * n * Real.sin α)) = K * (1 / √n) := by
    rw [show 2 / (π * n * Real.sin α) = 2 / (π * Real.sin α) / n by field_simp,
      Real.sqrt_div (by positivity)]
    ring
  set q := Real.Gamma (n + 1 / 2) / n.factorial
  set c := Real.cos (n * α + α / 2 - π / 4)
  have hc : |c| ≤ 1 := Real.abs_cos_le_one _
  have hd : |K * q * c - K * (1 / √n) * c| ≤ K * (1 / √n - 1 / √(n + 1 / 2)) := by
    rw [show K * q * c - K * (1 / √n) * c = K * c * (q - 1 / √n) by ring, abs_mul, abs_mul,
      abs_of_nonneg hK, abs_of_nonpos (by linarith : q - 1 / √n ≤ 0)]
    calc K * |c| * -(q - 1 / √n) ≤ K * 1 * -(q - 1 / √n) := by gcongr; linarith
      _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left (by linarith : -(q - 1 / √n) ≤
            1 / √n - 1 / √(n + 1 / 2)) hK]
  have hm := nat_mul_inv_sqrt_sub_le hn
  rw [hroot]
  calc (n : ℝ) * |legendreP n (Real.cos α) - K * (1 / √n) * c|
      ≤ n * (|legendreP n (Real.cos α) - K * q * c| + |K * q * c - K * (1 / √n) * c|) := by
        gcongr; exact abs_sub_le _ _ _
    _ ≤ n * |legendreP n (Real.cos α) - K * q * c| +
        K * (n * (1 / √n - 1 / √(n + 1 / 2))) := by
        rw [mul_add]
        linarith [mul_le_mul_of_nonneg_left hd hn0.le,
          show (n : ℝ) * (K * (1 / √n - 1 / √(n + 1 / 2))) =
            K * (n * (1 / √n - 1 / √(n + 1 / 2))) by ring]
    _ ≤ n * |legendreP n (Real.cos α) - K * q * c| + K * (1 / (4 * √n)) := by gcongr
    _ = _ := by simp only [q, c, mul_one_div]

/-- **Erratum** (DLMF: `α ∈ (0, 2π)`): for `π < α < 2π` the right side of 2.10.36 (with the
principal square root) is purely imaginary, and 2.10.36 fails. -/
theorem dlmf_2_10_36_false {α : ℝ} (hα : α ∈ Set.Ioo π (2 * π)) :
    ¬ Tendsto (fun n : ℕ => (n : ℝ) * ‖(legendreP n (Real.cos α) : ℂ) -
      ((2 / (π * n * Real.sin α) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
        Real.cos (n * α + α / 2 - π / 4)‖) atTop (𝓝 0) := by
  intro h
  have hs : Real.sin α < 0 := by
    have := Real.sin_pos_of_pos_of_lt_pi (x := α - π) (by linarith [hα.1]) (by linarith [hα.2])
    rw [Real.sin_sub_pi] at this
    linarith
  set c : ℕ → ℝ := fun n => Real.cos (n * α + α / 2 - π / 4)
  set K := √(2 / (π * -Real.sin α))
  have hK : 0 < K := Real.sqrt_pos.mpr (div_pos two_pos (mul_pos Real.pi_pos (by linarith)))
  -- `|cos θₙ| ≤ n|wₙ|/K`
  have hb : ∀ n : ℕ, 1 ≤ n → ‖c n‖ ≤ (n : ℝ) * ‖(legendreP n (Real.cos α) : ℂ) -
      ((2 / (π * n * Real.sin α) : ℝ) : ℂ) ^ (1 / 2 : ℂ) * Real.cos (n * α + α / 2 - π / 4)‖ /
        K := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    set x : ℝ := 2 / (π * n * Real.sin α)
    have hx : x ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num)
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hs.le)
    have hroot : (x : ℂ) ^ (1 / 2 : ℂ) = (√(-x) : ℂ) * I := by
      rw [Complex.ofReal_cpow_of_nonpos hx, Real.sqrt_eq_rpow,
        Complex.ofReal_cpow (by linarith), show π * I * (1 / 2 : ℂ) = (π / 2 : ℝ) * I by
          push_cast; ring, exp_pi_div_two_I]
      push_cast; ring
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hK' : K ≤ n * √(-x) := by
      have : √(2 * n / (π * -Real.sin α)) = n * √(-x) := by
        rw [show 2 * n / (π * -Real.sin α) = (n : ℝ) ^ 2 * -x by
            simp only [x]; field_simp,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hn0.le]
      rw [← this]
      exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith)
        (mul_pos Real.pi_pos (by linarith)).le)
    rw [hroot, le_div_iff₀ hK]
    have him := Complex.abs_im_le_norm ((legendreP n (Real.cos α) : ℂ) -
      (√(-x) : ℂ) * I * (c n : ℂ))
    have e : ((legendreP n (Real.cos α) : ℂ) - (√(-x) : ℂ) * I * (c n : ℂ)).im =
        -(√(-x) * c n) := by
      simp
    rw [e, abs_neg, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at him
    rw [Real.norm_eq_abs]
    calc |c n| * K ≤ |c n| * (n * √(-x)) := by gcongr
      _ = n * (√(-x) * |c n|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left him hn0.le
  have hc : Tendsto c atTop (𝓝 0) := by
    have hh := h.div_const K
    rw [zero_div] at hh
    refine squeeze_zero_norm' ?_ hh
    filter_upwards [eventually_ge_atTop 1] with n hn using hb n hn
  have hc1 : Tendsto (fun n => c (n + 1)) atTop (𝓝 0) := (tendsto_add_atTop_iff_nat 1).mpr hc
  have hsin : Tendsto (fun n : ℕ => Real.sin (n * α + α / 2 - π / 4)) atTop (𝓝 0) := by
    have hlim := (hc.mul_const (Real.cos α)).sub hc1
    rw [zero_mul, sub_zero] at hlim
    have hl2 := hlim.div_const (Real.sin α)
    rw [zero_div] at hl2
    refine hl2.congr fun n => ?_
    simp only [c]
    rw [show ((n + 1 : ℕ) : ℝ) * α + α / 2 - π / 4 = (n * α + α / 2 - π / 4) + α by
      push_cast; ring, Real.cos_add]
    have hs0 : Real.sin α ≠ 0 := hs.ne
    field_simp
    ring
  have h1 := (hc.pow 2).add (hsin.pow 2)
  rw [show (0 : ℝ) ^ 2 + 0 ^ 2 = 0 by norm_num] at h1
  have h1' : Tendsto (fun n : ℕ => c n ^ 2 + Real.sin (n * α + α / 2 - π / 4) ^ 2) atTop (𝓝 1) :=
    tendsto_const_nhds.congr fun n => by simp only [c]; rw [Real.cos_sq_add_sin_sq]
  exact one_ne_zero (tendsto_nhds_unique h1' h1)

end Azurite.DLMF
