/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14TableMellin
import Azurite.DLMF.Chapter2.Section5Residues

/-!
# DLMF §2.5(i), Example (2.5.8–2.5.16): what can be done without Bessel functions

The example is `I(x) = ∫₀^∞ J_ν²(xt)/(1 + t) dt` (2.5.8), `h = J_ν²`, `f = 1/(1 + t)`.

* 2.5.9: `𝓜f(1 − z) = π/sin(πz)` for `0 < ℜz < 1` (`dlmf_2_5_9`, from Table 1.14.5).
* 2.5.11: at a pole of order two of `G(z) = 𝓜f(1 − z)𝓜h(z)` with Laurent coefficients
  `a/(z − n)² + b/(z − n)`, `res_{z=n}[x^{−z} G(z)] = (−a ln x + b) x^{−n}`
  (`residue_cpow_mul_double_pole`); with the Laurent data of 2.5.10 this is 2.5.11–2.5.13.
* 2.5.15 → 2.5.16: when the even coefficients vanish, the sum up to `2n` reindexes to the odd
  terms (`sum_range_odd_of_even_zero`).

**Deferred** (not in Mathlib): the Bessel function `J_ν` and its Mellin transform 2.5.10, hence
the explicit coefficients 2.5.12–2.5.13 and the expansions 2.5.15–2.5.16; and 2.5.14, the
behaviour `|Γ(x + iy)| = √(2π) e^{−π|y|/2} |y|^{x−1/2}(1 + o(1))` as `y → ±∞` (complex Stirling),
which is what makes the contour translation of §2.5(i) legitimate in this example.
-/

open MeasureTheory Filter Topology Set Complex Metric
open scoped Real

namespace Azurite.DLMF

/-- **DLMF 2.5.9**: for `f(t) = 1/(1 + t)`, `𝓜f(1 − z) = π/sin(πz)`, `0 < ℜz < 1`. -/
theorem dlmf_2_5_9 {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    mellin (fun t : ℝ => 1 / (1 + (t : ℂ))) (1 - z) = π / Complex.sin (π * z) := by
  rw [dlmf_table_1_14_5_r4 (by simp; linarith) (by simp; linarith), sub_mul, one_mul,
    Complex.sin_pi_sub, mul_comm]

/-- **DLMF 2.5.11** in general: if `G(z) = a/(z − n)² + b/(z − n) + g(z)` near `n` with `g`
analytic, then `res_{z=n}[x^{−z} G(z)] = (−a ln x + b) x^{−n}` for `x > 0`. -/
theorem residue_cpow_mul_double_pole {x : ℝ} (hx : 0 < x) {G g : ℂ → ℂ} {n a b : ℂ} {R : ℝ}
    (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball n R))
    (hG : ∀ z ∈ annulus n 0 R, G z = a / (z - n) ^ 2 + b / (z - n) + g z) :
    residue (fun z => (x : ℂ) ^ (-z) * G z) n R = (-a * Real.log x + b) * (x : ℂ) ^ (-n) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hpow : Differentiable ℂ fun z : ℂ => (x : ℂ) ^ (-z) :=
    fun z => ((hasDerivAt_neg z).const_cpow (Or.inl hx0)).differentiableAt
  have hr : R / 2 ∈ Ioo 0 R := ⟨by positivity, by linarith⟩
  have hball : closedBall n (R / 2) ⊆ ball n R := closedBall_subset_ball (by linarith)
  -- `F` is analytic on the punctured disc
  have hF : DifferentiableOn ℂ (fun z => (x : ℂ) ^ (-z) * G z) (annulus n 0 R) := by
    intro z hz
    have hz0 : z - n ≠ 0 := norm_pos_iff.mp hz.1
    have hzb : z ∈ ball n R := by rw [mem_ball, dist_eq_norm]; exact hz.2
    have hGd : DifferentiableAt ℂ (fun w => a / (w - n) ^ 2 + b / (w - n) + g w) z :=
      ((differentiableAt_const a).div (((differentiableAt_id).sub_const n).pow 2)
          (pow_ne_zero 2 hz0)).add
        ((differentiableAt_const b).div ((differentiableAt_id).sub_const n) hz0) |>.add
        (hg.differentiableAt (isOpen_ball.mem_nhds hzb))
    refine ((hpow z).mul (hGd.congr_of_eventuallyEq ?_)).differentiableWithinAt
    filter_upwards [(isOpen_annulus n 0 R).mem_nhds hz] with w hw
    exact hG w hw
  rw [residue_eq hF hr]
  -- the integrand on the circle
  have hsph : ∀ z ∈ sphere n (R / 2), z - n ≠ 0 := fun z hz => by
    rw [mem_sphere, dist_eq_norm] at hz
    exact norm_pos_iff.mp (by rw [hz]; exact hr.1)
  have hcongr : ∀ z ∈ sphere n (R / 2), (x : ℂ) ^ (-z) * G z =
      a • ((1 / (z - n) ^ 2) • (x : ℂ) ^ (-z)) + b • ((z - n)⁻¹ • (x : ℂ) ^ (-z)) +
        (x : ℂ) ^ (-z) * g z := fun z hz => by
    have hzA : z ∈ annulus n 0 R := by
      rw [mem_sphere, dist_eq_norm] at hz
      exact ⟨by rw [hz]; exact hr.1, by rw [hz]; exact hr.2⟩
    have := hsph z hz
    rw [hG z hzA]
    simp only [smul_eq_mul]
    field_simp
  have hcont : ContinuousOn (fun z : ℂ => (x : ℂ) ^ (-z)) (sphere n (R / 2)) :=
    hpow.continuous.continuousOn
  have hsub : ContinuousOn (fun z : ℂ => z - n) (sphere n (R / 2)) :=
    (continuous_id.sub continuous_const).continuousOn
  have c1 : ContinuousOn (fun z => a • ((1 / (z - n) ^ 2) • (x : ℂ) ^ (-z)))
      (sphere n (R / 2)) := by
    have h1 : ContinuousOn (fun z : ℂ => 1 / (z - n) ^ 2) (sphere n (R / 2)) :=
      (continuousOn_const (c := (1 : ℂ))).div (hsub.pow 2) fun z hz => pow_ne_zero 2 (hsph z hz)
    have h2 : ContinuousOn (fun z : ℂ => (1 / (z - n) ^ 2) • (x : ℂ) ^ (-z)) (sphere n (R / 2)) :=
      h1.smul hcont
    exact (continuousOn_const (c := a)).smul h2
  have c2 : ContinuousOn (fun z => b • ((z - n)⁻¹ • (x : ℂ) ^ (-z))) (sphere n (R / 2)) := by
    have h1 : ContinuousOn (fun z : ℂ => (z - n)⁻¹) (sphere n (R / 2)) := hsub.inv₀ hsph
    have h2 : ContinuousOn (fun z : ℂ => (z - n)⁻¹ • (x : ℂ) ^ (-z)) (sphere n (R / 2)) :=
      h1.smul hcont
    exact (continuousOn_const (c := b)).smul h2
  have i1 : CircleIntegrable (fun z => a • ((1 / (z - n) ^ 2) • (x : ℂ) ^ (-z))) n (R / 2) :=
    ContinuousOn.circleIntegrable hr.1.le c1
  have i2 : CircleIntegrable (fun z => b • ((z - n)⁻¹ • (x : ℂ) ^ (-z))) n (R / 2) :=
    ContinuousOn.circleIntegrable hr.1.le c2
  have i3 : CircleIntegrable (fun z => (x : ℂ) ^ (-z) * g z) n (R / 2) :=
    ContinuousOn.circleIntegrable hr.1.le
      (hcont.mul (hg.continuousOn.mono (sphere_subset_closedBall.trans hball)))
  have i12 : CircleIntegrable (fun z => a • ((1 / (z - n) ^ 2) • (x : ℂ) ^ (-z)) +
      b • ((z - n)⁻¹ • (x : ℂ) ^ (-z))) n (R / 2) := i1.add i2
  rw [circleIntegral.integral_congr hr.1.le hcongr, circleIntegral.integral_add i12 i3,
    circleIntegral.integral_add i1 i2, circleIntegral.integral_smul, circleIntegral.integral_smul]
  -- the three pieces
  have hd : DifferentiableOn ℂ (fun z : ℂ => (x : ℂ) ^ (-z)) (closedBall n (R / 2)) :=
    hpow.differentiableOn
  have e1 := hd.deriv_eq_smul_circleIntegral hr.1
  have e2 := hd.circleIntegral_sub_inv_smul (mem_ball_self hr.1)
  have e3 : (∮ z in C(n, R / 2), (x : ℂ) ^ (-z) * g z) = 0 := by
    have hc : ContinuousOn (fun z : ℂ => (x : ℂ) ^ (-z) * g z) (closedBall n (R / 2)) :=
      hpow.continuous.continuousOn.mul (hg.continuousOn.mono hball)
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable hr.1.le countable_empty hc
      fun z hz => (hpow z).mul (hg.differentiableAt (isOpen_ball.mem_nhds ?_))
    exact hball (ball_subset_closedBall hz.1)
  have hderiv : deriv (fun z : ℂ => (x : ℂ) ^ (-z)) n = -((x : ℂ) ^ (-n) * Real.log x) := by
    rw [((hasDerivAt_neg n).const_cpow (Or.inl hx0)).deriv, ← Complex.ofReal_log hx.le]
    ring
  rw [e1, e2, e3, hderiv]
  simp only [smul_eq_mul]
  have h2πI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  field_simp
  ring

/-- **DLMF 2.5.15 → 2.5.16**: when the even coefficients vanish, the sum up to `2n` reduces to
the odd terms,
`∑_{s=0}^{2n} (aₛ ln x + bₛ) x^{−s} = ∑_{s=0}^{n−1} (a₂ₛ₊₁ ln x + b₂ₛ₊₁) x^{−2s−1}`. -/
theorem sum_range_odd_of_even_zero {a b : ℕ → ℂ} (ha : ∀ s, a (2 * s) = 0)
    (hb : ∀ s, b (2 * s) = 0) (L x : ℂ) (n : ℕ) :
    ∑ s ∈ Finset.range (2 * n + 1), (a s * L + b s) * x ^ (-(s : ℂ)) =
      ∑ s ∈ Finset.range n, (a (2 * s + 1) * L + b (2 * s + 1)) * x ^ (-(2 * (s : ℂ) + 1)) := by
  induction n with
  | zero => simp [ha 0, hb 0]
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ,
      show 2 * n + 1 + 1 = 2 * (n + 1) by ring, ha, hb]
    push_cast
    ring

end Azurite.DLMF
