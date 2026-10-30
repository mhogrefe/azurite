/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14HilbertPichorides
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# DLMF 1.14.45: subharmonic functions of holomorphic functions on the half-plane

Let `F` be holomorphic on `{Im z > −c}` with `F = O(1/z)` and `F′ = O(1/z²)` on the closed upper
half-plane. Let `Ψ` be `C²`, vanishing to second order at `0`, with
`D²Ψ(w)(v, v) + D²Ψ(w)(iv, iv) ≥ 0`. Then `∫_ℝ Ψ(F(x)) dx ≥ 0` (`integral_comp_nonneg`).

Green's identity on `[−R, R] × [0, R]` (Mathlib's `integral2_divergence_prod_of_hasFDerivAt`)
applied to `(y ∂ₓs, y ∂ᵧs − s)`, `s = Ψ ∘ F`, has divergence `y Δs ≥ 0` (`hasFDerivAt_green`). The
far sides contribute `O(1/R)` (`integral_comp_ge_rect`).
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real Interval

namespace Azurite.DLMF

/-- A `C²` function with `Ψ(0) = 0` and `DΨ(0) = 0` is `O(|w|²)`, with derivative `O(|w|)`, on
balls. -/
theorem exists_quadratic_bound {Ψ : ℂ → ℝ} (hΨ : ContDiff ℝ 2 Ψ) (h0 : Ψ 0 = 0)
    (hd0 : fderiv ℝ Ψ 0 = 0) (K : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ w : ℂ, ‖w‖ ≤ K → |Ψ w| ≤ M * ‖w‖ ^ 2 ∧ ‖fderiv ℝ Ψ w‖ ≤ M * ‖w‖ := by
  have hD1 : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right (m := 1) (by norm_num)
  obtain ⟨L, hL⟩ := (hD1.contDiffOn (s := Metric.closedBall (0 : ℂ) K)).exists_lipschitzOnWith
    one_ne_zero (convex_closedBall _ _) (isCompact_closedBall _ _)
  set M : ℝ := (L : ℝ) with hM
  have hM0 : 0 ≤ M := L.2
  refine ⟨M, hM0, fun w hw => ?_⟩
  have hK : 0 ≤ K := (norm_nonneg w).trans hw
  have h1 : ∀ u : ℂ, ‖u‖ ≤ K → ‖fderiv ℝ Ψ u‖ ≤ M * ‖u‖ := fun u hu => by
    have := hL.norm_sub_le (by simpa using hu) (Metric.mem_closedBall_self hK)
    rwa [hd0, sub_zero, sub_zero] at this
  refine ⟨?_, h1 w hw⟩
  have := (convex_closedBall (0 : ℂ) ‖w‖).norm_image_sub_le_of_norm_fderiv_le (x := 0) (y := w)
    (fun x _ => hΨ.differentiable (by norm_num) x)
    (fun u hu => (h1 u ((by simpa using hu : ‖u‖ ≤ ‖w‖).trans hw)).trans
      (mul_le_mul_of_nonneg_left (by simpa using hu) hM0))
    (Metric.mem_closedBall_self (norm_nonneg w)) (by simp)
  rw [h0, sub_zero, sub_zero, Real.norm_eq_abs] at this
  calc |Ψ w| ≤ M * ‖w‖ * ‖w‖ := this
    _ = M * ‖w‖ ^ 2 := by ring

/-! ### The vector field `(y ∂ₓs, y ∂ᵧs − s)` for `s(x, y) = Ψ(F(x + iy))` -/

/-- The embedding `(x, y) ↦ x + iy`. -/
noncomputable abbrev toC : ℝ × ℝ →L[ℝ] ℂ := (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)

theorem toC_apply (p : ℝ × ℝ) : toC p = p.1 + p.2 * I := equivRealProdCLM_symm_apply p

theorem toC_im (p : ℝ × ℝ) : (toC p).im = p.2 := by simp [toC_apply]

/-- `∂ₓ s`. -/
noncomputable def greenSx (F : ℂ → ℂ) (Ψ : ℂ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ Ψ (F (toC p)) (deriv F (toC p))

/-- `∂ᵧ s`. -/
noncomputable def greenSy (F : ℂ → ℂ) (Ψ : ℂ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ Ψ (F (toC p)) (deriv F (toC p) * I)

/-- The Laplacian factor `D²Ψ(F)(F′, F′) + D²Ψ(F)(iF′, iF′)`. -/
noncomputable def greenQ (F : ℂ → ℂ) (Ψ : ℂ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ Ψ) (F (toC p)) (deriv F (toC p)) (deriv F (toC p)) +
    fderiv ℝ (fderiv ℝ Ψ) (F (toC p)) (deriv F (toC p) * I) (deriv F (toC p) * I)

theorem hasFDerivAt_green {F : ℂ → ℂ} {c : ℝ} (hF : DifferentiableOn ℂ F {z | -c < z.im})
    {Ψ : ℂ → ℝ} (hΨ : ContDiff ℝ 2 Ψ) {p : ℝ × ℝ} (hp : -c < p.2) :
    ∃ L₁ L₂ : ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun q : ℝ × ℝ => q.2 * greenSx F Ψ q) L₁ p ∧
      HasFDerivAt (fun q : ℝ × ℝ => q.2 * greenSy F Ψ q - Ψ (F (toC q))) L₂ p ∧
      L₁ (1, 0) + L₂ (0, 1) = p.2 * greenQ F Ψ p := by
  have hUo : IsOpen {z : ℂ | -c < z.im} := isOpen_lt continuous_const continuous_im
  set z := toC p with hz
  have hzU : z ∈ {z : ℂ | -c < z.im} := by simp [hz, hp]
  have hF1 : HasDerivAt F (deriv F z) z :=
    (hF.differentiableAt (hUo.mem_nhds hzU)).hasDerivAt
  have hF2 : HasDerivAt (deriv F) (deriv (deriv F) z) z :=
    ((hF.deriv hUo).differentiableAt (hUo.mem_nhds hzU)).hasDerivAt
  have hD1 : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right (m := 1) (by norm_num)
  have hΨd : HasFDerivAt Ψ (fderiv ℝ Ψ (F z)) (F z) :=
    (hΨ.differentiable (by norm_num) _).hasFDerivAt
  have hD1d : HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) (F z)) (F z) :=
    (hD1.differentiable (by norm_num) _).hasFDerivAt
  have hι : HasFDerivAt (fun q : ℝ × ℝ => toC q) toC p := toC.hasFDerivAt
  have hFι := (hF1.hasFDerivAt.restrictScalars ℝ).comp p hι
  have hF'ι := (hF2.hasFDerivAt.restrictScalars ℝ).comp p hι
  have hs := hΨd.comp p hFι
  have hsx := (hD1d.comp p hFι).clm_apply hF'ι
  have hsy := (hD1d.comp p hFι).clm_apply (hF'ι.mul_const I)
  have hsnd : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    hasFDerivAt_snd
  refine ⟨_, _, hsnd.mul hsx, (hsnd.mul hsy).sub hs, ?_⟩
  have h10 : equivRealProdCLM.symm ((1, 0) : ℝ × ℝ) = 1 := by simp [equivRealProdCLM_symm_apply]
  have h01 : equivRealProdCLM.symm ((0, 1) : ℝ × ℝ) = I := by simp [equivRealProdCLM_symm_apply]
  have hzp : equivRealProdCLM.symm p = z := rfl
  have hII : I * (I * deriv (deriv F) z) = -deriv (deriv F) z := by
    rw [← mul_assoc, I_mul_I, neg_one_mul]
  simp
  simp only [h10, h01, hzp, one_mul, hII, map_neg, greenQ, ← hz, mul_comm I (deriv F z)]
  ring

section Green

variable {F : ℂ → ℂ} {c K : ℝ} {Ψ : ℂ → ℝ}

/-- Decay of `s`, `∂ₓs`, `∂ᵧs` in the closed upper half-plane. -/
theorem green_bounds (hK : 0 ≤ K) (hFb : ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ ≤ K / (1 + ‖z‖))
    (hF'b : ∀ z : ℂ, 0 ≤ z.im → ‖deriv F z‖ ≤ K / (1 + ‖z‖) ^ 2) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ w : ℂ, ‖w‖ ≤ K → |Ψ w| ≤ M * ‖w‖ ^ 2 ∧ ‖fderiv ℝ Ψ w‖ ≤ M * ‖w‖)
    {z : ℂ} (hz : 0 ≤ z.im) :
    |Ψ (F z)| ≤ M * K ^ 2 / (1 + ‖z‖) ^ 2 ∧
    |fderiv ℝ Ψ (F z) (deriv F z)| ≤ M * K ^ 2 / (1 + ‖z‖) ^ 3 ∧
    |fderiv ℝ Ψ (F z) (deriv F z * I)| ≤ M * K ^ 2 / (1 + ‖z‖) ^ 3 := by
  have h1 : 0 < 1 + ‖z‖ := by positivity
  have hF := hFb z hz
  have hFK : ‖F z‖ ≤ K := hF.trans (div_le_self hK (by linarith [norm_nonneg z]))
  obtain ⟨hΨ1, hΨ2⟩ := hM (F z) hFK
  have hF' := hF'b z hz
  have hd : ∀ v : ℂ, ‖v‖ = ‖deriv F z‖ →
      |fderiv ℝ Ψ (F z) v| ≤ M * K ^ 2 / (1 + ‖z‖) ^ 3 := fun v hv => by
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ Ψ (F z) v‖ ≤ ‖fderiv ℝ Ψ (F z)‖ * ‖v‖ := (fderiv ℝ Ψ (F z)).le_opNorm v
      _ ≤ (M * (K / (1 + ‖z‖))) * (K / (1 + ‖z‖) ^ 2) := by
          rw [hv]
          exact mul_le_mul (hΨ2.trans (mul_le_mul_of_nonneg_left hF hM0)) hF'
            (norm_nonneg _) (by positivity)
      _ = M * K ^ 2 / (1 + ‖z‖) ^ 3 := by field_simp
  refine ⟨?_, hd _ rfl, hd _ (by rw [norm_mul, Complex.norm_I, mul_one])⟩
  calc |Ψ (F z)| ≤ M * ‖F z‖ ^ 2 := hΨ1
    _ ≤ M * (K / (1 + ‖z‖)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hF 2) hM0
    _ = M * K ^ 2 / (1 + ‖z‖) ^ 2 := by field_simp

theorem div_pow_le_of_le {A R r : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) (hr : R ≤ r) (k : ℕ) :
    A / (1 + r) ^ k ≤ A / (1 + R) ^ k :=
  div_le_div_of_nonneg_left hA (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) k)

/-- The rectangle estimate: `∫_{−R}^R Ψ(F(x)) dx ≥ −6MK²/(1 + R)`. -/
theorem integral_comp_ge_rect (hc : 0 < c) (hF : DifferentiableOn ℂ F {z | -c < z.im})
    (hK : 0 ≤ K) (hFb : ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ ≤ K / (1 + ‖z‖))
    (hF'b : ∀ z : ℂ, 0 ≤ z.im → ‖deriv F z‖ ≤ K / (1 + ‖z‖) ^ 2) (hΨ : ContDiff ℝ 2 Ψ)
    (hSH : ∀ w v : ℂ, 0 ≤ fderiv ℝ (fderiv ℝ Ψ) w v v + fderiv ℝ (fderiv ℝ Ψ) w (v * I) (v * I))
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ w : ℂ, ‖w‖ ≤ K → |Ψ w| ≤ M * ‖w‖ ^ 2 ∧ ‖fderiv ℝ Ψ w‖ ≤ M * ‖w‖)
    {R : ℝ} (hR : 0 < R) :
    -(6 * (M * K ^ 2) / (1 + R)) ≤ ∫ x in -R..R, Ψ (F x) := by
  have hB := fun z hz => green_bounds (Ψ := Ψ) hK hFb hF'b hM0 hM (z := z) hz
  have hUo : IsOpen {z : ℂ | -c < z.im} := isOpen_lt continuous_const continuous_im
  set A := M * K ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  set f₁ := fun q : ℝ × ℝ => q.2 * greenSx F Ψ q with hf₁
  set g₁ := fun q : ℝ × ℝ => q.2 * greenSy F Ψ q - Ψ (F (toC q)) with hg₁
  have hd : ∀ q : ℝ × ℝ, -c < q.2 → HasFDerivAt f₁ (fderiv ℝ f₁ q) q ∧
      HasFDerivAt g₁ (fderiv ℝ g₁ q) q ∧
      fderiv ℝ f₁ q (1, 0) + fderiv ℝ g₁ q (0, 1) = q.2 * greenQ F Ψ q := fun q hq => by
    obtain ⟨L₁, L₂, h1, h2, h3⟩ := hasFDerivAt_green hF hΨ hq
    rw [h1.fderiv, h2.fderiv]
    exact ⟨h1, h2, h3⟩
  set Rect := uIcc (-R) R ×ˢ uIcc (0 : ℝ) R with hRect
  have hrect : ∀ q ∈ Rect, 0 ≤ q.2 := fun q hq => by
    have := hq.2
    rw [uIcc_of_le hR.le] at this
    exact this.1
  have hrc : ∀ q ∈ Rect, -c < q.2 := fun q hq => by linarith [hrect q hq]
  have hmaps : MapsTo (fun q : ℝ × ℝ => toC q) Rect {z : ℂ | -c < z.im} := fun q hq => by
    simp only [Set.mem_ofPred_eq, toC_im]; exact hrc q hq
  have hFt : ContinuousOn (fun q => F (toC q)) Rect :=
    hF.continuousOn.comp toC.continuous.continuousOn hmaps
  have hF't : ContinuousOn (fun q => deriv F (toC q)) Rect :=
    (hF.deriv hUo).continuousOn.comp toC.continuous.continuousOn hmaps
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ Ψ)) :=
    (hΨ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hQc : ContinuousOn (fun q : ℝ × ℝ => q.2 * greenQ F Ψ q) Rect := by
    refine continuous_snd.continuousOn.mul ?_
    exact (((hD2c.comp_continuousOn hFt).clm_apply hF't).clm_apply hF't).add
      (((hD2c.comp_continuousOn hFt).clm_apply (hF't.mul continuousOn_const)).clm_apply
        (hF't.mul continuousOn_const))
  have hint : ∀ q ∈ Ioo (min (-R) R) (max (-R) R) ×ˢ Ioo (min 0 R) (max 0 R), -c < q.2 :=
    fun q hq => by
      have := hq.2.1
      rw [min_eq_left hR.le] at this
      linarith
  have hdiv := integral2_divergence_prod_of_hasFDerivAt f₁ g₁ (fderiv ℝ f₁) (fderiv ℝ g₁)
    (-R) 0 R R (fun q hq => (hd q (hrc q hq)).1.continuousAt.continuousWithinAt)
    (fun q hq => (hd q (hrc q hq)).2.1.continuousAt.continuousWithinAt)
    (fun q hq => (hd q (hint q hq)).1) (fun q hq => (hd q (hint q hq)).2.1)
    ((hQc.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).congr_fun
      (fun q hq => ((hd q (hrc q hq)).2.2).symm)
      (measurableSet_uIcc.prod measurableSet_uIcc))
  -- the interior integral is nonnegative
  have hLHS : 0 ≤ ∫ x in -R..R, ∫ y in (0 : ℝ)..R,
      fderiv ℝ f₁ (x, y) (1, 0) + fderiv ℝ g₁ (x, y) (0, 1) := by
    refine intervalIntegral.integral_nonneg (by linarith) fun x _ => ?_
    refine intervalIntegral.integral_nonneg hR.le fun y hy => ?_
    rw [(hd (x, y) (by simp only; linarith [hy.1])).2.2]
    exact mul_nonneg hy.1 (hSH _ _)
  -- boundary terms
  have hbot : ∫ x in -R..R, g₁ (x, 0) = -∫ x in -R..R, Ψ (F x) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp [hg₁, toC_apply]
  have hnorm : ∀ q : ℝ × ℝ, |q.1| ≤ ‖toC q‖ ∧ |q.2| ≤ ‖toC q‖ := fun q => by
    have h1 := Complex.abs_re_le_norm (toC q)
    have h2 := Complex.abs_im_le_norm (toC q)
    have hre : (toC q).re = q.1 := by simp [toC_apply]
    rw [hre] at h1
    rw [toC_im] at h2
    exact ⟨h1, h2⟩
  have htop : |∫ x in -R..R, g₁ (x, R)| ≤ 4 * A / (1 + R) := by
    have hpt : ∀ x ∈ Ι (-R) R, ‖g₁ (x, R)‖ ≤ 2 * A / (1 + R) ^ 2 := fun x _ => by
      have hz : 0 ≤ (toC (x, R)).im := by rw [toC_im]; exact hR.le
      obtain ⟨b1, -, b3⟩ := hB _ hz
      have hRz : R ≤ ‖toC (x, R)‖ := by
        have := (hnorm (x, R)).2; rwa [abs_of_pos hR] at this
      have e1 := (b1.trans (div_pow_le_of_le hA0 hR.le hRz 2))
      have e3 := (b3.trans (div_pow_le_of_le hA0 hR.le hRz 3))
      rw [Real.norm_eq_abs]
      simp only [hg₁, greenSy]
      calc |R * fderiv ℝ Ψ (F (toC (x, R))) (deriv F (toC (x, R)) * I) - Ψ (F (toC (x, R)))|
          ≤ R * (A / (1 + R) ^ 3) + A / (1 + R) ^ 2 := by
            refine (abs_sub _ _).trans (add_le_add ?_ e1)
            rw [abs_mul, abs_of_pos hR]
            exact mul_le_mul_of_nonneg_left e3 hR.le
        _ ≤ 2 * A / (1 + R) ^ 2 := by
            have h1 : R * (A / (1 + R) ^ 3) ≤ A / (1 + R) ^ 2 := by
              rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
              nlinarith [mul_nonneg hA0 (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + R) 2)]
            have h2 : 2 * A / (1 + R) ^ 2 = A / (1 + R) ^ 2 + A / (1 + R) ^ 2 := by ring
            linarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [Real.norm_eq_abs, show R - -R = 2 * R by ring,
      abs_of_pos (by linarith : (0 : ℝ) < 2 * R)] at this
    refine this.trans ?_
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hA0 (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + R) 2)]
  have hside : ∀ x : ℝ, |x| = R → |∫ y in (0 : ℝ)..R, f₁ (x, y)| ≤ A / (1 + R) := by
    intro x hx
    have hpt : ∀ y ∈ Ι (0 : ℝ) R, ‖f₁ (x, y)‖ ≤ R * (A / (1 + R) ^ 3) := fun y hy => by
      rw [uIoc_of_le hR.le] at hy
      have hz : 0 ≤ (toC (x, y)).im := by rw [toC_im]; exact hy.1.le
      obtain ⟨-, b2, -⟩ := hB _ hz
      have hRz : R ≤ ‖toC (x, y)‖ := by rw [← hx]; exact (hnorm (x, y)).1
      rw [Real.norm_eq_abs]
      simp only [hf₁, greenSx]
      rw [abs_mul, abs_of_pos hy.1]
      exact mul_le_mul hy.2 (b2.trans (div_pow_le_of_le hA0 hR.le hRz 3)) (abs_nonneg _)
        hR.le
    have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos hR] at this
    refine this.trans ?_
    rw [mul_div_assoc', div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 0 ≤ (1 + R) ^ 2 - R ^ 2 := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hA0 (by linarith : (0 : ℝ) ≤ 1 + R)) h1]
  have hs1 := hside R (abs_of_pos hR)
  have hs2 := hside (-R) (by rw [abs_neg, abs_of_pos hR])
  rw [hbot] at hdiv
  have := abs_le.mp htop
  have := abs_le.mp hs1
  have := abs_le.mp hs2
  have h6 : 6 * A / (1 + R) = 4 * A / (1 + R) + A / (1 + R) + A / (1 + R) := by ring
  linarith

/-- **Subharmonic composition integrated along the boundary.** Suppose `F` is holomorphic on
`{Im z > −c}` and, on the closed upper half-plane, `|F(z)| ≤ K/(1 + |z|)` and
`|F′(z)| ≤ K/(1 + |z|)²`. Suppose also that `Ψ` is `C²` and vanishes to second order at `0`, and
is subharmonic: `D²Ψ(w)(v, v) + D²Ψ(w)(iv, iv) ≥ 0`. Then `Ψ ∘ F` is integrable on `ℝ` and
`∫_ℝ Ψ(F(x)) dx ≥ 0`. The proof applies Green's identity on `[−R, R] × [0, R]` to
`(y ∂ₓs, y ∂ᵧs − s)`, whose divergence is `y Δs ≥ 0`. -/
theorem integral_comp_nonneg (hc : 0 < c) (hF : DifferentiableOn ℂ F {z | -c < z.im})
    (hK : 0 ≤ K) (hFb : ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ ≤ K / (1 + ‖z‖))
    (hF'b : ∀ z : ℂ, 0 ≤ z.im → ‖deriv F z‖ ≤ K / (1 + ‖z‖) ^ 2) (hΨ : ContDiff ℝ 2 Ψ)
    (h0 : Ψ 0 = 0) (hd0 : fderiv ℝ Ψ 0 = 0)
    (hSH : ∀ w v : ℂ, 0 ≤ fderiv ℝ (fderiv ℝ Ψ) w v v + fderiv ℝ (fderiv ℝ Ψ) w (v * I) (v * I)) :
    Integrable (fun x : ℝ => Ψ (F x)) ∧ 0 ≤ ∫ x : ℝ, Ψ (F x) := by
  obtain ⟨M, hM0, hM⟩ := exists_quadratic_bound hΨ h0 hd0 K
  have hreal : ∀ x : ℝ, (x : ℂ) ∈ {z : ℂ | -c < z.im} := fun x => by simp [hc]
  have hcont : Continuous fun x : ℝ => Ψ (F x) :=
    hΨ.continuous.comp (hF.continuousOn.comp_continuous continuous_ofReal hreal)
  have hint : Integrable fun x : ℝ => Ψ (F x) := by
    refine (integrable_inv_one_add_sq.const_mul (M * K ^ 2)).mono' hcont.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    have h1 := (green_bounds (Ψ := Ψ) hK hFb hF'b hM0 hM (z := (x : ℂ)) (by simp)).1
    rw [Real.norm_eq_abs]
    refine h1.trans ?_
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine inv_anti₀ (by positivity) ?_
    nlinarith [sq_abs x, abs_nonneg x]
  refine ⟨hint, ?_⟩
  have hlim := intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hE : Tendsto (fun R : ℝ => -(6 * (M * K ^ 2) / (1 + R))) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := 6 * (M * K ^ 2))).div_atTop
      (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    simpa using this.neg
  refine le_of_tendsto_of_tendsto hE hlim ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  exact integral_comp_ge_rect hc hF hK hFb hF'b hΨ hSH hM0 hM hR

end Green

end Azurite.DLMF
