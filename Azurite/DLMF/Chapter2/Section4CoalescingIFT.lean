/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section4CoalescingLinear

/-!
# The normal-form map and its local inverse

`cfuΦ r (b, c, h) = ⅓(z + h)³ + b(z + h) + c` on `ℂ × ℂ × discAlg r`. Its strict derivative at
`0` is `cfuL r`, a continuous linear equivalence, so by the inverse function theorem in Banach
spaces `cfuΦ r` has a continuous local inverse `cfuΨ` near `cfuΦ r 0 = ⅓z³`: every `g` in the
disc algebra close to `⅓z³` is `⅓w³ + bw + c` with `w = z + h`, `(b, c, h) = cfuΨ g` small and
depending continuously on `g`. This is the uniform (Chester–Friedman–Ursell) normal form.
-/

open Set Filter Topology Complex Metric

namespace Azurite.DLMF

variable (r : ℝ)

/-- `Φ(b, c, h) = ⅓(z + h)(z + h)(z + h) + b(z + h) + c`. -/
noncomputable def cfuΦ (x : ℂ × ℂ × discAlg r) : discAlg r :=
  (1 / 3 : ℂ) • ((discZ r + x.2.2) * (discZ r + x.2.2) * (discZ r + x.2.2)) +
    x.1 • (discZ r + x.2.2) + x.2.1 • (1 : discAlg r)

theorem cfuΦ_zero : cfuΦ r 0 = (1 / 3 : ℂ) • (discZ r * discZ r * discZ r) := by
  simp [cfuΦ]

variable {r}

theorem hasStrictFDerivAt_cfuΦ (hr : 0 < r) :
    HasStrictFDerivAt (cfuΦ r) (cfuLE hr : (ℂ × ℂ × discAlg r) →L[ℂ] discAlg r) 0 := by
  set Z := discZ r
  set d : (ℂ × ℂ × discAlg r) →L[ℂ] discAlg r :=
    (ContinuousLinearMap.snd ℂ ℂ (discAlg r)).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × discAlg r))
  set pb : (ℂ × ℂ × discAlg r) →L[ℂ] ℂ := ContinuousLinearMap.fst ℂ ℂ (ℂ × discAlg r)
  set pc : (ℂ × ℂ × discAlg r) →L[ℂ] ℂ :=
    (ContinuousLinearMap.fst ℂ ℂ (discAlg r)).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × discAlg r))
  have h1 : HasStrictFDerivAt (fun x : ℂ × ℂ × discAlg r => Z + x.2.2) d 0 :=
    (d.hasStrictFDerivAt).const_add Z
  have h2 := (h1.mul h1).mul h1
  have h3 := h2.const_smul (1 / 3 : ℂ)
  have h4 := (pb.hasStrictFDerivAt).smul h1
  have h5 := (pc.hasStrictFDerivAt).smul
    (hasStrictFDerivAt_const (1 : discAlg r) (0 : ℂ × ℂ × discAlg r))
  have h6 := (h3.add h4).add h5
  refine h6.congr_fderiv (ContinuousLinearMap.ext fun δ => ?_)
  obtain ⟨δb, δc, δh⟩ := δ
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    Pi.mul_apply, Prod.snd_zero, Prod.fst_zero, add_zero, zero_smul, smul_zero, zero_add,
    d, pb, pc, Z, smul_eq_mul]
  rw [show ((cfuLE hr : (ℂ × ℂ × discAlg r) →L[ℂ] discAlg r) (δb, δc, δh)) =
    cfuL r (δb, δc, δh) from rfl, cfuL_apply]
  have key : discZ r * discZ r * δh + discZ r * (discZ r * δh + discZ r * δh) =
      (3 : ℂ) • (discZ r ^ 2 * δh) := by
    rw [Algebra.smul_def, map_ofNat]
    ring
  rw [key, smul_smul]
  norm_num
  abel

/-! ### The local inverse -/

/-- The inverse function theorem applied to `Φ` at `0`: a local homeomorphism. -/
noncomputable def cfuPH (hr : 0 < r) : OpenPartialHomeomorph (ℂ × ℂ × discAlg r) (discAlg r) :=
  HasStrictFDerivAt.toOpenPartialHomeomorph (cfuΦ r) (hasStrictFDerivAt_cfuΦ hr)

theorem cfuPH_apply (hr : 0 < r) (x : ℂ × ℂ × discAlg r) : cfuPH hr x = cfuΦ r x := by
  rw [cfuPH, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]

theorem zero_mem_cfuPH_source (hr : 0 < r) : (0 : ℂ × ℂ × discAlg r) ∈ (cfuPH hr).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source (hasStrictFDerivAt_cfuΦ hr)

theorem cfuΦ_zero_mem_cfuPH_target (hr : 0 < r) : cfuΦ r 0 ∈ (cfuPH hr).target :=
  HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target (hasStrictFDerivAt_cfuΦ hr)

theorem isOpen_cfuPH_target (hr : 0 < r) : IsOpen (cfuPH hr).target := (cfuPH hr).open_target

theorem continuousOn_cfuPH_symm (hr : 0 < r) :
    ContinuousOn (cfuPH hr).symm (cfuPH hr).target := (cfuPH hr).continuousOn_symm

theorem cfuΦ_cfuPH_symm (hr : 0 < r) {g : discAlg r} (hg : g ∈ (cfuPH hr).target) :
    cfuΦ r ((cfuPH hr).symm g) = g := by
  rw [← cfuPH_apply]
  exact (cfuPH hr).right_inv hg

theorem cfuPH_symm_zero (hr : 0 < r) : (cfuPH hr).symm (cfuΦ r 0) = 0 := by
  rw [← cfuPH_apply]
  exact (cfuPH hr).left_inv (zero_mem_cfuPH_source hr)

/-- Pointwise meaning of `Φ`: `Φ(b, c, h)(z) = ⅓(z + h(z))³ + b(z + h(z)) + c`. -/
theorem discExt_cfuΦ (x : ℂ × ℂ × discAlg r) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) :
    discExt r (cfuΦ r x : C(closedBall (0 : ℂ) r, ℂ)) z =
      (1 / 3 : ℂ) * (z + discExt r (x.2.2 : C(closedBall (0 : ℂ) r, ℂ)) z) ^ 3 +
        x.1 * (z + discExt r (x.2.2 : C(closedBall (0 : ℂ) r, ℂ)) z) + x.2.1 := by
  rw [cfuΦ]
  simp only [Subalgebra.coe_add, Subalgebra.coe_smul, Subalgebra.coe_mul, Subalgebra.coe_one]
  simp only [discExt_add r _ _ hz, discExt_smul r _ _ hz, discExt_mul r _ _ hz, discExt_one r hz,
    discExt_discZ r hz]
  ring

/-! ### Small perturbations of the identity -/

/-- Cauchy's estimate: for `h` in the disc algebra and `|W| < r₂ < r`,
`|h′(W)| ≤ ‖h‖/(r − r₂)`. -/
theorem norm_deriv_discExt_le (h : discAlg r) {r₂ : ℝ} (hr₂ : r₂ < r) {W : ℂ}
    (hW : W ∈ ball (0 : ℂ) r₂) :
    ‖deriv (discExt r (h : C(closedBall (0 : ℂ) r, ℂ))) W‖ ≤ ‖h‖ / (r - r₂) := by
  have hpos : 0 < r - r₂ := sub_pos.mpr hr₂
  have hWn : ‖W‖ < r₂ := by simpa using hW
  have hsub : closedBall W (r - r₂) ⊆ ball 0 r := fun ξ hξ => by
    rw [mem_closedBall, dist_eq_norm] at hξ
    rw [mem_ball, dist_zero_right]
    calc ‖ξ‖ = ‖(ξ - W) + W‖ := by ring_nf
      _ ≤ ‖ξ - W‖ + ‖W‖ := norm_add_le _ _
      _ < r := by linarith
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hpos
    (((differentiableOn_discExt r h).mono (closure_ball_subset_closedBall.trans hsub)).diffContOnCl)
    fun ξ hξ => norm_discExt_le r h (ball_subset_closedBall (hsub (sphere_subset_closedBall hξ)))

/-- If `‖h‖ < (r − r₂)/2`, then `W ↦ W + h(W)` is one-to-one with nonzero derivative on
`|W| < r₂`. -/
theorem injOn_add_discExt (h : discAlg r) {r₂ : ℝ} (hr₂ : r₂ < r)
    (hsmall : ‖h‖ < (r - r₂) / 2) :
    InjOn (fun W => W + discExt r (h : C(closedBall (0 : ℂ) r, ℂ)) W) (ball 0 r₂) ∧
      ∀ W ∈ ball (0 : ℂ) r₂,
        deriv (fun W => W + discExt r (h : C(closedBall (0 : ℂ) r, ℂ)) W) W ≠ 0 := by
  have hpos : 0 < r - r₂ := sub_pos.mpr hr₂
  set H := discExt r (h : C(closedBall (0 : ℂ) r, ℂ)) with hH
  have hbound : ∀ W ∈ ball (0 : ℂ) r₂, ‖deriv H W‖ ≤ 1 / 2 := fun W hW =>
    (norm_deriv_discExt_le h hr₂ hW).trans (by
      rw [div_le_iff₀ hpos]
      linarith)
  have hdiff : ∀ W ∈ ball (0 : ℂ) r₂, DifferentiableAt ℂ H W := fun W hW =>
    (differentiableOn_discExt r h).differentiableAt
      (isOpen_ball.mem_nhds (ball_subset_ball hr₂.le hW))
  constructor
  · intro W₁ h₁ W₂ h₂ heq
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_ball 0 r₂) h₁ h₂
    have e : W₂ - W₁ = -(H W₂ - H W₁) := by
      simp only at heq
      linear_combination -heq
    have h3 : ‖W₂ - W₁‖ ≤ 1 / 2 * ‖W₂ - W₁‖ :=
      calc ‖W₂ - W₁‖ = ‖H W₂ - H W₁‖ := by rw [e, norm_neg]
        _ ≤ 1 / 2 * ‖W₂ - W₁‖ := hmv
    have h4 : ‖W₂ - W₁‖ = 0 := by linarith [norm_nonneg (W₂ - W₁)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp h4)).symm
  · intro W hW
    have hd : HasDerivAt (fun W => W + H W) (1 + deriv H W) W :=
      (hasDerivAt_id' W).add (hdiff W hW).hasDerivAt
    rw [hd.deriv]
    intro h0
    have h1 := hbound W hW
    have e : deriv H W = -1 := by linear_combination h0
    rw [e, norm_neg, norm_one] at h1
    linarith

end Azurite.DLMF
