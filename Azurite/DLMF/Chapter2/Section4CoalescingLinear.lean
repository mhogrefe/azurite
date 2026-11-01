/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section4CoalescingDisc

/-!
# The linearized normal-form map on the disc algebra

`cfuL r : ℂ × ℂ × discAlg r →L[ℂ] discAlg r`, `(b, c, h) ↦ c + b z + z² h`, is the derivative at
`0` of `(b, c, h) ↦ ⅓(z + h)³ + b(z + h) + c`. It is a continuous linear bijection (`cfuLE`):
injective by evaluating at `0`, differentiating at `0` and dividing by `z²`; surjective since
`g = g(0) + g′(0) z + z² k` with `k = dslope (dslope g 0) 0` in the disc algebra.
-/

open Set Filter Topology Complex Metric

namespace Azurite.DLMF

variable {r : ℝ}

/-- An element of the disc algebra from a function continuous on the closed disc and analytic
inside. -/
noncomputable def discMk (k : ℂ → ℂ) (hk : ContinuousOn k (closedBall (0 : ℂ) r))
    (hd : DifferentiableOn ℂ k (ball 0 r)) : discAlg r :=
  ⟨⟨fun x => k x, continuousOn_iff_continuous_domRestrict.mp hk⟩, by
    rw [mem_discAlg]
    exact hd.congr fun z hz => by
      rw [discExt_apply r _ (ball_subset_closedBall hz)]
      rfl⟩

theorem discExt_discMk {k : ℂ → ℂ} (hk : ContinuousOn k (closedBall (0 : ℂ) r))
    (hd : DifferentiableOn ℂ k (ball 0 r)) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) :
    discExt r (discMk k hk hd : C(closedBall (0 : ℂ) r, ℂ)) z = k z := by
  rw [discExt_apply r _ hz]
  rfl

theorem discAlg_ext {F G : discAlg r}
    (h : ∀ z ∈ closedBall (0 : ℂ) r, discExt r (F : C(closedBall (0 : ℂ) r, ℂ)) z =
      discExt r (G : C(closedBall (0 : ℂ) r, ℂ)) z) : F = G := by
  refine Subtype.ext (ContinuousMap.ext fun x => ?_)
  have := h x x.2
  rwa [discExt_coe, discExt_coe] at this

variable (r)

/-- `(b, c, h) ↦ c + b z + z² h`. -/
noncomputable def cfuL : (ℂ × ℂ × discAlg r) →L[ℂ] discAlg r :=
  (ContinuousLinearMap.toSpanSingleton ℂ (discZ r)).comp
      (ContinuousLinearMap.fst ℂ ℂ (ℂ × discAlg r)) +
    (ContinuousLinearMap.toSpanSingleton ℂ (1 : discAlg r)).comp
      ((ContinuousLinearMap.fst ℂ ℂ (discAlg r)).comp
        (ContinuousLinearMap.snd ℂ ℂ (ℂ × discAlg r))) +
    (ContinuousLinearMap.mul ℂ (discAlg r) (discZ r ^ 2)).comp
      ((ContinuousLinearMap.snd ℂ ℂ (discAlg r)).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × discAlg r)))

theorem cfuL_apply (x : ℂ × ℂ × discAlg r) :
    cfuL r x = x.1 • discZ r + x.2.1 • (1 : discAlg r) + discZ r ^ 2 * x.2.2 := by
  simp [cfuL, ContinuousLinearMap.toSpanSingleton_apply]

theorem discExt_cfuL (x : ℂ × ℂ × discAlg r) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) :
    discExt r (cfuL r x : C(closedBall (0 : ℂ) r, ℂ)) z =
      x.1 * z + x.2.1 + z ^ 2 * discExt r (x.2.2 : C(closedBall (0 : ℂ) r, ℂ)) z := by
  rw [cfuL_apply]
  simp only [Subalgebra.coe_add, Subalgebra.coe_smul, Subalgebra.coe_mul, Subalgebra.coe_pow,
    Subalgebra.coe_one]
  rw [discExt_add r _ _ hz, discExt_add r _ _ hz, discExt_smul r _ _ hz, discExt_smul r _ _ hz,
    discExt_mul r _ _ hz, discExt_one r hz, pow_two, discExt_mul r _ _ hz, discExt_discZ r hz]
  ring

theorem discExt_zero {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) :
    discExt r ((0 : discAlg r) : C(closedBall (0 : ℂ) r, ℂ)) z = 0 := by
  simp only [Subalgebra.coe_zero, discExt_apply r _ hz, ContinuousMap.zero_apply]

variable {r}

theorem cfuL_ker (hr : 0 < r) : (cfuL r).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  rintro ⟨b, c, h⟩ hx
  set H := discExt r (h : C(closedBall (0 : ℂ) r, ℂ)) with hH
  have h0 : ∀ z ∈ closedBall (0 : ℂ) r, b * z + c + z ^ 2 * H z = 0 := fun z hz => by
    have := discExt_cfuL r (b, c, h) hz
    have hx' : cfuL r (b, c, h) = 0 := hx
    rw [hx', discExt_zero r hz] at this
    exact this.symm
  have hc : c = 0 := by simpa using h0 0 (mem_closedBall_self hr.le)
  have hHd : DifferentiableOn ℂ H (ball 0 r) := differentiableOn_discExt r h
  have hn : ball (0 : ℂ) r ∈ 𝓝 0 := isOpen_ball.mem_nhds (mem_ball_self hr)
  have hfun : ∀ᶠ z in 𝓝 (0 : ℂ), b * z + z ^ 2 * H z = 0 := by
    filter_upwards [hn] with z hz
    have := h0 z (ball_subset_closedBall hz)
    rwa [hc, add_zero] at this
  have hb : b = 0 := by
    have h1 : HasDerivAt (fun z => b * z + z ^ 2 * H z) (b * 1 + (2 * (0 : ℂ) ^ 1 * H 0 +
        0 ^ 2 * deriv H 0)) 0 :=
      ((hasDerivAt_id' 0).const_mul b).add
        ((hasDerivAt_pow 2 0).mul (hHd.differentiableAt hn).hasDerivAt)
    have h2 : HasDerivAt (fun z => b * z + z ^ 2 * H z) 0 0 :=
      (hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hfun
    have := h1.unique h2
    simpa using this
  have hH0 : ∀ z ∈ closedBall (0 : ℂ) r, z ≠ 0 → H z = 0 := fun z hz hz0 => by
    have := h0 z hz
    rw [hb, hc, zero_mul, zero_add, zero_add] at this
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hz0)
  have hH00 : H 0 = 0 := by
    have hcont : ContinuousAt H 0 := (hHd.differentiableAt hn).continuousAt
    have hev : H =ᶠ[𝓝[≠] 0] fun _ => 0 := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hn] with z hz hzb
      exact hH0 z (ball_subset_closedBall hzb) hz
    exact tendsto_nhds_unique ((hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' hev)
      tendsto_const_nhds
  have hh : h = 0 := discAlg_ext fun z hz => by
    rw [discExt_zero r hz]
    by_cases hz0 : z = 0
    · rw [hz0]
      exact hH00
    · exact hH0 z hz hz0
  rw [hb, hc, hh]
  rfl

theorem cfuL_range (hr : 0 < r) : (cfuL r).range = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro g
  set G := discExt r (g : C(closedBall (0 : ℂ) r, ℂ)) with hG
  have hGd : DifferentiableOn ℂ G (ball 0 r) := differentiableOn_discExt r g
  have hGc : ContinuousOn G (closedBall 0 r) := continuousOn_discExt r g
  have hn : ball (0 : ℂ) r ∈ 𝓝 0 := isOpen_ball.mem_nhds (mem_ball_self hr)
  set k : ℂ → ℂ := dslope (dslope G 0) 0 with hk
  have hkd : DifferentiableOn ℂ k (ball 0 r) :=
    (Complex.differentiableOn_dslope hn).mpr ((Complex.differentiableOn_dslope hn).mpr hGd)
  have kform : ∀ w : ℂ, w ≠ 0 → k w = (G w - G 0 - deriv G 0 * w) / w ^ 2 := fun w hw => by
    rw [hk, dslope_of_ne _ hw, slope_def_field, dslope_same, dslope_of_ne _ hw, slope_def_field]
    field_simp
    ring
  have hkc : ContinuousOn k (closedBall 0 r) := by
    intro z hz
    by_cases hzb : z ∈ ball (0 : ℂ) r
    · exact (hkd.differentiableAt (isOpen_ball.mem_nhds hzb)).continuousAt.continuousWithinAt
    · have hz0 : z ≠ 0 := by
        rintro rfl
        exact hzb (mem_ball_self hr)
      have hq : ContinuousWithinAt (fun w => (G w - G 0 - deriv G 0 * w) / w ^ 2)
          (closedBall 0 r) z :=
        (((hGc z hz).sub continuousWithinAt_const).sub
          (continuousWithinAt_const.mul continuousWithinAt_id)).div
          (continuousWithinAt_id.pow 2) (pow_ne_zero 2 hz0)
      refine hq.congr_of_eventuallyEq ?_ (kform z hz0)
      filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hz0)] with w hw
      exact kform w hw
  refine ⟨(deriv G 0, G 0, discMk k hkc hkd), discAlg_ext fun z hz => ?_⟩
  show discExt r ((cfuL r (deriv G 0, G 0, discMk k hkc hkd) : discAlg r) :
    C(closedBall (0 : ℂ) r, ℂ)) z = _
  rw [discExt_cfuL r _ hz, discExt_discMk hkc hkd hz]
  have h1 := sub_smul_dslope G 0 z
  have h2 := sub_smul_dslope (dslope G 0) 0 z
  simp only [smul_eq_mul, sub_zero, dslope_same] at h1 h2
  show _ = G z
  dsimp only
  have hkz : k z = dslope (dslope G 0) 0 z := rfl
  linear_combination h1 + z * h2 + z ^ 2 * hkz

/-- The linearized normal-form map as a continuous linear equivalence. -/
noncomputable def cfuLE (hr : 0 < r) : (ℂ × ℂ × discAlg r) ≃L[ℂ] discAlg r :=
  ContinuousLinearEquiv.ofBijective (cfuL r) (cfuL_ker hr) (cfuL_range hr)

theorem cfuLE_apply (hr : 0 < r) (x : ℂ × ℂ × discAlg r) : cfuLE hr x = cfuL r x := rfl

end Azurite.DLMF
