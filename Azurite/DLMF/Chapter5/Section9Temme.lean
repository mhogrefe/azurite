/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section9Hankel

/-!
# DLMF §5.9(i): equation 5.9.2_5

Formalization of <https://dlmf.nist.gov/5.9>, equation 5.9.2_5 (added in DLMF 1.1.7):
`1/Γ(z) = (e^z z^{1−z}/(2π)) ∫_{−π}^{π} e^{−zΦ(t)} dt`, `Φ(t) = 1 − t cot t + ln(t/sin t)`,
`ℜz > 0` (`dlmf_5_9_2_5`).

Proof (Temme's): substitute `t = zs` in Hankel's loop 5.9.2 and deform the loop onto the curve
`s(θ) = θ cot θ + iθ = (θ/sin θ) e^{iθ}`, `−π < θ < π`, on which `s − ln s = 1 − Φ(θ)` is real.

* A homotopy form of Cauchy's theorem (`integral_homotopy`): for `f` holomorphic on an open set
  containing the segments `[h₀(θ), h₁(θ)]`, `∫ f(h₁) h₁′ − ∫ f(h₀) h₀′` over `[a, b]` equals the
  difference of the integrals along the segments at `θ = b` and `θ = a` (differentiate under the
  integral, Fubini on the rectangle).
* The loop in the `s`-plane, rays `arg s = ±a` and the arc `|s| = δ`, is `z^{z−1}` times a keyhole
  of §5.9.2 with angles `a ± arg z` (`keyholeS_eq`), hence `2πi z^{z−1}/Γ(z)` for
  `a > ½π + |arg z|`.
* The homotopy between the arc and `s([−a, a])` leaves the ray pieces beyond `|s| = a/sin a`,
  which tend to `0` as `a → π` (`tendsto_rayTail`).
* On the curve `e^{zs} s^{−z} = e^{z(1 − Φ)}` is even and `s′(θ) + s′(−θ) = 2i`, so the integral
  along the curve is `i e^z ∫ e^{−zΦ}`.
-/

open Complex Filter Topology Set MeasureTheory Asymptotics
open scoped Real

namespace Azurite.DLMF

/-! ### A homotopy form of Cauchy's theorem -/

/-- **Cauchy's theorem for a linear homotopy.** If `f` is holomorphic on an open set `U`
containing every segment `[h₀(θ), h₁(θ)]`, `a ≤ θ ≤ b`, then
`∫ₐᵇ f(h₁) h₁′ − ∫ₐᵇ f(h₀) h₀′ =
∫₀¹ f(H(λ, b)) (h₁(b) − h₀(b)) dλ − ∫₀¹ f(H(λ, a)) (h₁(a) − h₀(a)) dλ`,
`H(λ, θ) = h₀(θ) + λ (h₁(θ) − h₀(θ))`. -/
theorem integral_homotopy {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {h₀ h₁ h₀' h₁' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hd₀ : ∀ θ ∈ Icc a b, HasDerivAt h₀ (h₀' θ) θ) (hd₁ : ∀ θ ∈ Icc a b, HasDerivAt h₁ (h₁' θ) θ)
    (hc₀ : ContinuousOn h₀' (Icc a b)) (hc₁ : ContinuousOn h₁' (Icc a b))
    (hseg : ∀ θ ∈ Icc a b, ∀ l ∈ Icc (0 : ℝ) 1, h₀ θ + l * (h₁ θ - h₀ θ) ∈ U) :
    (∫ θ in a..b, f (h₁ θ) * h₁' θ) - (∫ θ in a..b, f (h₀ θ) * h₀' θ) =
      (∫ l in (0 : ℝ)..1, f (h₀ b + l * (h₁ b - h₀ b)) * (h₁ b - h₀ b)) -
        ∫ l in (0 : ℝ)..1, f (h₀ a + l * (h₁ a - h₀ a)) * (h₁ a - h₀ a) := by
  set Rect : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc a b with hRect
  obtain ⟨H, hH⟩ : ∃ H : ℝ → ℝ → ℂ, H = fun (l θ : ℝ) => h₀ θ + (l : ℂ) * (h₁ θ - h₀ θ) := ⟨_, rfl⟩
  obtain ⟨Hθ, hHθ⟩ : ∃ Hθ : ℝ → ℝ → ℂ, Hθ = fun (l θ : ℝ) => h₀' θ + (l : ℂ) * (h₁' θ - h₀' θ) :=
    ⟨_, rfl⟩
  obtain ⟨f', hf'⟩ : ∃ f' : ℂ → ℂ, f' = deriv f := ⟨_, rfl⟩
  have hfd : ∀ w ∈ U, HasDerivAt f (f' w) w := fun w hw => by
    rw [hf']; exact (hf.differentiableAt (hU.mem_nhds hw)).hasDerivAt
  have hf'c : ContinuousOn f' U := by rw [hf']; exact (hf.deriv hU).continuousOn
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ → ℂ, g = fun l θ => f' (H l θ) * (h₁ θ - h₀ θ) * Hθ l θ +
    f (H l θ) * (h₁' θ - h₀' θ) := ⟨_, rfl⟩
  have hHdef : ∀ l θ, H l θ = h₀ θ + l * (h₁ θ - h₀ θ) := fun l θ => by rw [hH]
  have hHθdef : ∀ l θ, Hθ l θ = h₀' θ + l * (h₁' θ - h₀' θ) := fun l θ => by rw [hHθ]
  have hgdef : ∀ l θ, g l θ = f' (H l θ) * (h₁ θ - h₀ θ) * Hθ l θ +
      f (H l θ) * (h₁' θ - h₀' θ) := fun l θ => by rw [hg]
  have hh₀c : ContinuousOn h₀ (Icc a b) := fun θ hθ => (hd₀ θ hθ).continuousAt.continuousWithinAt
  have hh₁c : ContinuousOn h₁ (Icc a b) := fun θ hθ => (hd₁ θ hθ).continuousAt.continuousWithinAt
  have hHc : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) Rect := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => h₀ p.2) Rect :=
      hh₀c.comp continuousOn_snd fun p (hp : p ∈ Rect) => hp.2
    have h2 : ContinuousOn (fun p : ℝ × ℝ => h₁ p.2) Rect :=
      hh₁c.comp continuousOn_snd fun p (hp : p ∈ Rect) => hp.2
    have h3 : ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℂ)) Rect :=
      (continuous_ofReal.comp continuous_fst).continuousOn
    exact (h1.add (h3.mul (h2.sub h1))).congr fun p _ => hHdef _ _
  have hHU : ∀ p ∈ Rect, H p.1 p.2 ∈ U := fun p hp => by
    rw [hHdef]; exact hseg p.2 hp.2 p.1 hp.1
  have hgc : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) Rect := by
    have h1 := hf'c.comp hHc hHU
    have h2 := hf.continuousOn.comp hHc hHU
    have hD : ContinuousOn (fun p : ℝ × ℝ => h₁ p.2 - h₀ p.2) Rect :=
      (hh₁c.comp continuousOn_snd fun p (hp : p ∈ Rect) => hp.2).sub
        (hh₀c.comp continuousOn_snd fun p (hp : p ∈ Rect) => hp.2)
    have hD' : ContinuousOn (fun p : ℝ × ℝ => h₁' p.2 - h₀' p.2) Rect :=
      (hc₁.comp continuousOn_snd fun p (hp : p ∈ Rect) => hp.2).sub
        (hc₀.comp continuousOn_snd fun p (hp : p ∈ Rect) => hp.2)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℂ)) Rect :=
      (continuous_ofReal.comp continuous_fst).continuousOn
    have hHθc : ContinuousOn (fun p : ℝ × ℝ => Hθ p.1 p.2) Rect :=
      ((hc₀.comp continuousOn_snd fun p (hp : p ∈ Rect) => hp.2).add (h3.mul hD')).congr
        fun p _ => hHθdef _ _
    exact (((h1.mul hD).mul hHθc).add (h2.mul hD')).congr fun p _ => hgdef _ _
  -- FTC in `λ`
  have hFTCl : ∀ θ ∈ Icc a b, ∫ l in (0 : ℝ)..1, g l θ = f (h₁ θ) * h₁' θ - f (h₀ θ) * h₀' θ := by
    intro θ hθ
    have hderiv : ∀ l ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun l => f (H l θ) * Hθ l θ) (g l θ) l := by
      intro l hl
      rw [uIcc_of_le zero_le_one] at hl
      have hH1 : HasDerivAt (fun l : ℝ => H l θ) (h₁ θ - h₀ θ) l := by
        have := ((hasDerivAt_id (l : ℂ)).mul_const (h₁ θ - h₀ θ)).comp_ofReal.const_add (h₀ θ)
        rw [show (fun l : ℝ => H l θ) = fun l : ℝ => h₀ θ + (l : ℂ) * (h₁ θ - h₀ θ) from
          funext fun l => hHdef l θ]
        simpa using this
      have hHθ1 : HasDerivAt (fun l : ℝ => Hθ l θ) (h₁' θ - h₀' θ) l := by
        have := ((hasDerivAt_id (l : ℂ)).mul_const (h₁' θ - h₀' θ)).comp_ofReal.const_add (h₀' θ)
        rw [show (fun l : ℝ => Hθ l θ) = fun l : ℝ => h₀' θ + (l : ℂ) * (h₁' θ - h₀' θ) from
          funext fun l => hHθdef l θ]
        simpa using this
      exact (((hfd _ (hHU (l, θ) ⟨hl, hθ⟩)).comp l hH1).mul hHθ1).congr_deriv
        (hgdef l θ).symm
    have e1 : H 1 θ = h₁ θ := by rw [hHdef]; push_cast; ring
    have e0 : H 0 θ = h₀ θ := by rw [hHdef]; push_cast; ring
    have e1' : Hθ 1 θ = h₁' θ := by rw [hHθdef]; push_cast; ring
    have e0' : Hθ 0 θ = h₀' θ := by rw [hHθdef]; push_cast; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
    · rw [e1, e0, e1', e0']
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le zero_le_one]
      have hm : MapsTo (fun l : ℝ => (l, θ)) (Icc (0 : ℝ) 1) Rect :=
        fun l hl => ⟨hl, hθ⟩
      exact hgc.comp ((continuous_id.prodMk continuous_const).continuousOn) hm
  -- FTC in `θ`
  have hFTCt : ∀ l ∈ Icc (0 : ℝ) 1, ∫ θ in a..b, g l θ =
      f (H l b) * (h₁ b - h₀ b) - f (H l a) * (h₁ a - h₀ a) := by
    intro l hl
    have hderiv : ∀ θ ∈ uIcc a b, HasDerivAt (fun θ => f (H l θ) * (h₁ θ - h₀ θ)) (g l θ) θ := by
      intro θ hθ
      rw [uIcc_of_le hab] at hθ
      have hH1 : HasDerivAt (fun θ => H l θ) (Hθ l θ) θ := by
        have := (hd₀ θ hθ).add (((hd₁ θ hθ).sub (hd₀ θ hθ)).const_mul (l : ℂ))
        rw [hHθdef]
        exact this.congr_of_eventuallyEq (Eventually.of_forall fun y => by
          simp only [hHdef, Pi.add_apply, Pi.sub_apply])
      have := ((hfd _ (hHU (l, θ) ⟨hl, hθ⟩)).comp θ hH1).mul ((hd₁ θ hθ).sub (hd₀ θ hθ))
      refine this.congr_deriv ?_
      rw [hgdef]
      simp only [Function.comp_apply, Pi.sub_apply]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    have hm : MapsTo (fun θ : ℝ => (l, θ)) (Icc a b) Rect :=
      fun θ hθ => ⟨hl, hθ⟩
    exact hgc.comp ((continuous_const.prodMk continuous_id).continuousOn) hm
  -- Fubini
  have hint : Integrable (Function.uncurry fun θ l => g l θ)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc 0 1))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hc : ContinuousOn (Function.uncurry fun θ l => g l θ) (Icc a b ×ˢ Icc 0 1) :=
      hgc.comp continuous_swap.continuousOn fun p hp => ⟨hp.2, hp.1⟩
    exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hswap := integral_integral_swap hint
  have hL : (∫ θ in a..b, f (h₁ θ) * h₁' θ) - (∫ θ in a..b, f (h₀ θ) * h₀' θ) =
      ∫ θ in Ioc a b, ∫ l in Ioc (0 : ℝ) 1, g l θ := by
    rw [← intervalIntegral.integral_sub, intervalIntegral.integral_of_le hab]
    · refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
      rw [← intervalIntegral.integral_of_le zero_le_one, hFTCl θ (Ioc_subset_Icc_self hθ)]
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hab]
      exact (hf.continuousOn.comp hh₁c fun θ hθ => by
        simpa [hH] using hseg θ hθ 1 ⟨zero_le_one, le_rfl⟩).mul hc₁
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hab]
      exact (hf.continuousOn.comp hh₀c fun θ hθ => by
        simpa [hH] using hseg θ hθ 0 ⟨le_rfl, zero_le_one⟩).mul hc₀
  have hRHS : (∫ l in (0 : ℝ)..1, f (H l b) * (h₁ b - h₀ b)) -
      (∫ l in (0 : ℝ)..1, f (H l a) * (h₁ a - h₀ a)) =
      ∫ l in Ioc (0 : ℝ) 1, ∫ θ in Ioc a b, g l θ := by
    have hcb : ∀ θ ∈ Icc a b, ContinuousOn (fun l => f (H l θ)) (Icc 0 1) := fun θ hθ =>
      hf.continuousOn.comp (hHc.comp (continuous_id.prodMk continuous_const).continuousOn
        fun l hl => ⟨hl, hθ⟩) fun l hl => hHU (l, θ) ⟨hl, hθ⟩
    rw [← intervalIntegral.integral_sub, intervalIntegral.integral_of_le zero_le_one]
    · refine setIntegral_congr_fun measurableSet_Ioc fun l hl => ?_
      rw [← intervalIntegral.integral_of_le hab, hFTCt l (Ioc_subset_Icc_self hl)]
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le zero_le_one]
      exact (hcb b ⟨hab, le_rfl⟩).mul continuousOn_const
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le zero_le_one]
      exact (hcb a ⟨le_rfl, hab⟩).mul continuousOn_const
  have e : ∀ c : ℝ, (fun l : ℝ => f (h₀ c + l * (h₁ c - h₀ c)) * (h₁ c - h₀ c)) =
      fun l => f (H l c) * (h₁ c - h₀ c) := fun c => funext fun l => by rw [hHdef]
  rw [hL, e b, e a, hRHS, hswap]

/-! ### The curve `s(θ) = (θ/sin θ) e^{iθ}` -/

/-- The entire function `sin w / w` (`1` at `0`). -/
noncomputable def csinc : ℂ → ℂ := dslope Complex.sin 0

theorem differentiable_csinc : Differentiable ℂ csinc := fun _ =>
  ((differentiableOn_dslope (s := univ) (c := 0) univ_mem).mpr
    Complex.differentiable_sin.differentiableOn).differentiableAt (univ_mem)

theorem csinc_ofReal (θ : ℝ) : csinc θ = Real.sinc θ := by
  rcases eq_or_ne θ 0 with rfl | hθ
  · simp [csinc, dslope_same, Real.sinc_zero]
  · have hθ' : (θ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hθ
    rw [csinc, dslope_of_ne _ hθ', slope_def_field, Real.sinc_of_ne_zero hθ]
    push_cast
    simp

theorem sinc_pos_of_mem {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) : 0 < Real.sinc θ :=
  Real.sinc_pos (abs_lt.mpr hθ)

/-- `s(θ) = e^{iθ}/sinc θ = θ cot θ + iθ`. -/
noncomputable def temmeCurve (θ : ℝ) : ℂ := cexp (θ * I) / csinc θ

/-- The complex function behind `temmeCurve`. -/
noncomputable def temmeF (w : ℂ) : ℂ := cexp (w * I) / csinc w

theorem differentiableAt_temmeF {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) :
    DifferentiableAt ℂ temmeF θ := by
  have h0 : csinc θ ≠ 0 := by rw [csinc_ofReal]; exact_mod_cast (sinc_pos_of_mem hθ).ne'
  exact ((differentiableAt_id.mul_const I).cexp).div (differentiable_csinc _) h0

theorem isOpen_temmeF_dom : IsOpen {w : ℂ | csinc w ≠ 0} :=
  isOpen_ne_fun differentiable_csinc.continuous continuous_const

theorem differentiableOn_temmeF : DifferentiableOn ℂ temmeF {w : ℂ | csinc w ≠ 0} :=
  fun _ hw => (((differentiableAt_id.mul_const I).cexp).div (differentiable_csinc _) hw)
    |>.differentiableWithinAt

theorem mem_temmeF_dom {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) : (θ : ℂ) ∈ {w : ℂ | csinc w ≠ 0} := by
  simp only [mem_ofPred_eq, csinc_ofReal]
  exact_mod_cast (sinc_pos_of_mem hθ).ne'

/-- The derivative of the curve. -/
noncomputable def temmeCurve' (θ : ℝ) : ℂ := deriv temmeF θ

theorem hasDerivAt_temmeCurve {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) :
    HasDerivAt temmeCurve (temmeCurve' θ) θ :=
  (differentiableAt_temmeF hθ).hasDerivAt.comp_ofReal

theorem continuousOn_temmeCurve' : ContinuousOn temmeCurve' (Ioo (-π) π) := by
  have h := (differentiableOn_temmeF.deriv isOpen_temmeF_dom).continuousOn
  exact h.comp continuous_ofReal.continuousOn fun θ hθ => mem_temmeF_dom hθ

/-- `ρ(θ) = 1/sinc θ = θ/sin θ`. -/
noncomputable def temmeRho (θ : ℝ) : ℝ := 1 / Real.sinc θ

theorem temmeRho_pos {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) : 0 < temmeRho θ :=
  one_div_pos.mpr (sinc_pos_of_mem hθ)

theorem temmeCurve_eq (θ : ℝ) : temmeCurve θ = (temmeRho θ : ℂ) * cexp (θ * I) := by
  rw [temmeCurve, csinc_ofReal, temmeRho]; push_cast; ring

theorem sin_ne_zero_of_mem {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) (h0 : θ ≠ 0) : Real.sin θ ≠ 0 := by
  rcases lt_or_gt_of_ne h0 with h | h
  · have := Real.sin_pos_of_pos_of_lt_pi (x := -θ) (by linarith) (by linarith [hθ.1])
    rw [Real.sin_neg] at this; linarith
  · exact (Real.sin_pos_of_pos_of_lt_pi h hθ.2).ne'

theorem temmeRho_mul_sin {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) : temmeRho θ * Real.sin θ = θ := by
  rcases eq_or_ne θ 0 with rfl | h0
  · simp
  · have := sin_ne_zero_of_mem hθ h0
    rw [temmeRho, Real.sinc_of_ne_zero h0]
    field_simp

theorem temmeRho_neg (θ : ℝ) : temmeRho (-θ) = temmeRho θ := by
  rw [temmeRho, temmeRho, Real.sinc_neg]

/-- `V(θ) = ρ cos θ − ln ρ`; on the curve `s − ln s = V(θ)` and `V = 1 − Φ`. -/
noncomputable def temmeV (θ : ℝ) : ℝ := temmeRho θ * Real.cos θ - Real.log (temmeRho θ)

/-- DLMF's `Φ(t) = 1 − t cot t + ln(t/sin t)`. -/
noncomputable def temmePhi (t : ℝ) : ℝ := 1 - t * Real.cot t + Real.log (t / Real.sin t)

theorem temmeV_neg (θ : ℝ) : temmeV (-θ) = temmeV θ := by
  rw [temmeV, temmeV, temmeRho_neg, Real.cos_neg]

theorem temmeV_eq {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) (h0 : θ ≠ 0) : temmeV θ = 1 - temmePhi θ := by
  have hs := sin_ne_zero_of_mem hθ h0
  have hρ : temmeRho θ = θ / Real.sin θ := by
    rw [temmeRho, Real.sinc_of_ne_zero h0]; field_simp
  rw [temmeV, temmePhi, hρ, Real.cot_eq_cos_div_sin]
  ring

theorem temmeV_le_one {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) : temmeV θ ≤ 1 := by
  have hs := sinc_pos_of_mem hθ
  have hρ1 : 1 ≤ temmeRho θ := by
    rw [temmeRho, le_div_iff₀ hs, one_mul]; exact Real.sinc_le_one θ
  have hcos : temmeRho θ * Real.cos θ ≤ 1 := by
    rw [temmeRho, div_mul_eq_mul_div, one_mul, div_le_one hs]
    by_cases h : |θ| < π / 2
    · exact Real.cos_le_sinc h
    · have : Real.cos θ ≤ 0 := by
        rw [← Real.cos_abs]
        refine Real.cos_nonpos_of_pi_div_two_le_of_le (not_lt.mp h) ?_
        have := abs_lt.mpr hθ; linarith
      linarith
  have := Real.log_nonneg hρ1
  rw [temmeV]; linarith

theorem continuousOn_temmeRho : ContinuousOn temmeRho (Ioo (-π) π) := fun _ hθ =>
  (continuousAt_const.div Real.continuous_sinc.continuousAt
    (sinc_pos_of_mem hθ).ne').continuousWithinAt

theorem continuousOn_temmeV : ContinuousOn temmeV (Ioo (-π) π) :=
  (continuousOn_temmeRho.mul Real.continuous_cos.continuousOn).sub
    (continuousOn_temmeRho.log fun _ hθ => (temmeRho_pos hθ).ne')

/-- On the curve: `e^{zs} s^{−z} = e^{zV(θ)}` (principal power). -/
theorem cexp_mul_cpow_temmeCurve (z : ℂ) {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) :
    cexp (z * temmeCurve θ) * temmeCurve θ ^ (-z) = cexp (z * temmeV θ) := by
  have hρ := temmeRho_pos hθ
  have hne : temmeCurve θ ≠ 0 := by
    rw [temmeCurve_eq]
    exact mul_ne_zero (ofReal_ne_zero.mpr hρ.ne') (Complex.exp_ne_zero _)
  have hlog : Complex.log (temmeCurve θ) = Real.log (temmeRho θ) + θ * I := by
    rw [temmeCurve_eq, log_ofReal_mul hρ (Complex.exp_ne_zero _),
      log_exp (by simpa using hθ.1) (by simpa using hθ.2.le)]
  rw [cpow_def_of_ne_zero hne, hlog, ← Complex.exp_add]
  congr 1
  have hsin := temmeRho_mul_sin hθ
  rw [temmeCurve_eq, temmeV, Complex.exp_mul_I]
  push_cast
  rw [← ofReal_cos, ← ofReal_sin]
  have : ((temmeRho θ : ℝ) : ℂ) * (Real.sin θ : ℂ) = θ := by exact_mod_cast hsin
  linear_combination (z * I) * this

theorem temmeCurve_sub_neg {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) :
    temmeCurve θ - temmeCurve (-θ) = 2 * I * θ := by
  rw [temmeCurve_eq, temmeCurve_eq, temmeRho_neg, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg, ← ofReal_sin]
  have : ((temmeRho θ : ℝ) : ℂ) * (Real.sin θ : ℂ) = θ := by exact_mod_cast temmeRho_mul_sin hθ
  linear_combination (2 * I) * this

theorem neg_mem_Ioo_pi {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) : -θ ∈ Ioo (-π) π :=
  ⟨by linarith [hθ.2], by linarith [hθ.1]⟩

theorem temmeCurve'_add_neg {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) :
    temmeCurve' θ + temmeCurve' (-θ) = 2 * I := by
  have h1 : HasDerivAt (fun x => temmeCurve x - temmeCurve (-x))
      (temmeCurve' θ + temmeCurve' (-θ)) θ := by
    have := (hasDerivAt_temmeCurve hθ).sub
      ((hasDerivAt_temmeCurve (neg_mem_Ioo_pi hθ)).scomp θ (hasDerivAt_neg θ))
    convert this using 1
    · rfl
    · rw [neg_one_smul, sub_neg_eq_add]
  have h2 : HasDerivAt (fun x => temmeCurve x - temmeCurve (-x)) (2 * I) θ := by
    have h3 : HasDerivAt (fun x : ℝ => 2 * I * (x : ℂ)) (2 * I) θ := by
      simpa using ((hasDerivAt_id (θ : ℂ)).const_mul (2 * I)).comp_ofReal
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
    exact temmeCurve_sub_neg hx
  exact h1.unique h2

/-- On the curve the integrand symmetrizes: `∫_{−a}^{a} e^{zV} s′ = i ∫_{−a}^{a} e^{zV}`. -/
theorem integral_temme_sym (z : ℂ) {a : ℝ} (ha0 : 0 ≤ a) (haπ : a < π) :
    ∫ θ in (-a)..a, cexp (z * temmeV θ) * temmeCurve' θ =
      I * ∫ θ in (-a)..a, cexp (z * temmeV θ) := by
  have hsub : Icc (-a) a ⊆ Ioo (-π) π := fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hE : ContinuousOn (fun θ => cexp (z * temmeV θ)) (Icc (-a) a) :=
    (continuous_exp.comp_continuousOn ((continuous_ofReal.comp_continuousOn
      (continuousOn_temmeV.mono hsub)).const_smul z))
  have hs' : ContinuousOn temmeCurve' (Icc (-a) a) := continuousOn_temmeCurve'.mono hsub
  have hs'n : ContinuousOn (fun θ => temmeCurve' (-θ)) (Icc (-a) a) :=
    continuousOn_temmeCurve'.comp continuous_neg.continuousOn fun θ hθ =>
      neg_mem_Ioo_pi (hsub hθ)
  have hii1 : IntervalIntegrable (fun θ => cexp (z * temmeV θ) * temmeCurve' θ) volume (-a) a :=
    (hE.mul hs').intervalIntegrable_of_Icc (by linarith)
  have hii2 : IntervalIntegrable (fun θ => cexp (z * temmeV θ) * temmeCurve' (-θ)) volume
      (-a) a := (hE.mul hs'n).intervalIntegrable_of_Icc (by linarith)
  have hrefl : ∫ θ in (-a)..a, cexp (z * temmeV θ) * temmeCurve' θ =
      ∫ θ in (-a)..a, cexp (z * temmeV θ) * temmeCurve' (-θ) := by
    have hc := intervalIntegral.integral_comp_neg (a := -a) (b := a)
      (f := fun θ => cexp (z * temmeV θ) * temmeCurve' θ)
    rw [neg_neg] at hc
    rw [← hc]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [temmeV_neg]
  have h2 : 2 * ∫ θ in (-a)..a, cexp (z * temmeV θ) * temmeCurve' θ =
      ∫ θ in (-a)..a, cexp (z * temmeV θ) * (2 * I) := by
    rw [two_mul]
    nth_rewrite 2 [hrefl]
    rw [← intervalIntegral.integral_add hii1 hii2]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le (by linarith)] at hθ
    rw [← mul_add, temmeCurve'_add_neg (hsub hθ)]
  rw [intervalIntegral.integral_mul_const] at h2
  linear_combination h2 / 2

/-! ### Tails of the Hankel rays -/

theorem norm_hankelF {z : ℂ} {R : ℝ} (hR : 0 < R) (ϑ : ℝ) :
    ‖hankelF z R ϑ * cexp (ϑ * I)‖ =
      Real.exp (R * Real.cos ϑ) * R ^ (-z.re) * Real.exp (ϑ * z.im) := by
  rw [hankelF, norm_mul, norm_mul, norm_mul, norm_cexp_mul_I_ofReal, mul_one, Complex.norm_exp,
    Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos hR]
  have h1 : ((R : ℂ) * cexp (ϑ * I)).re = R * Real.cos ϑ := by
    rw [re_ofReal_mul, exp_ofReal_mul_I_re]
  have h2 : (-(z * ϑ * I)).re = ϑ * z.im := by simp; ring
  rw [h1, h2, neg_re]
  ring

theorem integrableOn_hankelRay_Ioi {z : ℂ} (hz : 0 ≤ z.re) {δ ϑ : ℝ} (hδ : 0 < δ)
    (hϑ : Real.cos ϑ < 0) :
    IntegrableOn (fun R : ℝ => hankelF z R ϑ * cexp (ϑ * I)) (Ioi δ) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi δ (b := -Real.cos ϑ) (by linarith)).const_mul
    (δ ^ (-z.re) * Real.exp (ϑ * z.im))) ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun R hR => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun R hR => ?_) measurableSet_Ioi
    have hR0 : 0 < R := lt_trans hδ hR
    unfold hankelF
    exact ((((continuous_ofReal.mul continuous_const).cexp).continuousAt).mul
      ((hasDerivAt_ofReal_cpow' (-z) hR0).continuousAt.mul continuousAt_const)).mul
      continuousAt_const |>.continuousWithinAt
  · have hR0 : 0 < R := lt_trans hδ hR
    rw [norm_hankelF hR0]
    have h1 : R ^ (-z.re) ≤ δ ^ (-z.re) :=
      Real.rpow_le_rpow_of_nonpos hδ (le_of_lt hR) (by linarith)
    have h2 : Real.exp (R * Real.cos ϑ) = Real.exp (-(-Real.cos ϑ) * R) := by ring_nf
    rw [h2]
    have := Real.exp_pos (-(-Real.cos ϑ) * R)
    have := Real.exp_pos (ϑ * z.im)
    calc Real.exp (-(-Real.cos ϑ) * R) * R ^ (-z.re) * Real.exp (ϑ * z.im)
        ≤ Real.exp (-(-Real.cos ϑ) * R) * δ ^ (-z.re) * Real.exp (ϑ * z.im) := by gcongr
      _ = _ := by ring

/-- The tail `∫_X^∞` of a Hankel ray with `cos ϑ ≤ −c`. -/
theorem norm_integral_hankelRay_tail_le {z : ℂ} (hz : 0 ≤ z.re) {ϑ c : ℝ} (hc : 0 < c)
    (hcos : Real.cos ϑ ≤ -c) (hϑ : |ϑ| ≤ 2 * π) {X : ℝ} (hX : 1 ≤ X) :
    ‖∫ R in Ioi X, hankelF z R ϑ * cexp (ϑ * I)‖ ≤
      Real.exp (2 * π * |z.im|) * (Real.exp (-c * X) / c) := by
  have hb : IntegrableOn (fun R : ℝ => Real.exp (2 * π * |z.im|) * Real.exp (-c * R)) (Ioi X) :=
    (exp_neg_integrableOn_Ioi X hc).const_mul _
  refine (norm_integral_le_of_norm_le hb ((ae_restrict_iff' measurableSet_Ioi).mpr
    (ae_of_all _ fun R hR => ?_))).trans (le_of_eq ?_)
  · have hR1 : 1 ≤ R := le_trans hX (le_of_lt hR)
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
    rw [norm_hankelF hR0]
    have h1 : R ^ (-z.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR1 (by linarith)
    have h2 : Real.exp (R * Real.cos ϑ) ≤ Real.exp (-c * R) := Real.exp_le_exp.mpr (by nlinarith)
    have h3 : Real.exp (ϑ * z.im) ≤ Real.exp (2 * π * |z.im|) := by
      refine Real.exp_le_exp.mpr ?_
      calc ϑ * z.im ≤ |ϑ * z.im| := le_abs_self _
        _ = |ϑ| * |z.im| := abs_mul _ _
        _ ≤ 2 * π * |z.im| := mul_le_mul_of_nonneg_right hϑ (abs_nonneg _)
    have := Real.exp_pos (R * Real.cos ϑ)
    have := Real.rpow_nonneg hR0.le (-z.re)
    calc Real.exp (R * Real.cos ϑ) * R ^ (-z.re) * Real.exp (ϑ * z.im)
        ≤ Real.exp (-c * R) * 1 * Real.exp (2 * π * |z.im|) := by gcongr
      _ = _ := by ring
  · rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) X]
    ring

/-! ### The substitution `t = zs` -/

/-- `e^{zs} s^{−z}` at `s = r e^{iϑ}` (principal power) in terms of `hankelF`. -/
theorem cexp_mul_cpow_eq_hankelF {z : ℂ} (hz : z ≠ 0) {r : ℝ} (hr : 0 < r) {ϑ : ℝ}
    (hϑ : ϑ ∈ Ioo (-π) π) :
    cexp (z * ((r : ℂ) * cexp (ϑ * I))) * ((r : ℂ) * cexp (ϑ * I)) ^ (-z) =
      z ^ z * hankelF z (‖z‖ * r) (ϑ + arg z) := by
  have hm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hlog : Complex.log ((r : ℂ) * cexp (ϑ * I)) = Real.log r + ϑ * I := by
    rw [log_ofReal_mul hr (Complex.exp_ne_zero _),
      log_exp (by simpa using hϑ.1) (by simpa using hϑ.2.le)]
  have hne : (r : ℂ) * cexp (ϑ * I) ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr hr.ne') (Complex.exp_ne_zero _)
  have hmr : ((‖z‖ * r : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (mul_pos hm hr).ne'
  have hzexp : (‖z‖ : ℂ) * cexp (arg z * I) = z := norm_mul_exp_arg_mul_I z
  have hzs : ((‖z‖ * r : ℝ) : ℂ) * cexp (((ϑ + arg z : ℝ) : ℂ) * I) =
      z * ((r : ℂ) * cexp (ϑ * I)) := by
    have e : ((‖z‖ * r : ℝ) : ℂ) * cexp (((ϑ + arg z : ℝ) : ℂ) * I) =
        ((‖z‖ : ℂ) * cexp (arg z * I)) * ((r : ℂ) * cexp (ϑ * I)) := by
      push_cast; rw [add_mul, Complex.exp_add]; ring
    rw [e, hzexp]
  have hlz : Complex.log z = Real.log ‖z‖ + arg z * I := rfl
  have hlmr : Complex.log ((‖z‖ * r : ℝ) : ℂ) = Real.log ‖z‖ + Real.log r := by
    rw [← ofReal_log (mul_pos hm hr).le, Real.log_mul hm.ne' hr.ne']; push_cast; ring
  unfold hankelF
  rw [cpow_def_of_ne_zero hne, hlog, cpow_def_of_ne_zero hz, cpow_def_of_ne_zero hmr, hzs,
    hlmr, hlz]
  rw [show ∀ A B C D : ℂ, cexp A * cexp B = cexp C * (cexp A * (cexp D * cexp (-(z * ((ϑ +
    arg z : ℝ) : ℂ) * I)))) ↔ cexp B = cexp (C + D + (-(z * ((ϑ + arg z : ℝ) : ℂ) * I))) from
    fun A B C D => by
      rw [Complex.exp_add, Complex.exp_add]
      constructor
      · intro h
        have hA := Complex.exp_ne_zero A
        apply mul_left_cancel₀ hA
        rw [h]; ring
      · intro h; rw [h]; ring]
  congr 1
  push_cast
  ring

/-! ### The pieces of the deformation -/

theorem abs_arg_lt_of_re_pos {z : ℂ} (hz : 0 < z.re) : |arg z| < π / 2 :=
  abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)

theorem ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := fun h => by
  rw [h, zero_re] at hz; exact lt_irrefl 0 hz

theorem cpow_sub_one_mul_self {z : ℂ} (hz : z ≠ 0) : z ^ (z - 1) * z = z ^ z := by
  rw [cpow_sub _ _ hz, cpow_one, div_mul_cancel₀ _ hz]

theorem cexp_mul_I_eq_div {z : ℂ} (hz : z ≠ 0) (ϑ : ℝ) :
    cexp (ϑ * I) = cexp (((ϑ + arg z : ℝ) : ℂ) * I) * ‖z‖ / z := by
  have hzexp : (‖z‖ : ℂ) * cexp (arg z * I) = z := norm_mul_exp_arg_mul_I z
  rw [eq_div_iff hz]
  push_cast
  rw [add_mul, Complex.exp_add]
  calc cexp (ϑ * I) * z = cexp (ϑ * I) * ((‖z‖ : ℂ) * cexp (arg z * I)) := by rw [hzexp]
    _ = _ := by ring

theorem one_le_temmeRho {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) : 1 ≤ temmeRho θ := by
  rw [temmeRho, le_div_iff₀ (sinc_pos_of_mem hθ), one_mul]; exact Real.sinc_le_one θ

/-- `e^{zs} s^{−z}`. -/
noncomputable def temmeIntegrand (z s : ℂ) : ℂ := cexp (z * s) * s ^ (-z)

theorem differentiableOn_temmeIntegrand (z : ℂ) :
    DifferentiableOn ℂ (temmeIntegrand z) slitPlane := fun _ hs =>
  (((differentiableAt_id.const_mul z).cexp).mul (differentiableAt_id.cpow_const hs))
    |>.differentiableWithinAt

/-- The arc `|s| = ½`, `|arg s| ≤ a`, is `z^{z−1}` times a Hankel arc of radius `|z|/2`. -/
theorem integral_arc_eq {z : ℂ} (hz : 0 < z.re) {a : ℝ} (ha0 : 0 ≤ a) (haπ : a < π) :
    ∫ θ in (-a)..a, temmeIntegrand z ((1 / 2 : ℝ) * cexp (θ * I)) *
        ((1 / 2 : ℝ) * (I * cexp (θ * I))) =
      z ^ (z - 1) * hankelArc z (‖z‖ * (1 / 2)) (a + arg z) (a - arg z) := by
  have hz0 := ne_zero_of_re_pos hz
  have hpt : ∀ θ ∈ uIcc (-a) a, temmeIntegrand z ((1 / 2 : ℝ) * cexp (θ * I)) *
      ((1 / 2 : ℝ) * (I * cexp (θ * I))) =
      z ^ (z - 1) * (hankelF z (‖z‖ * (1 / 2)) (θ + arg z) *
        (I * ((‖z‖ * (1 / 2) : ℝ) : ℂ) * cexp (((θ + arg z : ℝ) : ℂ) * I))) := by
    intro θ hθ
    rw [uIcc_of_le (by linarith)] at hθ
    have hθ' : θ ∈ Ioo (-π) π := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    rw [temmeIntegrand, cexp_mul_cpow_eq_hankelF hz0 (by norm_num) hθ',
      cexp_mul_I_eq_div hz0 θ, ← cpow_sub_one_mul_self hz0]
    push_cast
    field_simp
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul, hankelArc]
  congr 1
  have := intervalIntegral.integral_comp_add_right (a := -a) (b := a)
    (fun θ => hankelF z (‖z‖ * (1 / 2)) θ * (I * ((‖z‖ * (1 / 2) : ℝ) : ℂ) * cexp (θ * I)))
    (arg z)
  rw [show -(a - arg z) = -a + arg z by ring]
  push_cast at this ⊢
  exact this

/-- A segment of the homotopy, `½ e^{iϑ} → ρ(ϑ) e^{iϑ}`, in terms of a Hankel ray and its tail. -/
theorem integral_segment_eq {z : ℂ} (hz : 0 < z.re) {ϑ : ℝ} (hϑ : ϑ ∈ Ioo (-π) π)
    (hcos : Real.cos (ϑ + arg z) < 0) :
    ∫ l in (0 : ℝ)..1, temmeIntegrand z ((1 / 2 : ℝ) * cexp (ϑ * I) +
        l * (temmeCurve ϑ - (1 / 2 : ℝ) * cexp (ϑ * I))) *
        (temmeCurve ϑ - (1 / 2 : ℝ) * cexp (ϑ * I)) =
      z ^ (z - 1) * (hankelRay z (‖z‖ * (1 / 2)) (ϑ + arg z) -
        ∫ R in Ioi (‖z‖ * temmeRho ϑ), hankelF z R (ϑ + arg z) *
          cexp (((ϑ + arg z : ℝ) : ℂ) * I)) := by
  have hz0 := ne_zero_of_re_pos hz
  have hm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hρ := one_le_temmeRho hϑ
  set c : ℝ := temmeRho ϑ - 1 / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  set K : ℝ → ℂ := fun R => hankelF z R (ϑ + arg z) * cexp (((ϑ + arg z : ℝ) : ℂ) * I) with hK
  have hpt : ∀ l ∈ uIcc (0 : ℝ) 1, temmeIntegrand z ((1 / 2 : ℝ) * cexp (ϑ * I) +
      l * (temmeCurve ϑ - (1 / 2 : ℝ) * cexp (ϑ * I))) *
      (temmeCurve ϑ - (1 / 2 : ℝ) * cexp (ϑ * I)) =
      z ^ (z - 1) * ((‖z‖ * c : ℝ) * K ((‖z‖ * c) * l + ‖z‖ * (1 / 2))) := by
    intro l hl
    rw [uIcc_of_le zero_le_one] at hl
    have hr : 0 < 1 / 2 + l * c := by nlinarith [hl.1]
    have e1 : temmeCurve ϑ - (1 / 2 : ℝ) * cexp (ϑ * I) = (c : ℂ) * cexp (ϑ * I) := by
      rw [temmeCurve_eq, hc]; push_cast; ring
    have e2 : (1 / 2 : ℝ) * cexp (ϑ * I) + l * (temmeCurve ϑ - (1 / 2 : ℝ) * cexp (ϑ * I)) =
        ((1 / 2 + l * c : ℝ) : ℂ) * cexp (ϑ * I) := by rw [e1]; push_cast; ring
    rw [e2, e1, temmeIntegrand, cexp_mul_cpow_eq_hankelF hz0 hr hϑ, hK]
    simp only
    rw [show ‖z‖ * (1 / 2 + l * c) = ‖z‖ * c * l + ‖z‖ * (1 / 2) by ring,
      cexp_mul_I_eq_div hz0 ϑ, ← cpow_sub_one_mul_self hz0]
    push_cast
    field_simp
  have hmc : (‖z‖ * c : ℝ) ≠ 0 := (mul_pos hm hc0).ne'
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_add K hmc]
  simp only [mul_zero, zero_add, mul_one, real_smul]
  push_cast
  have hmc' : (‖z‖ : ℂ) * c ≠ 0 := by exact_mod_cast hmc
  rw [← mul_assoc ((‖z‖ : ℂ) * c), mul_inv_cancel₀ hmc', one_mul]
  congr 1
  have hX : ‖z‖ * c + ‖z‖ * (1 / 2) = ‖z‖ * temmeRho ϑ := by rw [hc]; ring
  rw [hX]
  have hδ : 0 < ‖z‖ * (1 / 2) := by positivity
  have hle : ‖z‖ * (1 / 2) ≤ ‖z‖ * temmeRho ϑ := by nlinarith
  have hi := integrableOn_hankelRay_Ioi hz.le hδ hcos
  rw [hankelRay, intervalIntegral.integral_of_le hle, ← Ioc_union_Ioi_eq_Ioi hle,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi hle))]
  ring

theorem ofReal_mul_cexp_mem_slitPlane {R : ℝ} (hR : 0 < R) {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) :
    (R : ℂ) * cexp (θ * I) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases eq_or_ne θ 0 with rfl | h0
  · left; simpa using hR
  · right
    rw [im_ofReal_mul, exp_ofReal_mul_I_im]
    exact mul_ne_zero hR.ne' (sin_ne_zero_of_mem hθ h0)

/-- The deformation for one `a`: with `T_ψ = ∫_{|z|ρ(a)}^∞` the tails of the Hankel rays,
`i ∫_{−a}^{a} e^{zV} = z^{z−1} (2πi/Γ(z) − T_{a+arg z} + T_{−a+arg z})`. -/
theorem temme_identity {z : ℂ} (hz : 0 < z.re) {a : ℝ} (ha1 : π / 2 + |arg z| < a)
    (ha2 : a < π) :
    I * ∫ θ in (-a)..a, cexp (z * temmeV θ) =
      z ^ (z - 1) * (2 * π * I * (Gamma z)⁻¹ -
        (∫ R in Ioi (‖z‖ * temmeRho a), hankelF z R (a + arg z) *
          cexp (((a + arg z : ℝ) : ℂ) * I)) +
        ∫ R in Ioi (‖z‖ * temmeRho a), hankelF z R (-a + arg z) *
          cexp (((-a + arg z : ℝ) : ℂ) * I)) := by
  have hω := abs_arg_lt_of_re_pos hz
  have hω' := abs_lt.mp hω
  have hab1 := le_abs_self (arg z)
  have hab2 := neg_abs_le (arg z)
  have ha0 : 0 < a := by linarith [abs_nonneg (arg z), Real.pi_pos]
  have hIcc : Icc (-a) a ⊆ Ioo (-π) π := fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have haI : a ∈ Ioo (-π) π := hIcc ⟨by linarith, le_rfl⟩
  have hnaI : -a ∈ Ioo (-π) π := hIcc ⟨le_rfl, by linarith⟩
  have hcos : ∀ ψ : ℝ, π / 2 < ψ → ψ < 3 * π / 2 → Real.cos ψ < 0 := fun ψ h1 h2 =>
    Real.cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith)
  have hc1 : Real.cos (a + arg z) < 0 := hcos _ (by linarith) (by linarith)
  have hc2 : Real.cos (-a + arg z) < 0 := by
    rw [show -a + arg z = -(a - arg z) by ring, Real.cos_neg]
    exact hcos _ (by linarith) (by linarith)
  have hhom := integral_homotopy (f := temmeIntegrand z) isOpen_slitPlane
    (differentiableOn_temmeIntegrand z)
    (h₀ := fun θ => ((1 / 2 : ℝ) : ℂ) * cexp (θ * I)) (h₁ := temmeCurve)
    (h₀' := fun θ => ((1 / 2 : ℝ) : ℂ) * (I * cexp (θ * I))) (h₁' := temmeCurve')
    (a := -a) (b := a) (by linarith)
    (fun θ _ => by
      have := (((hasDerivAt_id (θ : ℂ)).mul_const I).cexp.comp_ofReal).const_mul
        ((1 / 2 : ℝ) : ℂ)
      simpa [mul_comm] using this)
    (fun θ hθ => hasDerivAt_temmeCurve (hIcc hθ))
    ((by fun_prop : Continuous fun θ : ℝ => ((1 / 2 : ℝ) : ℂ) * (I * cexp (θ * I))).continuousOn)
    (continuousOn_temmeCurve'.mono hIcc)
    (fun θ hθ l hl => by
      have hθ' := hIcc hθ
      have hρ := one_le_temmeRho hθ'
      have e : ((1 / 2 : ℝ) : ℂ) * cexp (θ * I) + l * (temmeCurve θ - ((1 / 2 : ℝ) : ℂ) *
          cexp (θ * I)) = ((1 / 2 + l * (temmeRho θ - 1 / 2) : ℝ) : ℂ) * cexp (θ * I) := by
        rw [temmeCurve_eq]; push_cast; ring
      rw [e]
      exact ofReal_mul_cexp_mem_slitPlane (by nlinarith [hl.1]) hθ')
  have hcurve : ∫ θ in (-a)..a, temmeIntegrand z (temmeCurve θ) * temmeCurve' θ =
      I * ∫ θ in (-a)..a, cexp (z * temmeV θ) := by
    rw [← integral_temme_sym z ha0.le ha2]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le (by linarith)] at hθ
    simp only [temmeIntegrand]
    rw [cexp_mul_cpow_temmeCurve z (hIcc hθ)]
  rw [hcurve, integral_arc_eq hz ha0.le ha2, integral_segment_eq hz haI hc1,
    integral_segment_eq hz hnaI hc2, temmeRho_neg] at hhom
  have hloop := hankelLoop_eq z (δ := ‖z‖ * (1 / 2)) (α := a + arg z) (β := a - arg z)
    (by have := norm_pos_iff.mpr (ne_zero_of_re_pos hz); positivity)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rw [hankelLoop, show -(a - arg z) = -a + arg z by ring] at hloop
  rw [← hloop]
  linear_combination hhom

/-! ### Limits as `a → π` -/

theorem tendsto_temmeRho : Tendsto temmeRho (𝓝[<] π) atTop := by
  have hsin : Tendsto Real.sin (𝓝[<] π) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (Real.continuous_sin.tendsto π).mono_left (nhdsWithin_le_nhds (s := Iio π))
      rwa [Real.sin_pi] at this
    · filter_upwards [Ioo_mem_nhdsLT Real.pi_pos] with a ha
      exact Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2
  have hid : Tendsto (fun a : ℝ => a) (𝓝[<] π) (𝓝 π) := nhdsWithin_le_nhds
  refine (hid.pos_mul_atTop Real.pi_pos (tendsto_inv_nhdsGT_zero.comp hsin)).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT Real.pi_pos] with a ha
  rw [Function.comp_apply, temmeRho, Real.sinc_of_ne_zero ha.1.ne']
  field_simp

theorem norm_temmeE_le {z : ℂ} (hz : 0 < z.re) {θ : ℝ} (hθ : θ ∈ Icc (-π) π) :
    ‖cexp (z * temmeV θ)‖ ≤ Real.exp z.re := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have hre : (z * (temmeV θ : ℂ)).re = z.re * temmeV θ := by simp
  rw [hre]
  have hV : temmeV θ ≤ 1 := by
    rcases eq_or_lt_of_le hθ.1 with h | h
    · rw [← h, temmeV, temmeRho, Real.sinc_of_ne_zero (by linarith [Real.pi_pos]),
        Real.sin_neg, Real.sin_pi]
      simp
    rcases eq_or_lt_of_le hθ.2 with h' | h'
    · rw [h', temmeV, temmeRho, Real.sinc_of_ne_zero Real.pi_ne_zero, Real.sin_pi]
      simp
    exact temmeV_le_one ⟨h, h'⟩
  nlinarith

theorem measurable_temmeV : Measurable temmeV := by
  unfold temmeV temmeRho
  fun_prop

theorem measurable_temmeE (z : ℂ) : Measurable fun θ => cexp (z * temmeV θ) :=
  Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
    measurable_temmeV))

theorem intervalIntegrable_temmeE {z : ℂ} (hz : 0 < z.re) {u v : ℝ} (huv : u ≤ v) (hu : -π ≤ u)
    (hv : v ≤ π) : IntervalIntegrable (fun θ => cexp (z * temmeV θ)) volume u v := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => Real.exp z.re) intervalIntegrable_const
    (measurable_temmeE z).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_uIoc).mpr (ae_of_all _ fun θ hθ => ?_))
  rw [uIoc_of_le huv] at hθ
  exact norm_temmeE_le hz ⟨by linarith [hθ.1], by linarith [hθ.2]⟩

theorem tendsto_temmeJ {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun a => ∫ θ in (-a)..a, cexp (z * temmeV θ)) (𝓝[<] π)
      (𝓝 (∫ θ in (-π)..π, cexp (z * temmeV θ))) := by
  set E : ℝ → ℂ := fun θ => cexp (z * temmeV θ) with hE
  set C := Real.exp z.re with hC
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun a : ℝ => 2 * C * (π - a)) (𝓝[<] π) (𝓝 0) := by
    have : Tendsto (fun a : ℝ => 2 * C * (π - a)) (𝓝 π) (𝓝 (2 * C * (π - π))) :=
      ((continuous_const.sub continuous_id).const_mul (2 * C)).tendsto π |>.congr fun _ => rfl
    rw [sub_self, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioo_mem_nhdsLT Real.pi_pos] with a ha
  have hpa : -π ≤ -a := by linarith [ha.2]
  have h1 := intervalIntegrable_temmeE hz hpa (by linarith [ha.1]) (by linarith [ha.1])
  have h2 := intervalIntegrable_temmeE hz (u := -a) (v := a) (by linarith [ha.1]) hpa
    (le_of_lt ha.2)
  have h3 := intervalIntegrable_temmeE hz (u := a) (v := π) (le_of_lt ha.2)
    (by linarith [ha.1]) le_rfl
  have hsplit : (∫ θ in (-π)..π, E θ) - ∫ θ in (-a)..a, E θ =
      (∫ θ in (-π)..(-a), E θ) + ∫ θ in a..π, E θ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals h1
      (h2.trans h3), ← intervalIntegral.integral_add_adjacent_intervals h2 h3]
    ring
  have hb : ∀ u v : ℝ, -π ≤ u → u ≤ v → v ≤ π → ‖∫ θ in u..v, E θ‖ ≤ C * |v - u| :=
    fun u v hu huv hv => intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => by
      rw [uIoc_of_le huv] at hθ
      exact norm_temmeE_le hz ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  rw [norm_norm, norm_sub_rev, hsplit]
  refine (norm_add_le _ _).trans ?_
  have e1 := hb (-π) (-a) le_rfl hpa (by linarith [ha.1])
  have e2 := hb a π (by linarith [ha.1]) (le_of_lt ha.2) le_rfl
  rw [abs_of_nonneg (by linarith [ha.2])] at e1
  rw [abs_of_nonneg (by linarith [ha.2])] at e2
  linarith

theorem tendsto_temme_tail {z : ℂ} (hz : 0 < z.re) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    Tendsto (fun a => ∫ R in Ioi (‖z‖ * temmeRho a), hankelF z R (σ * a + arg z) *
      cexp (((σ * a + arg z : ℝ) : ℂ) * I)) (𝓝[<] π) (𝓝 0) := by
  have hω := abs_lt.mp (abs_arg_lt_of_re_pos hz)
  have hm : 0 < ‖z‖ := norm_pos_iff.mpr (ne_zero_of_re_pos hz)
  set c := Real.cos (arg z) / 2 with hc
  have hcos0 : 0 < Real.cos (arg z) := Real.cos_pos_of_mem_Ioo ⟨hω.1, hω.2⟩
  have hc0 : 0 < c := by rw [hc]; linarith
  -- eventually `cos(σa + arg z) ≤ −c`
  have hcosev : ∀ᶠ a in 𝓝[<] π, Real.cos (σ * a + arg z) ≤ -c := by
    have hcont : Tendsto (fun a => Real.cos (σ * a + arg z)) (𝓝 π)
        (𝓝 (Real.cos (σ * π + arg z))) :=
      ((Real.continuous_cos.comp ((continuous_const.mul continuous_id).add continuous_const))
        |>.tendsto π)
    have hval : Real.cos (σ * π + arg z) = -Real.cos (arg z) := by
      rcases hσ with rfl | rfl
      · rw [one_mul, add_comm, Real.cos_add_pi]
      · rw [show -1 * π + arg z = arg z - π by ring, Real.cos_sub_pi]
    rw [hval] at hcont
    exact (hcont.eventually (ge_mem_nhds (by linarith : -Real.cos (arg z) < -c))).filter_mono
      nhdsWithin_le_nhds
  have hX : Tendsto (fun a => ‖z‖ * temmeRho a) (𝓝[<] π) atTop :=
    tendsto_temmeRho.const_mul_atTop hm
  have hbound : Tendsto (fun a => Real.exp (2 * π * |z.im|) *
      (Real.exp (-c * (‖z‖ * temmeRho a)) / c)) (𝓝[<] π) (𝓝 0) := by
    have h1 : Tendsto (fun a => Real.exp (-c * (‖z‖ * temmeRho a))) (𝓝[<] π) (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hX.const_mul_atTop hc0)
      refine this.congr fun a => ?_
      simp [neg_mul]
    simpa using (h1.div_const c).const_mul (Real.exp (2 * π * |z.im|))
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [hcosev, hX.eventually (eventually_ge_atTop 1),
    Ioo_mem_nhdsLT (show (0 : ℝ) < π by linarith [Real.pi_pos])] with a ha hXa haI
  refine norm_integral_hankelRay_tail_le hz.le hc0 ha ?_ hXa
  rw [abs_le]
  rcases hσ with rfl | rfl <;> constructor <;> linarith [haI.1, haI.2, Real.pi_pos]

/-- **DLMF 5.9.2_5** (Temme): for `ℜz > 0`,
`1/Γ(z) = (e^z z^{1−z}/(2π)) ∫_{−π}^{π} e^{−zΦ(t)} dt`, `Φ(t) = 1 − t cot t + ln(t/sin t)`. -/
theorem dlmf_5_9_2_5 {z : ℂ} (hz : 0 < z.re) :
    1 / Gamma z = cexp z * z ^ (1 - z) / (2 * π) *
      ∫ t in (-π)..π, cexp (-(z * temmePhi t)) := by
  have hz0 := ne_zero_of_re_pos hz
  have hω := abs_arg_lt_of_re_pos hz
  set J : ℝ → ℂ := fun a => ∫ θ in (-a)..a, cexp (z * temmeV θ) with hJ
  set T : ℝ → ℝ → ℂ := fun σ a => ∫ R in Ioi (‖z‖ * temmeRho a), hankelF z R (σ * a + arg z) *
    cexp (((σ * a + arg z : ℝ) : ℂ) * I) with hT
  have hid : ∀ᶠ a in 𝓝[<] π, I * J a =
      z ^ (z - 1) * (2 * π * I * (Gamma z)⁻¹ - T 1 a + T (-1) a) := by
    filter_upwards [Ioo_mem_nhdsLT (show π / 2 + |arg z| < π by linarith)] with a ha
    have := temme_identity hz ha.1 ha.2
    simp only [hJ, hT, one_mul, neg_one_mul]
    exact this
  have hL := (tendsto_temmeJ hz).const_mul I
  have hR : Tendsto (fun a => z ^ (z - 1) * (2 * π * I * (Gamma z)⁻¹ - T 1 a + T (-1) a))
      (𝓝[<] π) (𝓝 (z ^ (z - 1) * (2 * π * I * (Gamma z)⁻¹ - 0 + 0))) :=
    (((tendsto_const_nhds.sub (tendsto_temme_tail hz (Or.inl rfl))).add
      (tendsto_temme_tail hz (Or.inr rfl))).const_mul _)
  have hJπ : I * J π = z ^ (z - 1) * (2 * π * I * (Gamma z)⁻¹) := by
    have := tendsto_nhds_unique (hL.congr' (hid.mono fun a h => h)) hR
    rw [this]; ring
  -- `J(π) = e^z ∫ e^{−zΦ}`
  have hnull : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({0, π} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp ((Set.toFinite _).measure_zero _)
  have hJΦ : J π = cexp z * ∫ t in (-π)..π, cexp (-(z * temmePhi t)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (hnull.mono fun x hx hxI => ?_)
    rw [uIoc_of_le (by linarith [Real.pi_pos])] at hxI
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hx
    have hxo : x ∈ Ioo (-π) π := ⟨hxI.1, lt_of_le_of_ne hxI.2 hx.2⟩
    rw [temmeV_eq hxo hx.1, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpow : z ^ (1 - z) * z ^ (z - 1) = 1 := by
    rw [← cpow_add _ _ hz0, show 1 - z + (z - 1) = 0 by ring, cpow_zero]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hJπ' : J π = z ^ (z - 1) * (2 * π * (Gamma z)⁻¹) := by
    have := hJπ
    apply mul_left_cancel₀ I_ne_zero
    rw [this]; ring
  rw [one_div, show cexp z * z ^ (1 - z) / (2 * π) * ∫ t in (-π)..π, cexp (-(z * temmePhi t)) =
    z ^ (1 - z) / (2 * π) * (cexp z * ∫ t in (-π)..π, cexp (-(z * temmePhi t))) by ring,
    ← hJΦ, hJπ']
  have h2π : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hπ
  rw [show z ^ (1 - z) / (2 * π) * (z ^ (z - 1) * (2 * π * (Gamma z)⁻¹)) =
    (z ^ (1 - z) * z ^ (z - 1)) * (Gamma z)⁻¹ * ((2 * π) / (2 * π)) by ring, hpow, div_self h2π]
  ring

end Azurite.DLMF
