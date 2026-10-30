/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14HilbertSubharmonic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# DLMF 1.14.45: the sharp bound for boundary values of holomorphic functions

`integral_im_rpow_le`: for `F` as in `integral_comp_nonneg` and `1 < p ≤ 2`,
`∫ |Im F|^p ≤ tan^p(π/2p) ∫ |Re F|^p` on `ℝ`. Pichorides' inequality is integrated, and
`∫ Re((|Re F| + i Im F)^p) ≥ 0` is the `δ → 0` limit of `∫ Ψ_δ(F) ≥ 0` by dominated
convergence.
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real

namespace Azurite.DLMF

theorem pichoridesB_pos {p : ℝ} (hp1 : 1 < p) : 0 < pichoridesB p := by
  obtain ⟨h0, h1⟩ := pichorides_theta0_mem hp1
  have hπ := Real.pi_pos
  exact div_pos (Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)) _)
    (Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩)

theorem abs_pichoridesPhi_le {p : ℝ} (w : ℂ) : |pichoridesPhi p w| ≤ ‖w‖ ^ p := by
  have hn : ‖(((|w.re| : ℝ) : ℂ) + w.im * I)‖ = ‖w‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      normSq_apply, normSq_apply]
    simp
  rw [pichoridesPhi]
  exact (abs_re_le_norm _).trans ((norm_cpow_real _ _).le.trans (by rw [hn]))

theorem measurable_pichoridesPhi (p : ℝ) : Measurable (pichoridesPhi p) := by
  unfold pichoridesPhi
  refine Complex.measurable_re.comp (Measurable.pow_const ?_ _)
  exact (Complex.measurable_ofReal.comp
    (_root_.continuous_abs.measurable.comp Complex.measurable_re)).add
    ((Complex.measurable_ofReal.comp Complex.measurable_im).mul_const I)

section Core

variable {F : ℂ → ℂ} {c K : ℝ}

/-- `|F(x)|^p` is integrable on `ℝ` when `|F(x)| ≤ K/(1 + |x|)` and `p > 1`. -/
theorem integrable_norm_rpow_of_decay {p : ℝ} (hp1 : 1 < p) (hFc : Continuous fun x : ℝ => F x)
    (hK : 0 ≤ K) (hFb : ∀ x : ℝ, ‖F x‖ ≤ K / (1 + |x|)) :
    Integrable fun x : ℝ => ‖F x‖ ^ p := by
  have hp0 : 0 < p := by linarith
  have hI : Integrable fun x : ℝ => (1 + ‖x‖) ^ (-p) :=
    integrable_one_add_norm (by simpa using hp1)
  refine (hI.const_mul (K ^ p)).mono'
    (hFc.norm.rpow_const fun _ => Or.inr hp0.le).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), Real.norm_eq_abs]
  have h1 : 0 < 1 + |x| := by positivity
  calc ‖F x‖ ^ p ≤ (K / (1 + |x|)) ^ p := Real.rpow_le_rpow (norm_nonneg _) (hFb x) hp0.le
    _ = K ^ p * (1 + |x|) ^ (-p) := by
        rw [Real.div_rpow hK h1.le, Real.rpow_neg h1.le, div_eq_mul_inv]

/-- **The core sharp bound** (Pichorides; DLMF 1.14.45 for `1 < p ≤ 2`): if `F` is holomorphic on
`{Im z > −c}`, with `|F(z)| ≤ K/(1 + |z|)` and `|F′(z)| ≤ K/(1 + |z|)²` on the closed upper
half-plane, then `∫ |Im F(x)|^p dx ≤ tan^p(π/2p) ∫ |Re F(x)|^p dx`. Both `|Re F|^p` and
`|Im F|^p` are integrable. -/
theorem integral_im_rpow_le {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) (hc : 0 < c)
    (hF : DifferentiableOn ℂ F {z | -c < z.im}) (hK : 0 ≤ K)
    (hFb : ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ ≤ K / (1 + ‖z‖))
    (hF'b : ∀ z : ℂ, 0 ≤ z.im → ‖deriv F z‖ ≤ K / (1 + ‖z‖) ^ 2) :
    Integrable (fun x : ℝ => |(F x).re| ^ p) ∧ Integrable (fun x : ℝ => |(F x).im| ^ p) ∧
      ∫ x : ℝ, |(F x).im| ^ p ≤ pichoridesA p ^ p * ∫ x : ℝ, |(F x).re| ^ p := by
  have hp0 : 0 < p := by linarith
  have hreal : ∀ x : ℝ, (x : ℂ) ∈ {z : ℂ | -c < z.im} := fun x => by simp [hc]
  have hFc : Continuous fun x : ℝ => F x := hF.continuousOn.comp_continuous continuous_ofReal hreal
  have hFbR : ∀ x : ℝ, ‖F x‖ ≤ K / (1 + |x|) := fun x => by
    have := hFb x (by simp); rwa [Complex.norm_real, Real.norm_eq_abs] at this
  have hN := integrable_norm_rpow_of_decay hp1 hFc hK hFbR
  have hre : Integrable fun x : ℝ => |(F x).re| ^ p :=
    hN.mono' ((Complex.continuous_re.comp hFc).abs.rpow_const fun _ => Or.inr hp0.le
      ).aestronglyMeasurable (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact Real.rpow_le_rpow (abs_nonneg _) (abs_re_le_norm _) hp0.le)
  have him : Integrable fun x : ℝ => |(F x).im| ^ p :=
    hN.mono' ((Complex.continuous_im.comp hFc).abs.rpow_const fun _ => Or.inr hp0.le
      ).aestronglyMeasurable (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact Real.rpow_le_rpow (abs_nonneg _) (abs_im_le_norm _) hp0.le)
  have hΦi : Integrable fun x : ℝ => pichoridesPhi p (F x) :=
    hN.mono' ((measurable_pichoridesPhi p).comp hFc.measurable).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_pichoridesPhi_le _)
  -- `∫ Φ(F) ≥ 0`, the limit of `∫ Ψ_δ(F) ≥ 0`
  obtain ⟨C, hC0, hC⟩ := exists_psiD_bound hp1 hp2
  have hΦ : 0 ≤ ∫ x : ℝ, pichoridesPhi p (F x) := by
    have hlim : Tendsto (fun δ : ℝ => ∫ x : ℝ, psiD p δ (F x)) (𝓝[>] 0)
        (𝓝 (∫ x : ℝ, pichoridesPhi p (F x))) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun x => C * ‖F x‖ ^ p) ?_ ?_
        (hN.const_mul C) (ae_of_all _ fun x => tendsto_psiD hp0 (F x))
      · filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact ((contDiff_psiD p hδ).continuous.comp hFc).aestronglyMeasurable
      · filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC δ hδ (F x)
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    exact (integral_comp_nonneg hc hF hK hFb hF'b ((contDiff_psiD p hδ).of_le le_top)
      (psiD_zero p hδ) (fderiv_psiD_zero p hδ) (psiD_subharmonic hp1 hp2 hδ)).2
  refine ⟨hre, him, ?_⟩
  have hpt : ∀ x : ℝ, |(F x).im| ^ p + pichoridesB p * pichoridesPhi p (F x) ≤
      pichoridesA p ^ p * |(F x).re| ^ p := fun x => pichorides_ineq hp1 hp2 _ _
  have hint := integral_mono (him.add (hΦi.const_mul _)) (hre.const_mul _) hpt
  simp only [Pi.add_apply] at hint
  rw [integral_add him (hΦi.const_mul _), integral_const_mul, integral_const_mul] at hint
  have hB := pichoridesB_pos hp1
  nlinarith [mul_nonneg hB.le hΦ]

end Core

end Azurite.DLMF
