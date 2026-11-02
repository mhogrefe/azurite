/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14Mellin
import Azurite.DLMF.Chapter2.Section4Inverse

/-!
# DLMF §2.5(i): Mellin transform methods, introduction (2.5.1–2.5.5)

The Mellin transform 2.5.1 is Mathlib's `mellin`; `MellinConvergent f s` says `t^{s−1} f(t)` is
integrable on `(0, ∞)`. The strip of analyticity and the inversion formula 2.5.2 are
§1.14(iv) (`dlmf_1_14_iv_analytic`, `dlmf_1_14_35`, `dlmf_1_14_34`).

* 2.5.3: `mellinConvInt f h x = ∫₀^∞ f(t) h(xt) dt`.
* 2.5.4: `𝓜I(z) = 𝓜f(1 − z) 𝓜h(z)` when `t^{−ℜz} f(t)` and `t^{ℜz − 1} h(t)` are integrable:
  `t ↦ 1/t` turns `I` into the Mellin convolution 1.14.39 of `f(1/t)/t` and `h`, whose
  transform is `𝓜f(1 − z)`, and 1.14.40 applies.
* 2.5.5: `I(x) = (2πi)⁻¹ ∫_{c−i∞}^{c+i∞} x^{−z} 𝓜f(1 − z) 𝓜h(z) dz` (1.14.36), with the
  Parseval-type formula at `x = 1` (1.14.37).

2.5.6–2.5.7 (the shift of the contour and the residue sum) are in `Section5Residues`.
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real

namespace Azurite.DLMF

/-- **DLMF 2.5.1**: `𝓜f(z) = ∫₀^∞ t^{z−1} f(t) dt` (Mathlib's `mellin`). -/
theorem dlmf_2_5_1 (f : ℝ → ℂ) (z : ℂ) :
    mellin f z = ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (z - 1) * f t := by
  simp only [mellin, smul_eq_mul]

/-- DLMF's hypothesis in §2.5(i): `f` locally integrable on `(0, ∞)`, i.e. `∫_ρ^T f` exists for
`0 < ρ < T < ∞`. -/
def LocallyIntegrableDLMF (f : ℝ → ℂ) : Prop :=
  ∀ ρ T : ℝ, 0 < ρ → ρ < T → IntervalIntegrable f volume ρ T

theorem LocallyIntegrableDLMF.of_mellinConvergent {f : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s) :
    LocallyIntegrableDLMF f := fun ρ T hρ hρT => by
  have hint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * f t) (Icc ρ T) :=
    hf.mono_set fun t ht => lt_of_lt_of_le hρ ht.1
  have hcont : ContinuousOn (fun t : ℝ => ((t : ℂ) ^ (s - 1))⁻¹) (Icc ρ T) :=
    ContinuousOn.inv₀
      ((continuousOn_ofReal_cpow_Ioi (s - 1)).mono fun t ht => lt_of_lt_of_le hρ ht.1)
      fun t ht => cpow_ne_zero_of_ne_zero (ofReal_ne_zero.mpr (lt_of_lt_of_le hρ ht.1).ne') _
  have : IntegrableOn f (Icc ρ T) := by
    refine (hint.mul_continuousOn_of_subset hcont measurableSet_Icc isCompact_Icc
      (subset_refl _)).congr_fun (fun t ht => ?_) measurableSet_Icc
    have hne : (t : ℂ) ^ (s - 1) ≠ 0 :=
      cpow_ne_zero_of_ne_zero (ofReal_ne_zero.mpr (lt_of_lt_of_le hρ ht.1).ne') _
    field_simp
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hρT.le]
  exact this

/-- **DLMF 2.5.1**, the strip of analyticity: if `t^{σ−1} f(t)` is integrable for every
`σ ∈ (a, b)`, then `𝓜f` is analytic on `a < ℜz < b` (§1.14(iv)). -/
theorem dlmf_2_5_1_analytic {f : ℝ → ℂ} {a b : ℝ} (hf : ∀ σ ∈ Ioo a b, MellinConvergent f σ) :
    AnalyticOnNhd ℂ (mellin f) {s | s.re ∈ Ioo a b} :=
  (dlmf_1_14_iv_analytic hf).2

/-- **DLMF 2.5.2**: the inversion formula `f(t) = (2πi)⁻¹ ∫_{c−i∞}^{c+i∞} t^{−z} 𝓜f(z) dz` at a
point of continuity, when `𝓜f` is integrable on the line `ℜz = c` (1.14.35); the line integral
is written as `(2π)⁻¹ ∫ t^{−(c+iy)} 𝓜f(c + iy) dy`. -/
theorem dlmf_2_5_2 {f : ℝ → ℂ} {c : ℝ} (hf : MellinConvergent f c)
    (hF : VerticalIntegrable (mellin f) c) {t : ℝ} (ht : 0 < t) (hc : ContinuousAt f t) :
    f t = (2 * π : ℂ)⁻¹ * ∫ y : ℝ, (t : ℂ) ^ (-((c : ℂ) + y * I)) * mellin f (c + y * I) :=
  dlmf_1_14_35 hf hF ht hc

/-- **DLMF 2.5.2** at a point of bounded variation, as a symmetric limit (1.14.34). -/
theorem dlmf_2_5_2_bv {f : ℝ → ℂ} {c : ℝ} (hf : MellinConvergent f c) {t δ : ℝ} (ht : 0 < t)
    (hδ : 0 < δ) (hbv : BoundedVariationOn f (Icc (t - δ) (t + δ))) {Lp Lm : ℂ}
    (hp : Tendsto f (𝓝[>] t) (𝓝 Lp)) (hm : Tendsto f (𝓝[<] t) (𝓝 Lm)) :
    Tendsto (fun T : ℝ => (2 * π : ℂ)⁻¹ *
      ∫ y in (-T)..T, (t : ℂ) ^ (-((c : ℂ) + y * I)) * mellin f (c + y * I))
      atTop (𝓝 ((Lp + Lm) / 2)) :=
  dlmf_1_14_34 hf ht hδ hbv hp hm

/-- **DLMF 2.5.3**: `I(x) = ∫₀^∞ f(t) h(xt) dt`. -/
noncomputable def mellinConvInt (f h : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), f t * h (x * t)

/-- **DLMF 2.5.5**: `I(x) = (2πi)⁻¹ ∫_{c−i∞}^{c+i∞} x^{−z} 𝓜f(1 − z) 𝓜h(z) dz` for `a < c < b` in
the common strip (1.14.36), under either integrability hypothesis of §1.14(iv). -/
theorem dlmf_2_5_5 {f h : ℝ → ℂ} {c : ℝ} (hf : MellinConvergent f (1 - c))
    (hh : MellinConvergent h c)
    (hint : VerticalIntegrable (mellin h) c ∨ Integrable fun y : ℝ => mellin f (1 - c - y * I))
    {x : ℝ} (hx : 0 < x) :
    mellinConvInt f h x = (2 * π : ℂ)⁻¹ * ∫ y : ℝ,
      (x : ℂ) ^ (-((c : ℂ) + y * I)) * mellin f (1 - (c + y * I)) * mellin h (c + y * I) :=
  dlmf_1_14_36 hf hh hint hx

/-- **DLMF 2.5.5** at `x = 1`: the Parseval-type formula (1.14.37). -/
theorem dlmf_2_5_5_parseval {f h : ℝ → ℂ} {c : ℝ} (hf : MellinConvergent f (1 - c))
    (hh : MellinConvergent h c)
    (hint : VerticalIntegrable (mellin h) c ∨ Integrable fun y : ℝ => mellin f (1 - c - y * I)) :
    ∫ t in Ioi (0 : ℝ), f t * h t = (2 * π : ℂ)⁻¹ * ∫ y : ℝ,
      mellin f (1 - (c + y * I)) * mellin h (c + y * I) :=
  dlmf_1_14_37 hf hh hint

/-! ### 2.5.4 -/

/-- Under `t ↦ 1/t`, `I(x) = ∫₀^∞ f(t) h(xt) dt` is the Mellin convolution 1.14.39 of
`t ↦ f(1/t)/t` and `h`. -/
theorem mellinConvInt_eq_mellinConv (f h : ℝ → ℂ) (x : ℝ) :
    mellinConvInt f h x = mellinConv (fun t => (t : ℂ) ^ (-1 : ℂ) • f t⁻¹) h x := by
  rw [mellinConvInt, mellinConv,
    ← integral_comp_rpow_Ioi (fun t => f t * h (x * t)) (p := -1) (by norm_num)]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  simp only [Real.rpow_neg_one, smul_eq_mul, abs_neg, abs_one, one_mul, cpow_neg_one,
    Complex.real_smul, div_eq_mul_inv]
  rw [show (-1 - 1 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hy0.le, Real.rpow_two]
  push_cast
  field_simp

theorem mellin_inv_smul (f : ℝ → ℂ) (s : ℂ) :
    mellin (fun t => (t : ℂ) ^ (-1 : ℂ) • f t⁻¹) s = mellin f (1 - s) := by
  rw [mellin_cpow_smul, mellin_comp_inv]
  congr 1
  ring

theorem mellinConvergent_inv_smul {f : ℝ → ℂ} {s : ℂ} :
    MellinConvergent (fun t => (t : ℂ) ^ (-1 : ℂ) • f t⁻¹) s ↔ MellinConvergent f (1 - s) := by
  rw [MellinConvergent.cpow_smul]
  have := MellinConvergent.comp_rpow (f := f) (s := s + -1) (a := -1) (by norm_num)
  simp only [Real.rpow_neg_one] at this
  rw [this, show (s + -1) / ((-1 : ℝ) : ℂ) = 1 - s by push_cast; ring]

/-- **DLMF 2.5.4**: `𝓜I(z) = 𝓜f(1 − z) 𝓜h(z)` for `ℜz = σ`, when `t^{−σ}f(t)` and
`t^{σ−1}h(t)` are integrable. -/
theorem dlmf_2_5_4 {f h : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f (1 - σ))
    (hh : MellinConvergent h σ) {z : ℂ} (hz : z.re = σ) :
    mellin (mellinConvInt f h) z = mellin f (1 - z) * mellin h z := by
  have hf'c : MellinConvergent (fun t => (t : ℂ) ^ (-1 : ℂ) • f t⁻¹) σ :=
    mellinConvergent_inv_smul.mpr hf
  have h1 : mellin (mellinConvInt f h) z =
      mellin (mellinConv (fun t => (t : ℂ) ^ (-1 : ℂ) • f t⁻¹) h) z := by
    simp only [mellin]
    exact setIntegral_congr_fun measurableSet_Ioi fun x _ => by
      rw [mellinConvInt_eq_mellinConv f h x]
  rw [h1, show mellin (mellinConv (fun t => (t : ℂ) ^ (-1 : ℂ) • f t⁻¹) h) z =
    ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (z - 1) * mellinConv (fun t => (t : ℂ) ^ (-1 : ℂ) • f t⁻¹) h x
    by simp only [mellin, smul_eq_mul], dlmf_1_14_40 hf'c hh hz, mellin_inv_smul]

end Azurite.DLMF
