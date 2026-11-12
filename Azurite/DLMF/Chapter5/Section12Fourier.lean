/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section12

/-!
# DLMF §5.12: the Fourier-type beta integral 5.12.8

`(2π)⁻¹ ∫_{−∞}^{∞} dt/((w + it)^a (z − it)^b) = (w + z)^{1−a−b}/((a + b − 1)B(a, b))` for
`ℜ(a + b) > 1`, `ℜw, ℜz > 0` (`dlmf_5_12_8`).

Proof. For `ℜa > 0`, `ℜb > 1` (`fourierBeta_eq_of_re`): `g(s) = s^{b−1}e^{−zs}` (`s > 0`) has
Fourier transform `𝓕g(ξ) = Γ(b)(z + 2πiξ)^{−b}` (`fourier_gammaDensity`), which is integrable, so
Fourier inversion (`MeasureTheory.Integrable.fourierInv_fourier_eq`) recovers `g`. Writing
`(w − 2πiξ)^{−a} = Γ(a)⁻¹∫₀^∞ s^{a−1}e^{−(w−2πiξ)s} ds` and exchanging the integrals (Fubini)
gives `Γ(a)⁻¹Γ(b)⁻¹ ∫₀^∞ s^{a+b−2}e^{−(w+z)s} ds = Γ(a + b − 1)(w + z)^{1−a−b}/(Γ(a)Γ(b))`.
Both sides are holomorphic in `a` on `ℜa > 1 − ℜb` and in `b` on `ℜb > 1 − ℜa`
(`differentiableOn_fourierBeta`, from the bound `|w + it| ≍ 1 + |t|`), which removes the extra
conditions in two steps.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real FourierTransform

namespace Azurite.DLMF

/-! ### Bounds on `|w + it|` -/

theorem norm_add_mul_I_ge {w : ℂ} (hw : 0 < w.re) (t : ℝ) :
    w.re / (1 + w.re + ‖w‖) * (1 + |t|) ≤ ‖w + t * I‖ := by
  have h1 : w.re ≤ ‖w + t * I‖ := by
    have := re_le_norm (w + t * I)
    simpa using this
  have h2 : |t| ≤ ‖w + t * I‖ + ‖w‖ := by
    have := norm_sub_le (w + t * I) w
    simp only [add_sub_cancel_left, norm_mul, norm_real, Real.norm_eq_abs, norm_I,
      mul_one] at this
    exact this
  have hn := norm_nonneg w
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

theorem norm_add_mul_I_le (w : ℂ) (t : ℝ) : ‖w + t * I‖ ≤ (1 + ‖w‖) * (1 + |t|) := by
  have := norm_add_le w (t * I)
  simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one] at this
  nlinarith [norm_nonneg w, abs_nonneg t]

/-- A power of a quantity squeezed between `κy` and `Ky`, uniformly for exponents in `[q₁, q₂]`. -/
theorem rpow_le_of_squeeze {κ K X y q₁ q₂ q : ℝ} (hκ : 0 < κ) (hy : 0 < y) (h1 : κ * y ≤ X)
    (h2 : X ≤ K * y) (hq1 : q₁ ≤ q) (hq2 : q ≤ q₂) :
    X ^ q ≤ (κ ^ q₁ + κ ^ q₂ + K ^ q₁ + K ^ q₂) * y ^ q := by
  have hX : 0 < X := lt_of_lt_of_le (by positivity) h1
  have hK : κ ≤ K := le_of_mul_le_mul_right (h1.trans h2) hy
  have hK0 : 0 < K := hκ.trans_le hK
  set lam := X / y
  have hl1 : κ ≤ lam := (le_div_iff₀ hy).mpr h1
  have hl2 : lam ≤ K := (div_le_iff₀ hy).mpr h2
  have hl0 : 0 < lam := hκ.trans_le hl1
  have hXe : X = lam * y := by simp only [lam]; field_simp
  rw [hXe, Real.mul_rpow hl0.le hy.le]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hb : ∀ p : ℝ, lam ^ p ≤ κ ^ p + K ^ p := fun p => by
    rcases le_total 0 p with hp | hp
    · have := Real.rpow_le_rpow hl0.le hl2 hp
      linarith [Real.rpow_nonneg hκ.le p]
    · have := Real.rpow_le_rpow_of_nonpos hκ hl1 hp
      linarith [Real.rpow_nonneg hK0.le p]
  have hm : lam ^ q ≤ lam ^ q₁ + lam ^ q₂ := by
    rcases le_total 1 lam with hl | hl
    · have := Real.rpow_le_rpow_of_exponent_le hl hq2
      linarith [Real.rpow_nonneg hl0.le q₁]
    · have := Real.rpow_le_rpow_of_exponent_ge hl0 hl hq1
      linarith [Real.rpow_nonneg hl0.le q₂]
  linarith [hb q₁, hb q₂]

/-- `|(w + it)^{−a}| ≤ M e^{π|ℑa|}(1 + |t|)^{−p₁}` uniformly for `p₁ ≤ ℜa ≤ p₂`. -/
theorem exists_bound_cpow_neg {w : ℂ} (hw : 0 < w.re) (p₁ p₂ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ℂ, p₁ ≤ a.re → a.re ≤ p₂ → ∀ t : ℝ,
      ‖(w + t * I) ^ (-a)‖ ≤ M * Real.exp (π * |a.im|) * (1 + |t|) ^ (-p₁) := by
  set κ := w.re / (1 + w.re + ‖w‖)
  set K := 1 + ‖w‖
  have hκ : 0 < κ := by positivity
  have hK : 0 < K := by positivity
  refine ⟨κ ^ (-p₂) + κ ^ (-p₁) + K ^ (-p₂) + K ^ (-p₁), by positivity, fun a ha1 ha2 t => ?_⟩
  have hX0 : w + t * I ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have hy : (0 : ℝ) < 1 + |t| := by positivity
  have h1 := norm_cpow_le_of_re (s := -a) hX0
  rw [neg_re, neg_im, abs_neg] at h1
  have h2 := rpow_le_of_squeeze hκ hy (norm_add_mul_I_ge hw t) (norm_add_mul_I_le w t)
    (neg_le_neg ha2) (neg_le_neg ha1)
  have h3 : (1 + |t|) ^ (-a.re) ≤ (1 + |t|) ^ (-p₁) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (neg_le_neg ha1)
  calc ‖(w + t * I) ^ (-a)‖ ≤ ‖w + t * I‖ ^ (-a.re) * Real.exp (π * |a.im|) := h1
    _ ≤ ((κ ^ (-p₂) + κ ^ (-p₁) + K ^ (-p₂) + K ^ (-p₁)) * (1 + |t|) ^ (-a.re)) *
        Real.exp (π * |a.im|) := by gcongr
    _ ≤ ((κ ^ (-p₂) + κ ^ (-p₁) + K ^ (-p₂) + K ^ (-p₁)) * (1 + |t|) ^ (-p₁)) *
        Real.exp (π * |a.im|) := by gcongr
    _ = _ := by ring

theorem integrable_one_add_abs_rpow {r : ℝ} (hr : 1 < r) :
    Integrable fun t : ℝ => (1 + |t|) ^ (-r) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simpa using hr)
  simpa [Real.norm_eq_abs] using this

/-! ### The integral as a function of `a` -/

/-- The integrand of 5.12.8, `(w + it)^{−a}(z − it)^{−b}`. -/
noncomputable def fourierBetaF (w z a b : ℂ) (t : ℝ) : ℂ := (w + t * I) ^ (-a) * (z - t * I) ^ (-b)

theorem sub_mul_I_eq (z : ℂ) (t : ℝ) : z - t * I = z + ((-t : ℝ) : ℂ) * I := by
  push_cast; ring

theorem exists_bound_fourierBetaF {w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re) (b : ℂ)
    (p₁ p₂ : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ℂ, p₁ ≤ a.re → a.re ≤ p₂ → ∀ t : ℝ,
      ‖fourierBetaF w z a b t‖ ≤ M * Real.exp (π * |a.im|) * (1 + |t|) ^ (-(p₁ + b.re)) := by
  obtain ⟨M₁, hM₁, h₁⟩ := exists_bound_cpow_neg hw p₁ p₂
  obtain ⟨M₂, hM₂, h₂⟩ := exists_bound_cpow_neg hz b.re b.re
  refine ⟨M₁ * (M₂ * Real.exp (π * |b.im|)), by positivity, fun a ha1 ha2 t => ?_⟩
  have hb := h₂ b le_rfl le_rfl (-t)
  rw [← sub_mul_I_eq, abs_neg] at hb
  have hy : (0 : ℝ) < 1 + |t| := by positivity
  rw [fourierBetaF, norm_mul, neg_add, Real.rpow_add hy]
  calc ‖(w + t * I) ^ (-a)‖ * ‖(z - t * I) ^ (-b)‖
      ≤ (M₁ * Real.exp (π * |a.im|) * (1 + |t|) ^ (-p₁)) *
        (M₂ * Real.exp (π * |b.im|) * (1 + |t|) ^ (-b.re)) :=
        mul_le_mul (h₁ a ha1 ha2 t) hb (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem measurable_fourierBetaF (w z a b : ℂ) : Measurable (fourierBetaF w z a b) := by
  unfold fourierBetaF; fun_prop

theorem integrable_fourierBetaF {w z a b : ℂ} (hw : 0 < w.re) (hz : 0 < z.re)
    (hab : 1 < (a + b).re) : Integrable (fourierBetaF w z a b) := by
  obtain ⟨M, -, hM⟩ := exists_bound_fourierBetaF hw hz b a.re a.re
  refine Integrable.mono' ((integrable_one_add_abs_rpow (r := a.re + b.re)
    (by simpa using hab)).const_mul (M * Real.exp (π * |a.im|)))
    (measurable_fourierBetaF w z a b).aestronglyMeasurable (ae_of_all _ fun t => ?_)
  exact hM a le_rfl le_rfl t

/-- `a ↦ ∫ (w + it)^{−a}(z − it)^{−b} dt` is holomorphic on `ℜa > 1 − ℜb`. -/
theorem differentiableOn_fourierBeta {w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re) (b : ℂ) :
    DifferentiableOn ℂ (fun a => ∫ t, fourierBetaF w z a b t) {a | 1 < (a + b).re} := by
  refine differentiableOn_integral_of_holo (F := fun a t => fourierBetaF w z a b t)
    (F' := fun a (t : ℝ) => -((w + t * I) ^ (-a) * Complex.log (w + t * I)) * (z - t * I) ^ (-b))
    (fun a _ => (measurable_fourierBetaF w z a b).aestronglyMeasurable)
    (fun a _ => (by fun_prop : Measurable fun t : ℝ =>
      -((w + t * I) ^ (-a) * Complex.log (w + t * I)) * (z - t * I) ^ (-b)).aestronglyMeasurable)
    fun a₀ ha₀ => ?_
  have ha₀' : 1 < a₀.re + b.re := by simpa using ha₀
  set r := (a₀.re + b.re - 1) / 4
  have hr : 0 < r := by simp only [r]; linarith
  have hrdef : 4 * r = a₀.re + b.re - 1 := by simp only [r]; ring
  obtain ⟨M, hM0, hM⟩ := exists_bound_fourierBetaF hw hz b (a₀.re - 2 * r) (a₀.re + 2 * r)
  have hre : ∀ a ∈ Metric.closedBall a₀ (2 * r), |a.re - a₀.re| ≤ 2 * r ∧
      |a.im| ≤ |a₀.im| + 2 * r := fun a ha => by
    have hd : ‖a - a₀‖ ≤ 2 * r := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp ha
    have hre' : |a.re - a₀.re| ≤ ‖a - a₀‖ := by rw [← sub_re]; exact abs_re_le_norm _
    refine ⟨hre'.trans hd, ?_⟩
    have := (abs_im_le_norm (a - a₀)).trans hd
    rw [sub_im] at this
    linarith [abs_sub_abs_le_abs_sub a.im a₀.im]
  refine ⟨r, hr, fun a ha => ?_, fun t => M * Real.exp (π * (|a₀.im| + 2 * r)) *
    (1 + |t|) ^ (-(a₀.re - 2 * r + b.re)),
    ((integrable_one_add_abs_rpow (r := a₀.re - 2 * r + b.re) (by linarith)).const_mul
    _), ae_of_all _ fun t a _ => ?_, ae_of_all _ fun t a ha => ?_⟩
  · have hd := Metric.mem_ball.mp ha
    rw [dist_eq_norm] at hd
    have := (abs_re_le_norm (a - a₀)).trans hd.le
    rw [sub_re] at this
    show 1 < (a + b).re
    rw [add_re]
    linarith [(abs_le.mp this).1]
  · have hX0 : w + t * I ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith
    have h := ((hasDerivAt_id a).neg).const_cpow (c := w + t * I) (Or.inl hX0)
    have := h.mul_const ((z - t * I) ^ (-b))
    convert this using 1
    · funext y; simp [fourierBetaF]
    · simp
  · obtain ⟨h1, h2⟩ := hre a ha
    have := hM a (by linarith [(abs_le.mp h1).1]) (by linarith [(abs_le.mp h1).2]) t
    refine this.trans ?_
    show _ ≤ M * Real.exp (π * (|a₀.im| + 2 * r)) * (1 + |t|) ^ (-(a₀.re - 2 * r + b.re))
    gcongr

/-! ### The case `ℜa > 0`, `ℜb > 1` by Fourier inversion -/

theorem integrable_cpow_neg_add_mul_I {z b : ℂ} (hz : 0 < z.re) (hb : 1 < b.re) :
    Integrable fun s : ℝ => (z + s * I) ^ (-b) := by
  obtain ⟨M, -, hM⟩ := exists_bound_cpow_neg hz b.re b.re
  refine Integrable.mono' ((integrable_one_add_abs_rpow hb).const_mul
    (M * Real.exp (π * |b.im|))) (by fun_prop : Measurable fun s : ℝ =>
      (z + s * I) ^ (-b)).aestronglyMeasurable (ae_of_all _ fun s => ?_)
  exact hM b le_rfl le_rfl s

/-- The gamma density `s^{b−1}e^{−zs}`, `s > 0`. -/
noncomputable def gammaDensity (z b : ℂ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator fun s => (s : ℂ) ^ (b - 1) * cexp (-(z * s))

theorem integrable_gammaDensity {z b : ℂ} (hz : 0 < z.re) (hb : 0 < b.re) :
    Integrable (gammaDensity z b) :=
  (integrable_indicator_iff measurableSet_Ioi).mpr (integrableOn_cpow_mul_cexp_neg hb hz)

/-- `𝓕g(ξ) = Γ(b)(z + 2πiξ)^{−b}`. -/
theorem fourier_gammaDensity {z b : ℂ} (hz : 0 < z.re) (hb : 0 < b.re) (ξ : ℝ) :
    𝓕 (gammaDensity z b) ξ = Gamma b * (z + ((2 * π * ξ : ℝ) : ℂ) * I) ^ (-b) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hr : 0 < (z + ((2 * π * ξ : ℝ) : ℂ) * I).re := by simpa using hz
  have e : ∀ v : ℝ, cexp (((-2 * π * v * ξ : ℝ) : ℂ) * I) • gammaDensity z b v =
      (Ioi (0 : ℝ)).indicator (fun s => (s : ℂ) ^ (b - 1) *
        cexp (-((z + ((2 * π * ξ : ℝ) : ℂ) * I) * s))) v := fun v => by
    simp only [gammaDensity, indicator]
    split_ifs
    · rw [smul_eq_mul, mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    · simp
  simp_rw [e]
  rw [integral_indicator measurableSet_Ioi, integral_cpow_mul_cexp_neg_complex hb hr,
    one_div_cpow_of_re_pos hr, mul_comm]

theorem integrable_fourier_gammaDensity {z b : ℂ} (hz : 0 < z.re) (hb : 1 < b.re) :
    Integrable (𝓕 (gammaDensity z b)) := by
  rw [funext (fourier_gammaDensity hz (by linarith))]
  have h := (integrable_cpow_neg_add_mul_I hz hb).comp_mul_left' (R := 2 * π)
    (by positivity)
  refine (h.const_mul (Gamma b)).congr (ae_of_all _ fun ξ => ?_)
  simp only

/-- Fourier inversion for the gamma density at `s > 0`. -/
theorem fourierInv_fourier_gammaDensity {z b : ℂ} (hz : 0 < z.re) (hb : 1 < b.re) {s : ℝ}
    (hs : 0 < s) : ∫ ξ : ℝ, cexp (((2 * π * s * ξ : ℝ) : ℂ) * I) *
      (Gamma b * (z + ((2 * π * ξ : ℝ) : ℂ) * I) ^ (-b)) = (s : ℂ) ^ (b - 1) * cexp (-(z * s)) := by
  have hc : ContinuousAt (gammaDensity z b) s := by
    have h1 : ContinuousAt (fun s : ℝ => (s : ℂ) ^ (b - 1) * cexp (-(z * s))) s :=
      ((continuousAt_ofReal_cpow_const _ _ (Or.inr hs.ne')).mul (by fun_prop))
    refine h1.congr ?_
    filter_upwards [Ioi_mem_nhds hs] with u hu
    simp [gammaDensity, indicator_of_mem hu]
  have h := (integrable_gammaDensity hz (by linarith)).fourierInv_fourier_eq
    (integrable_fourier_gammaDensity hz hb) hc
  have hg : gammaDensity z b s = (s : ℂ) ^ (b - 1) * cexp (-(z * s)) :=
    indicator_of_mem (show s ∈ Ioi 0 from hs) _
  rw [Real.fourierInv_eq', hg] at h
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only
  rw [fourier_gammaDensity hz (by linarith : 0 < b.re), smul_eq_mul]
  congr 3
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

/-- 5.12.8 for `ℜa > 0`, `ℜb > 1`, in Gamma form. -/
theorem fourierBeta_eq_of_re {w z a b : ℂ} (hw : 0 < w.re) (hz : 0 < z.re) (ha : 0 < a.re)
    (hb : 1 < b.re) : ∫ t, fourierBetaF w z a b t =
      2 * π * (Gamma (a + b - 1) * (w + z) ^ (1 - a - b) * (Gamma a)⁻¹ * (Gamma b)⁻¹) := by
  have hb0 : 0 < b.re := by linarith
  have hGa := Complex.Gamma_ne_zero_of_re_pos ha
  have hGb := Complex.Gamma_ne_zero_of_re_pos hb0
  have hπ : (0 : ℝ) < 2 * π := by positivity
  set φ : ℝ → ℂ := fun s => (s : ℂ) ^ (a - 1) * cexp (-(w * s))
  set ψ : ℝ → ℂ := fun ξ => Gamma b * (z + ((2 * π * ξ : ℝ) : ℂ) * I) ^ (-b)
  set K : ℝ → ℝ → ℂ := fun ξ s => φ s * (cexp (((2 * π * s * ξ : ℝ) : ℂ) * I) * ψ ξ)
  -- the substitution `t = −2πξ`
  have hsub : ∫ t, fourierBetaF w z a b t =
      2 * π * ∫ ξ : ℝ, fourierBetaF w z a b (-(2 * π) * ξ) := by
    rw [Measure.integral_comp_mul_left, abs_inv, abs_neg, abs_of_pos hπ, Complex.real_smul,
      ← mul_assoc]
    push_cast
    field_simp
  -- each value of the integrand is an inner integral
  have hpt : ∀ ξ : ℝ, fourierBetaF w z a b (-(2 * π) * ξ) =
      (Gamma a)⁻¹ * (Gamma b)⁻¹ * ∫ s in Ioi (0 : ℝ), K ξ s := fun ξ => by
    have hr : 0 < (w - ((2 * π * ξ : ℝ) : ℂ) * I).re := by simpa using hw
    have h1 := integral_cpow_mul_cexp_neg_complex ha hr
    rw [one_div_cpow_of_re_pos hr] at h1
    have h2 : ∫ s in Ioi (0 : ℝ), K ξ s =
        (∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (a - 1) *
          cexp (-((w - ((2 * π * ξ : ℝ) : ℂ) * I) * s))) * ψ ξ := by
      rw [← integral_mul_const]
      refine integral_congr_ae (ae_of_all _ fun s => ?_)
      simp only [K, φ]
      have e : -((w - ((2 * π * ξ : ℝ) : ℂ) * I) * (s : ℂ)) =
          -(w * s) + ((2 * π * s * ξ : ℝ) : ℂ) * I := by push_cast; ring
      rw [e, Complex.exp_add]
      ring
    rw [h2, h1]
    simp only [fourierBetaF, ψ]
    field_simp
    congr 2 <;> push_cast <;> ring_nf
  -- Fubini
  have hφi : IntegrableOn φ (Ioi 0) := integrableOn_cpow_mul_cexp_neg ha hw
  have hψi : Integrable ψ := by
    have := integrable_fourier_gammaDensity hz hb
    rwa [funext (fourier_gammaDensity hz hb0)] at this
  have hKi : Integrable (Function.uncurry K) (volume.prod (volume.restrict (Ioi 0))) := by
    refine Integrable.mono' (hψi.norm.mul_prod hφi.norm) ?_ (ae_of_all _ fun p => ?_)
    · exact (by fun_prop : Measurable fun p : ℝ × ℝ => (p.2 : ℂ) ^ (a - 1) * cexp (-(w * p.2)) *
        (cexp (((2 * π * p.2 * p.1 : ℝ) : ℂ) * I) * (Gamma b *
          (z + ((2 * π * p.1 : ℝ) : ℂ) * I) ^ (-b)))).aestronglyMeasurable
    · simp only [Function.uncurry, K, norm_mul, norm_exp_ofReal_mul_I, one_mul]
      exact le_of_eq (mul_comm _ _)
  have hswap := integral_integral_swap hKi
  -- the inner `ξ`-integral is Fourier inversion
  have hinner : ∫ s in Ioi (0 : ℝ), ∫ ξ : ℝ, K ξ s =
      ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ ((a + b - 1) - 1) * cexp (-((w + z) * s)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    simp only [K]
    rw [integral_const_mul]
    simp only [ψ]
    rw [fourierInv_fourier_gammaDensity hz hb hs]
    simp only [φ]
    have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hs)
    rw [show (a + b - 1) - 1 = (a - 1) + (b - 1) by ring, cpow_add _ _ hs0]
    rw [show -((w + z) * s) = -(w * s) + -(z * s) by ring, Complex.exp_add]
    ring
  have hab : 0 < (a + b - 1).re := by simp only [sub_re, add_re, one_re]; linarith
  have hwz : 0 < (w + z).re := by simp only [add_re]; linarith
  have hfin := integral_cpow_mul_cexp_neg_complex hab hwz
  rw [one_div_cpow_of_re_pos hwz] at hfin
  rw [hsub, funext hpt, integral_const_mul, hswap, hinner, hfin,
    show -(a + b - 1) = 1 - a - b by ring]
  ring

/-! ### Analytic continuation -/

/-- The Gamma form of the right side of 5.12.8 (without the factor `2π`). -/
noncomputable def fourierBetaG (w z a b : ℂ) : ℂ :=
  Gamma (a + b - 1) * (w + z) ^ (1 - a - b) * (Gamma a)⁻¹ * (Gamma b)⁻¹

theorem fourierBetaG_comm (w z a b : ℂ) : fourierBetaG w z a b = fourierBetaG z w b a := by
  simp only [fourierBetaG, add_comm w z, add_comm a b]
  ring_nf

theorem isOpen_re_add_gt (b : ℂ) : IsOpen {a : ℂ | 1 < (a + b).re} :=
  isOpen_lt continuous_const (continuous_re.comp (continuous_id.add continuous_const))

theorem isPreconnected_re_add_gt (b : ℂ) : IsPreconnected {a : ℂ | 1 < (a + b).re} := by
  have : {a : ℂ | 1 < (a + b).re} = {a : ℂ | 1 - b.re < a.re} := by
    ext a; simp only [mem_ofPred_eq, add_re]; constructor <;> intro h <;> linarith
  rw [this]
  exact (convex_halfSpace_re_gt _).isPreconnected

theorem differentiableOn_fourierBetaG (w z b : ℂ) (hwz : w + z ≠ 0) :
    DifferentiableOn ℂ (fun a => fourierBetaG w z a b) {a | 1 < (a + b).re} := by
  intro a ha
  have ha' : 0 < (a + b - 1).re := by
    simp only [mem_ofPred_eq] at ha; simp only [sub_re, one_re]; linarith
  have hG : DifferentiableAt ℂ (fun a => Gamma (a + b - 1)) a := by
    refine (Complex.differentiableAt_Gamma _ fun m h => ?_).comp a
      ((differentiableAt_id.add_const b).sub_const 1)
    have := congrArg re h
    simp only [neg_re, natCast_re] at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hinv : Differentiable ℂ fun a : ℂ => (Gamma a)⁻¹ := by
    simpa [one_div] using Complex.differentiable_one_div_Gamma
  have hpow : DifferentiableAt ℂ (fun a : ℂ => (w + z) ^ (1 - a - b)) a :=
    ((differentiableAt_const _).sub differentiableAt_id |>.sub_const b).const_cpow (Or.inl hwz)
  exact (((hG.mul hpow).mul (hinv a)).mul_const _).differentiableWithinAt

theorem integral_fourierBetaF_comm (w z a b : ℂ) :
    ∫ t, fourierBetaF w z a b t = ∫ t, fourierBetaF z w b a t := by
  have h := Measure.integral_comp_mul_left (fun t => fourierBetaF z w b a t) (-1)
  simp only [inv_neg, inv_one, abs_neg, abs_one, one_smul, neg_one_mul] at h
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [fourierBetaF]
  push_cast
  rw [mul_comm]
  ring_nf

theorem fourierBeta_eq_of_re_b {w z a b : ℂ} (hw : 0 < w.re) (hz : 0 < z.re)
    (hab : 1 < (a + b).re) (hb : 1 < b.re) :
    ∫ t, fourierBetaF w z a b t = 2 * π * fourierBetaG w z a b := by
  have hwz : w + z ≠ 0 := fun h => by
    have := congrArg re h; simp only [add_re, zero_re] at this; linarith
  have hf := (differentiableOn_fourierBeta hw hz b).analyticOnNhd (isOpen_re_add_gt b)
  have hg := ((differentiableOn_fourierBetaG w z b hwz).const_mul (2 * (π : ℂ))).analyticOnNhd
    (isOpen_re_add_gt b)
  have h1 : (1 : ℂ) ∈ {a : ℂ | 1 < (a + b).re} := by
    simp only [mem_ofPred_eq, add_re, one_re]; linarith
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg (isPreconnected_re_add_gt b) h1 ?_ hab
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (show (1 : ℂ) ∈ {a : ℂ | 0 < a.re} by simp)] with a ha
  exact fourierBeta_eq_of_re hw hz ha hb

/-- 5.12.8 in Gamma form for `ℜ(a + b) > 1`. -/
theorem fourierBeta_eq {w z a b : ℂ} (hw : 0 < w.re) (hz : 0 < z.re) (hab : 1 < (a + b).re) :
    ∫ t, fourierBetaF w z a b t = 2 * π * fourierBetaG w z a b := by
  rcases lt_or_ge 1 b.re with hb | hb
  · exact fourierBeta_eq_of_re_b hw hz hab hb
  have ha : 0 < a.re := by rw [add_re] at hab; linarith
  have hzw : z + w ≠ 0 := fun h => by
    have := congrArg re h; simp only [add_re, zero_re] at this; linarith
  rw [integral_fourierBetaF_comm, fourierBetaG_comm]
  have hf := (differentiableOn_fourierBeta hz hw a).analyticOnNhd (isOpen_re_add_gt a)
  have hg := ((differentiableOn_fourierBetaG z w a hzw).const_mul (2 * (π : ℂ))).analyticOnNhd
    (isOpen_re_add_gt a)
  have h2 : (2 : ℂ) ∈ {b : ℂ | 1 < (b + a).re} := by
    simp only [mem_ofPred_eq, add_re]; norm_num; linarith
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg (isPreconnected_re_add_gt a) h2 ?_
    (by simpa [add_comm] using hab)
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (show (2 : ℂ) ∈ {b : ℂ | 1 < b.re} by norm_num)] with b' hb'
  rw [integral_fourierBetaF_comm, fourierBetaG_comm]
  exact fourierBeta_eq_of_re_b hw hz (by simp only [add_re]; linarith [hb'.le]) hb'

/-- The right side of 5.12.8 in DLMF's form equals the Gamma form. -/
theorem div_beta_eq_fourierBetaG {w z a b : ℂ} (hab : 1 < (a + b).re) :
    (w + z) ^ (1 - a - b) / ((a + b - 1) * dlmfBeta a b) = fourierBetaG w z a b := by
  have h0 : a + b - 1 ≠ 0 := fun h => by
    have := congrArg re h; simp only [sub_re, add_re, one_re, zero_re] at this
    simp only [add_re] at hab; linarith
  have hG : Gamma (a + b - 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    simp only [sub_re, add_re, one_re]; simp only [add_re] at hab; linarith)
  have hs : Gamma (a + b) = (a + b - 1) * Gamma (a + b - 1) := by
    rw [← Complex.Gamma_add_one _ h0, sub_add_cancel]
  rw [dlmfBeta, hs, mul_div_assoc', mul_div_mul_left _ _ h0, div_div_eq_mul_div, fourierBetaG,
    div_eq_mul_inv, mul_inv]
  ring

/-- **DLMF 5.12.8**: `(2π)⁻¹ ∫_{−∞}^{∞} dt/((w + it)^a (z − it)^b) =
(w + z)^{1−a−b}/((a + b − 1)B(a, b))`, `ℜ(a + b) > 1`, `ℜw > 0`, `ℜz > 0` (principal powers,
which are continuous for `ℜw, ℜz > 0`). -/
theorem dlmf_5_12_8 {w z a b : ℂ} (hab : 1 < (a + b).re) (hw : 0 < w.re) (hz : 0 < z.re) :
    1 / (2 * π) * ∫ t : ℝ, 1 / ((w + I * t) ^ a * (z - I * t) ^ b) =
      (w + z) ^ (1 - a - b) / ((a + b - 1) * dlmfBeta a b) := by
  have e : ∀ t : ℝ, 1 / ((w + I * t) ^ a * (z - I * t) ^ b) = fourierBetaF w z a b t := fun t => by
    rw [fourierBetaF, cpow_neg, cpow_neg, one_div, mul_inv, mul_comm I]
  simp_rw [e]
  rw [fourierBeta_eq hw hz hab, div_beta_eq_fourierBetaG hab]
  field_simp

end Azurite.DLMF
