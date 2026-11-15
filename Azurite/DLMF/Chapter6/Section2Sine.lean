/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section2

/-!
# DLMF §6.2(ii): sine and cosine integrals

Formalizations of <https://dlmf.nist.gov/6.2.ii>, equations 6.2.9–6.2.16.

`Si`, `Cin`, `Shi` and the integral of 6.2.16 are defined by their segment integrals from `0`
(as `Ein` in 6.2.3); `si` and `Ci` by improper integrals along the horizontal ray from `z`.
Each segment integral is identified with a closed form in `Ein` (`Si = (Ein(iz) − Ein(−iz))/(2i)`,
`Cin = (Ein(iz) + Ein(−iz))/2`, `Shi = (Ein(z) − Ein(−z))/2`, `∫_0^z (cosh t − 1)/t dt =
−(Ein(z) + Ein(−z))/2`) by `segment_eq_sub`, which gives entireness, parity and path
independence.  The values at infinity (6.2.14) come from 6.2.4 at `±ix` and
`|E₁(±ix)| ≤ 1/x` (`norm_expIntE₁_le`), with no Dirichlet integral; the complex limits along the
ray from the vertical estimate `tendsto_of_vertical`.

* 6.2.9: `Si`, `dlmf_6_2_9_entire`, `dlmf_6_2_9_odd`, `dlmf_6_2_9_contour`.
* 6.2.10: `si`, `dlmf_6_2_10` (the improper integral converges for every `z`, `si = Si − π/2`),
  `dlmf_6_2_10_contour`.
* 6.2.11: `Ci`, `dlmf_6_2_11` (any contour off the cut), `dlmf_6_2_11_cut` (boundary values).
* 6.2.12: `Cin`, `dlmf_6_2_12_entire`, `dlmf_6_2_12_even`, `dlmf_6_2_12_contour`.
* 6.2.13: `dlmf_6_2_13` (with the ray limit).
* 6.2.14: `dlmf_6_2_14`.
* 6.2.15: `Shi`, `dlmf_6_2_15_entire`, `dlmf_6_2_15_contour`.
* 6.2.16: `Chi`, `chiInt`, `dlmf_6_2_16_entire`, `dlmf_6_2_16_deriv` (`Chi′ = cosh z / z`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Interval

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-! ### Generic tools -/

/-- A segment integral `∫_0^z g(t) dt = ∫_0^1 g(zs) z ds` of a function `g` that agrees off `0`
with the derivative `f` of an entire primitive `F` is `F(z) − F(0)`. -/
theorem segment_eq_sub {F f g : ℂ → ℂ} (hF : ∀ w, HasDerivAt F (f w) w) (hf : Continuous f)
    (hg : ∀ t, t ≠ 0 → g t = f t) (z : ℂ) :
    ∫ s in (0 : ℝ)..1, g (z * s) * z = F z - F 0 := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => F (z * s)) (f (z * s) * z) s := by
    intro s _
    have h1 : HasDerivAt (fun w : ℂ => F (z * w)) (f (z * s) * z) (s : ℂ) := by
      have := (hF (z * s)).comp (s : ℂ) ((hasDerivAt_id (s : ℂ)).const_mul z)
      simp only [Function.comp_def, mul_one] at this
      exact this
    exact h1.comp_ofReal
  have hc : Continuous fun s : ℝ => f (z * s) * z :=
    (hf.comp (continuous_const.mul continuous_ofReal)).mul continuous_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 1)
  simp only [ofReal_one, mul_one, ofReal_zero, mul_zero] at hftc
  rw [← hftc]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
  rw [uIoc_of_le zero_le_one] at hs
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [hg _ (mul_ne_zero hz (ofReal_ne_zero.mpr hs.1.ne'))]

/-- The same along the horizontal segment: `∫_0^R g(z + s) ds = F(z + R) − F(z)`. -/
theorem integral_shift_eq_sub {F f g : ℂ → ℂ} (hF : ∀ w, HasDerivAt F (f w) w)
    (hf : Continuous f) (hg : ∀ t, t ≠ 0 → g t = f t) (z : ℂ) (R : ℝ) :
    ∫ s in (0 : ℝ)..R, g (z + s) = F (z + R) - F z := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) R, HasDerivAt (fun s : ℝ => F (z + s)) (f (z + s)) s := by
    intro s _
    have h1 : HasDerivAt (fun w : ℂ => F (z + w)) (f (z + s)) (s : ℂ) := by
      have := (hF (z + s)).comp (s : ℂ) ((hasDerivAt_id (s : ℂ)).const_add z)
      simp only [Function.comp_def, mul_one] at this
      exact this
    exact h1.comp_ofReal
  have hc : Continuous fun s : ℝ => f (z + s) :=
    hf.comp (continuous_const.add continuous_ofReal)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 R)
  simp only [ofReal_zero, add_zero] at hftc
  rw [← hftc]
  refine intervalIntegral.integral_congr_ae ?_
  have hnull : volume ({-z.re} : Set ℝ) = 0 := measure_singleton _
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with s hs _
  refine hg _ fun h => hs ?_
  have := congrArg Complex.re h
  simp only [add_re, ofReal_re, zero_re] at this
  simp only [mem_singleton_iff]
  linarith

/-- **Vertical estimate**: if `F′ = f` on `ℜv > 0` with `|f(v)| ≤ e^{|ℑv|}/ℜv` and `F(x) → L` along
the real axis, then `F(w) → L` as `ℜw → ∞` with `ℑw` bounded. -/
theorem tendsto_of_vertical {F f : ℂ → ℂ} {L : ℂ}
    (hF : ∀ v : ℂ, 0 < v.re → HasDerivAt F (f v) v)
    (hf : ∀ v : ℂ, 0 < v.re → ‖f v‖ ≤ Real.exp |v.im| / v.re)
    (hreal : Tendsto (fun x : ℝ => F x) atTop (𝓝 L))
    {α : Type*} {l : Filter α} {w : α → ℂ} (hre : Tendsto (fun x => (w x).re) l atTop)
    (him : ∃ C, ∀ᶠ x in l, |(w x).im| ≤ C) :
    Tendsto (fun x => F (w x)) l (𝓝 L) := by
  obtain ⟨C, hC⟩ := him
  have hsmall : Tendsto (fun x => F (w x) - F ((w x).re : ℂ)) l (𝓝 0) := by
    have hb : Tendsto (fun x => Real.exp C * C / (w x).re) l (𝓝 0) :=
      tendsto_const_nhds.div_atTop hre
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hC, hre.eventually (eventually_gt_atTop 0)] with x hx ha
    set a := (w x).re
    set c := |(w x).im|
    have hc0 : 0 ≤ c := abs_nonneg _
    set S : Set ℂ := {v | a ≤ v.re} ∩ {v | v.im ≤ c} ∩ {v | -c ≤ v.im}
    have hS : Convex ℝ S :=
      ((convex_halfSpace_re_ge a).inter (convex_halfSpace_im_le c)).inter
        (convex_halfSpace_im_ge (-c))
    have hd : ∀ v ∈ S, HasDerivWithinAt F (f v) S v :=
      fun v hv => (hF v (ha.trans_le hv.1.1)).hasDerivWithinAt
    have hbound : ∀ v ∈ S, ‖f v‖ ≤ Real.exp c / a := by
      intro v hv
      have hv1 : a ≤ v.re := hv.1.1
      have hv2 : |v.im| ≤ c := abs_le.mpr ⟨hv.2, hv.1.2⟩
      exact (hf v (ha.trans_le hv1)).trans
        (div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr hv2) ha hv1)
    have hmem1 : (a : ℂ) ∈ S := ⟨⟨by simp, by simp [hc0]⟩, by simp [hc0]⟩
    have hmem2 : w x ∈ S :=
      ⟨⟨show a ≤ (w x).re from le_rfl, show (w x).im ≤ c from le_abs_self _⟩,
        show -c ≤ (w x).im from neg_abs_le _⟩
    have h := hS.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound hmem1 hmem2
    have hdiff : w x - (a : ℂ) = ((w x).im : ℂ) * I := by
      apply Complex.ext <;> simp [a]
    rw [hdiff, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs] at h
    refine h.trans ?_
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right
      (mul_le_mul (Real.exp_le_exp.mpr hx) hx hc0 (Real.exp_pos _).le) ha.le
  have h2 := hreal.comp hre
  simpa using hsmall.add h2

theorem norm_sin_le_exp_abs_im (v : ℂ) : ‖Complex.sin v‖ ≤ Real.exp |v.im| := by
  rw [Complex.sin, norm_div, norm_mul, norm_I, mul_one, RCLike.norm_ofNat]
  have h1 : ‖cexp (-v * I)‖ ≤ Real.exp |v.im| := by
    rw [norm_exp]
    exact Real.exp_le_exp.mpr (by simp [le_abs_self])
  have h2 : ‖cexp (v * I)‖ ≤ Real.exp |v.im| := by
    rw [norm_exp]
    exact Real.exp_le_exp.mpr (by simpa using neg_le_abs v.im)
  have := norm_sub_le (cexp (-v * I)) (cexp (v * I))
  linarith

theorem norm_cos_le_exp_abs_im (v : ℂ) : ‖Complex.cos v‖ ≤ Real.exp |v.im| := by
  rw [Complex.cos, norm_div, RCLike.norm_ofNat]
  have h1 : ‖cexp (v * I)‖ ≤ Real.exp |v.im| := by
    rw [norm_exp]
    exact Real.exp_le_exp.mpr (by simpa using neg_le_abs v.im)
  have h2 : ‖cexp (-v * I)‖ ≤ Real.exp |v.im| := by
    rw [norm_exp]
    exact Real.exp_le_exp.mpr (by simp [le_abs_self])
  have := norm_add_le (cexp (v * I)) (cexp (-v * I))
  linarith

/-- The ray bound `|E₁(z)| ≤ e^{−ℜz}/max(|ℑz|, ℜz)` off the cut. -/
theorem norm_expIntE₁_le {z : ℂ} (hz : z ∈ slitPlane) :
    ‖expIntE₁ z‖ ≤ Real.exp (-z.re) / max |z.im| z.re := by
  set m := max |z.im| z.re
  have hm : 0 < m := max_abs_im_re_pos hz
  have hexp : IntegrableOn (fun s : ℝ => Real.exp (-z.re) / m * Real.exp (-s)) (Ioi 0) := by
    have h1 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
      simpa using exp_neg_integrableOn_Ioi 0 one_pos
    exact h1.const_mul _
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi 0))
    (f := fun s : ℝ => cexp (-(z + s)) / (z + s)) hexp
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun s (hs : (0 : ℝ) < s) => by
      have hle := le_norm_add_ofReal (z := z) hs.le
      rw [norm_div, norm_exp]
      simp only [neg_re, add_re, ofReal_re]
      rw [show -(z.re + s) = -z.re + -s by ring, Real.exp_add, div_mul_eq_mul_div]
      exact div_le_div₀ (by positivity) le_rfl hm hle))
  rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one] at h
  exact h

/-- `E₁(±ix) → 0` as `x → ∞`. -/
theorem tendsto_expIntE₁_I_mul (σ : ℂ) (hσ : σ = I ∨ σ = -I) :
    Tendsto (fun x : ℝ => expIntE₁ (σ * x)) atTop (𝓝 0) := by
  have hb : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_gt_atTop 0] with x hx
  have him : |(σ * x).im| = x := by
    rcases hσ with rfl | rfl <;> simp [abs_of_pos hx]
  have hre : (σ * x).re = 0 := by rcases hσ with rfl | rfl <;> simp
  have hz : σ * x ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr (by
    intro h; rw [h, abs_zero] at him; linarith))
  have := norm_expIntE₁_le hz
  rwa [him, hre, neg_zero, Real.exp_zero, max_eq_left hx.le] at this

/-- `Ein(σx) = E₁(σx) + ln x + (π/2)·(σ/i)·i + γ`: `ln(±ix) = ln x ± πi/2`. -/
theorem ein_I_mul {x : ℝ} (hx : 0 < x) :
    ein (I * x) = expIntE₁ (I * x) + Real.log x + π / 2 * I + γ ∧
      ein (-I * x) = expIntE₁ (-I * x) + Real.log x - π / 2 * I + γ := by
  have h1 : I * x ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr (by simp [hx.ne']))
  have h2 : -I * x ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr (by simp [hx.ne']))
  have hl1 : log (I * x) = Real.log x + π / 2 * I := by
    rw [mul_comm, log_ofReal_mul hx I_ne_zero, log_I]
  have hl2 : log (-I * x) = Real.log x - π / 2 * I := by
    rw [mul_comm, log_ofReal_mul hx (neg_ne_zero.mpr I_ne_zero), log_neg_I]
    ring
  constructor
  · rw [dlmf_6_2_4 h1, hl1]; ring
  · rw [dlmf_6_2_4 h2, hl2]; ring

theorem hasDerivAt_ein (w : ℂ) : HasDerivAt ein (BZ.EinDeriv w) w := by
  rw [ein_eq_fun]
  exact BZ.hasDerivAt_Ein w

theorem hasDerivAt_ein_mul (c w : ℂ) :
    HasDerivAt (fun w => ein (c * w)) (BZ.EinDeriv (c * w) * c) w := by
  have := (hasDerivAt_ein (c * w)).comp w ((hasDerivAt_id w).const_mul c)
  simp only [Function.comp_def, mul_one] at this
  exact this

theorem continuous_EinDeriv_mul (c : ℂ) : Continuous fun t => BZ.EinDeriv (c * t) :=
  continuous_EinDeriv.comp (continuous_const.mul continuous_id)

theorem I_mul_ne_zero {t : ℂ} (ht : t ≠ 0) : I * t ≠ 0 := mul_ne_zero I_ne_zero ht

theorem neg_I_mul_ne_zero {t : ℂ} (ht : t ≠ 0) : -I * t ≠ 0 :=
  mul_ne_zero (neg_ne_zero.mpr I_ne_zero) ht

/-! ### 6.2.9, 6.2.10: the sine integrals -/

/-- The entire continuation of `sin t / t` (`1` at `0`), the integrand of 6.2.9. -/
noncomputable def sincC (t : ℂ) : ℂ := (BZ.EinDeriv (I * t) + BZ.EinDeriv (-I * t)) / 2

/-- The closed form `(Ein(iz) − Ein(−iz))/(2i)` of `Si`. -/
noncomputable def SiF (z : ℂ) : ℂ := (ein (I * z) - ein (-I * z)) / (2 * I)

theorem continuous_sincC : Continuous sincC :=
  ((continuous_EinDeriv_mul I).add (continuous_EinDeriv_mul (-I))).div_const 2

theorem sincC_of_ne {t : ℂ} (ht : t ≠ 0) : sincC t = Complex.sin t / t := by
  rw [sincC, EinDeriv_of_ne (I_mul_ne_zero ht), EinDeriv_of_ne (neg_I_mul_ne_zero ht),
    Complex.sin]
  field_simp
  ring_nf
  rw [I_sq]
  ring_nf

theorem hasDerivAt_SiF (w : ℂ) : HasDerivAt SiF (sincC w) w := by
  have h := ((hasDerivAt_ein_mul I w).sub (hasDerivAt_ein_mul (-I) w)).div_const (2 * I)
  refine h.congr_deriv ?_
  rw [sincC]
  field_simp
  ring

/-- **DLMF 6.2.9**: the sine integral `Si(z) = ∫_0^z sin t/t dt`, along the segment `t = zs`. -/
noncomputable def Si (z : ℂ) : ℂ := ∫ s in (0 : ℝ)..1, Complex.sin (z * s) / (z * s) * z

theorem Si_eq (z : ℂ) : Si z = SiF z := by
  rw [Si, segment_eq_sub hasDerivAt_SiF continuous_sincC (fun t ht => (sincC_of_ne ht).symm)]
  simp [SiF]

theorem Si_eq_fun : Si = SiF := funext Si_eq

/-- **DLMF §6.2(ii)**: `Si` is entire. -/
theorem dlmf_6_2_9_entire : Differentiable ℂ Si := by
  rw [Si_eq_fun]
  exact fun w => (hasDerivAt_SiF w).differentiableAt

/-- **DLMF §6.2(ii)**: `Si` is odd. -/
theorem dlmf_6_2_9_odd (z : ℂ) : Si (-z) = -Si z := by
  rw [Si_eq, Si_eq, SiF, SiF, show I * -z = -I * z by ring, show -I * -z = I * z by ring]
  ring

/-- **DLMF 6.2.9** along any contour (integrand `sincC`, the entire `sin t / t`). -/
theorem dlmf_6_2_9_contour {c : ℝ → ℂ} {a b : ℝ} (hc : IsContour c a b) :
    contourIntegral sincC c a b = Si (c b) - Si (c a) := by
  rw [Si_eq_fun]
  exact contourIntegral_eq_sub_of_hasDerivAt (U := univ) hc (fun _ _ => mem_univ _)
    (fun w _ => hasDerivAt_SiF w) continuous_sincC.continuousOn

theorem norm_sincC_le {v : ℂ} (hv : 0 < v.re) : ‖sincC v‖ ≤ Real.exp |v.im| / v.re := by
  have hv0 : v ≠ 0 := fun h => by simp [h] at hv
  rw [sincC_of_ne hv0, norm_div]
  exact div_le_div₀ (Real.exp_pos _).le (norm_sin_le_exp_abs_im v) hv (re_le_norm v)

/-- `Si(x) = π/2 + (E₁(ix) − E₁(−ix))/(2i)` for `x > 0`. -/
theorem SiF_ofReal {x : ℝ} (hx : 0 < x) :
    SiF x = π / 2 + (expIntE₁ (I * x) - expIntE₁ (-I * x)) / (2 * I) := by
  obtain ⟨h1, h2⟩ := ein_I_mul hx
  rw [SiF, h1, h2]
  field_simp
  ring

theorem tendsto_SiF_atTop : Tendsto (fun x : ℝ => SiF x) atTop (𝓝 (π / 2)) := by
  have h := ((tendsto_expIntE₁_I_mul I (Or.inl rfl)).sub
    (tendsto_expIntE₁_I_mul (-I) (Or.inr rfl))).div_const (2 * I)
  have h2 := h.const_add ((π : ℂ) / 2)
  rw [sub_zero, zero_div, add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [SiF_ofReal hx]

/-- `Si(w) → π/2` as `ℜw → ∞` with `ℑw` bounded. -/
theorem tendsto_Si {α : Type*} {l : Filter α} {w : α → ℂ}
    (hre : Tendsto (fun x => (w x).re) l atTop) (him : ∃ C, ∀ᶠ x in l, |(w x).im| ≤ C) :
    Tendsto (fun x => Si (w x)) l (𝓝 (π / 2)) := by
  rw [Si_eq_fun]
  exact tendsto_of_vertical (fun v _ => hasDerivAt_SiF v) (fun v hv => norm_sincC_le hv)
    tendsto_SiF_atTop hre him

/-- **DLMF 6.2.10** (first form): `si(z) = −∫_z^∞ sin t/t dt`, along the horizontal ray `t = z + s`
(an improper integral: the limit of `∫_0^R` as `R → ∞`). -/
noncomputable def si (z : ℂ) : ℂ :=
  -limUnder atTop (fun R : ℝ => ∫ s in (0 : ℝ)..R, Complex.sin (z + s) / (z + s))

/-- **DLMF 6.2.10**: the improper integral `∫_z^∞ sin t/t dt` converges for every `z`, and
`si(z) = Si(z) − π/2`. -/
theorem dlmf_6_2_10 (z : ℂ) :
    Tendsto (fun R : ℝ => ∫ s in (0 : ℝ)..R, Complex.sin (z + s) / (z + s)) atTop
        (𝓝 (π / 2 - Si z)) ∧ si z = Si z - π / 2 := by
  have h : Tendsto (fun R : ℝ => ∫ s in (0 : ℝ)..R, Complex.sin (z + s) / (z + s)) atTop
      (𝓝 (π / 2 - Si z)) := by
    have h1 := (tendsto_Si (w := fun R : ℝ => z + R) (by
      simpa using tendsto_atTop_add_const_left _ z.re tendsto_id)
      ⟨|z.im|, Eventually.of_forall fun R => by simp⟩).sub_const (Si z)
    refine h1.congr fun R => ?_
    rw [Si_eq_fun, integral_shift_eq_sub hasDerivAt_SiF continuous_sincC
      (fun t ht => (sincC_of_ne ht).symm)]
  refine ⟨h, ?_⟩
  rw [si, h.limUnder_eq]
  ring

/-- **DLMF 6.2.10** along a contour: for any contour from `z` going to infinity with `ℜt → ∞`
and `ℑt` bounded, `∫_z^∞ sin t/t dt = −si(z)`. -/
theorem dlmf_6_2_10_contour {z : ℂ} {c : ℝ → ℂ} {a : ℝ} (hca : c a = z)
    (hc : ∀ b, a ≤ b → IsContour c a b) (hre : Tendsto (fun t => (c t).re) atTop atTop)
    (him : ∃ C, ∀ᶠ t in atTop, |(c t).im| ≤ C) :
    ContourConvergesAtTop sincC c a (-si z) := by
  have h := (tendsto_Si hre him).sub_const (Si z)
  rw [show (π : ℂ) / 2 - Si z = -si z by rw [(dlmf_6_2_10 z).2]; ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop a] with b hb
  rw [dlmf_6_2_9_contour (hc b hb), hca]

/-! ### 6.2.12: `Cin` -/

/-- The entire continuation of `(1 − cos t)/t` (`0` at `0`), the integrand of 6.2.12. -/
noncomputable def cinC (t : ℂ) : ℂ := (BZ.EinDeriv (I * t) - BZ.EinDeriv (-I * t)) * I / 2

/-- The closed form `(Ein(iz) + Ein(−iz))/2` of `Cin`. -/
noncomputable def CinF (z : ℂ) : ℂ := (ein (I * z) + ein (-I * z)) / 2

theorem continuous_cinC : Continuous cinC :=
  (((continuous_EinDeriv_mul I).sub (continuous_EinDeriv_mul (-I))).mul
    continuous_const).div_const 2

theorem cinC_of_ne {t : ℂ} (ht : t ≠ 0) : cinC t = (1 - Complex.cos t) / t := by
  rw [cinC, EinDeriv_of_ne (I_mul_ne_zero ht), EinDeriv_of_ne (neg_I_mul_ne_zero ht),
    Complex.cos]
  field_simp
  ring_nf

theorem hasDerivAt_CinF (w : ℂ) : HasDerivAt CinF (cinC w) w := by
  have h := ((hasDerivAt_ein_mul I w).add (hasDerivAt_ein_mul (-I) w)).div_const 2
  refine h.congr_deriv ?_
  rw [cinC]
  ring

/-- **DLMF 6.2.12**: `Cin(z) = ∫_0^z (1 − cos t)/t dt`, along the segment `t = zs`. -/
noncomputable def Cin (z : ℂ) : ℂ := ∫ s in (0 : ℝ)..1, (1 - Complex.cos (z * s)) / (z * s) * z

theorem Cin_eq (z : ℂ) : Cin z = CinF z := by
  rw [Cin, segment_eq_sub hasDerivAt_CinF continuous_cinC (fun t ht => (cinC_of_ne ht).symm)]
  simp [CinF, ein_eq, BZ.Ein_zero]

theorem Cin_eq_fun : Cin = CinF := funext Cin_eq

/-- **DLMF §6.2(ii)**: `Cin` is entire. -/
theorem dlmf_6_2_12_entire : Differentiable ℂ Cin := by
  rw [Cin_eq_fun]
  exact fun w => (hasDerivAt_CinF w).differentiableAt

/-- **DLMF §6.2(ii)**: `Cin` is even. -/
theorem dlmf_6_2_12_even (z : ℂ) : Cin (-z) = Cin z := by
  rw [Cin_eq, Cin_eq, CinF, CinF, show I * -z = -I * z by ring, show -I * -z = I * z by ring]
  ring

/-- **DLMF 6.2.12** along any contour (integrand `cinC`, the entire `(1 − cos t)/t`). -/
theorem dlmf_6_2_12_contour {c : ℝ → ℂ} {a b : ℝ} (hc : IsContour c a b) :
    contourIntegral cinC c a b = Cin (c b) - Cin (c a) := by
  rw [Cin_eq_fun]
  exact contourIntegral_eq_sub_of_hasDerivAt (U := univ) hc (fun _ _ => mem_univ _)
    (fun w _ => hasDerivAt_CinF w) continuous_cinC.continuousOn

/-! ### 6.2.11, 6.2.13: `Ci` -/

/-- The right side `−Cin z + ln z + γ` of 6.2.13. -/
noncomputable def CiG (z : ℂ) : ℂ := -Cin z + log z + γ

theorem hasDerivAt_CiG {w : ℂ} (hw : w ∈ slitPlane) :
    HasDerivAt CiG (Complex.cos w / w) w := by
  have hw0 := slitPlane_ne_zero hw
  have h := (((dlmf_6_2_12_entire w).hasDerivAt).neg.add (hasDerivAt_log hw)).add_const (γ : ℂ)
  refine h.congr_deriv ?_
  rw [Cin_eq_fun, (hasDerivAt_CinF w).deriv, cinC_of_ne hw0]
  field_simp
  ring

theorem CiG_ofReal {x : ℝ} (hx : 0 < x) :
    CiG x = -(expIntE₁ (I * x) + expIntE₁ (-I * x)) / 2 := by
  obtain ⟨h1, h2⟩ := ein_I_mul hx
  rw [CiG, Cin_eq, CinF, h1, h2, ← ofReal_log hx.le]
  ring

theorem tendsto_CiG_atTop : Tendsto (fun x : ℝ => CiG x) atTop (𝓝 0) := by
  have h := (((tendsto_expIntE₁_I_mul I (Or.inl rfl)).add
    (tendsto_expIntE₁_I_mul (-I) (Or.inr rfl))).neg).div_const 2
  rw [add_zero, neg_zero, zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [CiG_ofReal hx]

theorem norm_cos_div_le {v : ℂ} (hv : 0 < v.re) :
    ‖Complex.cos v / v‖ ≤ Real.exp |v.im| / v.re := by
  rw [norm_div]
  exact div_le_div₀ (Real.exp_pos _).le (norm_cos_le_exp_abs_im v) hv (re_le_norm v)

theorem mem_slitPlane_of_re_pos {v : ℂ} (hv : 0 < v.re) : v ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl hv)

/-- `−Cin(w) + ln w + γ → 0` as `ℜw → ∞` with `ℑw` bounded. -/
theorem tendsto_CiG {α : Type*} {l : Filter α} {w : α → ℂ}
    (hre : Tendsto (fun x => (w x).re) l atTop) (him : ∃ C, ∀ᶠ x in l, |(w x).im| ≤ C) :
    Tendsto (fun x => CiG (w x)) l (𝓝 0) :=
  tendsto_of_vertical (fun _ hv => hasDerivAt_CiG (mem_slitPlane_of_re_pos hv))
    (fun _ hv => norm_cos_div_le hv) tendsto_CiG_atTop hre him

/-- **DLMF 6.2.11**: the principal value `Ci(z) = −∫_z^∞ cos t/t dt`, along the horizontal ray
`t = z + s` (an improper integral; off the cut `(−∞, 0]` this path neither crosses the negative
real axis nor passes through the origin, and other such paths give the same value:
`dlmf_6_2_11`). -/
noncomputable def Ci (z : ℂ) : ℂ :=
  -limUnder atTop (fun R : ℝ => ∫ s in (0 : ℝ)..R, Complex.cos (z + s) / (z + s))

theorem integral_cos_div_ray {z : ℂ} (hz : z ∈ slitPlane) {R : ℝ} (hR : 0 ≤ R) :
    ∫ s in (0 : ℝ)..R, Complex.cos (z + s) / (z + s) = CiG (z + R) - CiG z := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) R, HasDerivAt (fun s : ℝ => CiG (z + s))
      (Complex.cos (z + s) / (z + s)) s := by
    intro s hs
    rw [uIcc_of_le hR] at hs
    have hw := add_ofReal_mem_slitPlane hz hs.1
    have h1 : HasDerivAt (fun v : ℂ => CiG (z + v)) (Complex.cos (z + s) / (z + s)) (s : ℂ) := by
      have := (hasDerivAt_CiG hw).comp (s : ℂ) ((hasDerivAt_id (s : ℂ)).const_add z)
      simp only [Function.comp_def, mul_one] at this
      exact this
    exact h1.comp_ofReal
  have hcont : ContinuousOn (fun s : ℝ => Complex.cos (z + s) / (z + s)) (uIcc 0 R) := by
    intro s hs
    rw [uIcc_of_le hR] at hs
    have hne := slitPlane_ne_zero (add_ofReal_mem_slitPlane hz hs.1)
    exact ((Complex.continuous_cos.comp (continuous_const.add continuous_ofReal)).continuousAt.div
      (continuous_const.add continuous_ofReal).continuousAt hne).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
  simp

/-- **DLMF 6.2.11** on the ray and **6.2.13**: for `z` off the cut the improper integral
`∫_z^∞ cos t/t dt` converges to `−Ci(z)`, and `Ci(z) = −Cin(z) + ln z + γ`. -/
theorem dlmf_6_2_13 {z : ℂ} (hz : z ∈ slitPlane) :
    Tendsto (fun R : ℝ => ∫ s in (0 : ℝ)..R, Complex.cos (z + s) / (z + s)) atTop
        (𝓝 (-CiG z)) ∧ Ci z = -Cin z + log z + γ := by
  have h : Tendsto (fun R : ℝ => ∫ s in (0 : ℝ)..R, Complex.cos (z + s) / (z + s)) atTop
      (𝓝 (-CiG z)) := by
    have h1 := (tendsto_CiG (w := fun R : ℝ => z + R) (by
      simpa using tendsto_atTop_add_const_left _ z.re tendsto_id)
      ⟨|z.im|, Eventually.of_forall fun R => by simp⟩).sub_const (CiG z)
    rw [zero_sub] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with R hR
    exact (integral_cos_div_ray hz hR).symm
  refine ⟨h, ?_⟩
  rw [Ci, h.limUnder_eq, neg_neg, CiG]

/-- **DLMF 6.2.11**, path independence: along any contour from `z` off the cut `(−∞, 0]` going
to infinity with `ℜt → ∞` and `ℑt` bounded, `∫_z^∞ cos t/t dt = −Ci(z)`. -/
theorem dlmf_6_2_11 {z : ℂ} {c : ℝ → ℂ} {a : ℝ} (hca : c a = z)
    (hc : ∀ b, a ≤ b → IsContour c a b) (hcU : ∀ t, a ≤ t → c t ∈ slitPlane)
    (hre : Tendsto (fun t => (c t).re) atTop atTop)
    (him : ∃ C, ∀ᶠ t in atTop, |(c t).im| ≤ C) :
    ContourConvergesAtTop (fun t => Complex.cos t / t) c a (-Ci z) := by
  have hz : z ∈ slitPlane := hca ▸ hcU a le_rfl
  have hf : ContinuousOn (fun w : ℂ => Complex.cos w / w) slitPlane := fun w hw =>
    (Complex.continuous_cos.continuousAt.div continuousAt_id
      (slitPlane_ne_zero hw)).continuousWithinAt
  have h := (tendsto_CiG hre him).sub_const (CiG z)
  rw [zero_sub, show -CiG z = -Ci z by rw [(dlmf_6_2_13 hz).2, CiG] ] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop a] with b hb
  rw [contourIntegral_eq_sub_of_hasDerivAt (hc b hb) (fun t ht => hcU t ht.1)
    (fun w hw => hasDerivAt_CiG hw) hf, hca]

/-- **DLMF §6.2(ii)**: on the cut, `Ci` has the two boundary values
`Ci(x ± i0) = −Cin(x) + ln|x| ± πi + γ`, `x < 0` (compare 6.2.1). -/
theorem dlmf_6_2_11_cut {x : ℝ} (hx : x < 0) :
    Tendsto Ci (𝓝[{z | 0 < z.im}] (x : ℂ)) (𝓝 (-Cin x + (Real.log (-x) + π * I) + γ)) ∧
      Tendsto Ci (𝓝[{z | z.im < 0}] (x : ℂ)) (𝓝 (-Cin x + (Real.log (-x) - π * I) + γ)) := by
  have hnorm : ‖(x : ℂ)‖ = -x := by rw [norm_real, Real.norm_eq_abs, abs_of_neg hx]
  have hcin : Tendsto Cin (𝓝 (x : ℂ)) (𝓝 (Cin x)) := (dlmf_6_2_12_entire x).continuousAt.tendsto
  have hre : (x : ℂ).re < 0 := by simpa using hx
  have him : (x : ℂ).im = 0 := ofReal_im x
  constructor
  · have hlog := (tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hre him).mono_left
      (nhdsWithin_mono _ fun z (hz : 0 < z.im) => le_of_lt hz)
    rw [hnorm] at hlog
    refine (((hcin.mono_left nhdsWithin_le_nhds).neg.add hlog).add_const (γ : ℂ)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z (hz : 0 < z.im)
    rw [(dlmf_6_2_13 (mem_slitPlane_iff.mpr (Or.inr hz.ne'))).2]
  · have hlog := tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him
    rw [hnorm] at hlog
    refine (((hcin.mono_left nhdsWithin_le_nhds).neg.add hlog).add_const (γ : ℂ)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z (hz : z.im < 0)
    rw [(dlmf_6_2_13 (mem_slitPlane_iff.mpr (Or.inr hz.ne))).2]

/-- **DLMF 6.2.14**: `Si(x) → π/2` and `Ci(x) → 0` as `x → ∞`. -/
theorem dlmf_6_2_14 :
    Tendsto (fun x : ℝ => Si x) atTop (𝓝 (π / 2)) ∧
      Tendsto (fun x : ℝ => Ci x) atTop (𝓝 0) := by
  refine ⟨by rw [Si_eq_fun]; exact tendsto_SiF_atTop, tendsto_CiG_atTop.congr' ?_⟩
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [(dlmf_6_2_13 (mem_slitPlane_of_re_pos (by simpa using hx))).2, CiG]

/-! ### 6.2.15, 6.2.16: the hyperbolic analogs -/

theorem hasDerivAt_ein_neg (w : ℂ) :
    HasDerivAt (fun w => ein (-w)) (BZ.EinDeriv (-w) * (-1)) w := by
  have := (hasDerivAt_ein (-w)).comp w (hasDerivAt_neg w)
  simp only [Function.comp_def] at this
  exact this

theorem continuous_EinDeriv_neg : Continuous fun t => BZ.EinDeriv (-t) :=
  continuous_EinDeriv.comp continuous_neg

/-- The entire continuation of `sinh t / t` (`1` at `0`), the integrand of 6.2.15. -/
noncomputable def shiC (t : ℂ) : ℂ := (BZ.EinDeriv t + BZ.EinDeriv (-t)) / 2

/-- The closed form `(Ein(z) − Ein(−z))/2` of `Shi`. -/
noncomputable def ShiF (z : ℂ) : ℂ := (ein z - ein (-z)) / 2

theorem continuous_shiC : Continuous shiC :=
  (continuous_EinDeriv.add continuous_EinDeriv_neg).div_const 2

theorem shiC_of_ne {t : ℂ} (ht : t ≠ 0) : shiC t = Complex.sinh t / t := by
  rw [shiC, EinDeriv_of_ne ht, EinDeriv_of_ne (neg_ne_zero.mpr ht), Complex.sinh]
  field_simp
  ring_nf

theorem hasDerivAt_ShiF (w : ℂ) : HasDerivAt ShiF (shiC w) w := by
  have h := ((hasDerivAt_ein w).sub (hasDerivAt_ein_neg w)).div_const 2
  refine h.congr_deriv ?_
  rw [shiC]
  ring

/-- **DLMF 6.2.15**: `Shi(z) = ∫_0^z sinh t/t dt`, along the segment `t = zs`. -/
noncomputable def Shi (z : ℂ) : ℂ := ∫ s in (0 : ℝ)..1, Complex.sinh (z * s) / (z * s) * z

theorem Shi_eq (z : ℂ) : Shi z = ShiF z := by
  rw [Shi, segment_eq_sub hasDerivAt_ShiF continuous_shiC (fun t ht => (shiC_of_ne ht).symm)]
  simp [ShiF]

/-- `Shi` is entire (`Shi(z) = (Ein(z) − Ein(−z))/2`). -/
theorem dlmf_6_2_15_entire : Differentiable ℂ Shi := by
  rw [funext Shi_eq]
  exact fun w => (hasDerivAt_ShiF w).differentiableAt

/-- **DLMF 6.2.15** along any contour (integrand `shiC`, the entire `sinh t / t`). -/
theorem dlmf_6_2_15_contour {c : ℝ → ℂ} {a b : ℝ} (hc : IsContour c a b) :
    contourIntegral shiC c a b = Shi (c b) - Shi (c a) := by
  rw [funext Shi_eq]
  exact contourIntegral_eq_sub_of_hasDerivAt (U := univ) hc (fun _ _ => mem_univ _)
    (fun w _ => hasDerivAt_ShiF w) continuous_shiC.continuousOn

/-- The entire continuation of `(cosh t − 1)/t` (`0` at `0`), the integrand of 6.2.16. -/
noncomputable def chiC (t : ℂ) : ℂ := -(BZ.EinDeriv t - BZ.EinDeriv (-t)) / 2

/-- The closed form `−(Ein(z) + Ein(−z))/2` of `∫_0^z (cosh t − 1)/t dt`. -/
noncomputable def chiIntF (z : ℂ) : ℂ := -(ein z + ein (-z)) / 2

theorem continuous_chiC : Continuous chiC :=
  ((continuous_EinDeriv.sub continuous_EinDeriv_neg).neg).div_const 2

theorem chiC_of_ne {t : ℂ} (ht : t ≠ 0) : chiC t = (Complex.cosh t - 1) / t := by
  rw [chiC, EinDeriv_of_ne ht, EinDeriv_of_ne (neg_ne_zero.mpr ht), Complex.cosh]
  field_simp
  ring_nf

theorem hasDerivAt_chiIntF (w : ℂ) : HasDerivAt chiIntF (chiC w) w := by
  have h := (((hasDerivAt_ein w).add (hasDerivAt_ein_neg w)).neg).div_const 2
  refine h.congr_deriv ?_
  rw [chiC]
  ring

/-- The integral `∫_0^z (cosh t − 1)/t dt` of 6.2.16, along the segment `t = zs`. -/
noncomputable def chiInt (z : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..1, (Complex.cosh (z * s) - 1) / (z * s) * z

theorem chiInt_eq (z : ℂ) : chiInt z = chiIntF z := by
  rw [chiInt, segment_eq_sub hasDerivAt_chiIntF continuous_chiC
    (fun t ht => (chiC_of_ne ht).symm)]
  simp [chiIntF, ein_eq, BZ.Ein_zero]

/-- **DLMF 6.2.16**: `Chi(z) = γ + ln z + ∫_0^z (cosh t − 1)/t dt` (principal branch of `ln`). -/
noncomputable def Chi (z : ℂ) : ℂ := γ + log z + chiInt z

/-- The integral in 6.2.16 is entire. -/
theorem dlmf_6_2_16_entire : Differentiable ℂ chiInt := by
  rw [funext chiInt_eq]
  exact fun w => (hasDerivAt_chiIntF w).differentiableAt

/-- `Chi′(z) = cosh z / z` off the cut. -/
theorem dlmf_6_2_16_deriv {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt Chi (Complex.cosh z / z) z := by
  have hz0 := slitPlane_ne_zero hz
  have h := ((hasDerivAt_log hz).const_add (γ : ℂ)).add (dlmf_6_2_16_entire z).hasDerivAt
  refine h.congr_deriv ?_
  rw [funext chiInt_eq, (hasDerivAt_chiIntF z).deriv, chiC_of_ne hz0]
  field_simp
  ring

end Azurite.DLMF
