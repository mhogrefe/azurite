/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.Exercises
import Azurite.DLMF.Chapter1.Section4
import Azurite.DLMF.Chapter1.Section9Integration
import Azurite.DLMF.Chapter2.Section5LaplaceExampleExpansion
import Azurite.DLMF.Chapter4.Section10
import Azurite.DLMF.Chapter5.Section9PsiEuler

/-!
# DLMF §6.2(i): exponential and logarithmic integrals

Formalizations of <https://dlmf.nist.gov/6.2.i>, equations 6.2.1–6.2.8.

* 6.2.1: `expIntE₁ z`, the integral of `e^{−t}/t` along the horizontal ray from `z`;
  `dlmf_6_2_1` (any contour from `z` to `∞` off the cut `(−∞, 0]`, going to infinity inside a
  sector `|ℑt| ≤ C ℜt`), by the contour FTC `contourIntegral_eq_sub_of_hasDerivAt` and the
  decay `tendsto_E1Ein_zero`; `dlmf_6_2_1_cut`, `dlmf_6_2_1_cut_ne` (the two boundary values
  `Ein(x) − ln|x| ∓ πi − γ` on the cut).
* 6.2.2: `dlmf_6_2_2` (`t ↦ z + t`).
* 6.2.3: `ein z`, the segment integral; equal to the Brent–Zimmermann power series `BZ.Ein`
  (`ein_eq`), entire (`dlmf_6_2_3_entire`), path independent (`dlmf_6_2_3_contour`).
* 6.2.4: `dlmf_6_2_4`, `E₁ = Ein − ln − γ` off the cut: on the real axis from the third form of
  5.9.18 (`integral_exp_neg_div_Ioi`), in the plane by FTC along the ray and the vertical mean
  value estimate `norm_E1Ein_sub_re_le`.
* 6.2.5–6.2.7: `Ei` (principal value `⨍_{−∞}^x e^t/t dt` for `x > 0`, ordinary integral for
  `x < 0`), `HasPrincipalValueIic`, `HasPrincipalValueIoi`; `dlmf_6_2_5`, `dlmf_6_2_6`,
  `dlmf_6_2_7`.
* 6.2.8: `dlmf_6_2_8` (`⨍_0^x dt/ln t = li x = Ei(ln x)`, `x > 1`, with §4.10's `li`, via the
  primitive `Ei(ln t)` of `1/ln t` and `ln(1 − ε)/ln(1 + ε) → −1`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Interval

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-! ### The real tail `∫_x^∞ e^{−t}/t dt` -/

/-- `t ↦ e^{−t}/t` is integrable on `(x, ∞)` for `x > 0`. -/
theorem integrableOn_exp_neg_div_Ioi {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioi x) := by
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t) / x) (Ioi x) := by
    have h1 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi x) := by
      simpa using exp_neg_integrableOn_Ioi x one_pos
    exact (h1.mul_const x⁻¹).congr (ae_of_all _ fun t => by simp [div_eq_mul_inv])
  refine hexp.mono' ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
  · exact ContinuousOn.aestronglyMeasurable (fun t ht => (((Real.continuous_exp.comp
      continuous_neg).continuousAt).div continuousAt_id
      (show id t ≠ 0 from ne_of_gt (hx.trans ht))).continuousWithinAt) measurableSet_Ioi
  · have ht' : x < t := ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos (hx.trans ht')]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hx ht'.le

/-- The real form `Ein x − ln x − γ` of the right side of 6.2.4. -/
noncomputable def expIntE₁R (x : ℝ) : ℝ := BZ.EinR x - Real.log x - γ

theorem hasDerivAt_expIntE₁R {x : ℝ} (hx : 0 < x) :
    HasDerivAt expIntE₁R (-(Real.exp (-x) / x)) x := by
  have h := ((BZ.hasDerivAt_EinR_of_ne hx.ne').sub (Real.hasDerivAt_log hx.ne')).sub_const γ
  refine h.congr_deriv ?_
  field_simp
  ring

/-- `∫_x^R e^{−t}/t dt = (Ein x − ln x − γ) − (Ein R − ln R − γ)` for `0 < x ≤ R`. -/
theorem integral_exp_neg_div_eq {x R : ℝ} (hx : 0 < x) (hxR : x ≤ R) :
    ∫ t in x..R, Real.exp (-t) / t = expIntE₁R x - expIntE₁R R := by
  have hd : ∀ t ∈ uIcc x R, HasDerivAt (fun t => -expIntE₁R t) (Real.exp (-t) / t) t := by
    intro t ht
    rw [uIcc_of_le hxR] at ht
    have h := (hasDerivAt_expIntE₁R (hx.trans_le ht.1)).neg
    rwa [neg_neg] at h
  have hc : ContinuousOn (fun t : ℝ => Real.exp (-t) / t) (uIcc x R) := by
    intro t ht
    rw [uIcc_of_le hxR] at ht
    exact (((Real.continuous_exp.comp continuous_neg).continuousAt).div continuousAt_id
      (show id t ≠ 0 from ne_of_gt (hx.trans_le ht.1))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  ring

theorem tendsto_expIntE₁R_aux {x : ℝ} (hx : 0 < x) :
    Tendsto expIntE₁R atTop
      (𝓝 (expIntE₁R x - ∫ t in Ioi x, Real.exp (-t) / t)) := by
  have h := intervalIntegral_tendsto_integral_Ioi x (integrableOn_exp_neg_div_Ioi hx) tendsto_id
  have h2 : Tendsto (fun R => expIntE₁R x - ∫ t in x..R, Real.exp (-t) / t) atTop
      (𝓝 (expIntE₁R x - ∫ t in Ioi x, Real.exp (-t) / t)) := tendsto_const_nhds.sub h
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop x] with R hR
  rw [integral_exp_neg_div_eq hx hR]
  ring

/-- `Ein x − ln x − γ → 0` as `x → ∞`: the limit exists by the previous lemma, and at `x = 1` it
is `Ein 1 − γ − ∫_1^∞ e^{−t}/t dt = 0` by the third form of 5.9.18. -/
theorem tendsto_expIntE₁R_atTop : Tendsto expIntE₁R atTop (𝓝 0) := by
  have h := tendsto_expIntE₁R_aux one_pos
  have h1 : expIntE₁R 1 - ∫ t in Ioi (1 : ℝ), Real.exp (-t) / t = 0 := by
    have hγ := dlmf_5_9_18_3
    rw [← BZ.EinR_eq_integral zero_le_one] at hγ
    simp only [expIntE₁R, Real.log_one]
    linarith
  rwa [h1] at h

/-- **The real case of 6.2.4**: `∫_x^∞ e^{−t}/t dt = Ein x − ln x − γ` for `x > 0`. -/
theorem integral_exp_neg_div_Ioi {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi x, Real.exp (-t) / t = expIntE₁R x := by
  have h := tendsto_nhds_unique (tendsto_expIntE₁R_aux hx) tendsto_expIntE₁R_atTop
  linarith

/-! ### A fundamental theorem of calculus for contours -/

/-- **Path independence**: if `F′ = f` on a set `U` containing a contour `c` (§1.9(iii)) and `f`
is continuous on `U`, then `∫_c f(z) dz = F(c(b)) − F(c(a))`. -/
theorem contourIntegral_eq_sub_of_hasDerivAt {F f : ℂ → ℂ} {U : Set ℂ} {c : ℝ → ℂ} {a b : ℝ}
    (hc : IsContour c a b) (hcU : ∀ t ∈ Icc a b, c t ∈ U)
    (hF : ∀ w ∈ U, HasDerivAt F (f w) w) (hf : ContinuousOn f U) :
    contourIntegral f c a b = F (c b) - F (c a) := by
  obtain ⟨n, t, g, hlt, h0, hn, hg, heq⟩ := hc
  have ha : ∀ i, i ≤ n → a ≤ t i := by
    intro i
    induction i with
    | zero => intro _; simp [h0]
    | succ k ih => intro hk; exact (ih (by omega)).trans (hlt k (by omega)).le
  have hb : ∀ i, i ≤ n → t i ≤ b := by
    have h : ∀ k, k ≤ n → t (n - k) ≤ b := by
      intro k
      induction k with
      | zero => intro _; simp [hn]
      | succ k ih =>
        intro hk
        have h1 := hlt (n - (k + 1)) (by omega)
        rw [show n - (k + 1) + 1 = n - k by omega] at h1
        exact h1.le.trans (ih (by omega))
    intro i hi
    have h1 := h (n - i) (by omega)
    rwa [show n - (n - i) = i by omega] at h1
  have piece : ∀ i < n,
      IntervalIntegrable (fun s => f (c s) * deriv c s) volume (t i) (t (i + 1)) ∧
        ∫ s in t i..t (i + 1), f (c s) * deriv c s = F (c (t (i + 1))) - F (c (t i)) := by
    intro i hi
    have hle := (hlt i hi).le
    have hsub : Icc (t i) (t (i + 1)) ⊆ Icc a b := Icc_subset_Icc (ha i hi.le) (hb (i + 1) hi)
    have hgU : ∀ s ∈ Icc (t i) (t (i + 1)), g i s ∈ U := fun s hs => by
      rw [← heq i hi hs]
      exact hcU s (hsub hs)
    have hgd : ∀ s, HasDerivAt (g i) (deriv (g i) s) s :=
      fun s => (((hg i hi).differentiable (by norm_num)) s).hasDerivAt
    have hcont : ContinuousOn (fun s => f (g i s) * deriv (g i) s) (uIcc (t i) (t (i + 1))) := by
      rw [uIcc_of_le hle]
      exact (hf.comp (hg i hi).continuous.continuousOn fun s hs => hgU s hs).mul
        ((hg i hi).continuous_deriv le_rfl).continuousOn
    have hint := hcont.intervalIntegrable (μ := volume)
    have hftc : ∫ s in t i..t (i + 1), f (g i s) * deriv (g i) s
        = F (g i (t (i + 1))) - F (g i (t i)) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => by
        rw [uIcc_of_le hle] at hs
        exact (hF _ (hgU s hs)).comp s (hgd s)) hint
    have hae : ∀ᵐ s ∂volume, s ∈ Ι (t i) (t (i + 1)) →
        f (c s) * deriv c s = f (g i s) * deriv (g i) s := by
      have hnull : volume ({t (i + 1)} : Set ℝ) = 0 := measure_singleton _
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with s hs hsI
      rw [uIoc_of_le hle] at hsI
      have hs' : s ∈ Ioo (t i) (t (i + 1)) :=
        ⟨hsI.1, lt_of_le_of_ne hsI.2 (by simpa using hs)⟩
      have hev : c =ᶠ[𝓝 s] g i := by
        filter_upwards [Ioo_mem_nhds hs'.1 hs'.2] with r hr
        exact heq i hi (Ioo_subset_Icc_self hr)
      rw [hev.deriv_eq, heq i hi (Ioo_subset_Icc_self hs')]
    refine ⟨?_, ?_⟩
    · rw [intervalIntegrable_iff] at hint ⊢
      exact hint.congr_fun_ae
        (((ae_restrict_iff' measurableSet_uIoc).mpr hae).mono fun s h => h.symm)
    · rw [intervalIntegral.integral_congr_ae hae, hftc, ← heq i hi (right_mem_Icc.mpr hle),
        ← heq i hi (left_mem_Icc.mpr hle)]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (fun k hk => (piece k hk).1)
  rw [h0, hn] at hsum
  rw [contourIntegral, ← hsum,
    Finset.sum_congr rfl fun k hk => (piece k (Finset.mem_range.mp hk)).2]
  exact (Finset.sum_range_sub (fun k => F (c (t k))) n).trans (by rw [h0, hn])

/-! ### 6.2.3: the complementary exponential integral -/

/-- **DLMF 6.2.3**: `Ein(z) = ∫_0^z (1 − e^{−t})/t dt`, along the segment `t = zs`, `0 ≤ s ≤ 1`
(any other path gives the same value: `dlmf_6_2_3_contour`). -/
noncomputable def ein (z : ℂ) : ℂ := ∫ s in (0 : ℝ)..1, (1 - cexp (-(z * s))) / (z * s) * z

theorem differentiable_BZEin : Differentiable ℂ BZ.Ein :=
  fun z => (BZ.hasDerivAt_Ein z).differentiableAt

theorem continuous_EinDeriv : Continuous BZ.EinDeriv := by
  have h : deriv BZ.Ein = BZ.EinDeriv := funext fun z => (BZ.hasDerivAt_Ein z).deriv
  rw [← h]
  exact (differentiable_BZEin.contDiff (n := 1)).continuous_deriv le_rfl

/-- The segment integral 6.2.3 is the power series `∑_{n≥1} (−1)^{n−1} zⁿ/(n! n)` of the
Brent–Zimmermann exercises (FTC for `s ↦ Ein(zs)`). -/
theorem ein_eq (z : ℂ) : ein z = BZ.Ein z := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => BZ.Ein (z * s)) (BZ.EinDeriv (z * s) * z) s := by
    intro s _
    have h1 : HasDerivAt (fun w : ℂ => BZ.Ein (z * w)) (BZ.EinDeriv (z * s) * z) (s : ℂ) := by
      have := (BZ.hasDerivAt_Ein (z * s)).comp (s : ℂ) ((hasDerivAt_id (s : ℂ)).const_mul z)
      simp only [Function.comp_def, mul_one] at this
      exact this
    exact h1.comp_ofReal
  have hc : Continuous fun s : ℝ => BZ.EinDeriv (z * s) * z :=
    (continuous_EinDeriv.comp (continuous_const.mul continuous_ofReal)).mul continuous_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 1)
  simp only [ofReal_one, mul_one, ofReal_zero, mul_zero, BZ.Ein_zero, sub_zero] at hftc
  rw [ein, ← hftc]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
  rw [uIoc_of_le zero_le_one] at hs
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · have hzs : z * s ≠ 0 := mul_ne_zero hz (ofReal_ne_zero.mpr hs.1.ne')
    simp [BZ.EinDeriv, hzs]

theorem ein_eq_fun : ein = BZ.Ein := funext ein_eq

/-- **DLMF §6.2(i)**: `Ein` is entire. -/
theorem dlmf_6_2_3_entire : Differentiable ℂ ein := by
  rw [ein_eq_fun]
  exact differentiable_BZEin

/-- **DLMF 6.2.3** along any contour: `∫_c (1 − e^{−t})/t dt = Ein(c(b)) − Ein(c(a))`, the
integrand taken as its entire continuation (`1` at `t = 0`, `BZ.EinDeriv`). -/
theorem dlmf_6_2_3_contour {c : ℝ → ℂ} {a b : ℝ} (hc : IsContour c a b) :
    contourIntegral BZ.EinDeriv c a b = ein (c b) - ein (c a) := by
  rw [ein_eq_fun]
  exact contourIntegral_eq_sub_of_hasDerivAt (U := univ) hc (fun _ _ => mem_univ _)
    (fun w _ => BZ.hasDerivAt_Ein w) continuous_EinDeriv.continuousOn

/-- The entire integrand of 6.2.3 is `(1 − e^{−t})/t` away from `t = 0`. -/
theorem EinDeriv_of_ne {t : ℂ} (ht : t ≠ 0) : BZ.EinDeriv t = (1 - cexp (-t)) / t := by
  simp [BZ.EinDeriv, ht]

/-- At a real point `ein` is the real `Ein`. -/
theorem ein_ofReal (x : ℝ) : ein x = (BZ.EinR x : ℂ) := by
  rw [ein_eq, BZ.Ein_ofReal]

/-! ### 6.2.1, 6.2.2, 6.2.4: the exponential integral `E₁` -/

/-- **DLMF 6.2.1**: the principal value of `E₁(z) = ∫_z^∞ e^{−t}/t dt`, along the horizontal
ray `t = z + s`, `s ≥ 0`.  For `z` off the cut `(−∞, 0]` this path neither crosses the negative
real axis nor passes through the origin; every other such path gives the same value
(`dlmf_6_2_1`).  On the cut the value is a junk value: the principal value is two-valued there
(`dlmf_6_2_1_cut`). -/
noncomputable def expIntE₁ (z : ℂ) : ℂ := ∫ s in Ioi (0 : ℝ), cexp (-(z + s)) / (z + s)

theorem add_ofReal_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) {s : ℝ} (hs : 0 ≤ s) :
    z + s ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
  rcases hz with h | h
  · left; linarith
  · right; exact h

theorem le_norm_add_ofReal {z : ℂ} {s : ℝ} (hs : 0 ≤ s) :
    max |z.im| z.re ≤ ‖z + s‖ := by
  refine max_le ?_ ?_
  · have := abs_im_le_norm (z + s)
    simpa using this
  · have := re_le_norm (z + s)
    simp only [add_re, ofReal_re] at this
    linarith

theorem max_abs_im_re_pos {z : ℂ} (hz : z ∈ slitPlane) : 0 < max |z.im| z.re := by
  rw [mem_slitPlane_iff] at hz
  rcases hz with h | h
  · exact lt_max_of_lt_right h
  · exact lt_max_of_lt_left (abs_pos.mpr h)

/-- The integrand of 6.2.1 on the ray is integrable for `z` off the cut. -/
theorem integrableOn_expIntE₁ {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun s : ℝ => cexp (-(z + s)) / (z + s)) (Ioi 0) := by
  set m := max |z.im| z.re
  have hm : 0 < m := max_abs_im_re_pos hz
  have hexp : IntegrableOn (fun s : ℝ => Real.exp (-z.re) / m * Real.exp (-s)) (Ioi 0) := by
    have h1 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
      simpa using exp_neg_integrableOn_Ioi 0 one_pos
    exact h1.const_mul _
  refine hexp.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun s hs => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun s hs => ?_) measurableSet_Ioi
    have hne : z + s ≠ 0 := slitPlane_ne_zero (add_ofReal_mem_slitPlane hz (le_of_lt hs))
    exact (((continuous_const.add continuous_ofReal).neg.cexp).continuousAt.div
      (continuous_const.add continuous_ofReal).continuousAt hne).continuousWithinAt
  · have hs' : (0 : ℝ) ≤ s := le_of_lt hs
    have hle := le_norm_add_ofReal (z := z) hs'
    rw [norm_div, norm_exp]
    simp only [neg_re, add_re, ofReal_re]
    rw [show -(z.re + s) = -z.re + -s by ring, Real.exp_add, div_mul_eq_mul_div]
    exact div_le_div₀ (by positivity) le_rfl hm hle

/-- At a positive real point the Brent–Zimmermann `E₁ = −γ − Log z + Ein z` is the real
`Ein x − ln x − γ`. -/
theorem E1Ein_ofReal {r : ℝ} (hr : 0 < r) : BZ.E1Ein r = (expIntE₁R r : ℂ) := by
  rw [BZ.E1Ein, BZ.Ein_ofReal, expIntE₁R, ← ofReal_log hr.le]
  push_cast
  ring

/-- The vertical estimate `|E₁(w) − E₁(ℜw)| ≤ |ℑw| e^{−ℜw}/ℜw` for `ℜw > 0` (mean value bound on
the half-plane `ℜv ≥ ℜw`, where `|E₁′(v)| = e^{−ℜv}/|v| ≤ e^{−ℜw}/ℜw`). -/
theorem norm_E1Ein_sub_re_le {w : ℂ} (hw : 0 < w.re) :
    ‖BZ.E1Ein w - BZ.E1Ein w.re‖ ≤ Real.exp (-w.re) / w.re * |w.im| := by
  set s : Set ℂ := {v | w.re ≤ v.re}
  have hs : Convex ℝ s := convex_halfSpace_re_ge w.re
  have hmem : ∀ v ∈ s, v ∈ slitPlane := fun v hv => by
    rw [mem_slitPlane_iff]
    left
    exact hw.trans_le hv
  have hf : ∀ v ∈ s, HasDerivWithinAt BZ.E1Ein (-cexp (-v) / v) s v :=
    fun v hv => (BZ.hasDerivAt_E1Ein (hmem v hv)).hasDerivWithinAt
  have hbound : ∀ v ∈ s, ‖-cexp (-v) / v‖ ≤ Real.exp (-w.re) / w.re := by
    intro v hv
    have hv' : w.re ≤ v.re := hv
    rw [norm_div, norm_neg, norm_exp, neg_re]
    exact div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by linarith)) hw
      (hv'.trans (re_le_norm v))
  have h := hs.norm_image_sub_le_of_norm_hasDerivWithin_le hf hbound
    (show (w.re : ℂ) ∈ s by simp [s]) (show w ∈ s by simp [s])
  have hdiff : w - (w.re : ℂ) = (w.im : ℂ) * I := by
    apply Complex.ext <;> simp
  rwa [hdiff, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs] at h

/-- `E₁(w) → 0` as `ℜw → ∞` inside a sector `|ℑw| ≤ C ℜw`. -/
theorem tendsto_E1Ein_zero {α : Type*} {l : Filter α} {w : α → ℂ}
    (hre : Tendsto (fun x => (w x).re) l atTop) (him : ∃ C, ∀ᶠ x in l, |(w x).im| ≤ C * (w x).re) :
    Tendsto (fun x => BZ.E1Ein (w x)) l (𝓝 0) := by
  obtain ⟨C, hC⟩ := him
  have hb : Tendsto (fun x => C * Real.exp (-(w x).re) + |expIntE₁R (w x).re|) l (𝓝 0) := by
    have h1 := (tendsto_const_nhds (x := C)).mul (Real.tendsto_exp_neg_atTop_nhds_zero.comp hre)
    have h2 := (tendsto_expIntE₁R_atTop.comp hre).abs
    simpa using h1.add h2
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [hC, hre.eventually (eventually_gt_atTop 0)] with x hx hpos
  have h1 := norm_E1Ein_sub_re_le hpos
  rw [E1Ein_ofReal hpos] at h1
  have h2 : Real.exp (-(w x).re) / (w x).re * |(w x).im| ≤ C * Real.exp (-(w x).re) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith [Real.exp_pos (-(w x).re)]
  calc ‖BZ.E1Ein (w x)‖
      ≤ ‖BZ.E1Ein (w x) - (expIntE₁R (w x).re : ℂ)‖ + ‖(expIntE₁R (w x).re : ℂ)‖ :=
        norm_le_norm_sub_add _ _
    _ ≤ C * Real.exp (-(w x).re) + |expIntE₁R (w x).re| := by
        rw [norm_real, Real.norm_eq_abs]
        linarith

/-- `E₁` along the ray equals `−γ − Log z + Ein z` off the cut: FTC on `[0, R]` and
`E₁(z + R) → 0`. -/
theorem expIntE₁_eq_E1Ein {z : ℂ} (hz : z ∈ slitPlane) : expIntE₁ z = BZ.E1Ein z := by
  have hint := integrableOn_expIntE₁ hz
  have hftc : ∀ R : ℝ, 0 ≤ R →
      ∫ s in (0 : ℝ)..R, cexp (-(z + s)) / (z + s) = BZ.E1Ein z - BZ.E1Ein (z + R) := by
    intro R hR
    have hd : ∀ s ∈ uIcc (0 : ℝ) R, HasDerivAt (fun s : ℝ => -BZ.E1Ein (z + s))
        (cexp (-(z + s)) / (z + s)) s := by
      intro s hs
      rw [uIcc_of_le hR] at hs
      have hw := add_ofReal_mem_slitPlane hz hs.1
      have h1 : HasDerivAt (fun v : ℂ => -BZ.E1Ein (z + v)) (cexp (-(z + s)) / (z + s))
          (s : ℂ) := by
        have := ((BZ.hasDerivAt_E1Ein hw).comp (s : ℂ)
          ((hasDerivAt_id (s : ℂ)).const_add z)).neg
        simp only [Function.comp_def, mul_one, neg_div, neg_neg] at this
        exact this
      exact h1.comp_ofReal
    have hcont : ContinuousOn (fun s : ℝ => cexp (-(z + s)) / (z + s)) (uIcc 0 R) := by
      intro s hs
      rw [uIcc_of_le hR] at hs
      have hne := slitPlane_ne_zero (add_ofReal_mem_slitPlane hz hs.1)
      exact (((continuous_const.add continuous_ofReal).neg.cexp).continuousAt.div
        (continuous_const.add continuous_ofReal).continuousAt hne).continuousWithinAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
    simp only [ofReal_zero, add_zero]
    ring
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have hlim2 : Tendsto (fun R : ℝ => BZ.E1Ein z - BZ.E1Ein (z + R)) atTop
      (𝓝 (BZ.E1Ein z - 0)) := by
    refine tendsto_const_nhds.sub (tendsto_E1Ein_zero ?_ ⟨1, ?_⟩)
    · simp only [add_re, ofReal_re]
      exact tendsto_atTop_add_const_left _ _ tendsto_id
    · filter_upwards [eventually_ge_atTop (|z.im| - z.re)] with R hR
      simp only [add_im, ofReal_im, add_zero, add_re, ofReal_re, one_mul]
      linarith
  rw [sub_zero] at hlim2
  refine tendsto_nhds_unique hlim (hlim2.congr' ?_)
  filter_upwards [eventually_ge_atTop 0] with R hR
  exact (hftc R hR).symm

/-- **DLMF 6.2.4**: `E₁(z) = Ein(z) − ln z − γ` (principal values, `z` off the cut). -/
theorem dlmf_6_2_4 {z : ℂ} (hz : z ∈ slitPlane) : expIntE₁ z = ein z - log z - γ := by
  rw [expIntE₁_eq_E1Ein hz, BZ.E1Ein, ein_eq]
  ring

/-- **DLMF 6.2.2**: `E₁(z) = e^{−z} ∫_0^∞ e^{−t}/(t + z) dt`, `|ph z| < π` (the substitution
`t ↦ z + t` of the ray integral 6.2.1). -/
theorem dlmf_6_2_2 {z : ℂ} (hz0 : z ≠ 0) (hz : |z.arg| < π) :
    expIntE₁ z = cexp (-z) * ∫ t in Ioi (0 : ℝ), cexp (-t) / (t + z) := by
  have _h : z ∈ slitPlane := by
    rw [mem_slitPlane_iff_arg]
    exact ⟨fun h => by rw [h, abs_of_pos Real.pi_pos] at hz; exact lt_irrefl _ hz, hz0⟩
  rw [expIntE₁, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [neg_add, Complex.exp_add, add_comm (t : ℂ) z]
  ring

/-- **DLMF 6.2.1**, path independence: along any contour `c` from `c(a) = z` to `∞` that stays off
the cut `(−∞, 0]` and goes to infinity inside a sector `|ℑt| ≤ C ℜt`, `ℜt → +∞` (where `e^{−t}`
decays), the infinite contour integral `∫_z^∞ e^{−t}/t dt` converges to `E₁(z)`. -/
theorem dlmf_6_2_1 {z : ℂ} {c : ℝ → ℂ} {a : ℝ} (hca : c a = z)
    (hc : ∀ b, a ≤ b → IsContour c a b) (hcU : ∀ t, a ≤ t → c t ∈ slitPlane)
    (hre : Tendsto (fun t => (c t).re) atTop atTop)
    (him : ∃ C, ∀ᶠ t in atTop, |(c t).im| ≤ C * (c t).re) :
    ContourConvergesAtTop (fun t => cexp (-t) / t) c a (expIntE₁ z) := by
  have hz : z ∈ slitPlane := hca ▸ hcU a le_rfl
  have hF : ∀ w ∈ slitPlane, HasDerivAt (fun v => -BZ.E1Ein v) (cexp (-w) / w) w := by
    intro w hw
    have := (BZ.hasDerivAt_E1Ein hw).neg
    rwa [neg_div, neg_neg] at this
  have hf : ContinuousOn (fun w : ℂ => cexp (-w) / w) slitPlane := fun w hw =>
    (continuous_neg.cexp.continuousAt.div continuousAt_id
      (slitPlane_ne_zero hw)).continuousWithinAt
  have hlim : Tendsto (fun b => BZ.E1Ein z - BZ.E1Ein (c b)) atTop (𝓝 (BZ.E1Ein z - 0)) :=
    tendsto_const_nhds.sub (tendsto_E1Ein_zero hre him)
  rw [sub_zero, ← expIntE₁_eq_E1Ein hz] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop a] with b hb
  rw [contourIntegral_eq_sub_of_hasDerivAt (hc b hb) (fun t ht => hcU t ht.1) hF hf, hca,
    expIntE₁_eq_E1Ein hz]
  ring

/-- **DLMF §6.2(i)**: on the cut, `E₁` has the two boundary values
`E₁(x ± i0) = Ein(x) − ln|x| ∓ πi − γ`, `x < 0` (from 6.2.4 and the boundary values of `ln`). -/
theorem dlmf_6_2_1_cut {x : ℝ} (hx : x < 0) :
    Tendsto expIntE₁ (𝓝[{z | 0 < z.im}] (x : ℂ))
        (𝓝 (ein x - (Real.log (-x) + π * I) - γ)) ∧
      Tendsto expIntE₁ (𝓝[{z | z.im < 0}] (x : ℂ))
        (𝓝 (ein x - (Real.log (-x) - π * I) - γ)) := by
  have hnorm : ‖(x : ℂ)‖ = -x := by rw [norm_real, Real.norm_eq_abs, abs_of_neg hx]
  have hein : Tendsto ein (𝓝 (x : ℂ)) (𝓝 (ein x)) := (dlmf_6_2_3_entire x).continuousAt.tendsto
  have hre : (x : ℂ).re < 0 := by simpa using hx
  have him : (x : ℂ).im = 0 := ofReal_im x
  constructor
  · have hlog := (tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hre him).mono_left
      (nhdsWithin_mono _ fun z (hz : 0 < z.im) => le_of_lt hz)
    rw [hnorm] at hlog
    refine (((hein.mono_left nhdsWithin_le_nhds).sub hlog).sub_const (γ : ℂ)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z (hz : 0 < z.im)
    rw [dlmf_6_2_4 (mem_slitPlane_iff.mpr (Or.inr hz.ne'))]
  · have hlog := tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him
    rw [hnorm] at hlog
    refine (((hein.mono_left nhdsWithin_le_nhds).sub hlog).sub_const (γ : ℂ)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z (hz : z.im < 0)
    rw [dlmf_6_2_4 (mem_slitPlane_iff.mpr (Or.inr hz.ne))]

/-- The two boundary values of `E₁` on the cut differ (by `2πi`), so the principal value is
two-valued on `(−∞, 0)`. -/
theorem dlmf_6_2_1_cut_ne {x : ℝ} (_hx : x < 0) :
    ein x - (Real.log (-x) + π * I) - γ ≠ ein x - (Real.log (-x) - π * I) - γ := by
  intro h
  have h2 : (2 * π : ℂ) * I = 0 := by linear_combination -h
  simp [Real.pi_ne_zero, I_ne_zero] at h2

/-- At a positive real point `E₁` is the real integral `∫_x^∞ e^{−t}/t dt`, i.e. §2.5's
`expIntegralE₁`. -/
theorem expIntE₁_ofReal {x : ℝ} (hx : 0 < x) :
    expIntE₁ x = ((∫ t in Ioi x, Real.exp (-t) / t : ℝ) : ℂ) := by
  rw [expIntE₁_eq_E1Ein (mem_slitPlane_iff.mpr (Or.inl (by simpa using hx))),
    E1Ein_ofReal hx, integral_exp_neg_div_Ioi hx]

theorem expIntE₁_eq_expIntegralE₁ {x : ℝ} (hx : 0 < x) :
    expIntE₁ x = (expIntegralE₁ x : ℂ) := by
  rw [expIntE₁_ofReal hx, expIntegralE₁]

/-! ### 6.2.5–6.2.7: the exponential integral `Ei` -/

/-- `⨍_{−∞}^b f(t) dt` with the singularity at `c < b` (DLMF 1.4.24 with an infinite lower
limit): `lim_{ε→0+} (∫_{−∞}^{c−ε} f + ∫_{c+ε}^b f) = L`. -/
def HasPrincipalValueIic (f : ℝ → ℝ) (c b L : ℝ) : Prop :=
  Tendsto (fun ε => (∫ t in Iic (c - ε), f t) + ∫ t in c + ε..b, f t) (𝓝[>] 0) (𝓝 L)

/-- `⨍_a^∞ f(t) dt` with the singularity at `c > a`:
`lim_{ε→0+} (∫_a^{c−ε} f + ∫_{c+ε}^∞ f) = L`. -/
def HasPrincipalValueIoi (f : ℝ → ℝ) (a c L : ℝ) : Prop :=
  Tendsto (fun ε => (∫ t in a..c - ε, f t) + ∫ t in Ioi (c + ε), f t) (𝓝[>] 0) (𝓝 L)

/-- **DLMF 6.2.5** (second form), with 6.2.6 for a negative argument: the exponential integral
`Ei(x) = ⨍_{−∞}^x e^t/t dt` for `x > 0` and `Ei(x) = ∫_{−∞}^x e^t/t dt` for `x < 0`.  (`Ei(0)` is
undefined in the DLMF; here it is a junk value.) -/
noncomputable def Ei (x : ℝ) : ℝ :=
  if 0 < x then
    limUnder (𝓝[>] (0 : ℝ))
      (fun ε => (∫ t in Iic (0 - ε), Real.exp t / t) + ∫ t in 0 + ε..x, Real.exp t / t)
  else ∫ t in Iic x, Real.exp t / t

/-- `∫_{−∞}^{−x} e^t/t dt = −∫_x^∞ e^{−t}/t dt = −(Ein x − ln x − γ)` for `x > 0`. -/
theorem integral_Iic_exp_div {x : ℝ} (hx : 0 < x) :
    ∫ t in Iic (-x), Real.exp t / t = -expIntE₁R x := by
  calc ∫ t in Iic (-x), Real.exp t / t
      = ∫ t in Iic (-x), (fun u => -(Real.exp (-u) / u)) (-t) := by
        congr 1
        funext t
        simp [div_neg]
    _ = ∫ u in Ioi (-(-x)), -(Real.exp (-u) / u) :=
        integral_comp_neg_Iic (-x) (fun u => -(Real.exp (-u) / u))
    _ = ∫ u in Ioi x, -(Real.exp (-u) / u) := by rw [neg_neg]
    _ = -∫ u in Ioi x, Real.exp (-u) / u := integral_neg _
    _ = -expIntE₁R x := by rw [integral_exp_neg_div_Ioi hx]

/-- `∫_a^b e^t/t dt = Ei(b) − Ei(a)` in the Brent–Zimmermann form `γ + ln|x| − Ein(−x)`, for
`0 < a ≤ b`. -/
theorem integral_exp_div_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, Real.exp t / t = BZ.EiEin b - BZ.EiEin a := by
  have hd : ∀ t ∈ uIcc a b, HasDerivAt BZ.EiEin (Real.exp t / t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact BZ.hasDerivAt_EiEin (ne_of_gt (ha.trans_le ht.1))
  have hc : ContinuousOn (fun t : ℝ => Real.exp t / t) (uIcc a b) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (Real.continuous_exp.continuousAt.div continuousAt_id
      (show id t ≠ 0 from ne_of_gt (ha.trans_le ht.1))).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)

theorem continuous_EinR : Continuous BZ.EinR :=
  continuous_iff_continuousAt.mpr fun x => (BZ.hasDerivAt_EinR x).continuousAt

/-- The principal value `⨍_{−∞}^x e^t/t dt` exists for `x > 0` and equals `γ + ln x − Ein(−x)`. -/
theorem hasPrincipalValueIic_exp_div {x : ℝ} (hx : 0 < x) :
    HasPrincipalValueIic (fun t => Real.exp t / t) 0 x (BZ.EiEin x) := by
  have hc : Tendsto (fun ε => BZ.EiEin x - BZ.EinR ε + BZ.EinR (-ε)) (𝓝 0)
      (𝓝 (BZ.EiEin x - BZ.EinR 0 + BZ.EinR (-0))) :=
    ((tendsto_const_nhds.sub (continuous_EinR.tendsto 0)).add
      ((continuous_EinR.comp continuous_neg).tendsto 0))
  rw [neg_zero, BZ.EinR_zero, sub_zero, add_zero] at hc
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hx] with ε hε
  simp only [zero_sub, zero_add]
  rw [integral_Iic_exp_div hε.1, integral_exp_div_eq hε.1 hε.2.le]
  simp only [expIntE₁R, BZ.EiEin]
  ring

theorem Ei_eq_EiEin {x : ℝ} (hx : 0 < x) : Ei x = BZ.EiEin x := by
  rw [Ei, ite_eq_left hx]
  exact (hasPrincipalValueIic_exp_div hx).limUnder_eq

theorem Ei_neg {x : ℝ} (hx : 0 < x) : Ei (-x) = -expIntE₁R x := by
  rw [Ei, ite_eq_right (by linarith), integral_Iic_exp_div hx]

/-- **DLMF 6.2.5**: for `x > 0`, `Ei(x) = −⨍_{−x}^∞ e^{−t}/t dt = ⨍_{−∞}^x e^t/t dt` (both
principal values exist). -/
theorem dlmf_6_2_5 {x : ℝ} (hx : 0 < x) :
    HasPrincipalValueIoi (fun t => Real.exp (-t) / t) (-x) 0 (-Ei x) ∧
      HasPrincipalValueIic (fun t => Real.exp t / t) 0 x (Ei x) := by
  have h := hasPrincipalValueIic_exp_div hx
  rw [← Ei_eq_EiEin hx] at h
  refine ⟨?_, h⟩
  refine h.neg.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hx] with ε hε
  simp only [zero_sub, zero_add]
  have hsub : ∫ t in -x..-ε, Real.exp (-t) / t = -∫ t in ε..x, Real.exp t / t := by
    calc ∫ t in -x..-ε, Real.exp (-t) / t
        = ∫ t in -x..-ε, (fun u => -(Real.exp u / u)) (-t) := by
          congr 1
          funext t
          simp [div_neg]
      _ = ∫ u in -(-ε)..-(-x), -(Real.exp u / u) :=
          intervalIntegral.integral_comp_neg (fun u => -(Real.exp u / u))
      _ = ∫ u in ε..x, -(Real.exp u / u) := by rw [neg_neg, neg_neg]
      _ = -∫ u in ε..x, Real.exp u / u := intervalIntegral.integral_neg
  rw [hsub, integral_Iic_exp_div hε.1, integral_exp_neg_div_Ioi hε.1]
  ring

/-- **DLMF 6.2.6**: for `x > 0`, `Ei(−x) = −∫_x^∞ e^{−t}/t dt = −E₁(x)`. -/
theorem dlmf_6_2_6 {x : ℝ} (hx : 0 < x) :
    Ei (-x) = -∫ t in Ioi x, Real.exp (-t) / t ∧ (Ei (-x) : ℂ) = -expIntE₁ x := by
  refine ⟨by rw [Ei_neg hx, integral_exp_neg_div_Ioi hx], ?_⟩
  rw [expIntE₁_ofReal hx, Ei_neg hx, integral_exp_neg_div_Ioi hx]
  push_cast
  ring

/-- **DLMF 6.2.7**: for `x > 0`, `Ei(±x) = −Ein(∓x) + ln x + γ`. -/
theorem dlmf_6_2_7 {x : ℝ} (hx : 0 < x) :
    (Ei x : ℂ) = -ein (-(x : ℂ)) + Real.log x + γ ∧
      (Ei (-x) : ℂ) = -ein (x : ℂ) + Real.log x + γ := by
  refine ⟨?_, ?_⟩
  · rw [Ei_eq_EiEin hx, ← ofReal_neg, ein_ofReal, BZ.EiEin]
    push_cast
    ring
  · rw [Ei_neg hx, ein_ofReal, expIntE₁R]
    push_cast
    ring

/-! ### 6.2.8: the logarithmic integral -/

/-- `Ei(u) → 0` as `u → −∞`. -/
theorem tendsto_EiEin_atBot : Tendsto BZ.EiEin atBot (𝓝 0) := by
  have h := (tendsto_expIntE₁R_atTop.comp tendsto_neg_atBot_atTop).neg
  rw [neg_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_lt_atBot 0] with u hu
  simp only [Function.comp, expIntE₁R, BZ.EiEin, Real.log_neg_eq_log]
  ring

theorem continuousWithinAt_Icc_zero {f : ℝ → ℝ} {b : ℝ}
    (h : Tendsto f (𝓝[>] 0) (𝓝 (f 0))) : ContinuousWithinAt f (Icc 0 b) 0 :=
  (continuousWithinAt_Ioi_iff_Ici.mp h).mono Icc_subset_Ici_self

/-- The primitive `Ei(ln t)` of `1/ln t`. -/
theorem hasDerivAt_EiEin_log {t : ℝ} (ht : 0 < t) (ht1 : t ≠ 1) :
    HasDerivAt (fun t => BZ.EiEin (Real.log t)) (1 / Real.log t) t := by
  have hl : Real.log t ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.mp h with h | h | h
    · exact ht.ne' h
    · exact ht1 h
    · linarith
  have := (BZ.hasDerivAt_EiEin hl).comp t (Real.hasDerivAt_log ht.ne')
  refine this.congr_deriv ?_
  rw [Real.exp_log ht]
  field_simp

theorem log_ne_zero_of_lt_one {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : Real.log t ≠ 0 :=
  (Real.log_neg ht ht1).ne

theorem log_ne_zero_of_one_lt {t : ℝ} (ht1 : 1 < t) : Real.log t ≠ 0 :=
  (Real.log_pos ht1).ne'

/-- `∫_0^b dt/ln t = Ei(ln b)` for `0 < b < 1`. -/
theorem integral_one_div_log_lt_one {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    ∫ t in (0 : ℝ)..b, 1 / Real.log t = BZ.EiEin (Real.log b) := by
  set F : ℝ → ℝ := fun t => if t = 0 then 0 else BZ.EiEin (Real.log t) with hF
  have hlim : Tendsto (fun t => BZ.EiEin (Real.log t)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_EiEin_atBot.comp Real.tendsto_log_nhdsGT_zero
  have hFeq : ∀ t, t ≠ 0 → F t = BZ.EiEin (Real.log t) := fun t ht => by simp [hF, ht]
  have hcont : ContinuousOn F (Icc 0 b) := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | htpos
    · refine continuousWithinAt_Icc_zero ?_
      rw [show F 0 = 0 by simp [hF] ]
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      exact (hFeq s hs.ne').symm
    · have hd := hasDerivAt_EiEin_log htpos (by linarith [ht.2])
      refine (hd.continuousAt.congr ?_).continuousWithinAt
      filter_upwards [lt_mem_nhds htpos] with s hs
      exact (hFeq s hs.ne').symm
  have hderiv : ∀ t ∈ Ioo 0 b, HasDerivAt F (1 / Real.log t) t := by
    intro t ht
    refine (hasDerivAt_EiEin_log ht.1 (by linarith [ht.2])).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds ht.1] with s hs
    exact hFeq s hs.ne'
  have hint : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Icc 0 b) := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | htpos
    · refine continuousWithinAt_Icc_zero ?_
      simp only [Real.log_zero, div_zero]
      have := tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero
      simpa [Function.comp_def] using this
    · exact (continuousAt_const.div (Real.continuousAt_log htpos.ne')
        (log_ne_zero_of_lt_one htpos (by linarith [ht.2]))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb.le hcont hderiv
    (hint.intervalIntegrable_of_Icc hb.le), hFeq b hb.ne', show F 0 = 0 by simp [hF], sub_zero]

/-- `∫_a^b dt/ln t = Ei(ln b) − Ei(ln a)` for `1 < a ≤ b`. -/
theorem integral_one_div_log_one_lt {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / Real.log t = BZ.EiEin (Real.log b) - BZ.EiEin (Real.log a) := by
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (fun t => BZ.EiEin (Real.log t)) (1 / Real.log t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact hasDerivAt_EiEin_log (by linarith [ht.1]) (by linarith [ht.1])
  have hc : ContinuousOn (fun t : ℝ => 1 / Real.log t) (uIcc a b) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (continuousAt_const.div (Real.continuousAt_log (by linarith [ht.1]))
      (log_ne_zero_of_one_lt (by linarith [ht.1]))).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable

/-- `ln(1 − ε)/ln(1 + ε) → −1` as `ε → 0+`. -/
theorem tendsto_log_one_sub_div_log_one_add :
    Tendsto (fun ε : ℝ => Real.log (1 - ε) / Real.log (1 + ε)) (𝓝[>] 0) (𝓝 (-1)) := by
  have hs := (Real.hasDerivAt_log one_ne_zero).tendsto_slope_zero
  simp only [Real.log_one, sub_zero, inv_one, smul_eq_mul] at hs
  have hA : Tendsto (fun ε : ℝ => ε⁻¹ * Real.log (1 + ε)) (𝓝[>] 0) (𝓝 1) :=
    hs.mono_left (nhdsWithin_mono _ fun t (ht : 0 < t) => ht.ne')
  have hneg : Tendsto (fun ε : ℝ => -ε) (𝓝[>] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun ε : ℝ => -ε) (𝓝 0) (𝓝 (-0)) := tendsto_id.neg
      rw [neg_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact neg_ne_zero.mpr ht.ne'
  have hB : Tendsto (fun ε : ℝ => ε⁻¹ * Real.log (1 - ε)) (𝓝[>] 0) (𝓝 (-1)) := by
    have := (hs.comp hneg).neg
    refine this.congr fun ε => ?_
    simp only [Function.comp, inv_neg, neg_mul, neg_neg, ← sub_eq_add_neg]
  have h := hB.div hA one_ne_zero
  rw [div_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact mul_div_mul_left _ _ (inv_ne_zero hε.ne')

/-- **DLMF 6.2.8**: for `x > 1` the principal value `li(x) = ⨍_0^x dt/ln t` exists and equals
`Ei(ln x)`.  (`li` is §4.10's closed form, which is this principal value by `dlmf_4_10_7`.) -/
theorem dlmf_6_2_8 {x : ℝ} (hx : 1 < x) :
    HasPrincipalValue (fun t => 1 / Real.log t) 0 x 1 (Ei (Real.log x)) ∧
      li x = Ei (Real.log x) := by
  have hpv : HasPrincipalValue (fun t => 1 / Real.log t) 0 x 1 (Ei (Real.log x)) := by
    rw [Ei_eq_EiEin (Real.log_pos hx)]
    -- `Ei(ln(1 − ε)) − Ei(ln(1 + ε)) → 0`
    have hl : Tendsto (fun ε : ℝ => Real.log (Real.log (1 - ε) / Real.log (1 + ε))) (𝓝[>] 0)
        (𝓝 0) := by
      have := ((Real.continuousAt_log (by norm_num : (-1 : ℝ) ≠ 0)).tendsto).comp
        tendsto_log_one_sub_div_log_one_add
      rwa [Real.log_neg_eq_log, Real.log_one] at this
    have hpm : ∀ s : ℝ, Tendsto (fun ε : ℝ => BZ.EinR (-Real.log (1 + s * ε))) (𝓝 0)
        (𝓝 0) := fun s => by
      have h1 : Tendsto (fun ε : ℝ => -Real.log (1 + s * ε)) (𝓝 0) (𝓝 (-Real.log (1 + s * 0))) :=
        ((Real.continuousAt_log (by norm_num)).tendsto.comp
          (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id))).neg
      simp only [mul_zero, add_zero, Real.log_one, neg_zero] at h1
      have := (continuous_EinR.tendsto 0).comp h1
      rwa [BZ.EinR_zero] at this
    have hsum := ((hl.add ((hpm 1).mono_left nhdsWithin_le_nhds)).sub
      ((hpm (-1)).mono_left nhdsWithin_le_nhds)).const_add (BZ.EiEin (Real.log x))
    simp only [add_zero, sub_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 (x - 1) from
      lt_min one_pos (by linarith))] with ε hε
    have hε1 : ε < 1 := hε.2.trans_le (min_le_left _ _)
    have hεx : ε < x - 1 := hε.2.trans_le (min_le_right _ _)
    have hm : Real.log (1 - ε) ≠ 0 := log_ne_zero_of_lt_one (by linarith) (by linarith [hε.1])
    have hp : Real.log (1 + ε) ≠ 0 := log_ne_zero_of_one_lt (by linarith [hε.1])
    rw [integral_one_div_log_lt_one (by linarith) (by linarith [hε.1]),
      integral_one_div_log_one_lt (by linarith [hε.1]) (by linarith), Real.log_div hm hp]
    simp only [BZ.EiEin, one_mul, neg_one_mul, ← sub_eq_add_neg]
    ring
  exact ⟨hpv, tendsto_nhds_unique (dlmf_4_10_7 hx) hpv⟩

end Azurite.DLMF
