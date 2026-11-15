/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section6

/-!
# DLMF §6.7(i): integral representations, exponential integrals

Formalizations of <https://dlmf.nist.gov/6.7.i>, equations 6.7.1–6.7.8.

Toolkit: `E₁′ = −e^{−w}/w` (`hasDerivAt_expIntE₁`), FTC along a line `t ↦ αt + β` off the cut
(`integral_lineE1`), decay of `E₁` (`tendsto_expIntE₁_zero`, along horizontal and vertical
lines), hence improper integrals of `e^{−αt}α/(αt + β)` (`tendsto_integral_of_lineE1`):
`∫_x^∞ e^{it}/(t ± ia)` and `∫_x^∞ e^{−t}/(t + c)`.  Partial fractions in `1/(a² + t²)` give 6.7.3–6.7.6.  Conditionally
convergent integrals (the second of 6.7.1, and 6.7.4) are stated as limits of `∫_x^R`.

* 6.7.1: `dlmf_6_7_1`; 6.7.2: `dlmf_6_7_2` (FTC with `Ei((1 − t)x)`); 6.7.3: `dlmf_6_7_3`;
  6.7.4: `dlmf_6_7_4`; 6.7.5: `dlmf_6_7_5`; 6.7.6: `dlmf_6_7_6`.
* 6.7.7, 6.7.8: `dlmf_6_7_7`, `dlmf_6_7_8` (imaginary/real parts of `Ein`'s segment integral,
  `ein_eq_integral_EinDeriv`).
* "Many integrals … `∫ e^z R(z) dz` … in finite form" (Lebedev): a pointer, not formalized.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Interval

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-! ### `E₁` along straight lines -/

/-- `E₁′(w) = −e^{−w}/w` off the cut. -/
theorem hasDerivAt_expIntE₁ {w : ℂ} (hw : w ∈ slitPlane) :
    HasDerivAt expIntE₁ (-cexp (-w) / w) w := by
  refine (BZ.hasDerivAt_E1Ein hw).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_slitPlane.mem_nhds hw] with v hv
  exact expIntE₁_eq_E1Ein hv

/-- The integrand of `E₁` along the line `t ↦ αt + β`. -/
noncomputable def lineE1 (α β : ℂ) (t : ℝ) : ℂ := -cexp (-(α * t + β)) / (α * t + β) * α

/-- FTC along a line off the cut: `∫_x^R (E₁(αt + β))′ dt = E₁(αR + β) − E₁(αx + β)`. -/
theorem integral_lineE1 (α β : ℂ) {x R : ℝ} (hxR : x ≤ R)
    (h : ∀ t ∈ Icc x R, α * t + β ∈ slitPlane) :
    ∫ t in x..R, lineE1 α β t = expIntE₁ (α * R + β) - expIntE₁ (α * x + β) := by
  have hd : ∀ t ∈ uIcc x R, HasDerivAt (fun t : ℝ => expIntE₁ (α * t + β)) (lineE1 α β t) t := by
    intro t ht
    rw [uIcc_of_le hxR] at ht
    have h1 : HasDerivAt (fun v : ℂ => expIntE₁ (α * v + β)) (lineE1 α β t) (t : ℂ) := by
      have := (hasDerivAt_expIntE₁ (h t ht)).comp (t : ℂ)
        (((hasDerivAt_id (t : ℂ)).const_mul α).add_const β)
      simp only [Function.comp_def, id, mul_one] at this
      exact this
    exact h1.comp_ofReal
  have hc : ContinuousOn (lineE1 α β) (uIcc x R) := by
    intro t ht
    rw [uIcc_of_le hxR] at ht
    have hne := slitPlane_ne_zero (h t ht)
    have hl : Continuous fun t : ℝ => α * t + β :=
      (continuous_const.mul continuous_ofReal).add continuous_const
    exact (((hl.neg.cexp).continuousAt.neg.div hl.continuousAt hne).mul
      continuousAt_const).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable

/-- `E₁(w) → 0` when `ℜw` stays bounded below and `max(|ℑw|, ℜw) → ∞` (off the cut). -/
theorem tendsto_expIntE₁_zero {α : Type*} {l : Filter α} {w : α → ℂ}
    (hs : ∀ᶠ x in l, w x ∈ slitPlane) {r₀ : ℝ} (hre : ∀ᶠ x in l, r₀ ≤ (w x).re)
    (hm : Tendsto (fun x => max |(w x).im| (w x).re) l atTop) :
    Tendsto (fun x => expIntE₁ (w x)) l (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_const_nhds.div_atTop hm :
    Tendsto (fun x => Real.exp (-r₀) / max |(w x).im| (w x).re) l (𝓝 0))
  filter_upwards [hs, hre, hm.eventually (eventually_gt_atTop 0)] with x hx hr hpos
  exact (norm_expIntE₁_le hx).trans
    (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hpos.le)

/-- The improper integral along a line: `∫_x^∞ (E₁(αt + β))′ dt = −E₁(αx + β)`. -/
theorem tendsto_integral_lineE1 (α β : ℂ) (x : ℝ)
    (h : ∀ t : ℝ, x ≤ t → α * t + β ∈ slitPlane)
    (hlim : Tendsto (fun R : ℝ => expIntE₁ (α * R + β)) atTop (𝓝 0)) :
    Tendsto (fun R => ∫ t in x..R, lineE1 α β t) atTop (𝓝 (-expIntE₁ (α * x + β))) := by
  have h2 := hlim.sub_const (expIntE₁ (α * x + β))
  rw [zero_sub] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop x] with R hR
  exact (integral_lineE1 α β hR fun t ht => h t ht.1).symm

/-- `E₁(αR + β) → 0` for `α > 0` real. -/
theorem tendsto_expIntE₁_pos_line {k : ℝ} (hk : 0 < k) (β : ℂ) :
    Tendsto (fun R : ℝ => expIntE₁ ((k : ℂ) * R + β)) atTop (𝓝 0) := by
  have hre : Tendsto (fun R : ℝ => (((k : ℂ) * R + β)).re) atTop atTop := by
    simp only [add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hk)
  refine tendsto_expIntE₁_zero (hre.eventually (eventually_gt_atTop 0) |>.mono
    fun R hR => mem_slitPlane_of_re_pos hR) (r₀ := 0)
    (hre.eventually (eventually_ge_atTop 0)) ?_
  exact tendsto_atTop_mono (fun R => le_max_right _ _) hre

/-- `E₁(u − ikR) → 0` for `k > 0` real (a vertical line). -/
theorem tendsto_expIntE₁_vertical_line {k : ℝ} (hk : 0 < k) (u : ℂ) :
    Tendsto (fun R : ℝ => expIntE₁ (-I * k * R + u)) atTop (𝓝 0) := by
  have e : ∀ R : ℝ, (-I * k * R + u).im = -(k * R) + u.im := fun R => by simp
  have him : Tendsto (fun R : ℝ => |(-I * k * R + u).im|) atTop atTop := by
    simp only [e]
    exact tendsto_abs_atBot_atTop.comp (tendsto_atBot_add_const_right _ _
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hk)))
  refine tendsto_expIntE₁_zero (him.eventually (eventually_gt_atTop 0) |>.mono fun R hR =>
    mem_slitPlane_iff.mpr (Or.inr fun h => by rw [h, abs_zero] at hR; exact lt_irrefl _ hR))
    (r₀ := u.re) (Eventually.of_forall fun R => by simp) ?_
  exact tendsto_atTop_mono (fun R => le_max_left _ _) him

theorem neg_exp_mul_lineE1 (α β : ℂ) (t : ℝ) :
    -cexp β * lineE1 α β t = cexp (-(α * t)) * α / (α * t + β) := by
  have h : cexp β * cexp (-β) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  simp only [lineE1]
  rw [neg_add, exp_add]
  linear_combination (cexp (-(α * t)) * α / (α * t + β)) * h

/-- The improper integral of `f` when `f(t) = e^{−αt} α/(αt + β) = −e^β (E₁(αt + β))′`. -/
theorem tendsto_integral_of_lineE1 (α β : ℂ) (x : ℝ) {f : ℝ → ℂ}
    (hf : ∀ t : ℝ, x ≤ t → f t = cexp (-(α * t)) * α / (α * t + β))
    (h : ∀ t : ℝ, x ≤ t → α * t + β ∈ slitPlane)
    (hlim : Tendsto (fun R : ℝ => expIntE₁ (α * R + β)) atTop (𝓝 0)) :
    Tendsto (fun R => ∫ t in x..R, f t) atTop (𝓝 (cexp β * expIntE₁ (α * x + β))) := by
  have h2 := (tendsto_integral_lineE1 α β x h hlim).const_mul (-cexp β)
  rw [mul_neg, neg_mul, neg_neg] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop x] with R hR
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hR] at ht
  rw [neg_exp_mul_lineE1, hf t ht.1]

theorem div_eq_of_line {α d E : ℂ} (hα : α ≠ 0) {u : ℂ} (hu : u + d ≠ 0) :
    E * α / (α * (u + d)) = E / (u + d) := by
  field_simp

/-- `∫_x^∞ e^{it}/(t + ia) dt = e^a E₁(a − ix)` (improper), `a > 0`. -/
theorem tendsto_integral_exp_I_div_add {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Tendsto (fun R => ∫ t in x..R, cexp (I * t) / (t + I * a)) atTop
      (𝓝 (cexp a * expIntE₁ (a - I * x))) := by
  have h := tendsto_integral_of_lineE1 (-I) (a : ℂ) x
    (f := fun t => cexp (I * t) / (t + I * a))
    (fun t _ => by
      have hne : (t : ℂ) + I * a ≠ 0 := fun h0 => by
        have := congrArg Complex.im h0; simp at this; linarith
      have e : -I * (t : ℂ) + a = -I * (t + I * a) := by linear_combination (a : ℂ) * I_sq
      rw [e, div_eq_of_line (neg_ne_zero.mpr I_ne_zero) hne, show -(-I * (t : ℂ)) = I * t by
        ring])
    (fun t _ => mem_slitPlane_of_re_pos (by simpa using ha))
    (by simpa using tendsto_expIntE₁_vertical_line one_pos (a : ℂ))
  convert h using 3
  ring_nf

/-- `∫_x^∞ e^{it}/(t − ia) dt = e^{−a} E₁(−a − ix)` (improper), `a > 0`, `x > 0`. -/
theorem tendsto_integral_exp_I_div_sub {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun R => ∫ t in x..R, cexp (I * t) / (t - I * a)) atTop
      (𝓝 (cexp (-a) * expIntE₁ (-a - I * x))) := by
  have h := tendsto_integral_of_lineE1 (-I) (-(a : ℂ)) x
    (f := fun t => cexp (I * t) / (t - I * a))
    (fun t _ => by
      have hne : (t : ℂ) + -(I * a) ≠ 0 := fun h0 => by
        have := congrArg Complex.im h0; simp at this; linarith
      have e : -I * (t : ℂ) + -a = -I * (t + -(I * a)) := by
        linear_combination (-(a : ℂ)) * I_sq
      rw [e, div_eq_of_line (neg_ne_zero.mpr I_ne_zero) hne, show -(-I * (t : ℂ)) = I * t by
        ring, ← sub_eq_add_neg])
    (fun t ht => mem_slitPlane_iff.mpr (Or.inr (by simp; linarith)))
    (by simpa using tendsto_expIntE₁_vertical_line one_pos (-(a : ℂ)))
  convert h using 3
  ring_nf

/-- `∫_x^∞ e^{−t}/(t + c) dt = e^c E₁(x + c)` (improper), `ℑc ≠ 0`. -/
theorem tendsto_integral_exp_neg_div_add {c : ℂ} (hc : c.im ≠ 0) (x : ℝ) :
    Tendsto (fun R => ∫ t in x..R, cexp (-(t : ℂ)) / (t + c)) atTop
      (𝓝 (cexp c * expIntE₁ (x + c))) := by
  have hs : ∀ t : ℝ, (1 : ℂ) * t + c ∈ slitPlane := fun t =>
    mem_slitPlane_iff.mpr (Or.inr (by simpa using hc))
  have h := tendsto_integral_of_lineE1 1 c x (f := fun t => cexp (-(t : ℂ)) / (t + c))
    (fun t _ => by simp only [one_mul, mul_one])
    (fun t _ => hs t) (by simpa using tendsto_expIntE₁_pos_line one_pos c)
  simpa using h

/-! ### 6.7.1 -/

/-- **DLMF 6.7.1**: `∫_0^∞ e^{−at}/(t + b) dt = ∫_0^∞ e^{iat}/(t + ib) dt = e^{ab} E₁(ab)`,
`a, b > 0` (the second integral converges only conditionally: an improper integral). -/
theorem dlmf_6_7_1 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Ioi (0 : ℝ), cexp (-(a * t)) / (t + b)) = cexp (a * b) * expIntE₁ (a * b) ∧
      Tendsto (fun R => ∫ t in (0 : ℝ)..R, cexp (I * a * t) / (t + I * b)) atTop
        (𝓝 (cexp (a * b) * expIntE₁ (a * b))) := by
  have hab : (0 : ℝ) < a * b := mul_pos ha hb
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have h1 := tendsto_integral_of_lineE1 (a : ℂ) (a * b) 0
    (f := fun t => cexp (-(a * t)) / (t + b))
    (fun t ht => by
      have hne : (t : ℂ) + b ≠ 0 := fun h0 => by
        have := congrArg Complex.re h0; simp at this; linarith
      rw [show (a : ℂ) * t + a * b = a * (t + b) by ring, div_eq_of_line ha0 hne])
    (fun t ht => mem_slitPlane_of_re_pos (by simp; nlinarith))
    (tendsto_expIntE₁_pos_line ha _)
  have h2 := tendsto_integral_of_lineE1 (-I * a) (a * b) 0
    (f := fun t => cexp (I * a * t) / (t + I * b))
    (fun t _ => by
      have hne : (t : ℂ) + I * b ≠ 0 := fun h0 => by
        have := congrArg Complex.im h0; simp at this; linarith
      have e : -I * (a : ℂ) * t + a * b = -I * a * (t + I * b) := by
        linear_combination ((a : ℂ) * b) * I_sq
      rw [e, div_eq_of_line (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) ha0) hne,
        show -(-I * (a : ℂ) * t) = I * a * t by ring])
    (fun t _ => mem_slitPlane_of_re_pos (by simpa using hab))
    (by simpa [mul_assoc] using tendsto_expIntE₁_vertical_line ha ((a : ℂ) * b))
  simp only [ofReal_zero, mul_zero, zero_add] at h1 h2
  refine ⟨?_, h2⟩
  have hint : IntegrableOn (fun t : ℝ => cexp (-(a * t)) / (t + b)) (Ioi 0) := by
    have hexp : IntegrableOn (fun t : ℝ => Real.exp (-a * t) / b) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 ha).div_const b
    refine hexp.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
      have hne : (t : ℂ) + b ≠ 0 := fun h0 => by
        have := congrArg Complex.re h0; simp at this; linarith [show (0 : ℝ) < t from ht]
      exact ((continuous_const.mul continuous_ofReal).neg.cexp.continuousAt.div
        (continuous_ofReal.add continuous_const).continuousAt hne).continuousWithinAt
    · have ht' : (0 : ℝ) < t := ht
      rw [norm_div, norm_exp]
      have hn : (b : ℝ) ≤ ‖(t : ℂ) + b‖ := by
        have := re_le_norm ((t : ℂ) + b); simp at this; linarith
      simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      rw [show -(a * t) = -a * t by ring]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hb hn
  exact tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id) h1

/-! ### 6.7.2 -/

/-- **DLMF 6.7.2**: `e^x ∫_0^α e^{−xt}/(1 − t) dt = Ei(x) − Ei((1 − α)x)`, `0 ≤ α < 1`, `x > 0`. -/
theorem dlmf_6_7_2 {α x : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hx : 0 < x) :
    Real.exp x * ∫ t in (0 : ℝ)..α, Real.exp (-(x * t)) / (1 - t) = Ei x - Ei ((1 - α) * x) := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) α, HasDerivAt (fun t => -Real.exp (-x) * BZ.EiEin ((1 - t) * x))
      (Real.exp (-(x * t)) / (1 - t)) t := by
    intro t ht
    rw [uIcc_of_le hα0] at ht
    have h1t : 0 < 1 - t := by linarith [ht.2]
    have hpos : (1 - t) * x ≠ 0 := (mul_pos h1t hx).ne'
    have hg : HasDerivAt (fun t : ℝ => (1 - t) * x) ((0 - 1) * x) t :=
      ((hasDerivAt_const t 1).sub (hasDerivAt_id t)).mul_const x
    have := ((BZ.hasDerivAt_EiEin hpos).comp t hg).const_mul (-Real.exp (-x))
    refine this.congr_deriv ?_
    rw [show -(x * t) = -x + (1 - t) * x by ring, Real.exp_add]
    field_simp
    ring
  have hc : ContinuousOn (fun t : ℝ => Real.exp (-(x * t)) / (1 - t)) (uIcc 0 α) := by
    intro t ht
    rw [uIcc_of_le hα0] at ht
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousAt.div
      (continuous_const.sub continuous_id).continuousAt
      (show (1 : ℝ) - t ≠ 0 by linarith [ht.2])).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable,
    Ei_eq_EiEin hx, Ei_eq_EiEin (mul_pos (by linarith) hx)]
  simp only [sub_zero, one_mul]
  rw [show Real.exp x * (-Real.exp (-x) * BZ.EiEin ((1 - α) * x) -
      -Real.exp (-x) * BZ.EiEin x) = (Real.exp x * Real.exp (-x)) *
      (BZ.EiEin x - BZ.EiEin ((1 - α) * x)) by ring, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, one_mul]

/-! ### 6.7.3–6.7.6 -/

/-- Linearity of improper integrals of continuous functions. -/
theorem tendsto_integral_lin {g₁ g₂ f : ℝ → ℂ} {x : ℝ} {L₁ L₂ κ₁ κ₂ : ℂ}
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (h₁ : Tendsto (fun R => ∫ t in x..R, g₁ t) atTop (𝓝 L₁))
    (h₂ : Tendsto (fun R => ∫ t in x..R, g₂ t) atTop (𝓝 L₂))
    (hf : ∀ t, f t = κ₁ * g₁ t + κ₂ * g₂ t) :
    Tendsto (fun R => ∫ t in x..R, f t) atTop (𝓝 (κ₁ * L₁ + κ₂ * L₂)) := by
  refine ((h₁.const_mul κ₁).add (h₂.const_mul κ₂)).congr fun R => ?_
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((hg₁.intervalIntegrable _ _).const_mul _)
      ((hg₂.intervalIntegrable _ _).const_mul _)]
  exact intervalIntegral.integral_congr fun t _ => (hf t).symm

/-- A Lebesgue integral over `(x, ∞)` equals the limit of `∫_x^R`. -/
theorem integral_Ioi_eq_of_tendsto {f : ℝ → ℂ} {x : ℝ} {L : ℂ} (hint : IntegrableOn f (Ioi x))
    (h : Tendsto (fun R => ∫ t in x..R, f t) atTop (𝓝 L)) : ∫ t in Ioi x, f t = L :=
  tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi x hint tendsto_id) h

theorem ne_zero_of_im_ne_zero {w : ℂ} (h : w.im ≠ 0) : w ≠ 0 := fun h0 => h (by simp [h0])

theorem continuous_div_line {g : ℝ → ℂ} (hg : Continuous g) {c : ℂ} (hc : c.im ≠ 0) :
    Continuous fun t : ℝ => g t / (t + c) :=
  hg.div (continuous_ofReal.add continuous_const) fun t =>
    ne_zero_of_im_ne_zero (by simpa using hc)

theorem sq_add_sq_eq {a t : ℝ} : (a : ℂ) ^ 2 + (t : ℂ) ^ 2 = (t + I * a) * (t + -(I * a)) := by
  linear_combination ((a : ℂ) ^ 2) * I_sq

theorem sq_add_sq_ne {a t : ℝ} (ha : 0 < a) : (a : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
  rw [← ofReal_pow, ← ofReal_pow, ← ofReal_add, ofReal_ne_zero]
  positivity

/-- The two improper integrals `∫_x^∞ e^{it}/(t ± ia) dt`, `x > 0`. -/
theorem tendsto_J {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun R => ∫ t in x..R, cexp (I * t) / (t + I * a)) atTop
        (𝓝 (cexp a * expIntE₁ (a - I * x))) ∧
      Tendsto (fun R => ∫ t in x..R, cexp (I * t) / (t + -(I * a))) atTop
        (𝓝 (cexp (-a) * expIntE₁ (-a - I * x))) := by
  refine ⟨tendsto_integral_exp_I_div_add ha x, ?_⟩
  simpa [sub_eq_add_neg] using tendsto_integral_exp_I_div_sub ha hx

theorem continuous_J {c : ℂ} (hc : c.im ≠ 0) :
    Continuous fun t : ℝ => cexp (I * t) / (t + c) :=
  continuous_div_line (continuous_const.mul continuous_ofReal).cexp hc

/-- **DLMF 6.7.3**: `∫_x^∞ e^{it}/(a² + t²) dt = (i/(2a))(e^a E₁(a − ix) − e^{−a} E₁(−a − ix))`,
`a > 0`, `x > 0`. -/
theorem dlmf_6_7_3 {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    ∫ t in Ioi x, cexp (I * t) / ((a : ℂ) ^ 2 + (t : ℂ) ^ 2) =
      I / (2 * a) * (cexp a * expIntE₁ (a - I * x) - cexp (-a) * expIntE₁ (-a - I * x)) := by
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  obtain ⟨hp, hm⟩ := tendsto_J ha hx
  have him1 : (I * (a : ℂ)).im ≠ 0 := by simp [ha.ne']
  have him2 : (-(I * (a : ℂ))).im ≠ 0 := by simp [ha.ne']
  have h := tendsto_integral_lin (κ₁ := -(1 / (2 * I * a))) (κ₂ := 1 / (2 * I * a))
    (f := fun t : ℝ => cexp (I * t) / ((a : ℂ) ^ 2 + (t : ℂ) ^ 2))
    (continuous_J him1) (continuous_J him2) hp hm (fun t => by
      have h1 : (t : ℂ) + I * a ≠ 0 := ne_zero_of_im_ne_zero (by simpa using him1)
      have h2 : (t : ℂ) + -(I * a) ≠ 0 := ne_zero_of_im_ne_zero (by simpa using him2)
      rw [sq_add_sq_eq]
      field_simp
      ring)
  rw [integral_Ioi_eq_of_tendsto ?_ h]
  · field_simp
    ring_nf
    rw [I_sq]
    ring
  · -- integrability: `|e^{it}/(a² + t²)| ≤ t^{−2}`
    refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx).mono' ?_
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
    · exact (((continuous_const.mul continuous_ofReal).cexp).div
        ((continuous_const).add (continuous_ofReal.pow 2)) fun t => sq_add_sq_ne ha)
        |>.aestronglyMeasurable
    · have ht' : (0 : ℝ) < t := hx.trans ht
      rw [norm_div, mul_comm, norm_exp_ofReal_mul_I, ← ofReal_pow, ← ofReal_pow, ← ofReal_add,
        norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), Real.rpow_neg ht'.le,
        Real.rpow_two, one_div]
      exact inv_anti₀ (by positivity) (by nlinarith)

/-- **DLMF 6.7.4**: `∫_x^∞ t e^{it}/(a² + t²) dt = ½(e^a E₁(a − ix) + e^{−a} E₁(−a − ix))`,
`a > 0`, `x > 0` (an improper integral). -/
theorem dlmf_6_7_4 {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    Tendsto (fun R => ∫ t in x..R, t * cexp (I * t) / ((a : ℂ) ^ 2 + (t : ℂ) ^ 2)) atTop
      (𝓝 (1 / 2 * (cexp a * expIntE₁ (a - I * x) + cexp (-a) * expIntE₁ (-a - I * x)))) := by
  obtain ⟨hp, hm⟩ := tendsto_J ha hx
  have him1 : (I * (a : ℂ)).im ≠ 0 := by simp [ha.ne']
  have him2 : (-(I * (a : ℂ))).im ≠ 0 := by simp [ha.ne']
  have h := tendsto_integral_lin (κ₁ := 1 / 2) (κ₂ := 1 / 2)
    (f := fun t : ℝ => t * cexp (I * t) / ((a : ℂ) ^ 2 + (t : ℂ) ^ 2))
    (continuous_J him1) (continuous_J him2) hp hm (fun t => by
      have h1 : (t : ℂ) + I * a ≠ 0 := ne_zero_of_im_ne_zero (by simpa using him1)
      have h2 : (t : ℂ) + -(I * a) ≠ 0 := ne_zero_of_im_ne_zero (by simpa using him2)
      rw [sq_add_sq_eq]
      field_simp
      ring)
  convert h using 2
  ring

theorem continuous_K {c : ℂ} (hc : c.im ≠ 0) :
    Continuous fun t : ℝ => cexp (-(t : ℂ)) / (t + c) :=
  continuous_div_line continuous_ofReal.neg.cexp hc

/-- The integrability of `e^{−t} p(t)/(a² + t²)` on `(x, ∞)` for `|p(t)|/(a² + t²) ≤ C`. -/
theorem integrableOn_exp_neg_mul {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ t, |g t| ≤ C) (x : ℝ) : IntegrableOn (fun t => Real.exp (-t) * g t) (Ioi x) := by
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t) * C) (Ioi x) := by
    have h1 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi x) := by
      simpa using exp_neg_integrableOn_Ioi x one_pos
    exact h1.mul_const C
  refine hexp.mono' (Real.continuous_exp.comp continuous_neg |>.mul hg).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hC t) (Real.exp_pos _).le

/-- **DLMF 6.7.5**:
`∫_x^∞ e^{−t}/(a² + t²) dt = −(1/(2ai))(e^{ia} E₁(x + ia) − e^{−ia} E₁(x − ia))`, `a > 0`,
`x ∈ ℝ`. -/
theorem dlmf_6_7_5 {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ((∫ t in Ioi x, Real.exp (-t) / (a ^ 2 + t ^ 2) : ℝ) : ℂ) =
      -(1 / (2 * a * I)) * (cexp (I * a) * expIntE₁ (x + I * a) -
        cexp (-(I * a)) * expIntE₁ (x - I * a)) := by
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have him1 : (I * (a : ℂ)).im ≠ 0 := by simp [ha.ne']
  have him2 : (-(I * (a : ℂ))).im ≠ 0 := by simp [ha.ne']
  have h := tendsto_integral_lin (κ₁ := -(1 / (2 * I * a))) (κ₂ := 1 / (2 * I * a))
    (f := fun t : ℝ => ((Real.exp (-t) / (a ^ 2 + t ^ 2) : ℝ) : ℂ))
    (continuous_K him1) (continuous_K him2) (tendsto_integral_exp_neg_div_add him1 x)
    (tendsto_integral_exp_neg_div_add him2 x) (fun t => by
      have h1 : (t : ℂ) + I * a ≠ 0 := ne_zero_of_im_ne_zero (by simpa using him1)
      have h2 : (t : ℂ) + -(I * a) ≠ 0 := ne_zero_of_im_ne_zero (by simpa using him2)
      push_cast
      rw [sq_add_sq_eq]
      field_simp
      ring)
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-t) / (a ^ 2 + t ^ 2)) (Ioi x) := by
    refine (integrableOn_exp_neg_mul (g := fun t => 1 / (a ^ 2 + t ^ 2))
      (continuous_const.div (continuous_const.add (continuous_pow 2)) fun t => by positivity)
      (C := 1 / a ^ 2) (fun t => ?_) x).congr_fun (fun t _ => by simp [div_eq_mul_inv])
      measurableSet_Ioi
    rw [abs_of_pos (by positivity)]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  rw [← integral_complex_ofReal]
  refine (integral_Ioi_eq_of_tendsto hint.ofReal h).trans ?_
  field_simp
  ring_nf

/-- **DLMF 6.7.6**: `∫_x^∞ t e^{−t}/(a² + t²) dt = ½(e^{ia} E₁(x + ia) + e^{−ia} E₁(x − ia))`,
`a > 0`, `x ∈ ℝ`. -/
theorem dlmf_6_7_6 {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ((∫ t in Ioi x, t * Real.exp (-t) / (a ^ 2 + t ^ 2) : ℝ) : ℂ) =
      1 / 2 * (cexp (I * a) * expIntE₁ (x + I * a) + cexp (-(I * a)) * expIntE₁ (x - I * a)) := by
  have him1 : (I * (a : ℂ)).im ≠ 0 := by simp [ha.ne']
  have him2 : (-(I * (a : ℂ))).im ≠ 0 := by simp [ha.ne']
  have h := tendsto_integral_lin (κ₁ := 1 / 2) (κ₂ := 1 / 2)
    (f := fun t : ℝ => ((t * Real.exp (-t) / (a ^ 2 + t ^ 2) : ℝ) : ℂ))
    (continuous_K him1) (continuous_K him2) (tendsto_integral_exp_neg_div_add him1 x)
    (tendsto_integral_exp_neg_div_add him2 x) (fun t => by
      have h1 : (t : ℂ) + I * a ≠ 0 := ne_zero_of_im_ne_zero (by simpa using him1)
      have h2 : (t : ℂ) + -(I * a) ≠ 0 := ne_zero_of_im_ne_zero (by simpa using him2)
      push_cast
      rw [sq_add_sq_eq]
      field_simp
      ring)
  have hint : IntegrableOn (fun t : ℝ => t * Real.exp (-t) / (a ^ 2 + t ^ 2)) (Ioi x) := by
    refine (integrableOn_exp_neg_mul (g := fun t => t / (a ^ 2 + t ^ 2))
      (continuous_id.div (continuous_const.add (continuous_pow 2)) fun t => by positivity)
      (C := 1 / (2 * a)) (fun t => ?_) x).congr_fun (fun t _ => by ring) measurableSet_Ioi
    rw [abs_div, abs_of_pos (show (0 : ℝ) < a ^ 2 + t ^ 2 by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (|t| - a)]
  rw [← integral_complex_ofReal]
  refine (integral_Ioi_eq_of_tendsto hint.ofReal h).trans ?_
  ring_nf

/-! ### 6.7.7, 6.7.8 -/

theorem EinDeriv_mul_eq (w : ℂ) {s : ℝ} (hs : s ≠ 0) :
    BZ.EinDeriv (w * s) * w = (1 - cexp (-(w * s))) / s := by
  have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs
  rcases eq_or_ne w 0 with rfl | hw
  · simp [BZ.EinDeriv]
  · rw [EinDeriv_of_ne (mul_ne_zero hw hs')]
    field_simp

theorem ein_eq_integral_EinDeriv (w : ℂ) :
    ein w = ∫ s in (0 : ℝ)..1, BZ.EinDeriv (w * s) * w := by
  rw [ein]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
  rw [uIoc_of_le zero_le_one] at hs
  have hs0 : s ≠ 0 := hs.1.ne'
  rw [EinDeriv_mul_eq w hs0]
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · field_simp

theorem continuous_EinDeriv_mul_const (w : ℂ) :
    Continuous fun s : ℝ => BZ.EinDeriv (w * s) * w :=
  (continuous_EinDeriv.comp (continuous_const.mul continuous_ofReal)).mul continuous_const

/-- **DLMF 6.7.7**: `∫_0^1 e^{−at} sin(bt)/t dt = ℑ Ein(a + ib)`, `a, b ∈ ℝ`. -/
theorem dlmf_6_7_7 (a b : ℝ) :
    ∫ t in (0 : ℝ)..1, Real.exp (-(a * t)) * Real.sin (b * t) / t = (ein (a + b * I)).im := by
  rw [ein_eq_integral_EinDeriv, ← imCLM_apply,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _
      ((continuous_EinDeriv_mul_const _).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
  rw [uIoc_of_le zero_le_one] at hs
  rw [imCLM_apply, EinDeriv_mul_eq _ hs.1.ne', div_ofReal_im]
  simp [Complex.exp_im, Real.sin_neg]

/-- **DLMF 6.7.8**: `∫_0^1 e^{−at}(1 − cos(bt))/t dt = ℜ Ein(a + ib) − Ein(a)`, `a, b ∈ ℝ`
(`Ein(a)` is real, `ein_ofReal`). -/
theorem dlmf_6_7_8 (a b : ℝ) :
    ∫ t in (0 : ℝ)..1, Real.exp (-(a * t)) * (1 - Real.cos (b * t)) / t =
      (ein (a + b * I)).re - (ein a).re := by
  have hi : ∀ w : ℂ, IntervalIntegrable (fun x : ℝ => reCLM (BZ.EinDeriv (w * x) * w))
      volume 0 1 := fun w =>
    (reCLM.continuous.comp (continuous_EinDeriv_mul_const w)).intervalIntegrable _ _
  rw [ein_eq_integral_EinDeriv, ein_eq_integral_EinDeriv, ← reCLM_apply, ← reCLM_apply,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _
      ((continuous_EinDeriv_mul_const _).intervalIntegrable _ _),
    ← ContinuousLinearMap.intervalIntegral_comp_comm _
      ((continuous_EinDeriv_mul_const _).intervalIntegrable _ _),
    ← intervalIntegral.integral_sub (hi _) (hi _)]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
  rw [uIoc_of_le zero_le_one] at hs
  simp only [reCLM_apply]
  rw [EinDeriv_mul_eq _ hs.1.ne', EinDeriv_mul_eq _ hs.1.ne', div_ofReal_re, div_ofReal_re]
  simp [Complex.exp_re]
  ring

end Azurite.DLMF
