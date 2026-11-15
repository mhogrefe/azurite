/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section13

/-!
# DLMF §6.14(i): Laplace transforms

Formalizations of <https://dlmf.nist.gov/6.14.i>.

## Main results

* `dlmf_6_14_1`: `∫_0^∞ e^{−at} E₁(t) dt = (1/a) ln(1 + a)`, `ℜa > −1`, `a ≠ 0`;
  `dlmf_6_14_1_zero`: `∫_0^∞ E₁(t) dt = 1` (the value at `a = 0`, as a limit).
* `dlmf_6_14_2`: `∫_0^∞ e^{−at} Ci(t) dt = −(1/(2a)) ln(1 + a²)`, `ℜa > 0`.
* `dlmf_6_14_3`: `∫_0^∞ e^{−at} si(t) dt = −(1/a) arctan a`, `ℜa > 0` (Mathlib's
  `Complex.arctan`, which is DLMF's principal value by §4.23's `arctanD_eq`).

All three are Lebesgue integrals, evaluated by integration by parts with explicit antiderivatives
built from `E₁(ct)`, `ℜc > 0` (`d/dt E₁(ct) = −e^{−ct}/t`): e.g. for 6.14.1
`Φ(t) = −(1/a)(e^{−at}E₁(t) − E₁((1 + a)t))`, and `e^{−at}Ci(t)` is paired with
`½E₁((a ∓ i)t)`, `e^{−at}si(t)` with `±E₁((a ∓ i)t)/(2i)`.  The values at `0+` come from
`E₁(cε) + ln ε → −γ − ln c` (`tendsto_expIntE₁_mul_add_log`, from §6.3) and
`Ci(ε) − ln ε → γ`; integrability from logarithmic bounds near `0` and `|Ci|, |si| ≤ 2` on
`[1, ∞)` (`abs_CiR_siR_le_two`, via §6.13's real `f`, `g`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Nat

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-! ### Tools: FTC on `(0, ∞)`, integrability, small-argument limits -/

/-- FTC on `(0, ∞)` with limits at both ends. -/
theorem integral_Ioi_zero_of_hasDerivAt {Φ h : ℝ → ℂ} (hd : ∀ t : ℝ, 0 < t → HasDerivAt Φ (h t) t)
    (hint : IntegrableOn h (Ioi 0)) {L₀ L₁ : ℂ} (h0 : Tendsto Φ (𝓝[>] 0) (𝓝 L₀))
    (h1 : Tendsto Φ atTop (𝓝 L₁)) : ∫ t in Ioi (0 : ℝ), h t = L₁ - L₀ := by
  have hu : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hu, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi zero_le_one)),
    ← intervalIntegral.integral_of_le zero_le_one]
  have hA := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun x hx => hd x hx.1)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
      (hint.mono_set Ioc_subset_Ioi_self)) h0
    ((hd 1 one_pos).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hB := integral_Ioi_of_hasDerivAt_of_tendsto
    (hd 1 one_pos).continuousAt.continuousWithinAt
    (fun x (hx : 1 < x) => hd x (by linarith)) (hint.mono_set (Ioi_subset_Ioi zero_le_one)) h1
  rw [hA, hB]; ring

/-- Integrability on `(0, ∞)` from a logarithmic bound on `(0, 1]` and exponential decay on
`(1, ∞)`. -/
theorem integrableOn_Ioi_of_log_exp_bound {h : ℝ → ℂ} (hc : ContinuousOn h (Ioi 0)) {A B c : ℝ}
    (hcpos : 0 < c) (h01 : ∀ t ∈ Ioc (0 : ℝ) 1, ‖h t‖ ≤ A + B * |Real.log t|)
    (h1 : ∀ t : ℝ, 1 < t → ‖h t‖ ≤ A * Real.exp (-c * t)) : IntegrableOn h (Ioi 0) := by
  have hu : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hu]
  refine IntegrableOn.union ?_ ?_
  · have hlog : IntegrableOn (fun t => A + B * |Real.log t|) (Ioc 0 1) := by
      refine (integrableOn_const (by simp)).add ?_
      have := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      exact this.norm.const_mul B
    refine hlog.mono' ((hc.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall h01))
  · refine ((exp_neg_integrableOn_Ioi 1 hcpos).const_mul A).mono'
      ((hc.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => h1 t ht))

/-- `E₁(cε) + ln ε → −γ − ln c` as `ε → 0+`, `ℜc > 0`. -/
theorem tendsto_expIntE₁_mul_add_log {c : ℂ} (hc : 0 < c.re) :
    Tendsto (fun ε : ℝ => expIntE₁ (c * ε) + Real.log ε) (𝓝[>] 0) (𝓝 (-(γ : ℂ) - log c)) := by
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hw : Tendsto (fun ε : ℝ => c * (ε : ℂ)) (𝓝[>] 0) (𝓝[slitPlane] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun ε : ℝ => c * (ε : ℂ)) (𝓝 0) (𝓝 (c * ((0 : ℝ) : ℂ))) :=
        (continuous_const.mul continuous_ofReal).tendsto 0
      rw [ofReal_zero, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact mem_slitPlane_of_re_pos (by simp; positivity)
  have h := (dlmf_6_3_F3_log.comp hw).sub_const (log c)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp only [Function.comp]
  rw [log_mul_ofReal ε hε c hc0]
  ring

/-- If `F(ε) + σ ln ε` has a limit as `ε → 0+`, then `εF(ε) → 0`. -/
theorem tendsto_mul_of_add_log {F : ℝ → ℂ} {σ L : ℂ}
    (h : Tendsto (fun ε : ℝ => F ε + σ * Real.log ε) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * F ε) (𝓝[>] 0) (𝓝 0) := by
  have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := (continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [ofReal_zero] at this
  have hlog : Tendsto (fun ε : ℝ => ((Real.log ε * ε : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos
    simp only [Real.rpow_one] at this
    have := (continuous_ofReal.tendsto 0).comp this
    rwa [ofReal_zero] at this
  have := (hε.mul h).sub (hlog.const_mul σ)
  rw [zero_mul, mul_zero, sub_zero] at this
  refine this.congr fun ε => ?_
  push_cast; ring

/-- `(e^{−aε} − 1) F(ε) → 0` when `εF(ε) → 0`. -/
theorem tendsto_exp_sub_one_mul {F : ℝ → ℂ} (a : ℂ)
    (h : Tendsto (fun ε : ℝ => (ε : ℂ) * F ε) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => (cexp (-(a * ε)) - 1) * F ε) (𝓝[>] 0) (𝓝 0) := by
  have h2 := h.norm.const_mul (2 * ‖a‖)
  rw [norm_zero, mul_zero] at h2
  refine squeeze_zero_norm' ?_ h2
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ‖a‖ * ε ≤ 1 ∧ 0 < ε := by
    have : Tendsto (fun ε : ℝ => ‖a‖ * ε) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous fun ε : ℝ => ‖a‖ * ε := by fun_prop
      have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    exact (this.eventually (eventually_le_nhds one_pos)).and self_mem_nhdsWithin
  filter_upwards [hsmall] with ε ⟨hε1, hε0⟩
  have hn : ‖-(a * (ε : ℂ))‖ = ‖a‖ * ε := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
  calc ‖cexp (-(a * ε)) - 1‖ * ‖F ε‖ ≤ (2 * (‖a‖ * ε)) * ‖F ε‖ := by
        gcongr; rw [← hn]; exact Complex.norm_exp_sub_one_le (by rw [hn]; exact hε1)
    _ = 2 * ‖a‖ * (ε * ‖F ε‖) := by ring

/-- `E₁(cR) → 0` as `R → ∞`, `ℜc > 0`. -/
theorem tendsto_expIntE₁_mul_atTop {c : ℂ} (hc : 0 < c.re) :
    Tendsto (fun R : ℝ => expIntE₁ (c * R)) atTop (𝓝 0) := by
  have hre : ∀ R : ℝ, (c * R).re = c.re * R := fun R => by simp
  refine tendsto_expIntE₁_zero (r₀ := 0) ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with R hR
    exact mem_slitPlane_of_re_pos (by rw [hre]; positivity)
  · filter_upwards [eventually_ge_atTop 0] with R hR
    rw [hre]; positivity
  · refine tendsto_atTop_mono (fun R => le_max_right _ _) ?_
    simp only [hre]
    exact tendsto_id.const_mul_atTop hc

theorem ofReal_mem_slitPlane_of_pos {t : ℝ} (ht : 0 < t) : (t : ℂ) ∈ slitPlane :=
  ofReal_mem_slitPlane.2 ht

theorem mul_ofReal_mem_slitPlane {c : ℂ} (hc : 0 < c.re) {t : ℝ} (ht : 0 < t) :
    c * (t : ℂ) ∈ slitPlane :=
  mem_slitPlane_of_re_pos (by simp; positivity)

/-- `d/dt E₁(ct) = −e^{−ct}/t` for `t > 0`, `ℜc > 0`. -/
theorem hasDerivAt_expIntE₁_mul {c : ℂ} (hc : 0 < c.re) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => expIntE₁ (c * s)) (-cexp (-(c * t)) / t) t := by
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have h := ((hasDerivAt_expIntE₁ (mul_ofReal_mem_slitPlane hc ht)).comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).const_mul c)).comp_ofReal
  refine h.congr_deriv ?_
  have : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
  simp only [mul_one]
  field_simp

/-! ### 6.14.1 -/

theorem hasDerivAt_expIntE₁_ofReal {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => expIntE₁ s) (-cexp (-(t : ℂ)) / t) t :=
  (hasDerivAt_expIntE₁ (ofReal_mem_slitPlane_of_pos ht)).comp_ofReal

theorem hasDerivAt_cexp_neg_mul_ofReal (a : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => cexp (-(a * s))) (-a * cexp (-(a * t))) t := by
  have h := (((hasDerivAt_id (t : ℂ)).const_mul a).neg.cexp).comp_ofReal
  refine h.congr_deriv ?_
  simp only [id, mul_one, Pi.neg_apply]
  ring

/-- `|E₁(t)| ≤ (Ein(1) + γ) + |ln t|` on `(0, 1]`. -/
theorem norm_expIntE₁_le_log {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖expIntE₁ t‖ ≤ (BZ.EinR 1 + γ) + |Real.log t| := by
  rw [dlmf_6_3_F1_real ht.1, Complex.norm_real, Real.norm_eq_abs, expIntE₁R]
  have h0 : 0 ≤ BZ.EinR t := by
    have := strictMono_EinR.monotone ht.1.le; rwa [BZ.EinR_zero] at this
  have h1 : BZ.EinR t ≤ BZ.EinR 1 := strictMono_EinR.monotone ht.2
  have hγ : 0 < γ := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  rw [abs_le]; constructor <;>
    linarith [le_abs_self (Real.log t), neg_abs_le (Real.log t)]

/-- `|E₁(t)| ≤ e^{−t}` for `t ≥ 1`. -/
theorem norm_expIntE₁_le_exp {t : ℝ} (ht : 1 ≤ t) : ‖expIntE₁ t‖ ≤ Real.exp (-t) := by
  refine (norm_expIntE₁_le (ofReal_mem_slitPlane_of_pos (by linarith))).trans ?_
  simp only [ofReal_re, ofReal_im, abs_zero]
  rw [max_eq_right (by linarith), div_le_iff₀ (by linarith)]
  exact le_mul_of_one_le_right (Real.exp_pos _).le ht

/-- `e^{−aR}E₁(R) → 0` for `ℜa > −1`. -/
theorem tendsto_cexp_mul_expIntE₁ {a : ℂ} (ha : -1 < a.re) :
    Tendsto (fun R : ℝ => cexp (-(a * R)) * expIntE₁ R) atTop (𝓝 0) := by
  have hlim : Tendsto (fun R : ℝ => Real.exp (-(1 + a.re) * R)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with R hR
  rw [norm_mul, norm_cexp_neg_mul]
  calc Real.exp (-(a.re * R)) * ‖expIntE₁ R‖ ≤ Real.exp (-(a.re * R)) * Real.exp (-R) := by
        gcongr; exact norm_expIntE₁_le_exp hR
    _ = _ := by rw [← Real.exp_add]; ring_nf

/-- The Laplace transform of `E₁` is integrable for `ℜa > −1`. -/
theorem integrableOn_laplace_expIntE₁ {a : ℂ} (ha : -1 < a.re) :
    IntegrableOn (fun t : ℝ => cexp (-(a * t)) * expIntE₁ t) (Ioi 0) := by
  set K := BZ.EinR 1 + γ
  have hK : 0 ≤ K := by
    have := strictMono_EinR.monotone zero_le_one
    rw [BZ.EinR_zero] at this
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  set M := Real.exp |a.re|
  refine integrableOn_Ioi_of_log_exp_bound (A := M * K + 1) (B := M) (c := 1 + a.re)
    (fun t ht => (((hasDerivAt_cexp_neg_mul_ofReal a t).mul
      (hasDerivAt_expIntE₁_ofReal ht)).continuousAt).continuousWithinAt) (by linarith)
    (fun t ht => ?_) (fun t ht => ?_)
  · rw [norm_mul, norm_cexp_neg_mul]
    have hM : Real.exp (-(a.re * t)) ≤ M := Real.exp_le_exp.2 (by
      have := neg_abs_le a.re; nlinarith [ht.1, ht.2, abs_nonneg a.re])
    calc Real.exp (-(a.re * t)) * ‖expIntE₁ t‖ ≤ M * (K + |Real.log t|) :=
          mul_le_mul hM (norm_expIntE₁_le_log ht) (norm_nonneg _) (by positivity)
      _ ≤ M * K + 1 + M * |Real.log t| := by nlinarith
  · rw [norm_mul, norm_cexp_neg_mul]
    calc Real.exp (-(a.re * t)) * ‖expIntE₁ t‖ ≤ Real.exp (-(a.re * t)) * Real.exp (-t) := by
          gcongr; exact norm_expIntE₁_le_exp ht.le
      _ = 1 * Real.exp (-(1 + a.re) * t) := by rw [← Real.exp_add]; ring_nf
      _ ≤ (M * K + 1) * Real.exp (-(1 + a.re) * t) := by
          gcongr; have : 0 ≤ M * K := by positivity
          linarith

/-- **DLMF 6.14.1**: `∫_0^∞ e^{−at} E₁(t) dt = (1/a) ln(1 + a)`, `ℜa > −1` (`a ≠ 0`; for `a = 0`
the right side is read as its limit `1`, `dlmf_6_14_1_zero`). -/
theorem dlmf_6_14_1 {a : ℂ} (ha : -1 < a.re) (ha0 : a ≠ 0) :
    ∫ t in Ioi (0 : ℝ), cexp (-(a * t)) * expIntE₁ t = 1 / a * log (1 + a) := by
  have h1a : 0 < (1 + a).re := by simp; linarith
  set Φ : ℝ → ℂ := fun t => -(1 / a) * (cexp (-(a * t)) * expIntE₁ t - expIntE₁ ((1 + a) * t))
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt Φ (cexp (-(a * t)) * expIntE₁ t) t := by
    intro t ht
    have h := (((hasDerivAt_cexp_neg_mul_ofReal a t).mul (hasDerivAt_expIntE₁_ofReal ht)).sub
      (hasDerivAt_expIntE₁_mul h1a ht)).const_mul (-(1 / a))
    refine h.congr_deriv ?_
    rw [show -((1 + a) * (t : ℂ)) = -(a * t) + -(t : ℂ) by ring, exp_add]
    have : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
    field_simp
    ring
  have h0 : Tendsto Φ (𝓝[>] 0) (𝓝 (-(1 / a) * log (1 + a))) := by
    have hE := tendsto_expIntE₁_mul_add_log (c := 1) (by simp)
    simp only [one_mul, log_one, sub_zero] at hE
    have hE' := tendsto_expIntE₁_mul_add_log h1a
    have hm := tendsto_exp_sub_one_mul a (tendsto_mul_of_add_log (σ := 1) (by simpa using hE))
    have := ((hm.add hE).sub hE').const_mul (-(1 / a))
    convert this using 2 with ε
    · simp only [Φ]; ring
    · ring
  have h1 : Tendsto Φ atTop (𝓝 0) := by
    have := ((tendsto_cexp_mul_expIntE₁ ha).sub (tendsto_expIntE₁_mul_atTop h1a)).const_mul
      (-(1 / a))
    rw [sub_zero, mul_zero] at this
    exact this
  rw [integral_Ioi_zero_of_hasDerivAt hd (integrableOn_laplace_expIntE₁ ha) h0 h1]
  ring

/-- **DLMF 6.14.1** at `a = 0` (the limit of the right side): `∫_0^∞ E₁(t) dt = 1`. -/
theorem dlmf_6_14_1_zero : ∫ t in Ioi (0 : ℝ), expIntE₁ t = 1 := by
  set Φ : ℝ → ℂ := fun t => t * expIntE₁ t - cexp (-(t : ℂ))
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt Φ (expIntE₁ t) t := by
    intro t ht
    have h := (((hasDerivAt_id t).ofReal_comp).mul (hasDerivAt_expIntE₁_ofReal ht)).sub
      ((hasDerivAt_cexp_neg_mul_ofReal 1 t))
    simp only [one_mul, id, ofReal_one] at h
    refine h.congr_deriv ?_
    have : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
    field_simp
    ring
  have hE := tendsto_expIntE₁_mul_add_log (c := 1) (by simp)
  simp only [one_mul, log_one, sub_zero] at hE
  have hm := tendsto_mul_of_add_log (σ := 1) (by simpa using hE)
  have hexp0 : Tendsto (fun t : ℝ => cexp (-(t : ℂ))) (𝓝[>] 0) (𝓝 1) := by
    have : Continuous fun t : ℝ => cexp (-(t : ℂ)) := by fun_prop
    have := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have h0 : Tendsto Φ (𝓝[>] 0) (𝓝 (0 - 1)) := hm.sub hexp0
  have h1 : Tendsto Φ atTop (𝓝 (0 - 0)) := by
    refine Tendsto.sub ?_ ?_
    · refine squeeze_zero_norm' ?_ (Real.tendsto_exp_neg_atTop_nhds_zero)
      filter_upwards [eventually_ge_atTop 1] with R hR
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      have := (norm_expIntE₁_le (ofReal_mem_slitPlane_of_pos (by linarith : (0 : ℝ) < R)))
      simp only [ofReal_re, ofReal_im, abs_zero, max_eq_right (by linarith : (0 : ℝ) ≤ R)]
        at this
      rw [le_div_iff₀ (by linarith)] at this
      linarith
    · have : Tendsto (fun R : ℝ => ((Real.exp (-R) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
        (continuous_ofReal.tendsto 0).comp Real.tendsto_exp_neg_atTop_nhds_zero
      rw [ofReal_zero] at this
      refine this.congr fun R => ?_
      push_cast; rfl
  rw [integral_Ioi_zero_of_hasDerivAt hd ?_ h0 h1]
  · ring
  · simpa using integrableOn_laplace_expIntE₁ (a := 0) (by norm_num)

/-! ### 6.14.2, 6.14.3 -/

theorem re_add_I_pos {a : ℂ} (ha : 0 < a.re) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) :
    0 < (a + σ * I).re := by
  rcases hσ with rfl | rfl <;> simpa using ha

/-- `|Ci(t)|, |si(t)| ≤ 2` for `t ≥ 1` (from `Ci = f sin − g cos`, `si = −f cos − g sin`). -/
theorem abs_CiR_siR_le_two {t : ℝ} (ht : 1 ≤ t) : |CiR t| ≤ 2 ∧ |SiR t - π / 2| ≤ 2 := by
  have ht0 : 0 < t := by linarith
  obtain ⟨-, -, hF0, -, hG0, -⟩ := fR_gR_spec ht0 0
  obtain ⟨-, -, hF1, -, hG1, -⟩ := fR_gR_spec ht0 1
  simp only [pow_zero, one_mul, pow_one, fS_one, gS_one, show fS 0 t = 0 by simp [fS],
    show gS 0 t = 0 by simp [gS], sub_zero] at hF0 hG0 hF1 hG1
  have h1 : 1 / t ≤ 1 := by rw [div_le_one ht0]; exact ht
  have h2 : 1 / t ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hs := Real.abs_sin_le_one t
  have hc := Real.abs_cos_le_one t
  have b1 : |fR t * Real.sin t| ≤ 1 := by
    rw [abs_mul, abs_of_pos hF0]; nlinarith [abs_nonneg (Real.sin t)]
  have b2 : |gR t * Real.cos t| ≤ 1 := by
    rw [abs_mul, abs_of_pos hG0]; nlinarith [abs_nonneg (Real.cos t)]
  have b3 : |fR t * Real.cos t| ≤ 1 := by
    rw [abs_mul, abs_of_pos hF0]; nlinarith [abs_nonneg (Real.cos t)]
  have b4 : |gR t * Real.sin t| ≤ 1 := by
    rw [abs_mul, abs_of_pos hG0]; nlinarith [abs_nonneg (Real.sin t)]
  constructor
  · rw [CiR_eq ht0]
    exact (abs_sub _ _).trans (by linarith)
  · rw [SiR_eq ht0, show π / 2 - fR t * Real.cos t - gR t * Real.sin t - π / 2 =
      -(fR t * Real.cos t) - gR t * Real.sin t by ring]
    exact (abs_sub _ _).trans (by rw [abs_neg]; linarith)

theorem Ci_ofReal {t : ℝ} (ht : 0 < t) : Ci t = (CiR t : ℂ) := dlmf_6_3_F2_Ci_real ht

theorem CinR_zero : CinR 0 = 0 := by simp [CinR]

/-- `Ci(ε) − ln ε → γ` as `ε → 0+`. -/
theorem tendsto_Ci_sub_log :
    Tendsto (fun ε : ℝ => Ci ε + (-1) * Real.log ε) (𝓝[>] 0) (𝓝 (γ : ℂ)) := by
  have h : Tendsto (fun ε : ℝ => ((-CinR ε + γ : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (((-CinR 0 + γ : ℝ)) : ℂ)) :=
    ((continuous_ofReal.comp (continuous_CinR.neg.add continuous_const)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  rw [CinR_zero, neg_zero, zero_add] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [Ci_ofReal hε, CiR]; push_cast; ring

/-- **DLMF 6.14.2**: `∫_0^∞ e^{−at} Ci(t) dt = −(1/(2a)) ln(1 + a²)`, `ℜa > 0`. -/
theorem dlmf_6_14_2 {a : ℂ} (ha : 0 < a.re) :
    ∫ t in Ioi (0 : ℝ), cexp (-(a * t)) * Ci t = -(1 / (2 * a)) * log (1 + a ^ 2) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hm := re_add_I_pos ha (-1) (Or.inr rfl)
  have hp := re_add_I_pos ha 1 (Or.inl rfl)
  set Φ : ℝ → ℂ := fun t => -(1 / a) * (cexp (-(a * t)) * Ci t +
    1 / 2 * expIntE₁ ((a + -1 * I) * t) + 1 / 2 * expIntE₁ ((a + 1 * I) * t))
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt Φ (cexp (-(a * t)) * Ci t) t := by
    intro t ht
    have hCi := (hasDerivAt_Ci (ofReal_mem_slitPlane_of_pos ht)).comp_ofReal
    have h := ((((hasDerivAt_cexp_neg_mul_ofReal a t).mul hCi).add
      ((hasDerivAt_expIntE₁_mul hm ht).const_mul (1 / 2))).add
      ((hasDerivAt_expIntE₁_mul hp ht).const_mul (1 / 2))).const_mul (-(1 / a))
    refine h.congr_deriv ?_
    have : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
    rw [show -((a + -1 * I) * (t : ℂ)) = -(a * t) + t * I by ring,
      show -((a + 1 * I) * (t : ℂ)) = -(a * t) + -t * I by ring, exp_add, exp_add,
      show Complex.cos t = (cexp (t * I) + cexp (-t * I)) / 2 by rw [← two_cos]; ring]
    field_simp
    ring
  -- integrability
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := CinR) continuous_CinR.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
  have hγ : 0 < γ := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hint : IntegrableOn (fun t : ℝ => cexp (-(a * t)) * Ci t) (Ioi 0) := by
    refine integrableOn_Ioi_of_log_exp_bound (A := B + γ + 2) (B := 1) (c := a.re)
      (fun t ht => (((hasDerivAt_cexp_neg_mul_ofReal a t).mul
        (hasDerivAt_Ci (ofReal_mem_slitPlane_of_pos ht)).comp_ofReal).continuousAt
          ).continuousWithinAt)
      ha (fun t ht => ?_) (fun t ht => ?_)
    · rw [norm_mul, norm_cexp_neg_mul, Ci_ofReal ht.1, Complex.norm_real, Real.norm_eq_abs, CiR]
      have he : Real.exp (-(a.re * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [ht.1])
      have hc : |CinR t| ≤ B := by
        have := hB t ⟨ht.1.le, ht.2⟩; rwa [Real.norm_eq_abs] at this
      have : |-CinR t + Real.log t + γ| ≤ B + γ + |Real.log t| := by
        rw [abs_le] at hc ⊢
        constructor <;> linarith [le_abs_self (Real.log t), neg_abs_le (Real.log t)]
      calc Real.exp (-(a.re * t)) * |-CinR t + Real.log t + γ| ≤ 1 * (B + γ + |Real.log t|) :=
            mul_le_mul he this (abs_nonneg _) zero_le_one
        _ ≤ _ := by linarith
    · rw [norm_mul, norm_cexp_neg_mul, Ci_ofReal (by linarith), Complex.norm_real,
        Real.norm_eq_abs]
      have := (abs_CiR_siR_le_two ht.le).1
      calc Real.exp (-(a.re * t)) * |CiR t| ≤ Real.exp (-(a.re * t)) * 2 := by gcongr
        _ ≤ (B + γ + 2) * Real.exp (-a.re * t) := by
            rw [neg_mul]; nlinarith [Real.exp_pos (-(a.re * t))]
  -- the limits
  have hlog : log (a + -1 * I) + log (a + 1 * I) = log (1 + a ^ 2) := by
    have h1 := abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hm))
    have h2 := abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hp))
    rw [← log_mul (fun h => by rw [h] at hm; simp at hm) (fun h => by rw [h] at hp; simp at hp)
      ⟨by linarith, by linarith⟩]
    congr 1; linear_combination -I_sq
  have h0 : Tendsto Φ (𝓝[>] 0) (𝓝 (-(1 / a) * (γ + 1 / 2 * (-(γ : ℂ) - log (a + -1 * I)) +
      1 / 2 * (-(γ : ℂ) - log (a + 1 * I))))) := by
    have hC := tendsto_Ci_sub_log
    have hEm := tendsto_expIntE₁_mul_add_log hm
    have hEp := tendsto_expIntE₁_mul_add_log hp
    have hmul := tendsto_exp_sub_one_mul a (tendsto_mul_of_add_log hC)
    have := (((hmul.add hC).add (hEm.const_mul (1 / 2))).add (hEp.const_mul (1 / 2))).const_mul
      (-(1 / a))
    rw [zero_add] at this
    convert this using 2 with ε
    simp only [Φ]; ring
  have h1 : Tendsto Φ atTop (𝓝 0) := by
    have hCi : Tendsto (fun R : ℝ => cexp (-(a * R)) * Ci R) atTop (𝓝 0) := by
      have hl : Tendsto (fun R : ℝ => 2 * Real.exp (-a.re * R)) atTop (𝓝 0) := by
        simpa using (Real.tendsto_exp_atBot.comp
          (tendsto_id.const_mul_atTop_of_neg (by linarith : -a.re < 0))).const_mul 2
      refine squeeze_zero_norm' ?_ hl
      filter_upwards [eventually_ge_atTop 1] with R hR
      rw [norm_mul, norm_cexp_neg_mul, Ci_ofReal (by linarith), Complex.norm_real,
        Real.norm_eq_abs, neg_mul]
      nlinarith [(abs_CiR_siR_le_two hR).1, Real.exp_pos (-(a.re * R))]
    have := ((hCi.add ((tendsto_expIntE₁_mul_atTop hm).const_mul (1 / 2))).add
      ((tendsto_expIntE₁_mul_atTop hp).const_mul (1 / 2))).const_mul (-(1 / a))
    simp only [mul_zero, add_zero] at this
    exact this
  rw [integral_Ioi_zero_of_hasDerivAt hd hint h0 h1, ← hlog]
  field_simp
  ring

/-- For `ℜa > 0`: `arctan a = π/2 − (1/(2i))(ln(a + i) − ln(a − i))`. -/
theorem arctan_eq_of_re_pos {a : ℂ} (ha : 0 < a.re) :
    Complex.arctan a = π / 2 - 1 / (2 * I) * (log (a + 1 * I) - log (a + -1 * I)) := by
  have hm := re_add_I_pos ha (-1) (Or.inr rfl)
  have hp := re_add_I_pos ha 1 (Or.inl rfl)
  have hm0 : a + -1 * I ≠ 0 := fun h => by rw [h] at hm; simp at hm
  have hp0 : a + 1 * I ≠ 0 := fun h => by rw [h] at hp; simp at hp
  have h1 := abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hm))
  have h2 := abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hp))
  -- `arg(a − i) < arg(a + i)`
  have hlt : arg (a + -1 * I) < arg (a + 1 * I) := by
    refine (Real.strictMonoOn_tan.lt_iff_lt ⟨h1.1, h1.2⟩ ⟨h2.1, h2.2⟩).1 ?_
    rw [tan_arg, tan_arg]
    have e1 : (a + -1 * I).re = a.re := by simp
    have e2 : (a + 1 * I).re = a.re := by simp
    rw [e1, e2, div_lt_div_iff_of_pos_right ha]
    simp
  set L := log (a + -1 * I) - log (a + 1 * I) + π * I
  have hL : log ((1 + a * I) / (1 - a * I)) = L := by
    have hexp : cexp L = (1 + a * I) / (1 - a * I) := by
      simp only [L]
      rw [exp_add, exp_sub, exp_log hm0, exp_log hp0, exp_pi_mul_I]
      have h1a : 1 - a * I ≠ 0 := by
        intro h; apply hp0; linear_combination I * h + a * I_sq
      rw [mul_neg_one, ← neg_div, div_eq_div_iff hp0 h1a]
      linear_combination (-2 * a) * I_sq
    have him : L.im = arg (a + -1 * I) - arg (a + 1 * I) + π := by
      simp [L, log_im]
    rw [← hexp, log_exp (by rw [him]; linarith) (by rw [him]; linarith)]
  rw [Complex.arctan, hL]
  simp only [L]
  field_simp
  ring_nf
  linear_combination (-I * (π : ℂ) - (log (-I + a) - log (I + a))) * I_sq

/-- **DLMF 6.14.3**: `∫_0^∞ e^{−at} si(t) dt = −(1/a) arctan a`, `ℜa > 0`. -/
theorem dlmf_6_14_3 {a : ℂ} (ha : 0 < a.re) :
    ∫ t in Ioi (0 : ℝ), cexp (-(a * t)) * si t = -(1 / a) * Complex.arctan a := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hm := re_add_I_pos ha (-1) (Or.inr rfl)
  have hp := re_add_I_pos ha 1 (Or.inl rfl)
  set Φ : ℝ → ℂ := fun t => -(1 / a) * (cexp (-(a * t)) * si t +
    1 / (2 * I) * (expIntE₁ ((a + -1 * I) * t) - expIntE₁ ((a + 1 * I) * t)))
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt Φ (cexp (-(a * t)) * si t) t := by
    intro t ht
    have hsi := (hasDerivAt_si (t : ℂ)).comp_ofReal
    have h := (((hasDerivAt_cexp_neg_mul_ofReal a t).mul hsi).add
      (((hasDerivAt_expIntE₁_mul hm ht).sub (hasDerivAt_expIntE₁_mul hp ht)).const_mul
        (1 / (2 * I)))).const_mul (-(1 / a))
    refine h.congr_deriv ?_
    have : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
    rw [sincC_of_ne this, show -((a + -1 * I) * (t : ℂ)) = -(a * t) + t * I by ring,
      show -((a + 1 * I) * (t : ℂ)) = -(a * t) + -t * I by ring, exp_add, exp_add,
      show Complex.sin t = (cexp (-t * I) - cexp (t * I)) * I / 2 by rw [← two_sin]; ring]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  -- integrability
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := SiR) continuous_SiR.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
  have hint : IntegrableOn (fun t : ℝ => cexp (-(a * t)) * si t) (Ioi 0) := by
    refine integrableOn_Ioi_of_log_exp_bound (A := B + π / 2 + 2) (B := 0) (c := a.re)
      (fun t ht => (((hasDerivAt_cexp_neg_mul_ofReal a t).mul
        (hasDerivAt_si (t : ℂ)).comp_ofReal).continuousAt).continuousWithinAt)
      ha (fun t ht => ?_) (fun t ht => ?_)
    · rw [norm_mul, norm_cexp_neg_mul, si_ofReal, Complex.norm_real, Real.norm_eq_abs]
      have he : Real.exp (-(a.re * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [ht.1])
      have hs : |SiR t| ≤ B := by
        have := hB t ⟨ht.1.le, ht.2⟩; rwa [Real.norm_eq_abs] at this
      have : |SiR t - π / 2| ≤ B + π / 2 + 2 := by
        rw [abs_le] at hs ⊢; constructor <;> linarith [Real.pi_pos]
      calc Real.exp (-(a.re * t)) * |SiR t - π / 2| ≤ 1 * (B + π / 2 + 2) :=
            mul_le_mul he this (abs_nonneg _) zero_le_one
        _ = _ := by ring
    · rw [norm_mul, norm_cexp_neg_mul, si_ofReal, Complex.norm_real, Real.norm_eq_abs]
      have := (abs_CiR_siR_le_two ht.le).2
      have hπ := Real.pi_pos
      calc Real.exp (-(a.re * t)) * |SiR t - π / 2| ≤ Real.exp (-(a.re * t)) * 2 := by gcongr
        _ ≤ (B + π / 2 + 2) * Real.exp (-a.re * t) := by
            rw [neg_mul]; nlinarith [Real.exp_pos (-(a.re * t))]
  -- the limits
  have h0 : Tendsto Φ (𝓝[>] 0) (𝓝 (-(1 / a) * (1 * si 0 +
      1 / (2 * I) * ((-(γ : ℂ) - log (a + -1 * I)) - (-(γ : ℂ) - log (a + 1 * I)))))) := by
    have hsi : Tendsto (fun ε : ℝ => si ε) (𝓝[>] 0) (𝓝 (si 0)) := by
      have := ((differentiable_si.continuous.comp continuous_ofReal).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa [Function.comp_def] using this
    have hexp : Tendsto (fun ε : ℝ => cexp (-(a * ε))) (𝓝[>] 0) (𝓝 1) := by
      have : Continuous fun ε : ℝ => cexp (-(a * ε)) := by fun_prop
      simpa using (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have hEm := tendsto_expIntE₁_mul_add_log hm
    have hEp := tendsto_expIntE₁_mul_add_log hp
    have := ((hexp.mul hsi).add ((hEm.sub hEp).const_mul (1 / (2 * I)))).const_mul (-(1 / a))
    convert this using 2 with ε
    simp only [Φ]; ring
  have h1 : Tendsto Φ atTop (𝓝 0) := by
    have hsi : Tendsto (fun R : ℝ => cexp (-(a * R)) * si R) atTop (𝓝 0) := by
      have hl : Tendsto (fun R : ℝ => 2 * Real.exp (-a.re * R)) atTop (𝓝 0) := by
        simpa using (Real.tendsto_exp_atBot.comp
          (tendsto_id.const_mul_atTop_of_neg (by linarith : -a.re < 0))).const_mul 2
      refine squeeze_zero_norm' ?_ hl
      filter_upwards [eventually_ge_atTop 1] with R hR
      rw [norm_mul, norm_cexp_neg_mul, si_ofReal, Complex.norm_real, Real.norm_eq_abs, neg_mul]
      nlinarith [(abs_CiR_siR_le_two hR).2, Real.exp_pos (-(a.re * R))]
    have := (hsi.add (((tendsto_expIntE₁_mul_atTop hm).sub
      (tendsto_expIntE₁_mul_atTop hp)).const_mul (1 / (2 * I)))).const_mul (-(1 / a))
    simp only [sub_zero, mul_zero, add_zero] at this
    exact this
  have hsi0 : si 0 = -(π / 2 : ℂ) := by
    have := si_ofReal 0
    rw [ofReal_zero] at this
    rw [this, SiR_zero]; push_cast; ring
  rw [integral_Ioi_zero_of_hasDerivAt hd hint h0 h1, arctan_eq_of_re_pos ha, hsi0]
  ring

end Azurite.DLMF
