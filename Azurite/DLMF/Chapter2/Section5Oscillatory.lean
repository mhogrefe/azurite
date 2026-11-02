/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section5Continuation

/-!
# DLMF §2.5(ii), 2.5.27 for `κ ≠ 0`: `𝓜h₂` continues to an entire function

When `κ ≠ 0` in 2.5.18, `h(t) ∼ e^{iκt^p} ∑ bₛ t^{−βₛ}` as `t → +∞`, the oscillatory terms
`∫₁^∞ t^{z−1−βₛ} e^{iκt^p} dt` (`oscInt κ p (z − 1 − βₛ)`, convergent for `ℜz < ℜβₛ`) continue to
entire functions: integrating by parts against `e^{iκt^p} = (iκp t^{p−1})⁻¹ (e^{iκt^p})'`,

`∫₁^∞ t^w e^{iκt^p} dt = −e^{iκ}/(iκp) − ((w − p + 1)/(iκp)) ∫₁^∞ t^{w−p} e^{iκt^p} dt`

(`oscInt_eq_succ`), and the right side is analytic on the larger half-plane `ℜw < p − 1`;
iterating (`oscExt`) and gluing (`oscEntire`) gives the entire continuation
(`differentiable_oscEntire`, `oscEntire_eq`). With the remainder
`(h − ∑_{s<N} bₛ e^{iκt^p} t^{−βₛ})` on `(1, ∞)`, whose transform is analytic for `ℜz < ℜβ_N`,
`𝓜h₂(z) = ∑_{s<N} bₛ oscInt(z − 1 − βₛ) + 𝓜(remainder)(z)` continues to all of `ℂ`
(`mellinTrunc₂Cont`, **`dlmf_2_5_27_ne`**).
-/

open MeasureTheory Filter Topology Set Complex Asymptotics
open scoped Real

namespace Azurite.DLMF

/-! ### The phase `e^{iκt^p}` and the oscillatory integral -/

/-- `e^{iκt^p}` as a function of the real variable `t`. -/
noncomputable def oscPhase (κ p : ℝ) (t : ℝ) : ℂ := cexp (I * κ * ((t ^ p : ℝ) : ℂ))

theorem norm_oscPhase (κ p t : ℝ) : ‖oscPhase κ p t‖ = 1 := by
  rw [oscPhase, norm_exp]
  simp

theorem continuous_oscPhase {p : ℝ} (κ : ℝ) (hp : 0 < p) : Continuous (oscPhase κ p) :=
  Complex.continuous_exp.comp
    (continuous_const.mul (continuous_ofReal.comp (Real.continuous_rpow_const hp.le)))

theorem hasDerivAt_oscPhase (κ p : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (oscPhase κ p) (oscPhase κ p t * (I * κ * ((p * t ^ (p - 1) : ℝ) : ℂ))) t :=
  ((Real.hasDerivAt_rpow_const (Or.inl ht.ne')).ofReal_comp.const_mul (I * κ)).cexp

/-- `∫₁^∞ t^w e^{iκt^p} dt`, absolutely convergent for `ℜw < −1`. -/
noncomputable def oscInt (κ p : ℝ) (w : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ w * oscPhase κ p t

theorem continuousOn_cpow_mul_oscPhase {p : ℝ} (κ : ℝ) (hp : 0 < p) (w : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ w * oscPhase κ p t) (Ioi 0) :=
  (continuousOn_ofReal_cpow_Ioi w).mul (continuous_oscPhase κ hp).continuousOn

theorem integrableOn_cpow_mul_oscPhase {p : ℝ} (κ : ℝ) (hp : 0 < p) {w : ℂ} (hw : w.re < -1) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ w * oscPhase κ p t) (Ioi 1) := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ w.re) (Ioi 1) :=
    (integrableOn_Ioi_rpow_iff zero_lt_one).mpr hw
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ w * oscPhase κ p t)
      (volume.restrict (Ioi 1)) :=
    ((continuousOn_cpow_mul_oscPhase κ hp w).mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi
  refine Integrable.mono' h1 hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : (1 : ℝ) < t := ht
  rw [norm_mul, norm_oscPhase, mul_one, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht1)]

/-- `t^{w−p+1} · t^{p−1} = t^w` for `t > 0`. -/
theorem cpow_mul_ofReal_rpow {t : ℝ} (ht : 0 < t) (w : ℂ) (p : ℝ) :
    (t : ℂ) ^ (w - p + 1) * ((t ^ (p - 1) : ℝ) : ℂ) = (t : ℂ) ^ w := by
  rw [ofReal_cpow ht.le, ← cpow_add _ _ (ofReal_ne_zero.mpr ht.ne')]
  congr 1
  push_cast
  ring

/-- `oscInt` as a Mellin transform: `∫₁^∞ t^w e^{iκt^p} dt = 𝓜(1_{(1,∞)} e^{iκt^p})(w + 1)`. -/
theorem oscInt_eq_mellin (κ p : ℝ) (w : ℂ) :
    oscInt κ p w = mellin ((Ioi 1).indicator (oscPhase κ p)) (w + 1) := by
  simp only [oscInt, mellin, add_sub_cancel_right]
  have : ∀ t : ℝ, (t : ℂ) ^ w • (Ioi 1).indicator (oscPhase κ p) t =
      (Ioi 1).indicator (fun t : ℝ => (t : ℂ) ^ w * oscPhase κ p t) t := fun t => by
    by_cases ht : t ∈ Ioi 1 <;> simp [indicator, ht]
  simp_rw [this]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one]

/-- A locally integrable function stays locally integrable after multiplication by an indicator. -/
theorem LocallyIntegrableOn.indicator' {f : ℝ → ℂ} {s t : Set ℝ} (hf : LocallyIntegrableOn f s)
    (ht : MeasurableSet t) : LocallyIntegrableOn (t.indicator f) s := fun x hx =>
  let ⟨u, hu, hint⟩ := hf x hx
  ⟨u, hu, hint.indicator ht⟩

/-- The indicator of `(1, ∞)` kills the `0+` behaviour. -/
theorem indicator_Ioi_one_isBigO_zero (g : ℝ → ℂ) (b : ℝ) :
    (Ioi 1).indicator g =O[𝓝[>] 0] (· ^ (-b)) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  rw [indicator_of_notMem (s := Ioi 1) (not_lt.mpr ht.2.le)]
  simp

theorem differentiableOn_oscInt {p : ℝ} (κ : ℝ) (hp : 0 < p) :
    DifferentiableOn ℂ (oscInt κ p) {w | w.re < -1} := by
  set F : ℝ → ℂ := (Ioi 1).indicator (oscPhase κ p) with hF
  rw [show oscInt κ p = fun w => mellin F (w + 1) from funext (oscInt_eq_mellin κ p)]
  intro w hw
  have hw : w.re < -1 := hw
  have hFtop : F =O[atTop] (· ^ (-(0 : ℝ))) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 1] with t ht
    rw [hF, indicator_of_mem (mem_Ioi.mpr ht), norm_oscPhase, neg_zero, Real.rpow_zero, norm_one,
      mul_one]
  have h1 : DifferentiableAt ℂ (mellin F) (w + 1) :=
    mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := w.re)
      (LocallyIntegrableOn.indicator'
        ((continuous_oscPhase κ hp).locallyIntegrable.locallyIntegrableOn _) measurableSet_Ioi)
      hFtop (by simp; linarith) (indicator_Ioi_one_isBigO_zero _ _) (by simp)
  exact (h1.comp w (differentiableAt_id.add_const 1)).differentiableWithinAt

/-! ### Integration by parts -/

/-- **Integration by parts** for the oscillatory integral, `ℜw < −1`, `κ ≠ 0`, `p > 0`:
`∫₁^∞ t^w e^{iκt^p} dt = −e^{iκ}/(iκp) − ((w − p + 1)/(iκp)) ∫₁^∞ t^{w−p} e^{iκt^p} dt`. -/
theorem oscInt_eq_succ {κ p : ℝ} (hκ : κ ≠ 0) (hp : 0 < p) {w : ℂ} (hw : w.re < -1) :
    oscInt κ p w = -(cexp (I * κ) / (I * κ * p)) -
      (w - p + 1) / (I * κ * p) * oscInt κ p (w - p) := by
  set c : ℂ := I * κ * p with hc
  have hc0 : c ≠ 0 := by
    simp only [hc]
    exact mul_ne_zero (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hκ)) (ofReal_ne_zero.mpr hp.ne')
  have hr : w - p + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hw' : (w - p).re < -1 := by simp; linarith
  -- the parts
  set u : ℝ → ℂ := fun t => (t : ℂ) ^ (w - p + 1) / c with hu
  set u' : ℝ → ℂ := fun t => (w - p + 1) * (t : ℂ) ^ (w - p) / c with hu'
  set v' : ℝ → ℂ := fun t => oscPhase κ p t * (I * κ * ((p * t ^ (p - 1) : ℝ) : ℂ)) with hv'
  have hud : ∀ t ∈ Ioi (1 : ℝ), HasDerivAt u (u' t) t := fun t ht => by
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    have := (hasDerivAt_ofReal_cpow_const ht0.ne' hr).div_const c
    simp only [hu, hu']
    convert this using 2
    ring_nf
  have hvd : ∀ t ∈ Ioi (1 : ℝ), HasDerivAt (oscPhase κ p) (v' t) t := fun t ht =>
    hasDerivAt_oscPhase κ p (zero_lt_one.trans ht)
  -- `u v' = t^w e^{iκt^p}` and `u' v = ((w−p+1)/c) t^{w−p} e^{iκt^p}`
  have huv' : ∀ t ∈ Ioi (1 : ℝ), u t * v' t = (t : ℂ) ^ w * oscPhase κ p t := fun t ht => by
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    simp only [hu, hv', hc]
    rw [← cpow_mul_ofReal_rpow ht0 w p]
    have hκ' : (κ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hκ
    have hp' : (p : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
    push_cast
    field_simp
  have hu'v : ∀ t ∈ Ioi (1 : ℝ), u' t * oscPhase κ p t =
      (w - p + 1) / c * ((t : ℂ) ^ (w - p) * oscPhase κ p t) := fun t _ => by
    simp only [hu']
    ring
  have hint1 : IntegrableOn (u * v') (Ioi 1) :=
    (integrableOn_cpow_mul_oscPhase κ hp hw).congr_fun (fun t ht => (huv' t ht).symm)
      measurableSet_Ioi
  have hint2 : IntegrableOn (u' * oscPhase κ p) (Ioi 1) :=
    IntegrableOn.congr_fun ((integrableOn_cpow_mul_oscPhase κ hp hw').const_mul ((w - p + 1) / c))
      (fun t ht => (hu'v t ht).symm) measurableSet_Ioi
  -- the boundary terms
  have hzero : Tendsto (u * oscPhase κ p) (𝓝[>] 1) (𝓝 (u 1 * oscPhase κ p 1)) := by
    have h1 : HasDerivAt u (u' 1) 1 := by
      have := (hasDerivAt_ofReal_cpow_const one_ne_zero hr).div_const c
      simp only [hu, hu']
      convert this using 2
      ring_nf
    exact ((h1.continuousAt.mul
      (hasDerivAt_oscPhase κ p zero_lt_one).continuousAt).tendsto).mono_left nhdsWithin_le_nhds
  have hinfty : Tendsto (u * oscPhase κ p) atTop (𝓝 0) := by
    have hy : 0 < -(w.re - p + 1) := by linarith
    have hlim : Tendsto (fun t : ℝ => t ^ (-(-(w.re - p + 1))) / ‖c‖) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop hy).div_const ‖c‖
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Pi.mul_apply, hu, norm_mul, norm_oscPhase, mul_one, norm_div,
      norm_cpow_eq_rpow_re_of_pos ht, neg_neg]
    simp
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hud hvd hint1 hint2 hzero hinfty
  -- assemble
  have hl : (∫ t in Ioi (1 : ℝ), u t * v' t) = oscInt κ p w :=
    setIntegral_congr_fun measurableSet_Ioi huv'
  have hr' : (∫ t in Ioi (1 : ℝ), u' t * oscPhase κ p t) =
      (w - p + 1) / c * oscInt κ p (w - p) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hu'v, integral_const_mul]
    rfl
  rw [hl, hr'] at key
  rw [key]
  simp only [hu, oscPhase, ofReal_one, Real.one_rpow, one_cpow, mul_one]
  ring

/-! ### The entire continuation of `oscInt` -/

/-- The `k`-fold integration by parts of `oscInt`: analytic on `ℜw < kp − 1`. -/
noncomputable def oscExt (κ p : ℝ) : ℕ → ℂ → ℂ
  | 0, w => oscInt κ p w
  | k + 1, w => -(cexp (I * κ) / (I * κ * p)) - (w - p + 1) / (I * κ * p) * oscExt κ p k (w - p)

/-- The half-plane `ℜw < kp − 1`. -/
def oscDomain (p : ℝ) (k : ℕ) : Set ℂ := {w | w.re < k * p - 1}

theorem isOpen_oscDomain (p : ℝ) (k : ℕ) : IsOpen (oscDomain p k) :=
  isOpen_lt continuous_re continuous_const

theorem oscDomain_mono {p : ℝ} (hp : 0 < p) : Monotone (oscDomain p) :=
  monotone_nat_of_le_succ fun k w hw => by
    show w.re < (k + 1 : ℕ) * p - 1
    have : w.re < k * p - 1 := hw
    push_cast
    nlinarith

theorem differentiableOn_oscExt {κ p : ℝ} (hp : 0 < p) (k : ℕ) :
    DifferentiableOn ℂ (oscExt κ p k) (oscDomain p k) := by
  induction k with
  | zero =>
    have : oscDomain p 0 = {w | w.re < -1} := by
      ext w
      simp [oscDomain]
    rw [this]
    exact differentiableOn_oscInt κ hp
  | succ k ih =>
    intro w hw
    have hw' : w - p ∈ oscDomain p k := by
      show (w - p).re < k * p - 1
      have : w.re < (k + 1 : ℕ) * p - 1 := hw
      push_cast at this
      simp
      linarith
    refine DifferentiableWithinAt.sub (differentiableWithinAt_const _) (DifferentiableWithinAt.mul
      ((differentiableWithinAt_id.sub_const _).add_const _ |>.div_const _) ?_)
    exact (ih (w - p) hw').comp w ((differentiableWithinAt_id.sub_const _))
      fun z hz => by
        show (z - p).re < k * p - 1
        have : z.re < (k + 1 : ℕ) * p - 1 := hz
        push_cast at this
        simp
        linarith

theorem oscExt_succ {κ p : ℝ} (hκ : κ ≠ 0) (hp : 0 < p) (k : ℕ) {w : ℂ}
    (hw : w ∈ oscDomain p k) : oscExt κ p (k + 1) w = oscExt κ p k w := by
  induction k generalizing w with
  | zero =>
    have hw' : w.re < -1 := by simpa [oscDomain] using hw
    exact (oscInt_eq_succ hκ hp hw').symm
  | succ k ih =>
    have hw' : w - p ∈ oscDomain p k := by
      show (w - p).re < k * p - 1
      have : w.re < (k + 1 : ℕ) * p - 1 := hw
      push_cast at this
      simp
      linarith
    show -(cexp (I * κ) / (I * κ * p)) - (w - p + 1) / (I * κ * p) * oscExt κ p (k + 1) (w - p) =
      -(cexp (I * κ) / (I * κ * p)) - (w - p + 1) / (I * κ * p) * oscExt κ p k (w - p)
    rw [ih hw']

/-- The entire continuation of `w ↦ ∫₁^∞ t^w e^{iκt^p} dt`. -/
noncomputable def oscEntire (κ p : ℝ) : ℂ → ℂ := glue (oscDomain p) (oscExt κ p)

theorem differentiable_oscEntire {κ p : ℝ} (hκ : κ ≠ 0) (hp : 0 < p) :
    Differentiable ℂ (oscEntire κ p) := by
  intro w
  obtain ⟨k, hk⟩ := exists_nat_gt ((w.re + 1) / p)
  have hw : w ∈ oscDomain p k := by
    show w.re < k * p - 1
    rw [div_lt_iff₀ hp] at hk
    linarith
  exact differentiableAt_glue (oscDomain_mono hp) (fun k w hw => oscExt_succ hκ hp k hw)
    (isOpen_oscDomain p) (differentiableOn_oscExt hp) hw

theorem oscEntire_eq {κ p : ℝ} (hκ : κ ≠ 0) (hp : 0 < p) {w : ℂ} (hw : w.re < -1) :
    oscEntire κ p w = oscInt κ p w :=
  glue_eq (oscDomain_mono hp) (fun k w hw => oscExt_succ hκ hp k hw) (N := 0)
    (by simpa [oscDomain] using hw)

theorem oscEntire_eq_oscExt {κ p : ℝ} (hκ : κ ≠ 0) (hp : 0 < p) {k : ℕ} {w : ℂ}
    (hw : w.re < k * p - 1) : oscEntire κ p w = oscExt κ p k w :=
  glue_eq (oscDomain_mono hp) (fun k _ hw => oscExt_succ hκ hp k hw) (N := k) hw

/-! ### The continuation of `𝓜h₂` -/

/-- One oscillatory term `e^{iκt^p} t^{−β}` of 2.5.18, on `(1, ∞)`. -/
noncomputable def oscTerm (κ p : ℝ) (β : ℂ) : ℝ → ℂ :=
  (Ioi 1).indicator fun t => oscPhase κ p t * (t : ℂ) ^ (-β)

/-- The remainder `h − ∑_{s<N} bₛ e^{iκt^p} t^{−βₛ}` of 2.5.18, on `(1, ∞)`. -/
noncomputable def oscRem (h : ℝ → ℂ) (bs β : ℕ → ℂ) (κ p : ℝ) (N : ℕ) : ℝ → ℂ :=
  (Ioi 1).indicator fun t => h t - ∑ s ∈ Finset.range N, bs s * oscPhase κ p t * (t : ℂ) ^ (-β s)

section Terms

variable {κ p : ℝ} (hp : 0 < p)
include hp

omit hp in
theorem oscTerm_isBigO_atTop (κ : ℝ) (β : ℂ) : oscTerm κ p β =O[atTop] (· ^ (-β.re)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
  rw [oscTerm, indicator_of_mem (mem_Ioi.mpr ht), norm_mul, norm_oscPhase, one_mul,
    norm_cpow_eq_rpow_re_of_pos ht0, neg_re, one_mul,
    Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]

theorem locallyIntegrableOn_oscTerm (κ : ℝ) (β : ℂ) :
    LocallyIntegrableOn (oscTerm κ p β) (Ioi 0) :=
  LocallyIntegrableOn.indicator' (((continuous_oscPhase κ hp).continuousOn.mul
    (continuousOn_ofReal_cpow_Ioi (-β))).locallyIntegrableOn measurableSet_Ioi) measurableSet_Ioi

theorem mellinConvergent_oscTerm (κ : ℝ) {β z : ℂ} (hz : z.re < β.re) :
    MellinConvergent (oscTerm κ p β) z :=
  mellinConvergent_of_isBigO_rpow (a := β.re) (b := z.re - 1) (locallyIntegrableOn_oscTerm hp κ β)
    (oscTerm_isBigO_atTop κ β) hz (indicator_Ioi_one_isBigO_zero _ _) (by linarith)

omit hp in
/-- `𝓜(e^{iκt^p} t^{−β} 1_{(1,∞)})(z) = ∫₁^∞ t^{z−1−β} e^{iκt^p} dt`. -/
theorem mellin_oscTerm (κ : ℝ) (β z : ℂ) : mellin (oscTerm κ p β) z = oscInt κ p (z - 1 - β) := by
  simp only [mellin, oscTerm, oscInt]
  have : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (z - 1) •
      (Ioi 1).indicator (fun t : ℝ => oscPhase κ p t * (t : ℂ) ^ (-β)) t =
      (Ioi 1).indicator (fun t : ℝ => (t : ℂ) ^ (z - 1 - β) * oscPhase κ p t) t := fun t ht => by
    have ht0 : (0 : ℝ) < t := ht
    by_cases h1 : t ∈ Ioi 1
    · simp only [indicator_of_mem h1, smul_eq_mul]
      rw [show z - 1 - β = z - 1 + -β by ring, cpow_add _ _ (ofReal_ne_zero.mpr ht0.ne')]
      ring
    · simp [indicator_of_notMem h1]
  rw [setIntegral_congr_fun measurableSet_Ioi this, setIntegral_indicator measurableSet_Ioi,
    Ioi_inter_Ioi, max_eq_right zero_le_one]

variable {h : ℝ → ℂ} {bs β : ℕ → ℂ}

theorem continuousOn_oscSum (κ : ℝ) (bs β : ℕ → ℂ) (N : ℕ) :
    ContinuousOn (fun t : ℝ => ∑ s ∈ Finset.range N, bs s * oscPhase κ p t * (t : ℂ) ^ (-β s))
      (Ioi 0) :=
  continuousOn_finsetSum _ fun _ _ =>
    (continuousOn_const.mul (continuous_oscPhase κ hp).continuousOn).mul
      (continuousOn_ofReal_cpow_Ioi _)

theorem locallyIntegrableOn_oscRem (hloc : LocallyIntegrableOn h (Ioi 0)) (N : ℕ) :
    LocallyIntegrableOn (oscRem h bs β κ p N) (Ioi 0) :=
  LocallyIntegrableOn.indicator'
    (hloc.sub ((continuousOn_oscSum hp κ bs β N).locallyIntegrableOn measurableSet_Ioi))
    measurableSet_Ioi

omit hp in
theorem oscRem_isBigO_atTop
    (hh : IsGenAsympExpansionDLMF atTop (fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ (-β s)) h
      fun s t => bs s * oscPhase κ p t * (t : ℂ) ^ (-β s)) (N : ℕ) :
    oscRem h bs β κ p N =O[atTop] (· ^ (-(β N).re)) := by
  refine (isBigO_rpow_re_of_isBigODLMF_cpow_top (hh.2 N)).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 1] with t ht
  rw [oscRem, indicator_of_mem (mem_Ioi.mpr ht)]

variable (hh : IsGenAsympExpansionDLMF atTop (fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ (-β s)) h
      fun s t => bs s * oscPhase κ p t * (t : ℂ) ^ (-β s))
include hh

theorem mellinConvergent_oscRem (hloc : LocallyIntegrableOn h (Ioi 0)) {N : ℕ} {z : ℂ}
    (hz : z.re < (β N).re) : MellinConvergent (oscRem h bs β κ p N) z :=
  mellinConvergent_of_isBigO_rpow (a := (β N).re) (b := z.re - 1)
    (locallyIntegrableOn_oscRem hp hloc N) (oscRem_isBigO_atTop hh N) hz
    (indicator_Ioi_one_isBigO_zero _ _) (by linarith)

theorem differentiableAt_mellin_oscRem (hloc : LocallyIntegrableOn h (Ioi 0)) {N : ℕ} {z : ℂ}
    (hz : z.re < (β N).re) : DifferentiableAt ℂ (mellin (oscRem h bs β κ p N)) z :=
  mellin_differentiableAt_of_isBigO_rpow (a := (β N).re) (b := z.re - 1)
    (locallyIntegrableOn_oscRem hp hloc N) (oscRem_isBigO_atTop hh N) hz
    (indicator_Ioi_one_isBigO_zero _ _) (by linarith)

/-- One step: for `ℜz < ℜβ_N`, `𝓜r_N(z) = b_N 𝓜(e^{iκt^p} t^{−β_N} 1_{(1,∞)})(z) + 𝓜r_{N+1}(z)`. -/
theorem mellin_oscRem_succ (hβ : StrictMono fun s => (β s).re)
    (hloc : LocallyIntegrableOn h (Ioi 0)) {N : ℕ} {z : ℂ} (hz : z.re < (β N).re) :
    mellin (oscRem h bs β κ p N) z =
      bs N * mellin (oscTerm κ p (β N)) z + mellin (oscRem h bs β κ p (N + 1)) z := by
  have h1 : MellinConvergent (fun t => bs N • oscTerm κ p (β N) t) z :=
    (mellinConvergent_oscTerm hp κ hz).const_smul (bs N)
  have h2 : MellinConvergent (oscRem h bs β κ p (N + 1)) z :=
    mellinConvergent_oscRem hp hh hloc (hz.trans (hβ (Nat.lt_succ_self N)))
  have hsplit : oscRem h bs β κ p N = fun t => bs N • oscTerm κ p (β N) t +
      oscRem h bs β κ p (N + 1) t := by
    ext t
    by_cases ht : t ∈ Ioi 1
    · simp only [oscRem, oscTerm, indicator_of_mem ht, Finset.sum_range_succ, smul_eq_mul]
      ring
    · simp only [oscRem, oscTerm, indicator_of_notMem ht, smul_zero, add_zero]
  have := hasMellin_add h1 h2
  rw [← hsplit, mellin_const_smul] at this
  rw [this.2, smul_eq_mul]

end Terms

/-- The `N`-th piece of the continuation of `𝓜h₂`:
`∑_{s<N} bₛ · (entire continuation of ∫₁^∞ t^{z−1−βₛ} e^{iκt^p} dt) + 𝓜r_N(z)`. -/
noncomputable def mellinTrunc₂Ext (h : ℝ → ℂ) (bs β : ℕ → ℂ) (κ p : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ s ∈ Finset.range N, bs s * oscEntire κ p (z - 1 - β s) + mellin (oscRem h bs β κ p N) z

/-- **DLMF 2.5.27**, `κ ≠ 0`: the entire continuation of `𝓜h₂`. -/
noncomputable def mellinTrunc₂Cont (h : ℝ → ℂ) (bs β : ℕ → ℂ) (κ p : ℝ) : ℂ → ℂ :=
  glue (fun N => {z | z.re < (β N).re}) (mellinTrunc₂Ext h bs β κ p)

section Cont

variable {h : ℝ → ℂ} {bs β : ℕ → ℂ} {κ p : ℝ} (hκ : κ ≠ 0) (hp : 0 < p)
  (hβ : StrictMono fun s => (β s).re) (hloc : LocallyIntegrableOn h (Ioi 0))
  (hh : IsGenAsympExpansionDLMF atTop (fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ (-β s)) h
    fun s t => bs s * oscPhase κ p t * (t : ℂ) ^ (-β s))
include hκ hp hβ hloc hh

theorem mellinTrunc₂Ext_succ {N : ℕ} {z : ℂ} (hz : z.re < (β N).re) :
    mellinTrunc₂Ext h bs β κ p (N + 1) z = mellinTrunc₂Ext h bs β κ p N z := by
  simp only [mellinTrunc₂Ext, Finset.sum_range_succ]
  rw [mellin_oscRem_succ hp hh hβ hloc hz, mellin_oscTerm, oscEntire_eq hκ hp (by simp; linarith)]
  ring

omit hβ in
theorem differentiableOn_mellinTrunc₂Ext (N : ℕ) :
    DifferentiableOn ℂ (mellinTrunc₂Ext h bs β κ p N) {z | z.re < (β N).re} := fun z hz =>
  DifferentiableAt.differentiableWithinAt (DifferentiableAt.add
    (DifferentiableAt.fun_sum fun _ _ => (differentiableAt_const _).mul
      ((differentiable_oscEntire hκ hp _).comp z
        ((differentiableAt_id.sub_const _).sub_const _)))
    (differentiableAt_mellin_oscRem hp hh hloc hz))

omit hκ hp hβ hloc hh in
theorem mellin_trunc₂_eq_oscRem_zero (h : ℝ → ℂ) (bs β : ℕ → ℂ) (κ p : ℝ) (z : ℂ) :
    mellin (trunc₂ h) z = mellin (oscRem h bs β κ p 0) z := by
  refine mellin_congr_ae ?_ z
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [trunc₂_eq_indicator ht]
  simp [oscRem]

theorem mellinTrunc₂Cont_eq {N : ℕ} {z : ℂ} (hz : z.re < (β N).re) :
    mellinTrunc₂Cont h bs β κ p z = mellinTrunc₂Ext h bs β κ p N z := by
  have hmono : Monotone fun N => {z : ℂ | z.re < (β N).re} :=
    monotone_nat_of_le_succ fun N z hz => lt_trans hz (hβ (Nat.lt_succ_self N))
  have hcompat : ∀ N, ∀ z ∈ {z : ℂ | z.re < (β N).re},
      mellinTrunc₂Ext h bs β κ p (N + 1) z = mellinTrunc₂Ext h bs β κ p N z :=
    fun _ _ hz => mellinTrunc₂Ext_succ hκ hp hβ hloc hh hz
  exact glue_eq hmono hcompat (N := N) hz

/-- **DLMF 2.5.27** for `κ ≠ 0`: `𝓜h₂(z)` can be continued analytically to an entire function,
`mellinTrunc₂Cont h bs β κ p`, which agrees with `𝓜h₂` on `ℜz < ℜβ₀` (Table 2.5.1). -/
theorem dlmf_2_5_27_ne (hβ' : Tendsto (fun s => (β s).re) atTop atTop) :
    Differentiable ℂ (mellinTrunc₂Cont h bs β κ p) ∧
      ∀ z : ℂ, z.re < (β 0).re → mellinTrunc₂Cont h bs β κ p z = mellin (trunc₂ h) z := by
  have hmono : Monotone fun N => {z : ℂ | z.re < (β N).re} :=
    monotone_nat_of_le_succ fun N z hz => lt_trans hz (hβ (Nat.lt_succ_self N))
  have hcompat : ∀ N, ∀ z ∈ {z : ℂ | z.re < (β N).re},
      mellinTrunc₂Ext h bs β κ p (N + 1) z = mellinTrunc₂Ext h bs β κ p N z :=
    fun _ _ hz => mellinTrunc₂Ext_succ hκ hp hβ hloc hh hz
  refine ⟨fun z => ?_, fun z hz => ?_⟩
  · obtain ⟨N, hN⟩ := (hβ'.eventually_gt_atTop z.re).exists
    exact differentiableAt_glue hmono hcompat (fun _ => isOpen_lt continuous_re continuous_const)
      (differentiableOn_mellinTrunc₂Ext hκ hp hloc hh) (N := N) hN
  · rw [mellinTrunc₂Cont, glue_eq hmono hcompat (N := 0) hz, mellinTrunc₂Ext,
      Finset.sum_range_zero, zero_add, mellin_trunc₂_eq_oscRem_zero]

end Cont

/-- **DLMF 2.5.27**, both cases: under the hypotheses of §2.5(ii), `𝓜h₂` continues analytically
to a function on `ℂ` analytic off `{βₛ}` (and entire when `κ ≠ 0`), agreeing with `𝓜h₂` on
`ℜz < ℜβ₀`. -/
theorem HandelsmanLewSetup.exists_mellinTrunc₂_cont {f h : ℝ → ℂ} {a α bs β : ℕ → ℂ} {κ p b c : ℝ}
    (H : HandelsmanLewSetup f h a α bs β κ p b c) :
    ∃ G : ℂ → ℂ, (∀ z : ℂ, z.re < (β 0).re → G z = mellin (trunc₂ h) z) ∧
      ∀ z : ℂ, (∀ s, z ≠ β s) → DifferentiableAt ℂ G z := by
  by_cases hκ : κ = 0
  · have hexp := H.h_exp
    subst hκ
    simp only [ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one] at hexp
    obtain ⟨G, h1, h2, -⟩ := dlmf_2_5_27_zero H.h_loc H.β_mono H.β_tendsto hexp
    exact ⟨G, h1, h2⟩
  · obtain ⟨h1, h2⟩ := dlmf_2_5_27_ne hκ H.p_pos H.β_mono H.h_loc H.h_exp H.β_tendsto
    exact ⟨_, h2, fun z _ => h1 z⟩

end Azurite.DLMF
