/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# DLMF §4.13: an auxiliary real function for the Wright `ω`-function

For `y` in the upper half-plane write `y = ρ e^{iα}` (`0 < α < π`). Then `y + ln y = a + ib` iff
`ρ sin α + α = b` and `ρ cos α + ln ρ = a`, i.e. `ρ = (b − α)/sin α` and `omegaG b α = a`, where

`omegaG b α = ln(b − α) − ln(sin α) + (b − α) cot α`, `0 < α < min(b, π)`.

* `omegaG_hasDerivAt`, `strictAntiOn_omegaG`: `G′ = −((sin α + (b − α) cos α)² + (b − α)² sin² α)/
  ((b − α) sin² α) < 0`.
* Limits: `+∞` as `α → 0⁺`; `−∞` at the right end when `b ≠ π`; `−1` as `α → π⁻` when `b = π`
  (and `G > −1` there). Hence `G` attains every value (`b ≠ π`), resp. exactly the values `> −1`
  (`b = π`): `exists_omegaG_eq`, `omegaG_pi_gt`.
-/

open Set Filter Topology Real

namespace Azurite.DLMF

/-- `ln(b − α) − ln(sin α) + (b − α) cot α`. -/
noncomputable def omegaG (b α : ℝ) : ℝ := log (b - α) - log (sin α) + (b - α) * cos α / sin α

/-- The domain `0 < α < min(b, π)`. -/
def omegaDom (b : ℝ) : Set ℝ := Ioo 0 (min b π)

theorem mem_omegaDom {b α : ℝ} (h : α ∈ omegaDom b) : 0 < α ∧ α < b ∧ α < π :=
  ⟨h.1, h.2.trans_le (min_le_left _ _), h.2.trans_le (min_le_right _ _)⟩

theorem omegaG_hasDerivAt {b α : ℝ} (h : α ∈ omegaDom b) :
    HasDerivAt (omegaG b) (-((sin α + (b - α) * cos α) ^ 2 + (b - α) ^ 2 * sin α ^ 2) /
      ((b - α) * sin α ^ 2)) α := by
  obtain ⟨h0, hb, hπ⟩ := mem_omegaDom h
  have hs : 0 < sin α := sin_pos_of_pos_of_lt_pi h0 hπ
  have hd : 0 < b - α := by linarith
  have h : HasDerivAt (omegaG b) _ α :=
    ((((hasDerivAt_id' α).const_sub b).log hd.ne').sub ((hasDerivAt_sin α).log hs.ne')).add
      ((((hasDerivAt_id' α).const_sub b).mul (hasDerivAt_cos α)).div (hasDerivAt_sin α) hs.ne')
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  field_simp
  ring

theorem omegaG_deriv_neg {b α : ℝ} (h : α ∈ omegaDom b) :
    -((sin α + (b - α) * cos α) ^ 2 + (b - α) ^ 2 * sin α ^ 2) / ((b - α) * sin α ^ 2) < 0 := by
  obtain ⟨h0, hb, hπ⟩ := mem_omegaDom h
  have hs : 0 < sin α := sin_pos_of_pos_of_lt_pi h0 hπ
  have hd : 0 < b - α := by linarith
  apply div_neg_of_neg_of_pos _ (by positivity)
  have : 0 < (b - α) ^ 2 * sin α ^ 2 := by positivity
  nlinarith [sq_nonneg (sin α + (b - α) * cos α)]

theorem continuousOn_omegaG (b : ℝ) : ContinuousOn (omegaG b) (omegaDom b) :=
  fun _ h => (omegaG_hasDerivAt h).continuousAt.continuousWithinAt

theorem strictAntiOn_omegaG (b : ℝ) : StrictAntiOn (omegaG b) (omegaDom b) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) (continuousOn_omegaG b) fun α h => ?_
  have h' : α ∈ omegaDom b := by
    rwa [interior_Ioo] at h
  rw [(omegaG_hasDerivAt h').deriv]
  exact omegaG_deriv_neg h'

/-! ### Limits at the ends of the domain -/

theorem tendsto_sin_nhdsGT_zero : Tendsto sin (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · exact (by simpa using Real.continuous_sin.tendsto 0 : Tendsto sin (𝓝 0) (𝓝 0)).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT pi_pos] with α hα
    exact sin_pos_of_pos_of_lt_pi hα.1 hα.2

theorem tendsto_sin_nhdsLT_pi : Tendsto sin (𝓝[<] π) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · exact (by simpa using Real.continuous_sin.tendsto π : Tendsto sin (𝓝 π) (𝓝 0)).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT pi_pos] with α hα
    exact sin_pos_of_pos_of_lt_pi hα.1 hα.2

/-- `G → +∞` as `α → 0⁺` (`b > 0`). -/
theorem tendsto_omegaG_zero {b : ℝ} (hb : 0 < b) : Tendsto (omegaG b) (𝓝[>] 0) atTop := by
  have hlog : Tendsto (fun α => log (b - α)) (𝓝[>] 0) (𝓝 (log b)) := by
    have : ContinuousAt (fun α => log (b - α)) 0 :=
      (continuousAt_const.sub continuousAt_id).log (by simp; exact hb.ne')
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hls : Tendsto (fun α => -log (sin α)) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp (tendsto_log_nhdsGT_zero.comp tendsto_sin_nhdsGT_zero)
  have hc : Tendsto (fun α => (b - α) * cos α) (𝓝[>] 0) (𝓝 b) := by
    have : Continuous fun α => (b - α) * cos α := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hcot : Tendsto (fun α => (b - α) * cos α / sin α) (𝓝[>] 0) atTop := by
    have := hc.pos_mul_atTop hb (tendsto_inv_nhdsGT_zero.comp tendsto_sin_nhdsGT_zero)
    simpa [div_eq_mul_inv] using this
  have := (hlog.add_atTop hls).atTop_add_atTop hcot
  refine this.congr fun α => ?_
  simp [omegaG, sub_eq_add_neg]

/-- `G → −∞` as `α → b⁻` (`0 < b < π`). -/
theorem tendsto_omegaG_b {b : ℝ} (hb : 0 < b) (hbπ : b < π) :
    Tendsto (omegaG b) (𝓝[<] b) atBot := by
  have hlog : Tendsto (fun α => log (b - α)) (𝓝[<] b) atBot := by
    refine tendsto_log_nhdsGT_zero.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Continuous fun α : ℝ => b - α := by fun_prop
      simpa using (this.tendsto b).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with α hα
      simpa using hα
  have hsb : 0 < sin b := sin_pos_of_pos_of_lt_pi hb hbπ
  have hrest : Tendsto (fun α => -log (sin α) + (b - α) * cos α / sin α) (𝓝[<] b)
      (𝓝 (-log (sin b) + (b - b) * cos b / sin b)) := by
    have : ContinuousAt (fun α => -log (sin α) + (b - α) * cos α / sin α) b :=
      ((continuous_sin.continuousAt.log hsb.ne').neg).add
        (((continuousAt_const.sub continuousAt_id).mul continuous_cos.continuousAt).div
          continuous_sin.continuousAt hsb.ne')
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have := hlog.atBot_add hrest
  refine this.congr fun α => ?_
  simp only [omegaG]; ring

/-- `G → −∞` as `α → π⁻` (`b > π`). -/
theorem tendsto_omegaG_pi_of_gt {b : ℝ} (hb : π < b) : Tendsto (omegaG b) (𝓝[<] π) atBot := by
  have hlog : Tendsto (fun α => log (b - α)) (𝓝[<] π) (𝓝 (log (b - π))) := by
    have : ContinuousAt (fun α => log (b - α)) π :=
      (continuousAt_const.sub continuousAt_id).log (by simp; linarith)
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  -- `−ln s + c/s = (c − s ln s)/s` with `c → −(b − π) < 0`
  have hnum : Tendsto (fun α => (b - α) * cos α - sin α * log (sin α)) (𝓝[<] π)
      (𝓝 ((b - π) * cos π - 0)) := by
    refine Tendsto.sub ?_ ?_
    · have : Continuous fun α => (b - α) * cos α := by fun_prop
      exact (this.tendsto π).mono_left nhdsWithin_le_nhds
    · have h0 : Tendsto (fun s : ℝ => s * log s) (𝓝[>] 0) (𝓝 0) := by
        have := Real.continuous_mul_log.tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      exact h0.comp tendsto_sin_nhdsLT_pi
  rw [cos_pi] at hnum
  have hneg : (b - π) * -1 - 0 < 0 := by linarith
  have hprod := (tendsto_inv_nhdsGT_zero.comp tendsto_sin_nhdsLT_pi).atTop_mul_neg hneg hnum
  have := hlog.add_atBot hprod
  refine this.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT pi_pos] with α hα
  have hs : sin α ≠ 0 := (sin_pos_of_pos_of_lt_pi hα.1 hα.2).ne'
  simp only [omegaG, Function.comp]
  field_simp
  ring

/-- `s cos s < sin s` for `0 < s < π`. -/
theorem mul_cos_lt_sin {s : ℝ} (hs0 : 0 < s) (hsπ : s < π) : s * cos s < sin s := by
  have hss : 0 < sin s := sin_pos_of_pos_of_lt_pi hs0 hsπ
  rcases le_or_gt (cos s) 0 with hc | hc
  · nlinarith
  · have hs2 : s < π / 2 := by
      by_contra h; push Not at h
      exact absurd (cos_nonpos_of_pi_div_two_le_of_le h (by linarith)) (not_le.mpr hc)
    have := lt_tan hs0 hs2
    rw [tan_eq_sin_div_cos, lt_div_iff₀ hc] at this
    exact this

/-- For `b = π`, `G(α) = ln(s/sin s) − s cot s` with `s = π − α`. -/
theorem omegaG_pi_eq {α : ℝ} (h : α ∈ omegaDom π) :
    omegaG π α = log ((π - α) / sin (π - α)) - (π - α) * cos (π - α) / sin (π - α) := by
  obtain ⟨h0, _, hπ⟩ := mem_omegaDom h
  have hss : 0 < sin (π - α) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [omegaG, log_div (by linarith) hss.ne', sin_pi_sub, cos_pi_sub]
  ring

/-- For `b = π`, `G > −1` on the domain. -/
theorem omegaG_pi_gt {α : ℝ} (h : α ∈ omegaDom π) : -1 < omegaG π α := by
  obtain ⟨h0, _, hπ⟩ := mem_omegaDom h
  rw [omegaG_pi_eq h]
  set s := π - α
  have hs0 : 0 < s := by simp only [s]; linarith
  have hsπ : s < π := by simp only [s]; linarith
  have hss : 0 < sin s := sin_pos_of_pos_of_lt_pi hs0 hsπ
  have h1 : 0 < log (s / sin s) := log_pos (by rw [one_lt_div hss]; exact sin_lt hs0)
  have h2 : s * cos s / sin s < 1 := by rw [div_lt_one hss]; exact mul_cos_lt_sin hs0 hsπ
  linarith

/-- For `b = π`, `G → −1` as `α → π⁻`. -/
theorem tendsto_omegaG_pi : Tendsto (omegaG π) (𝓝[<] π) (𝓝 (-1)) := by
  have hs : Tendsto (fun α => π - α) (𝓝[<] π) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Continuous fun α : ℝ => π - α := by fun_prop
      simpa using (this.tendsto π).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with α hα
      simpa using hα
  have hsinc : Tendsto (fun s : ℝ => sin s / s) (𝓝[>] 0) (𝓝 1) :=
    tendsto_sin_div_nhdsNE_zero.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  have hinv : Tendsto (fun s : ℝ => s / sin s) (𝓝[>] 0) (𝓝 1) := by
    have := hsinc.inv₀ one_ne_zero
    simpa using this
  have hcos : Tendsto (fun s : ℝ => cos s) (𝓝[>] 0) (𝓝 1) := by
    simpa using (continuous_cos.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun s : ℝ => log (s / sin s) - s / sin s * cos s) (𝓝[>] 0)
      (𝓝 (log 1 - 1 * 1)) :=
    ((continuousAt_log one_ne_zero).tendsto.comp hinv).sub (hinv.mul hcos)
  rw [log_one] at hlim
  have := hlim.comp hs
  norm_num at this
  refine this.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT pi_pos] with α hα
  rw [omegaG_pi_eq ⟨hα.1, by simp [hα.2]⟩]
  simp only [Function.comp]
  ring

/-- `G` attains `a` on the domain when `b > 0` and (`b ≠ π` or `a > −1`). -/
theorem exists_omegaG_eq {a b : ℝ} (hb : 0 < b) (h : b ≠ π ∨ -1 < a) :
    ∃ α ∈ omegaDom b, omegaG b α = a := by
  set r := min b π with hr
  have hr0 : 0 < r := lt_min hb pi_pos
  obtain ⟨α₁, h1, h1'⟩ := (((tendsto_omegaG_zero hb).eventually (eventually_gt_atTop a)).and
    (Ioo_mem_nhdsGT (half_pos hr0))).exists
  have hα₂ : ∃ α₂ ∈ Ioo (r / 2) r, omegaG b α₂ < a := by
    rcases lt_trichotomy b π with hbπ | rfl | hbπ
    · have hrb : r = b := min_eq_left hbπ.le
      obtain ⟨α₂, h2, h2'⟩ := (((tendsto_omegaG_b hb hbπ).eventually (eventually_lt_atBot a)).and
        (Ioo_mem_nhdsLT (by rw [← hrb]; linarith : r / 2 < b))).exists
      exact ⟨α₂, ⟨h2'.1, by rw [hrb]; exact h2'.2⟩, h2⟩
    · have hrπ : r = π := min_self π
      have ha : -1 < a := h.resolve_left (fun h => h rfl)
      obtain ⟨α₂, h2, h2'⟩ := ((tendsto_omegaG_pi.eventually (Iio_mem_nhds ha)).and
        (Ioo_mem_nhdsLT (by rw [← hrπ]; linarith : r / 2 < π))).exists
      exact ⟨α₂, ⟨h2'.1, by rw [hrπ]; exact h2'.2⟩, h2⟩
    · have hrπ : r = π := min_eq_right hbπ.le
      obtain ⟨α₂, h2, h2'⟩ :=
        (((tendsto_omegaG_pi_of_gt hbπ).eventually (eventually_lt_atBot a)).and
        (Ioo_mem_nhdsLT (by rw [← hrπ]; linarith : r / 2 < π))).exists
      exact ⟨α₂, ⟨h2'.1, by rw [hrπ]; exact h2'.2⟩, h2⟩
  obtain ⟨α₂, h2', h2⟩ := hα₂
  have hsub : Icc α₁ α₂ ⊆ omegaDom b := fun x hx =>
    ⟨h1'.1.trans_le hx.1, hx.2.trans_lt h2'.2⟩
  obtain ⟨α, hα, hαa⟩ := intermediate_value_Icc' (by linarith [h1'.2, h2'.1])
    ((continuousOn_omegaG b).mono hsub) ⟨h2.le, h1.le⟩
  exact ⟨α, hsub hα, hαa⟩

end Azurite.DLMF
