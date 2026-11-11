/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11ShiftCoeff
import Azurite.DLMF.Chapter2.Section2Reversion
import Azurite.DLMF.Chapter5.Section9Boyd

/-!
# DLMF §5.11(i): 5.11.7 and 5.11.8

Formalization of <https://dlmf.nist.gov/5.11>, equations 5.11.7–5.11.8.

* 5.11.8 (`dlmf_5_11_8`): with `R_h(z) = J(z + h) + (z + h − ½)(ln(z + h) − ln z) − h`
  (`lnGammaShiftRem`), `Γ(z + h) = exp((z + h − ½) ln z − z + ½ ln(2π) + R_h(z))` whenever
  `z + h` is in the slit plane, so `R_h(z) = Ln Γ(z + h) − (z + h − ½) ln z + z − ½ ln(2π)` for a
  value of `Ln Γ(z + h)`, and `R_h(z) ∼ ∑_{k≥2} (−1)ᵏ Bₖ(h)/(k(k − 1) z^{k−1})` in
  `|ph z| ≤ π − δ`, for every complex `h`. Stirling's series 5.11.1 is composed with
  `1/(z + h) = w (1 + hw)^{−1}`, `w = 1/z` (`HasPowExpansion.subst_comp`), and
  `ln(z + h) − ln z = ln(1 + hw)` eventually (`eventually_shift_sector`); the coefficients are
  identified in `Section11ShiftCoeff.lean`.
* 5.11.7 (`dlmf_5_11_7`): `Γ(az + b) ∼ √(2π) e^{−az} (az)^{az+b−½}` for `a > 0`, `b ∈ ℂ`
  (`R_b(az) → 0`).
-/

open Filter Topology Set Asymptotics PowerSeries
open scoped Real

namespace Azurite.DLMF

/-! ### Expansions -/

/-- Composition with a change of variable: if `F ∼ A(v)` along `L`, `k → L` and `v ∘ k ∼ U` in
`y` with `U(0) = 0`, then `F ∘ k ∼ A(U)` in `y`. -/
theorem HasPowExpansion.subst_comp {α β : Type*} {l : Filter α} {y : α → ℂ}
    (hy : Tendsto y l (𝓝 0)) {L : Filter β} {v F : β → ℂ} {A : ℂ⟦X⟧}
    (hF : HasPowExpansion L v F A) {k : α → β} (hk : Tendsto k l L) {U : ℂ⟦X⟧}
    (hu : HasPowExpansion l y (fun x => v (k x)) U) (hU0 : constantCoeff U = 0) :
    HasPowExpansion l y (fun x => F (k x)) (A.subst U) := fun n => by
  have huO : (fun x => v (k x)) =O[l] y := by
    simpa [trunc_one_left, hU0] using hu 1
  have e1 : (fun x => F (k x) - (trunc n A).eval (v (k x))) =O[l] fun x => y x ^ n :=
    ((hF n).comp_tendsto hk).trans (huO.pow n)
  have h2 := hu.polyEval hy (trunc n A) n
  rw [trunc_aeval_trunc hU0 A n] at h2
  exact (e1.add h2).congr_left fun x => by ring

/-- `ln(1 + v) ∼ ∑ (−1)^{j+1} vʲ/j` as `v → 0`. -/
theorem hasPowExpansion_log_one_add :
    HasPowExpansion (𝓝 (0 : ℂ)) id (fun v => Complex.log (1 + v))
      (mk fun j => (-1) ^ (j + 1) / (j : ℂ)) := by
  intro n
  cases n with
  | zero =>
    simp only [trunc_zero', Polynomial.eval_zero, sub_zero, pow_zero]
    have hc : ContinuousAt (fun v : ℂ => Complex.log (1 + v)) 0 :=
      (continuousAt_clog (by simp)).comp (continuous_const.add continuous_id).continuousAt
    exact hc.tendsto.isBigO_one ℂ
  | succ n =>
    have e : ∀ v : ℂ, (trunc (n + 1) (mk fun j => (-1) ^ (j + 1) / (j : ℂ))).eval (id v) =
        Complex.logTaylor (n + 1) v := fun v => by
      rw [eval_trunc_eq_sum, Complex.logTaylor]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [coeff_mk, id]
      ring
    simp only [e]
    refine IsBigO.of_bound 2 ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with v hv
    rw [mem_ball_zero_iff] at hv
    have hb := Complex.norm_log_sub_logTaylor_le n (by linarith : ‖v‖ < 1)
    have h1 : (1 - ‖v‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) two_pos]; linarith
    have h2 : (1 : ℝ) ≤ n + 1 := by have := n.cast_nonneg (α := ℝ); linarith
    have hp := pow_nonneg (norm_nonneg v) (n + 1)
    rw [id, norm_pow]
    refine hb.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hp]

/-- `ln(1 + hy) ∼ ∑ ℓⱼ yʲ` (`logShiftSeries`) whenever `y → 0`. -/
theorem hasPowExpansion_log_shift {α : Type*} {l : Filter α} {y : α → ℂ}
    (hy : Tendsto y l (𝓝 0)) (h : ℂ) :
    HasPowExpansion l y (fun x => Complex.log (1 + h * y x)) (logShiftSeries h) := fun n => by
  have hk : Tendsto (fun x => h * y x) l (𝓝 0) := by simpa using hy.const_mul h
  have e1 := (hasPowExpansion_log_one_add n).comp_tendsto hk
  have e2 : (fun x => (h * y x) ^ n) =O[l] fun x => y x ^ n := by
    simp_rw [mul_pow]; exact isBigO_const_mul_self _ _ _
  refine (e1.trans e2).congr_left fun x => ?_
  simp only [Function.comp, id]
  congr 1
  rw [eval_trunc_eq_sum, eval_trunc_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [logShiftSeries, logShiftCoeff, coeff_mk]
  ring

/-! ### Geometry of the shift -/

theorem mem_closedSector_zero_iff {z : ℂ} {θ : ℝ} :
    z ∈ closedSectorDLMF 0 θ ↔ z ≠ 0 ∧ |Complex.arg z| ≤ θ := by
  simp [closedSectorDLMF]

/-- For large `z` in `|ph z| ≤ π − δ`: `ln(z + h) = ln z + ln(1 + h/z)` and
`|ph(z + h)| ≤ π − δ/2`. -/
theorem eventually_shift_sector {δ : ℝ} (hδ : 0 < δ) (h : ℂ) :
    ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ)),
      z ≠ 0 ∧ z + h ≠ 0 ∧
        Complex.log (z + h) = Complex.log z + Complex.log (1 + h * z⁻¹) ∧
        |Complex.arg (z + h)| ≤ π - δ / 2 := by
  set l := Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ))
  have ht : Tendsto (fun z : ℂ => 1 + h * z⁻¹) l (𝓝 1) := by
    simpa using tendsto_const_nhds.add ((tendsto_inv_atInf _).const_mul h)
  have harg : Tendsto (fun z : ℂ => Complex.arg (1 + h * z⁻¹)) l (𝓝 0) := by
    have := (Complex.continuousAt_arg (by simp : (1 : ℂ) ∈ Complex.slitPlane)).tendsto.comp ht
    rw [Complex.arg_one] at this
    exact this
  have hs : ∀ᶠ z in l, z ∈ closedSectorDLMF 0 (π - δ) := mem_inf_of_right (mem_principal_self _)
  filter_upwards [eventually_ne_zero_atInf _, ht.eventually_ne one_ne_zero,
    harg.eventually (Metric.ball_mem_nhds 0 (half_pos hδ)), hs] with z hz0 hz1 hza hzs
  have hzarg := (mem_closedSector_zero_iff.mp hzs).2
  rw [Real.dist_eq, sub_zero] at hza
  have hmul : z + h = z * (1 + h * z⁻¹) := by field_simp
  have ha := abs_le.mp hzarg
  have hb := abs_lt.mp hza
  have hsum : Complex.arg z + Complex.arg (1 + h * z⁻¹) ∈ Ioc (-π) π :=
    ⟨by linarith, by linarith⟩
  have hlog := (Complex.log_mul_eq_add_log_iff hz0 hz1).mpr hsum
  have harg' : Complex.arg (z + h) = Complex.arg z + Complex.arg (1 + h * z⁻¹) := by
    rw [← Complex.log_im, hmul, hlog, Complex.add_im, Complex.log_im, Complex.log_im]
  refine ⟨hz0, by rw [hmul]; exact mul_ne_zero hz0 hz1, by rw [hmul, hlog], ?_⟩
  rw [harg']
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem tendsto_shift_sector {δ : ℝ} (hδ : 0 < δ) (h : ℂ) :
    Tendsto (fun z => z + h) (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ)))
      (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ / 2))) := by
  refine tendsto_inf.mpr ⟨tendsto_norm_atTop_iff_cobounded.mp ?_, tendsto_principal.mpr ?_⟩
  · have hn : Tendsto (fun z : ℂ => ‖z‖ + -‖h‖)
        (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ))) atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_norm_cobounded_atTop.mono_left inf_le_left)
    refine tendsto_atTop_mono (fun z => ?_) hn
    have := norm_sub_le (z + h) h
    rw [add_sub_cancel_right] at this
    linarith
  · filter_upwards [eventually_shift_sector hδ h] with z hz
    obtain ⟨-, hzh, -, harg⟩ := hz
    exact mem_closedSector_zero_iff.mpr ⟨hzh, harg⟩

/-! ### 5.11.8 -/

/-- `R_h(z) = J(z + h) + (z + h − ½)(ln(z + h) − ln z) − h`: `Ln Γ(z + h)` minus the leading
terms of 5.11.8. -/
noncomputable def lnGammaShiftRem (h z : ℂ) : ℂ :=
  stirlingJ (z + h) + (z + h - 1 / 2) * (Complex.log (z + h) - Complex.log z) - h

theorem Gamma_add_eq_exp_lnGammaShiftRem {h z : ℂ} (hz : z + h ∈ Complex.slitPlane) :
    Complex.Gamma (z + h) = Complex.exp ((z + h - 1 / 2) * Complex.log z - z +
      1 / 2 * Complex.log (2 * π) + lnGammaShiftRem h z) := by
  rw [Gamma_eq_exp_stirlingJ hz, lnGammaShiftRem]
  congr 1
  ring

/-- **DLMF 5.11.8**: `Ln Γ(z + h) ∼ (z + h − ½) ln z − z + ½ ln(2π) +
∑_{k≥2} (−1)ᵏ Bₖ(h)/(k(k − 1) z^{k−1})` as `z → ∞` in `|ph z| ≤ π − δ`, for fixed `h ∈ ℂ`:
`Γ(z + h)` is the exponential of the leading terms plus `R_h(z)`, and `R_h` has the expansion
with coefficients `lnGammaShiftCoeff h` (`n = k − 1`). -/
theorem dlmf_5_11_8 (h : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) :
    (∀ z, z + h ∈ Complex.slitPlane → Complex.Gamma (z + h) =
      Complex.exp ((z + h - 1 / 2) * Complex.log z - z + 1 / 2 * Complex.log (2 * π) +
        lnGammaShiftRem h z)) ∧
    IsAsympExpansionDLMF (closedSectorDLMF 0 (π - δ)) (lnGammaShiftRem h)
      (lnGammaShiftCoeff h) := by
  refine ⟨fun z hz => Gamma_add_eq_exp_lnGammaShiftRem hz, ?_⟩
  rw [isAsympExpansionDLMF_iff, ← lnGammaShiftSeries_eq]
  have hy := tendsto_inv_atInf (closedSectorDLMF 0 (π - δ))
  have hy0 := eventually_ne_zero_atInf (closedSectorDLMF 0 (π - δ))
  have hgeo := eventually_shift_sector hδ h
  have hJ := isAsympExpansionDLMF_iff.mp (dlmf_5_11_1 (half_pos hδ) (by linarith)).2
  have hW := (hasPowExpansion_const hy 1).add ((hasPowExpansion_id hy).const_mul h)
  rw [map_one] at hW
  have hU : HasPowExpansion (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ)))
      (fun z => z⁻¹) (fun z => (z + h)⁻¹) (X * shiftV h) := by
    rw [shiftV_eq_inv]
    refine ((hasPowExpansion_id hy).mul hy (hW.inv hy (by simp))).congr' ?_
    filter_upwards [hgeo] with z hz
    obtain ⟨hz0, hzh, -, -⟩ := hz
    simp only [Pi.mul_apply, Pi.add_apply]
    have : 1 + h * z⁻¹ ≠ 0 := by
      rw [show 1 + h * z⁻¹ = (z + h) / z by field_simp]; exact div_ne_zero hzh hz0
    field_simp
  have hJs := HasPowExpansion.subst_comp hy hJ (tendsto_shift_sector hδ h) hU (by simp)
  have hL := hasPowExpansion_log_shift hy h
  have hL1 := hL.div_var (by simp [logShiftSeries, logShiftCoeff])
    (hy0.mono fun z hz => inv_ne_zero hz)
  refine (((hJs.add hL1).add (hL.const_mul (h - 1 / 2))).sub
    (hasPowExpansion_const hy h)).congr' ?_
  filter_upwards [hgeo] with z hz
  obtain ⟨hz0, hzh, hlog, -⟩ := hz
  simp only [Pi.add_apply, Pi.sub_apply, lnGammaShiftRem, hlog]
  field_simp
  ring

/-! ### 5.11.7 -/

/-- `z ↦ az` (`a > 0`) preserves `z → ∞` in `|ph z| ≤ ω`. -/
theorem tendsto_real_mul_sector {a : ℝ} (ha : 0 < a) (ω : ℝ) :
    Tendsto (fun z : ℂ => (a : ℂ) * z) (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 ω))
      (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 ω)) := by
  refine tendsto_inf.mpr ⟨tendsto_norm_atTop_iff_cobounded.mp ?_, tendsto_principal.mpr ?_⟩
  · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    exact (tendsto_norm_cobounded_atTop.mono_left inf_le_left).const_mul_atTop ha
  · filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    obtain ⟨hz0, harg⟩ := mem_closedSector_zero_iff.mp hz
    exact mem_closedSector_zero_iff.mpr ⟨mul_ne_zero (by exact_mod_cast ha.ne') hz0,
      by rwa [Complex.arg_real_mul _ ha]⟩

/-- **DLMF 5.11.7**: `Γ(az + b) ∼ √(2π) e^{−az} (az)^{az+b−½}` as `z → ∞` in `|ph z| ≤ π − δ`,
for fixed `a > 0` and `b ∈ ℂ` (principal powers). -/
theorem dlmf_5_11_7 {a : ℝ} (ha : 0 < a) (b : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) :
    AsympEqDLMF (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ)))
      (fun z => Complex.Gamma (a * z + b))
      (fun z => (Real.sqrt (2 * π) : ℂ) * Complex.exp (-(a * z)) *
        (a * z) ^ (a * z + b - 1 / 2)) := by
  have hR : Tendsto (lnGammaShiftRem b)
      (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ))) (𝓝 0) := by
    have := (isAsympExpansionDLMF_iff.mp (dlmf_5_11_8 b hδ hδπ).2).tendsto (tendsto_inv_atInf _)
    simpa [lnGammaShiftCoeff] using this
  have hk := tendsto_real_mul_sector ha (π - δ)
  have hlim : Tendsto (fun z => Complex.exp (lnGammaShiftRem b (a * z)))
      (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ))) (𝓝 1) := by
    have := (Complex.continuous_exp.tendsto 0).comp (hR.comp hk)
    rw [Complex.exp_zero] at this
    exact this
  refine hlim.congr' ?_
  filter_upwards [hk.eventually (eventually_shift_sector hδ b)] with z hz
  obtain ⟨hw0, hwb, -, hwarg⟩ := hz
  have hslit : (a : ℂ) * z + b ∈ Complex.slitPlane := Complex.mem_slitPlane_iff_arg.mpr
    ⟨fun h => by rw [h, abs_of_pos Real.pi_pos] at hwarg; linarith, hwb⟩
  rw [Gamma_add_eq_exp_lnGammaShiftRem hslit, Complex.cpow_def_of_ne_zero hw0, sqrt_two_pi_eq_exp,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  ring

end Azurite.DLMF
