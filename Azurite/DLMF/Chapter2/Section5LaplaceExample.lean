/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Normed.Module.Connected
import Azurite.DLMF.Chapter1.Section14TableMellin
import Azurite.DLMF.Chapter2.Section5LaplaceResidues

/-!
# DLMF §2.5(iii), Example (2.5.45–2.5.47): `ℒ[1/(1+t)](ζ)` as `ζ → 0+`, the residues

`h(t) = 1/(1 + t)`: `𝓜h(z) = π csc(πz)` for `0 < ℜz < 1` (Table 1.14.5), and in the notation of
2.5.18 and 2.5.20, `κ = 0`, `βₛ = s + 1`, `bₛ = (−1)^s`, `c = 0` (`laplaceSmallSetup_oneDivOneAdd`).
Since the `βₛ` are positive integers, 2.5.44 does not apply and the poles of
`Γ(1 − z) 𝓜h(z)` at `z = k` are double. "Straightforward calculation gives"

* 2.5.46: `res_{z=k} [−ζ^{z−1} Γ(1 − z) π csc(πz)] = (−ln ζ + ψ(k)) ζ^{k−1}/(k − 1)!`
  (`dlmf_2_5_46`): with `Γ(z) Γ(1 − z) = π csc(πz)` and `Γ(1 − z) = −GammaNum(1 − z)/(z − k)`
  the integrand is `A(z)/(z − k)²`, and the residue is `A'(k)`; the derivative of the `Γ`-factor
  at the pole is its value times `ψ(k)` (`hasDerivAt_GammaNum_neg_nat`).
* 2.5.47: `res_{z=1} [−ζ^{z−1} Γ(1 − z) 𝓜h₂(z)] = (−ln ζ − γ) − 𝓜h₁(1)` (`dlmf_2_5_47`), from
  2.5.28 (`𝓜h₂ = 𝓜h − 𝓜h₁` off the poles) and 2.5.41's residue.

The identity `𝓜h₁(z) + 𝓜h₂(z) = π csc(πz)` for the continued transforms holds on `ℂ ∖ ℤ` by the
identity theorem (`cont_add_cont_eq`): both sides are analytic off `ℤ`, whose complement is
connected, and they agree on the strip `0 < ℜz < 1`.
-/

open MeasureTheory Filter Topology Set Complex Metric Asymptotics
open scoped Real Nat

namespace Azurite.DLMF

/-! ### The function `1/(1 + t)` and its expansions -/

/-- `h(t) = 1/(1 + t)`. -/
noncomputable def oneDivOneAdd (t : ℝ) : ℂ := 1 / (1 + (t : ℂ))

theorem one_add_ofReal_ne_zero {t : ℝ} (ht : 0 < t) : (1 : ℂ) + t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem le_norm_one_add_ofReal {t : ℝ} (ht : 0 < t) : 1 + t ≤ ‖(1 : ℂ) + t‖ := by
  have := abs_re_le_norm ((1 : ℂ) + t)
  rw [add_re, one_re, ofReal_re, abs_of_pos (by linarith)] at this
  exact this

/-- The geometric remainder at `+∞`: `1/(1+t) − ∑_{s<n} (−1)^s t^{−(s+1)} = (−1)^n t^{−n}/(1+t)`. -/
theorem oneDivOneAdd_sub_sum_top {t : ℝ} (ht : 0 < t) (n : ℕ) :
    oneDivOneAdd t - ∑ s ∈ Finset.range n, (-1) ^ s * (t : ℂ) ^ (-((s : ℂ) + 1)) =
      (-1) ^ n * ((t : ℂ) ^ n)⁻¹ / (1 + t) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hden := one_add_ofReal_ne_zero ht
  induction n with
  | zero => simp [oneDivOneAdd]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih, show -((n : ℂ) + 1) = -(((n + 1 : ℕ) : ℂ)) by
      push_cast; ring, cpow_neg, cpow_natCast, pow_succ]
    field_simp
    ring

/-- The geometric remainder at `0+`: `1/(1+t) − ∑_{s<n} (−1)^s t^s = (−1)^n t^n/(1+t)`. -/
theorem oneDivOneAdd_sub_sum_zero {t : ℝ} (ht : 0 < t) (n : ℕ) :
    oneDivOneAdd t - ∑ s ∈ Finset.range n, (-1) ^ s * (t : ℂ) ^ (s : ℂ) =
      (-1) ^ n * (t : ℂ) ^ n / (1 + t) := by
  have hden := one_add_ofReal_ne_zero ht
  induction n with
  | zero => simp [oneDivOneAdd]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih, cpow_natCast, pow_succ]
    field_simp
    ring

theorem norm_oneDivOneAdd_le {t : ℝ} (ht : 0 < t) : ‖oneDivOneAdd t‖ ≤ 1 := by
  rw [oneDivOneAdd, norm_div, norm_one, div_le_one (norm_pos_iff.mpr (one_add_ofReal_ne_zero ht))]
  linarith [le_norm_one_add_ofReal ht]

theorem norm_ofReal_div_one_add_le {t : ℝ} (ht : 0 < t) : ‖(t : ℂ) / (1 + t)‖ ≤ 1 := by
  rw [norm_div, norm_real, Real.norm_of_nonneg ht.le,
    div_le_one (norm_pos_iff.mpr (one_add_ofReal_ne_zero ht))]
  linarith [le_norm_one_add_ofReal ht]

/-- `(t : ℂ)⁻¹ → 0` as `t → +∞`. -/
theorem tendsto_inv_ofReal_atTop_zero : Tendsto (fun t : ℝ => ((t : ℂ))⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_inv_atTop_zero.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [abs_of_pos ht]

/-- `h(t) = 1/(1+t)` satisfies the hypotheses of §2.5(iii) with `κ = 0`, `βₛ = s + 1`,
`bₛ = (−1)^s`, `c = 0` (and `p = 1`). -/
theorem laplaceSmallSetup_oneDivOneAdd :
    LaplaceSmallSetup oneDivOneAdd (fun s => (-1) ^ s) (fun s => (s : ℂ) + 1) 0 1 0 where
  h_loc := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    exact continuousOn_const.div (continuousOn_const.add continuous_ofReal.continuousOn)
      fun t ht => one_add_ofReal_ne_zero ht
  β_mono := strictMono_nat_of_lt_succ fun s => by simp
  β_tendsto := by
    simp only [add_re, natCast_re, one_re]
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  p_pos := one_pos
  h_exp := by
    refine ⟨fun s => ?_, fun n => ?_⟩
    · unfold IsLittleODLMF
      refine tendsto_inv_ofReal_atTop_zero.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
      rw [← cpow_sub _ _ ht0]
      push_cast
      rw [show -((s : ℂ) + 1 + 1) - -((s : ℂ) + 1) = -1 by ring, cpow_neg_one]
    · refine ⟨1, eventually_map.mpr ?_⟩
      filter_upwards [eventually_gt_atTop 0] with t ht
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
      have hden := one_add_ofReal_ne_zero ht
      simp only [ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
      rw [oneDivOneAdd_sub_sum_top ht n]
      have e : (-1 : ℂ) ^ n * ((t : ℂ) ^ n)⁻¹ / (1 + t) / (t : ℂ) ^ (-((n : ℂ) + 1)) =
          (-1) ^ n * ((t : ℂ) / (1 + t)) := by
        rw [show -((n : ℂ) + 1) = -(((n + 1 : ℕ) : ℂ)) by push_cast; ring, cpow_neg, cpow_natCast,
          pow_succ]
        field_simp
      rw [e, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact norm_ofReal_div_one_add_le ht
  h_zero := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using norm_oneDivOneAdd_le ht
  c_gt := by norm_num

/-- 2.5.17 for `h(t) = 1/(1+t)` at `0+`: `h(t) ∼ ∑ (−1)^s t^s`, `αₛ = s`. -/
theorem isGenAsympExpansion_oneDivOneAdd_zero :
    IsGenAsympExpansionDLMF (𝓝[>] (0 : ℝ))
      (fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ ((fun s : ℕ => (s : ℂ)) s)) oneDivOneAdd
      fun s t => (-1) ^ s * (t : ℂ) ^ ((fun s : ℕ => (s : ℂ)) s) := by
  refine ⟨fun s => ?_, fun n => ?_⟩
  · unfold IsLittleODLMF
    dsimp only
    have h0 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 0) := by
      have := (continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    refine h0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    rw [← cpow_sub _ _ ht0]
    push_cast
    rw [show (s : ℂ) + 1 - s = 1 by ring, cpow_one]
  · refine ⟨1, eventually_map.mpr ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht : (0 : ℝ) < t := ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have hden := one_add_ofReal_ne_zero ht
    rw [oneDivOneAdd_sub_sum_zero ht n, cpow_natCast]
    have e : (-1 : ℂ) ^ n * (t : ℂ) ^ n / (1 + t) / (t : ℂ) ^ n = (-1) ^ n * (1 / (1 + t)) := by
      field_simp
    rw [e, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact norm_oneDivOneAdd_le ht

/-! ### The continued transforms and the identity `𝓜h₁ + 𝓜h₂ = π csc(πz)` -/

/-- The continuation of `𝓜h₁` (2.5.25), poles at `0, −1, −2, …`. -/
noncomputable def contH₁ : ℂ → ℂ :=
  mellinTrunc₁Cont oneDivOneAdd (fun s => (-1) ^ s) fun s => (s : ℂ)

/-- The continuation of `𝓜h₂` (2.5.27), poles at `1, 2, 3, …`. -/
noncomputable def contH₂ : ℂ → ℂ :=
  mellinTrunc₂ContZero oneDivOneAdd (fun s => (-1) ^ s) fun s => (s : ℂ) + 1

theorem mellin_oneDivOneAdd {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin oneDivOneAdd s = π / sin (π * s) := by
  rw [show mellin oneDivOneAdd s = mellin (fun x : ℝ => 1 / (1 + (x : ℂ))) s from rfl,
    dlmf_table_1_14_5_r4 hs0 hs1, mul_comm]

theorem α_mono : StrictMono fun s : ℕ => ((fun s : ℕ => (s : ℂ)) s).re :=
  strictMono_nat_of_lt_succ fun s => by simp

theorem α_tendsto : Tendsto (fun s : ℕ => ((fun s : ℕ => (s : ℂ)) s).re) atTop atTop := by
  simp only [natCast_re]
  exact tendsto_natCast_atTop_atTop

theorem contH₁_eq {z : ℂ} (hz : 0 < z.re) : contH₁ z = mellin (trunc₁ oneDivOneAdd) z :=
  (dlmf_2_5_25 α_mono isGenAsympExpansion_oneDivOneAdd_zero laplaceSmallSetup_oneDivOneAdd.h_loc
    α_tendsto).1 z (by simpa using hz)

theorem differentiableAt_contH₁ {z : ℂ} (hz : ∀ s : ℕ, z ≠ -(s : ℂ)) :
    DifferentiableAt ℂ contH₁ z :=
  (dlmf_2_5_25 α_mono isGenAsympExpansion_oneDivOneAdd_zero laplaceSmallSetup_oneDivOneAdd.h_loc
    α_tendsto).2.1 z hz

theorem contH₂_eq {z : ℂ} (hz : z.re < 1) : contH₂ z = mellin (trunc₂ oneDivOneAdd) z :=
  mellinTrunc₂ContZero_eq laplaceSmallSetup_oneDivOneAdd.h_loc laplaceSmallSetup_oneDivOneAdd.β_mono
    laplaceSmallSetup_oneDivOneAdd.β_tendsto laplaceSmallSetup_oneDivOneAdd.h_exp_zero
    (by simpa using hz)

theorem differentiableAt_contH₂ {z : ℂ} (hz : ∀ s : ℕ, z ≠ (s : ℂ) + 1) :
    DifferentiableAt ℂ contH₂ z :=
  differentiableAt_mellinTrunc₂ContZero laplaceSmallSetup_oneDivOneAdd.h_loc
    laplaceSmallSetup_oneDivOneAdd.β_mono laplaceSmallSetup_oneDivOneAdd.β_tendsto
    laplaceSmallSetup_oneDivOneAdd.h_exp_zero hz

/-- The set of integers in `ℂ` is closed (its points are at mutual distance `≥ 1`). -/
theorem isClosed_range_intCast : IsClosed (range ((↑) : ℤ → ℂ)) := by
  refine Metric.isClosed_of_pairwise_le_dist one_pos ?_
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ hmn
  rw [dist_eq_norm, ← Int.cast_sub, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr fun h => hmn (by rw [h]))

theorem notMem_range_intCast_iff {z : ℂ} : z ∉ range ((↑) : ℤ → ℂ) ↔ ∀ n : ℤ, z ≠ n := by
  simp [eq_comm]

theorem sin_pi_mul_ne_zero {z : ℂ} (hz : ∀ n : ℤ, z ≠ n) : sin (π * z) ≠ 0 := by
  rw [Ne, sin_eq_zero_iff]
  rintro ⟨k, hk⟩
  exact hz k (mul_left_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) (by rw [hk]; ring))

/-- **The identity `𝓜h₁(z) + 𝓜h₂(z) = π csc(πz)`** for the continued transforms, on `ℂ ∖ ℤ`. -/
theorem cont_add_cont_eq {z : ℂ} (hz : ∀ n : ℤ, z ≠ n) : contH₁ z + contH₂ z = π / sin (π * z) := by
  set U : Set ℂ := (range ((↑) : ℤ → ℂ))ᶜ with hU
  have hUo : IsOpen U := isClosed_range_intCast.isOpen_compl
  have hUc : IsPreconnected U :=
    ((countable_range _).isConnected_compl_of_one_lt_rank (by
      rw [rank_real_complex]; norm_num)).isPreconnected
  have hmem : ∀ w, w ∈ U ↔ ∀ n : ℤ, w ≠ n := fun w => notMem_range_intCast_iff
  have hf : AnalyticOnNhd ℂ (fun w => contH₁ w + contH₂ w) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    have hw := (hmem w).mp hw
    exact ((differentiableAt_contH₁ fun s h => hw (-s) (by rw [h]; push_cast; ring)).add
      (differentiableAt_contH₂ fun s h =>
        hw (s + 1) (by rw [h]; push_cast; ring))).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun w => (π : ℂ) / sin (π * w)) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    exact ((differentiableAt_const _).div
      ((differentiableAt_const _).mul differentiableAt_id |>.csin)
      (sin_pi_mul_ne_zero ((hmem w).mp hw))).differentiableWithinAt
  have h₀ : (1 / 2 : ℂ) ∈ U := (hmem _).mpr fun n h => by
    have := congrArg Complex.re h
    simp at this
    have h2 : (2 : ℝ) * n = 1 := by linarith
    have : (2 : ℤ) * n = 1 := by exact_mod_cast h2
    omega
  have hfg : (fun w => contH₁ w + contH₂ w) =ᶠ[𝓝 (1 / 2 : ℂ)] fun w => (π : ℂ) / sin (π * w) := by
    filter_upwards [Metric.ball_mem_nhds (1 / 2 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
    rw [mem_ball, dist_eq_norm] at hw
    have hre := abs_re_le_norm (w - 1 / 2)
    rw [sub_re, show ((1 / 2 : ℂ)).re = 1 / 2 by norm_num] at hre
    have h1 : 0 < w.re := by linarith [(abs_lt.mp (hre.trans_lt hw)).1]
    have h2 : w.re < 1 := by linarith [(abs_lt.mp (hre.trans_lt hw)).2]
    rw [contH₁_eq h1, contH₂_eq h2, ← mellin_eq_trunc_add
      (laplaceSmallSetup_oneDivOneAdd.mellinConvergent_h₁ (by simpa using h1))
      (laplaceSmallSetup_oneDivOneAdd.mellinConvergent_h₂ (by simpa using h2)),
      mellin_oneDivOneAdd h1 h2]
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc h₀ hfg ((hmem z).mpr hz)

/-- **DLMF 2.5.28** in the Example: `𝓜h₂(z) = π csc(πz) − 𝓜h₁(z)` for `ℜz > 0`, `z ∉ ℤ`. -/
theorem contH₂_eq_sub {z : ℂ} (hz : 0 < z.re) (hz' : ∀ n : ℤ, z ≠ n) :
    contH₂ z = π / sin (π * z) - mellin (trunc₁ oneDivOneAdd) z := by
  rw [← cont_add_cont_eq hz', contH₁_eq hz]
  ring

/-! ### The derivative of the `Γ`-factor at a pole -/

theorem sum_inv_neg_add_eq (m : ℕ) :
    ∑ j ∈ Finset.range m, (-(m : ℂ) + j)⁻¹ = -∑ k ∈ Finset.range m, ((1 : ℂ) + k)⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    push_cast
    have : ∀ j : ℕ, (-((m : ℂ) + 1) + ((j : ℂ) + 1))⁻¹ = (-(m : ℂ) + j)⁻¹ := fun j => by
      congr 1
      ring
    simp only [this, ih]
    have e : (-((m : ℂ) + 1) + 0)⁻¹ = -((1 : ℂ) + m)⁻¹ := by
      rw [add_zero, ← inv_neg]
      congr 1
      ring
    rw [e, neg_add]

theorem GammaNum_neg_nat_ne_zero (m : ℕ) : GammaNum m (-(m : ℂ)) ≠ 0 := by
  rw [GammaNum_neg_nat]
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast m.factorial_ne_zero)

/-- `GammaNum m` is differentiable at `−m`, with derivative `GammaNum m (−m) · ψ(m + 1)`. -/
theorem hasDerivAt_GammaNum_neg_nat (m : ℕ) :
    HasDerivAt (GammaNum m) (GammaNum m (-(m : ℂ)) * digamma (m + 1)) (-(m : ℂ)) := by
  have hd : DifferentiableAt ℂ (GammaNum m) (-(m : ℂ)) :=
    (differentiableOn_GammaNum m).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  have hne := GammaNum_neg_nat_ne_zero m
  have hP : ∀ j ∈ Finset.range m, -(m : ℂ) + j ≠ 0 := fun j hj h => by
    have := congrArg Complex.re h
    simp at this
    have : (j : ℝ) < m := by exact_mod_cast Finset.mem_range.mp hj
    linarith
  have hprod : (∏ j ∈ Finset.range m, (-(m : ℂ) + j)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hP
  -- the logarithmic derivative
  have hlog : logDeriv (GammaNum m) (-(m : ℂ)) = digamma (m + 1) := by
    have hdef : GammaNum m =
        (fun w : ℂ => Gamma (w + m + 1)) / (fun w : ℂ => ∏ j ∈ Finset.range m, (w + j)) := by
      funext w
      rfl
    have hΓ : DifferentiableAt ℂ (fun w : ℂ => Gamma (w + m + 1)) (-(m : ℂ)) :=
      (differentiableAt_Gamma _ fun n h => by
        have := congrArg Complex.re h
        simp at this
        linarith [n.cast_nonneg (α := ℝ)]).comp _ ((differentiableAt_id.add_const _).add_const _)
    have hΓ0 : Gamma (-(m : ℂ) + m + 1) ≠ 0 := by
      rw [show -(m : ℂ) + m + 1 = 1 by ring, Gamma_one]
      exact one_ne_zero
    have hprodfun : (fun w : ℂ => ∏ j ∈ Finset.range m, (w + j)) =
        ∏ j ∈ Finset.range m, fun w : ℂ => w + j := by
      funext w
      simp [Finset.prod_apply]
    rw [hdef, logDeriv_div (-(m : ℂ)) (f := fun w : ℂ => Gamma (w + m + 1))
      (g := fun w : ℂ => ∏ j ∈ Finset.range m, (w + j)) hΓ0 hprod hΓ
      (differentiable_prod_range_add m).differentiableAt]
    have h1 : logDeriv (fun w : ℂ => Gamma (w + m + 1)) (-(m : ℂ)) = digamma 1 := by
      have := logDeriv_comp (f := Gamma) (g := fun w : ℂ => w + m + 1) (x := -(m : ℂ))
        (by rw [show -(m : ℂ) + m + 1 = 1 by ring]; exact differentiableAt_Gamma_one)
        ((differentiableAt_id.add_const _).add_const _)
      rw [show (Gamma ∘ fun w : ℂ => w + m + 1) = fun w => Gamma (w + m + 1) from rfl] at this
      rw [this, show -(m : ℂ) + m + 1 = 1 by ring, digamma_def]
      have hder : deriv (fun w : ℂ => w + m + 1) (-(m : ℂ)) = 1 :=
        ((hasDerivAt_id (-(m : ℂ))).add_const (m : ℂ) |>.add_const 1).deriv
      rw [hder, mul_one]
    have h2 : logDeriv (fun w : ℂ => ∏ j ∈ Finset.range m, (w + j)) (-(m : ℂ)) =
        ∑ j ∈ Finset.range m, (-(m : ℂ) + j)⁻¹ := by
      rw [hprodfun, logDeriv_prod hP fun j _ => differentiableAt_id.add_const _]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [logDeriv_apply]
      simp
    rw [h1, h2, sum_inv_neg_add_eq, sub_neg_eq_add,
      ← digamma_apply_add_nat (s := 1) (fun n h => by
        have := congrArg Complex.re h
        simp at this
        linarith [n.cast_nonneg (α := ℝ)]) m, add_comm]
  have := hd.hasDerivAt
  rwa [show deriv (GammaNum m) (-(m : ℂ)) = GammaNum m (-(m : ℂ)) * digamma (m + 1) by
    have := hlog
    rw [logDeriv_apply, div_eq_iff hne] at this
    rw [this, mul_comm]] at this

/-! ### Residues of double poles -/

/-- If `F(z) = A(z)/(z − n)²` on a punctured disc with `A` analytic on the disc, then
`res_{z=n} F = A'(n)`. -/
theorem residue_eq_deriv_of_eq_div_sq {F A : ℂ → ℂ} {n : ℂ} {R : ℝ} (hR : 0 < R)
    (hA : DifferentiableOn ℂ A (ball n R)) (hF : ∀ z ∈ annulus n 0 R, F z = A z / (z - n) ^ 2) :
    residue F n R = deriv A n := by
  have hr : R / 2 ∈ Ioo 0 R := ⟨by positivity, by linarith⟩
  have hball : closedBall n (R / 2) ⊆ ball n R := closedBall_subset_ball (by linarith)
  have hFd : DifferentiableOn ℂ F (annulus n 0 R) := by
    intro z hz
    have hz0 : z - n ≠ 0 := norm_pos_iff.mp hz.1
    have hzb : z ∈ ball n R := by rw [mem_ball, dist_eq_norm]; exact hz.2
    have hd : DifferentiableAt ℂ (fun w => A w / (w - n) ^ 2) z :=
      (hA.differentiableAt (isOpen_ball.mem_nhds hzb)).div
        ((differentiableAt_id.sub_const n).pow 2) (pow_ne_zero 2 hz0)
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [(isOpen_annulus n 0 R).mem_nhds hz] with w hw
    exact hF w hw
  rw [residue_eq hFd hr]
  have hcongr : ∀ z ∈ sphere n (R / 2), F z = (1 / (z - n) ^ 2) • A z := fun z hz => by
    have hzA : z ∈ annulus n 0 R := by
      rw [mem_sphere, dist_eq_norm] at hz
      exact ⟨by rw [hz]; exact hr.1, by rw [hz]; exact hr.2⟩
    rw [hF z hzA, smul_eq_mul, one_div, div_eq_inv_mul]
  rw [circleIntegral.integral_congr hr.1.le hcongr,
    (hA.mono hball).deriv_eq_smul_circleIntegral hr.1, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (by simp [Real.pi_ne_zero] : (2 * π * I : ℂ) ≠ 0), one_mul]

/-- Residues are additive. -/
theorem residue_add {F G : ℂ → ℂ} {s : ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (annulus s 0 R)) (hG : DifferentiableOn ℂ G (annulus s 0 R)) :
    residue (fun z => F z + G z) s R = residue F s R + residue G s R := by
  have hr : R / 2 ∈ Ioo 0 R := ⟨by positivity, by linarith⟩
  have hsub : sphere s (R / 2) ⊆ annulus s 0 R := sphere_subset_annulus hr.1 hr.2
  have hFG : DifferentiableOn ℂ (fun z => F z + G z) (annulus s 0 R) := hF.add hG
  rw [residue_eq hFG hr, residue_eq hF hr, residue_eq hG hr, ← mul_add,
    ← circleIntegral.integral_add
      (ContinuousOn.circleIntegrable hr.1.le (hF.continuousOn.mono hsub))
      (ContinuousOn.circleIntegrable hr.1.le (hG.continuousOn.mono hsub))]

/-! ### 2.5.46 and 2.5.47 -/

/-- A point of the punctured unit disc about an integer `k` is not an integer. -/
theorem not_int_of_mem_annulus {k : ℕ} {z : ℂ} {R : ℝ} (hR1 : R ≤ 1)
    (hz : z ∈ annulus (k : ℂ) 0 R) : ∀ n : ℤ, z ≠ n := fun n hn => by
  obtain ⟨h0, h1⟩ := hz
  rw [hn, ← Int.cast_natCast, ← Int.cast_sub, Complex.norm_intCast] at h0 h1
  have h2 : (1 : ℝ) ≤ |((n - k : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (fun h => by
      rw [h] at h0
      simp at h0)
  linarith

theorem GammaNum_neg_nat_sq (m : ℕ) : GammaNum m (-(m : ℂ)) ^ 2 = 1 / (m ! : ℂ) ^ 2 := by
  rw [GammaNum_neg_nat, div_pow, ← pow_mul, mul_comm, pow_mul]
  simp

/-- **DLMF 2.5.46**: for `k = m + 1 ≥ 1` and `ζ > 0`,
`res_{z=k} [−ζ^{z−1} Γ(1 − z) π csc(πz)] = (−ln ζ + ψ(k)) ζ^{k−1}/(k − 1)!`. -/
theorem dlmf_2_5_46 {ζ : ℝ} (hζ : 0 < ζ) (m : ℕ) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) :
    residue (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * (π / sin (π * z))))) (m + 1) R =
      (-(Real.log ζ : ℂ) + digamma (m + 1)) * (ζ : ℂ) ^ (m : ℂ) / m ! := by
  have hζ0 : (ζ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hζ.ne'
  set A : ℂ → ℂ := fun z => -((ζ : ℂ) ^ (z - 1) * Gamma z * GammaNum m (1 - z) ^ 2) with hA
  have hball : ∀ z ∈ ball ((m : ℂ) + 1) R, 1 - z ∈ ball (-(m : ℂ)) 1 := fun z hz => by
    rw [mem_ball, dist_eq_norm] at hz ⊢
    rw [show (1 : ℂ) - z - -(m : ℂ) = -(z - ((m : ℂ) + 1)) by ring, norm_neg]
    exact hz.trans_le hR1
  have hAd : DifferentiableOn ℂ A (ball ((m : ℂ) + 1) R) := by
    intro z hz
    have hre : (m : ℝ) < z.re := by
      rw [mem_ball, dist_eq_norm] at hz
      have := (abs_le.mp (abs_re_le_norm (z - ((m : ℂ) + 1)))).1
      simp only [sub_re, add_re, natCast_re, one_re] at this
      linarith
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.neg (DifferentiableAt.mul
      (DifferentiableAt.mul ?_ ?_) ?_))
    · exact (differentiable_cpow_sub_one hζ) z
    · exact differentiableAt_Gamma _ fun n h => by
        have := congrArg Complex.re h
        simp at this
        linarith [n.cast_nonneg (α := ℝ)]
    · exact (((differentiableOn_GammaNum m).differentiableAt
        (isOpen_ball.mem_nhds (hball z hz))).comp z
        ((differentiableAt_const _).sub differentiableAt_id)).pow 2
  have hFeq : ∀ z ∈ annulus ((m : ℂ) + 1) 0 R,
      -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * (π / sin (π * z)))) = A z / (z - ((m : ℂ) + 1)) ^ 2 :=
    fun z hz => by
      have hz' : ∀ n : ℤ, z ≠ n := not_int_of_mem_annulus (k := m + 1) hR1 (by
        rw [show (((m + 1 : ℕ) : ℂ)) = (m : ℂ) + 1 by push_cast; rfl]; exact hz)
      have hpole : ∀ j ≤ m, (1 - z) + (j : ℂ) ≠ 0 := fun j _ h =>
        hz' (j + 1) (by push_cast; linear_combination -h)
      have hsin := sin_pi_mul_ne_zero hz'
      have hzk : z - ((m : ℂ) + 1) ≠ 0 := fun h => hz' (m + 1) (by push_cast; linear_combination h)
      rw [← Gamma_mul_Gamma_one_sub z, show Gamma (1 - z) = -(GammaNum m (1 - z) / (z - (m + 1))) by
        rw [← neg_Gamma_one_sub_eq hpole, neg_neg], hA]
      field_simp
  rw [residue_eq_deriv_of_eq_div_sq hR hAd hFeq]
  -- the derivative of `A` at `m + 1`
  have h1 : HasDerivAt (fun z : ℂ => (ζ : ℂ) ^ (z - 1)) ((ζ : ℂ) ^ (m : ℂ) * Real.log ζ)
      ((m : ℂ) + 1) := by
    have := ((hasDerivAt_id ((m : ℂ) + 1)).sub_const 1).const_cpow (Or.inl hζ0)
    simp only [id, add_sub_cancel_right, mul_one] at this
    rwa [← ofReal_log hζ.le] at this
  have hΓ0 : Gamma ((m : ℂ) + 1) ≠ 0 := by
    rw [Gamma_nat_eq_factorial]; exact_mod_cast m.factorial_ne_zero
  have h2 : HasDerivAt Gamma (digamma (m + 1) * Gamma ((m : ℂ) + 1)) ((m : ℂ) + 1) := by
    have hd := (differentiableAt_Gamma ((m : ℂ) + 1) fun n h => by
      have := congrArg Complex.re h
      simp at this
      linarith [n.cast_nonneg (α := ℝ), m.cast_nonneg (α := ℝ)]).hasDerivAt
    rwa [show deriv Gamma ((m : ℂ) + 1) = digamma (m + 1) * Gamma ((m : ℂ) + 1) by
      rw [digamma_def, logDeriv_apply, div_mul_cancel₀ _ hΓ0]] at hd
  have h3 : HasDerivAt (fun z : ℂ => GammaNum m (1 - z))
      (-(GammaNum m (-(m : ℂ)) * digamma (m + 1))) ((m : ℂ) + 1) := by
    have hg := hasDerivAt_GammaNum_neg_nat m
    rw [show -(m : ℂ) = 1 - ((m : ℂ) + 1) by ring] at hg
    have := hg.comp ((m : ℂ) + 1) ((hasDerivAt_const _ (1 : ℂ)).sub (hasDerivAt_id _))
    simp only [zero_sub, mul_neg, mul_one] at this
    rwa [show (1 : ℂ) - ((m : ℂ) + 1) = -(m : ℂ) by ring] at this
  have hAderiv : HasDerivAt A (-(((ζ : ℂ) ^ (m : ℂ) * Real.log ζ * Gamma ((m : ℂ) + 1) +
      (ζ : ℂ) ^ ((m : ℂ) + 1 - 1) * (digamma (m + 1) * Gamma ((m : ℂ) + 1))) *
        GammaNum m (1 - ((m : ℂ) + 1)) ^ 2 + (ζ : ℂ) ^ ((m : ℂ) + 1 - 1) * Gamma ((m : ℂ) + 1) *
        (↑(2 : ℕ) * GammaNum m (1 - ((m : ℂ) + 1)) ^ (2 - 1) *
          -(GammaNum m (-(m : ℂ)) * digamma (m + 1))))) ((m : ℂ) + 1) :=
    ((h1.mul h2).mul (h3.pow 2)).neg
  rw [hAderiv.deriv, show (1 : ℂ) - ((m : ℂ) + 1) = -(m : ℂ) by ring,
    show (m : ℂ) + 1 - 1 = m by ring, Gamma_nat_eq_factorial]
  simp only [show (2 : ℕ) - 1 = 1 by norm_num, pow_one, Nat.cast_ofNat]
  have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hsq : GammaNum m (-(m : ℂ)) ^ 2 * (m ! : ℂ) ^ 2 = 1 := by
    rw [GammaNum_neg_nat_sq]
    field_simp
  rw [eq_div_iff hm]
  linear_combination ((ζ : ℂ) ^ (m : ℂ) * (digamma (m + 1) - Real.log ζ)) * hsq

/-- **DLMF 2.5.47**: `res_{z=1} [−ζ^{z−1} Γ(1 − z) 𝓜h₂(z)] = (−ln ζ − γ) − 𝓜h₁(1)`, with `𝓜h₂`
continued (2.5.28: `𝓜h₂ = π csc(πz) − 𝓜h₁`). -/
theorem dlmf_2_5_47 {ζ : ℝ} (hζ : 0 < ζ) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) :
    residue (fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * contH₂ z))) 1 R =
      (-(Real.log ζ : ℂ) - Real.eulerMascheroniConstant) - mellin (trunc₁ oneDivOneAdd) 1 := by
  have hann : ∀ z ∈ annulus (1 : ℂ) 0 R, (∀ n : ℤ, z ≠ n) ∧ 0 < z.re := fun z hz => by
    refine ⟨not_int_of_mem_annulus (k := 1) hR1 (by simpa using hz), ?_⟩
    have := (abs_le.mp (abs_re_le_norm (z - 1))).1
    rw [sub_re, one_re] at this
    linarith [hz.2]
  have hfree : ∀ z ∈ ball (1 : ℂ) R, z ≠ 1 → ∀ n : ℕ, z ≠ n + 1 := fun z hz hz1 n h => by
    have hz' : z ∈ annulus (1 : ℂ) 0 R := ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hz1), by
      rw [mem_ball, dist_eq_norm] at hz; exact hz⟩
    exact (hann z hz').1 (n + 1) (by rw [h]; push_cast; rfl)
  -- `F = F_full + (−F₁)` on the punctured disc
  set F₁ : ℂ → ℂ := fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * mellin (trunc₁ oneDivOneAdd) z))
    with hF₁def
  set Ff : ℂ → ℂ := fun z => -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * (π / sin (π * z)))) with hFfdef
  have hΓd : ∀ z ∈ annulus (1 : ℂ) 0 R, DifferentiableAt ℂ (fun z => Gamma (1 - z)) z := fun z hz =>
    differentiableAt_Gamma_one_sub fun n h => (hann z hz).1 (n + 1) (by rw [h]; push_cast; rfl)
  have hF₁d : DifferentiableOn ℂ F₁ (annulus (1 : ℂ) 0 R) := fun z hz =>
    ((((differentiable_cpow_sub_one hζ) z).mul ((hΓd z hz).mul
      (laplaceSmallSetup_oneDivOneAdd.differentiableAt_h₁
        (by simpa using (hann z hz).2)))).neg).differentiableWithinAt
  have hFfd : DifferentiableOn ℂ Ff (annulus (1 : ℂ) 0 R) := fun z hz =>
    ((((differentiable_cpow_sub_one hζ) z).mul ((hΓd z hz).mul ((differentiableAt_const _).div
      (((differentiableAt_const _).mul differentiableAt_id).csin)
      (sin_pi_mul_ne_zero (hann z hz).1)))).neg).differentiableWithinAt
  have hcongr : ∀ z ∈ annulus (1 : ℂ) 0 R,
      -((ζ : ℂ) ^ (z - 1) * (Gamma (1 - z) * contH₂ z)) = Ff z + -F₁ z := fun z hz => by
    rw [contH₂_eq_sub (hann z hz).2 (hann z hz).1]
    simp only [Ff, F₁]
    ring
  have hnF₁ : DifferentiableOn ℂ (fun z => -F₁ z) (annulus (1 : ℂ) 0 R) := hF₁d.neg
  rw [residue_congr hR hcongr, residue_add hR hFfd hnF₁, residue_neg F₁]
  have h46 := dlmf_2_5_46 hζ 0 hR hR1
  simp only [Nat.cast_zero, zero_add, Nat.factorial_zero, Nat.cast_one, div_one, cpow_zero,
    mul_one, digamma_one] at h46
  have h41 := residue_neg_cpow_Gamma_mul hζ (A := mellin (trunc₁ oneDivOneAdd)) 0 hR
    (fun z hz => (laplaceSmallSetup_oneDivOneAdd.differentiableAt_h₁ (by
      rw [mem_ball, dist_eq_norm, Nat.cast_zero, zero_add] at hz
      have := (abs_le.mp (abs_re_le_norm (z - 1))).1
      rw [sub_re, one_re] at this
      simp
      linarith)).differentiableWithinAt)
    (by simpa using hfree)
  simp only [Nat.cast_zero, zero_add, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    cpow_zero, one_mul] at h41
  rw [hFfdef, hF₁def, h46, h41]
  ring

end Azurite.DLMF
