/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section5LaplaceExample
import Azurite.DLMF.Chapter2.Section6StieltjesExpansion

/-!
# DLMF §2.6: the expansion 2.6.7 of `S(x) = ∫₀^∞ dt/((1 + t)^{1/3}(x + t))`

DLMF: "The expansion (2.6.7) follows immediately from (2.6.27) with `z = x` and
`f(t) = (1 + t)^{−1/3}`". Here `f` is `cbrtInv`, with `aₛ = binom(−1/3, s)` (`binomThird`) and
`α = 1/3`:

* `cbrtInv_setup`: `f` satisfies the hypotheses of §2.6(ii) (`StieltjesSetup`), the expansion at
  `∞` coming from the binomial series (`one_add_rpow_sub_sum_isBigO`).
* `mellin_cbrtInv`: `𝓜f(w) = Γ(w) Γ(1/3 − w)/Γ(1/3)` on `0 < ℜw < 1/3` (the beta integral 2.6.4
  with `x = 1`), and `cbrtCont_eq_of_ne`: the continued transform `𝓜f₁ + [𝓜f₂]_cont` equals
  `Γ(w) Γ(1/3 − w)/Γ(1/3)` away from the poles `−s` and `s + 1/3` (identity theorem on the
  complement of a closed countable set, plus continuity at the integers `n + 1`).
* `mellinCont_cbrtInv_succ`, `factorial_mul_stieltjesC`: the coefficients of 2.6.18 become
  `s! c_{s+1} = 3^{s+1} s!/(2·5⋯(3s+2))` (`dlmfB s`), DLMF's `3^s (s−1)!/(2·5⋯(3s−1))` for the
  index `s + 1`.
* 2.6.7 (`dlmf_2_6_7_remainder`): for every `n`,
  `S(x) − (2π/√3) ∑_{s<n} (−1)^s binom(−1/3, s) x^{−s−1/3} + ∑_{s<n} dlmfB s · x^{−s−1} =
  O(x^{−n−1/3})` as `x → +∞`, i.e. 2.6.7 as a generalized asymptotic expansion along the
  positive axis (`dlmf_2_6_7`, with the interleaved scale `x^{−1/3}, x^{−1}, x^{−4/3}, x^{−2}, …`).
  DLMF also states validity for `|ph x| ≤ π − δ`; only real `x` is treated here
  (`docs/dlmf_plan.md`).
* `dlmf_2_6_6_false`: the formal result 2.6.6 is *not* an asymptotic expansion of `S(x)` (the
  remainder after one term is `−(3/2) x^{−1} + O(x^{−4/3})`, not `O(x^{−4/3})`).
-/

open MeasureTheory Filter Topology Set Complex Asymptotics
open scoped Real Nat

namespace Azurite.DLMF

/-! ### The binomial remainder and `O`-bookkeeping -/

/-- `(1 + y)^a − ∑_{s<n} binom(a, s) y^s = O(y^n)` as `y → 0`. -/
theorem one_add_rpow_sub_sum_isBigO (a : ℝ) (n : ℕ) :
    (fun y : ℝ => (1 + y) ^ a - ∑ s ∈ Finset.range n, Ring.choose a s * y ^ s) =O[𝓝 0]
      fun y => ‖y‖ ^ n := by
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := a)).hasFPowerSeriesAt
    |>.isBigO_sub_partialSum_pow n
  refine h.congr' (Eventually.of_forall fun y => ?_) EventuallyEq.rfl
  simp only [zero_add, FormalMultilinearSeries.partialSum, binomialSeries_apply, List.prod_ofFn,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- From Mathlib's `O(t^{−ℜw})` at `∞` to DLMF's `O(t^{−w})`. -/
theorem isBigODLMF_cpow_top_of_isBigO_rpow {g : ℝ → ℂ} {w : ℂ} (h : g =O[atTop] (· ^ (-w.re))) :
    IsBigODLMF atTop g fun t : ℝ => (t : ℂ) ^ (-w) := by
  have hne : ∀ᶠ t : ℝ in atTop, (t : ℂ) ^ (-w) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact fun h => ofReal_ne_zero.mpr ht.ne' ((cpow_eq_zero_iff _ _).mp h).1
  refine (dlmf_2_1_3 hne).mpr (h.trans (IsBigO.of_bound 1 ?_))
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_cpow_eq_rpow_re_of_pos ht, one_mul, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),
    neg_re]

/-- From Mathlib's `O(t^{ℜw})` at `0+` to DLMF's `O(t^w)`. -/
theorem isBigODLMF_cpow_zero_of_isBigO_rpow {g : ℝ → ℂ} {w : ℂ} (h : g =O[𝓝[>] 0] (· ^ w.re)) :
    IsBigODLMF (𝓝[>] (0 : ℝ)) g fun t : ℝ => (t : ℂ) ^ w := by
  have hne : ∀ᶠ t : ℝ in 𝓝[>] 0, (t : ℂ) ^ w ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact fun h => ofReal_ne_zero.mpr (ne_of_gt ht) ((cpow_eq_zero_iff _ _).mp h).1
  refine (dlmf_2_1_3 hne).mpr (h.trans (IsBigO.of_bound 1 ?_))
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht : (0 : ℝ) < t := ht
  rw [norm_cpow_eq_rpow_re_of_pos ht, one_mul, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]

/-- `{t^{−βₛ}}` is an asymptotic scale at `∞` when `ℜβₛ` is increasing. -/
theorem isAsympScale_cpow_neg_atTop (β : ℕ → ℂ) (hβ : ∀ s, (β s).re < (β (s + 1)).re) :
    IsAsympScaleDLMF atTop fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ (-β s) := by
  intro s
  unfold IsLittleODLMF
  have h : Tendsto (fun t : ℝ => (t : ℂ) ^ (β s - β (s + 1))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (tendsto_rpow_neg_atTop (sub_pos.mpr (hβ s))).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [norm_cpow_eq_rpow_re_of_pos ht, sub_re, neg_sub]
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [← cpow_sub _ _ (ofReal_ne_zero.mpr ht.ne')]
  congr 1
  ring

/-! ### `f(t) = (1 + t)^{−1/3}` -/

/-- `f(t) = (1 + t)^{−1/3}`. -/
noncomputable def cbrtInv (t : ℝ) : ℂ := (((1 + t) ^ (-1 / 3 : ℝ) : ℝ) : ℂ)

/-- `aₛ = binom(−1/3, s)`. -/
noncomputable def binomThird (s : ℕ) : ℂ := ((Ring.choose (-1 / 3 : ℝ) s : ℝ) : ℂ)

/-- The remainder at `∞`, as a real expression:
`f(t) − ∑_{s<n} aₛ t^{−s−1/3} = t^{−1/3} ((1 + 1/t)^{−1/3} − ∑_{s<n} aₛ t^{−s})`. -/
theorem cbrtInv_sub_sum_top {t : ℝ} (ht : 0 < t) (n : ℕ) :
    cbrtInv t - ∑ s ∈ Finset.range n, binomThird s * (t : ℂ) ^ (-((s : ℂ) + ((1 / 3 : ℝ) : ℂ))) =
      ((t ^ (-1 / 3 : ℝ) * ((1 + t⁻¹) ^ (-1 / 3 : ℝ) -
        ∑ s ∈ Finset.range n, Ring.choose (-1 / 3 : ℝ) s * t⁻¹ ^ s) : ℝ) : ℂ) := by
  have e1 : (1 + t) ^ (-1 / 3 : ℝ) = t ^ (-1 / 3 : ℝ) * (1 + t⁻¹) ^ (-1 / 3 : ℝ) := by
    rw [← Real.mul_rpow ht.le (by positivity)]
    congr 1
    field_simp
    ring
  have e2 : ∀ s : ℕ, (t : ℂ) ^ (-((s : ℂ) + ((1 / 3 : ℝ) : ℂ))) =
      ((t ^ (-1 / 3 : ℝ) * t⁻¹ ^ s : ℝ) : ℂ) := by
    intro s
    rw [show -((s : ℂ) + ((1 / 3 : ℝ) : ℂ)) = ((-1 / 3 + -(s : ℝ) : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow ht.le, Real.rpow_add ht, Real.rpow_neg ht.le, Real.rpow_natCast, inv_pow]
  simp only [cbrtInv, binomThird, e1, e2]
  push_cast
  rw [mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- `f` satisfies the hypotheses of §2.6(ii) with `aₛ = binom(−1/3, s)`, `α = 1/3`. -/
theorem cbrtInv_setup : StieltjesSetup cbrtInv binomThird (1 / 3) where
  f_loc R := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine continuous_ofReal.comp_continuousOn ?_
    exact (continuousOn_const.add continuousOn_id).rpow_const fun x hx =>
      Or.inl (by show (1 : ℝ) + x ≠ 0; linarith [hx.1])
  f_exp := by
    refine ⟨isAsympScale_cpow_neg_atTop _ fun s => ?_, fun n => ?_⟩
    · simp only [add_re, natCast_re, ofReal_re]
      push_cast
      linarith
    · refine isBigODLMF_cpow_top_of_isBigO_rpow ?_
      have h := (one_add_rpow_sub_sum_isBigO (-1 / 3) n).comp_tendsto tendsto_inv_atTop_zero
      have h2 := (isBigO_refl (fun t : ℝ => t ^ (-1 / 3 : ℝ)) atTop).mul h
      refine (isBigO_ofReal_left.mpr h2).congr' ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with t ht
        exact (cbrtInv_sub_sum_top ht n).symm
      · filter_upwards [eventually_gt_atTop 0] with t ht
        simp only [Function.comp_apply, add_re, natCast_re, ofReal_re]
        rw [Real.norm_of_nonneg (inv_nonneg.mpr ht.le), inv_pow, ← Real.rpow_natCast,
          ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
        congr 1
        ring
  α_pos := by norm_num
  α_le := by norm_num

/-- The expansion of `f` at `0+`: `f(t) ∼ ∑ binom(−1/3, s) t^s` (the binomial series). -/
theorem cbrtInv_exp_zero :
    IsGenAsympExpansionDLMF (𝓝[>] (0 : ℝ)) (fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ (s : ℂ)) cbrtInv
      fun s t => binomThird s * (t : ℂ) ^ (s : ℂ) := by
  refine ⟨fun s => ?_, fun n => ?_⟩
  · unfold IsLittleODLMF
    have h0 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 0) := by
      have := (continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    refine h0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    rw [← cpow_sub _ _ ht0]
    push_cast
    rw [show (s : ℂ) + 1 - s = 1 by ring, cpow_one]
  · refine isBigODLMF_cpow_zero_of_isBigO_rpow ?_
    rw [natCast_re]
    have h := (one_add_rpow_sub_sum_isBigO (-1 / 3) n).mono
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    refine (isBigO_ofReal_left.mpr h).congr' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t _
      simp only [cbrtInv, binomThird, ofReal_sub, ofReal_sum, ofReal_mul, ofReal_pow,
        cpow_natCast]
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht : (0 : ℝ) < t := ht
      rw [Real.norm_of_nonneg ht.le, Real.rpow_natCast]

/-! ### The Mellin transform and its continuation -/

/-- `𝓜f(w) = Γ(w) Γ(1/3 − w)/Γ(1/3)` for `0 < ℜw < 1/3` (2.6.4 with `x = 1`). -/
theorem mellin_cbrtInv {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1 / 3) :
    mellin cbrtInv w = Gamma w * Gamma (1 / 3 - w) / Gamma (1 / 3) := by
  have h := dlmf_2_6_4 (α := w) (β := 1 / 3 - w) h0 (by simp; linarith) one_pos
  rw [add_sub_cancel, ofReal_one, one_cpow, mul_one] at h
  rw [← h, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht : (0 : ℝ) < t := ht
  have e : ((1 + t : ℝ) : ℂ) ^ (((-1 / 3 : ℝ)) : ℂ) = (((1 + t : ℝ) : ℂ) ^ (1 / 3 : ℂ))⁻¹ := by
    rw [← cpow_neg]
    congr 1
    push_cast
    ring
  rw [smul_eq_mul, cbrtInv, ofReal_cpow (by linarith : (0 : ℝ) ≤ 1 + t), e,
    div_eq_mul_inv ((t : ℂ) ^ (w - 1))]

/-- The continued transform `𝓜f₁ + [𝓜f₂]_cont` (2.5.25 at `0+` and 2.5.27 at `∞`). -/
noncomputable def cbrtCont (w : ℂ) : ℂ :=
  mellinTrunc₁Cont cbrtInv binomThird (fun s : ℕ => (s : ℂ)) w +
    mellinTrunc₂ContZero cbrtInv binomThird (fun s : ℕ => (s : ℂ) + ((1 / 3 : ℝ) : ℂ)) w

/-- A closed countable set containing the poles `−s` and `s + 1/3`: `ℤ ∪ (ℤ + 1/3)`. -/
def cbrtPoles : Set ℂ :=
  range ((↑) : ℤ → ℂ) ∪ (fun z => z + 1 / 3) '' range ((↑) : ℤ → ℂ)

theorem isClosed_cbrtPoles : IsClosed cbrtPoles :=
  isClosed_range_intCast.union
    ((Homeomorph.addRight (1 / 3 : ℂ)).isClosedMap _ isClosed_range_intCast)

theorem countable_cbrtPoles : cbrtPoles.Countable :=
  (countable_range _).union ((countable_range _).image _)

theorem ne_of_notMem_cbrtPoles {w : ℂ} (hw : w ∉ cbrtPoles) :
    (∀ s : ℕ, w ≠ -s) ∧ ∀ s : ℕ, w ≠ s + 1 / 3 := by
  refine ⟨fun s h => hw (Or.inl ⟨-(s : ℤ), by rw [h]; push_cast; ring⟩),
    fun s h => hw (Or.inr ⟨(s : ℤ), ⟨s, rfl⟩, by rw [h]; push_cast; ring⟩)⟩

theorem differentiableAt_cbrtCont {w : ℂ} (h1 : ∀ s : ℕ, w ≠ -s) (h2 : ∀ s : ℕ, w ≠ s + 1 / 3) :
    DifferentiableAt ℂ cbrtCont w := by
  have hA := (dlmf_2_5_25 α_mono cbrtInv_exp_zero cbrtInv_setup.hloc α_tendsto).2.1 w h1
  have hB := differentiableAt_mellinTrunc₂ContZero cbrtInv_setup.hloc
    (StieltjesSetup.β_mono (α := 1 / 3)) (StieltjesSetup.β_tendsto (α := 1 / 3))
    cbrtInv_setup.f_exp (z := w) fun s h => h2 s (by rw [h]; push_cast; ring)
  exact hA.add hB

theorem differentiableAt_gammaRatio {w : ℂ} (h1 : ∀ s : ℕ, w ≠ -s) (h2 : ∀ s : ℕ, w ≠ s + 1 / 3) :
    DifferentiableAt ℂ (fun w : ℂ => Gamma w * Gamma (1 / 3 - w) / Gamma (1 / 3)) w := by
  refine ((differentiableAt_Gamma w h1).mul ?_).div_const _
  refine (differentiableAt_Gamma (1 / 3 - w) fun s h => h2 s ?_).comp w
    ((differentiableAt_const _).sub differentiableAt_id)
  linear_combination -h

/-- `cbrtCont = Γ(w) Γ(1/3 − w)/Γ(1/3)` off `ℤ ∪ (ℤ + 1/3)`, by the identity theorem. -/
theorem cbrtCont_eq {w : ℂ} (hw : w ∉ cbrtPoles) :
    cbrtCont w = Gamma w * Gamma (1 / 3 - w) / Gamma (1 / 3) := by
  set U : Set ℂ := cbrtPolesᶜ with hU
  have hUo : IsOpen U := isClosed_cbrtPoles.isOpen_compl
  have hUc : IsPreconnected U :=
    (countable_cbrtPoles.isConnected_compl_of_one_lt_rank (by
      rw [rank_real_complex]; norm_num)).isPreconnected
  have hf : AnalyticOnNhd ℂ cbrtCont U :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      (differentiableAt_cbrtCont (ne_of_notMem_cbrtPoles hw).1
        (ne_of_notMem_cbrtPoles hw).2).differentiableWithinAt) hUo
  have hg : AnalyticOnNhd ℂ (fun w : ℂ => Gamma w * Gamma (1 / 3 - w) / Gamma (1 / 3)) U :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      (differentiableAt_gammaRatio (ne_of_notMem_cbrtPoles hw).1
        (ne_of_notMem_cbrtPoles hw).2).differentiableWithinAt) hUo
  have h₀ : (1 / 6 : ℂ) ∈ U := by
    rintro (⟨n, hn⟩ | ⟨_, ⟨n, rfl⟩, hn⟩)
    · have := congrArg Complex.re hn
      simp at this
      have h6 : (6 : ℝ) * n = 1 := by linarith
      have : (6 : ℤ) * n = 1 := by exact_mod_cast h6
      omega
    · have := congrArg Complex.re hn
      simp at this
      have h6 : (6 : ℝ) * n = -1 := by linarith
      have : (6 : ℤ) * n = -1 := by exact_mod_cast h6
      omega
  have hfg : cbrtCont =ᶠ[𝓝 (1 / 6 : ℂ)] fun w => Gamma w * Gamma (1 / 3 - w) / Gamma (1 / 3) := by
    filter_upwards [Metric.ball_mem_nhds (1 / 6 : ℂ) (by norm_num : (0 : ℝ) < 1 / 6)] with w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hre := abs_re_le_norm (w - 1 / 6)
    rw [sub_re, show ((1 / 6 : ℂ)).re = 1 / 6 by norm_num] at hre
    have h1 : 0 < w.re := by linarith [(abs_lt.mp (hre.trans_lt hw)).1]
    have h2 : w.re < 1 / 3 := by linarith [(abs_lt.mp (hre.trans_lt hw)).2]
    have hc₁ : MellinConvergent (trunc₁ cbrtInv) w := by
      have hb := isBigO_rpow_re_of_isBigODLMF_cpow_zero (cbrtInv_exp_zero.2 0)
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero, Nat.cast_zero, zero_re] at hb
      exact mellinConvergent_trunc₁ cbrtInv_setup.hloc hb (by simpa using h1)
    have hc₂ : MellinConvergent (trunc₂ cbrtInv) w :=
      mellinConvergent_trunc₂ cbrtInv_setup.hloc cbrtInv_setup.f_isBigO h2
    rw [cbrtCont, (dlmf_2_5_25 α_mono cbrtInv_exp_zero cbrtInv_setup.hloc α_tendsto).1 w
      (by simpa using h1), mellinTrunc₂ContZero_eq cbrtInv_setup.hloc
      (StieltjesSetup.β_mono (α := 1 / 3)) (StieltjesSetup.β_tendsto (α := 1 / 3))
      cbrtInv_setup.f_exp (by simpa using h2), ← mellin_eq_trunc_add hc₁ hc₂, mellin_cbrtInv h1 h2]
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc h₀ hfg hw

/-- `cbrtCont = Γ(w) Γ(1/3 − w)/Γ(1/3)` at every non-pole, by continuity from the dense
set `ℂ ∖ (ℤ ∪ (ℤ + 1/3))`. -/
theorem cbrtCont_eq_of_ne {w : ℂ} (h1 : ∀ s : ℕ, w ≠ -s) (h2 : ∀ s : ℕ, w ≠ s + 1 / 3) :
    cbrtCont w = Gamma w * Gamma (1 / 3 - w) / Gamma (1 / 3) := by
  have hc1 : ContinuousAt cbrtCont w := (differentiableAt_cbrtCont h1 h2).continuousAt
  have hc2 : ContinuousAt (fun w : ℂ => Gamma w * Gamma (1 / 3 - w) / Gamma (1 / 3)) w :=
    (differentiableAt_gammaRatio h1 h2).continuousAt
  have hdense : Dense cbrtPolesᶜ := Set.Countable.dense_compl ℂ countable_cbrtPoles
  have hne : (𝓝[cbrtPolesᶜ] w).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by rw [hdense.closure_eq]; exact mem_univ w)
  refine tendsto_nhds_unique (hc1.continuousWithinAt (s := cbrtPolesᶜ))
    (Tendsto.congr' ?_ (hc2.continuousWithinAt (s := cbrtPolesᶜ)))
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact (cbrtCont_eq hv).symm

/-- The continued Mellin transform of 2.6.18 for `f`: `𝓜f(w) = Γ(w) Γ(1/3 − w)/Γ(1/3)` for
`ℜw > 0`, `w ≠ s + 1/3`. -/
theorem mellinCont_cbrtInv_eq {w : ℂ} (hw : 0 < w.re) (h2 : ∀ s : ℕ, w ≠ s + 1 / 3) :
    mellinCont cbrtInv binomThird (1 / 3) w = Gamma w * Gamma (1 / 3 - w) / Gamma (1 / 3) := by
  have h1 : ∀ s : ℕ, w ≠ -s := fun s h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
  rw [← cbrtCont_eq_of_ne h1 h2, cbrtCont, mellinCont]
  congr 1
  rw [mellinTrunc₁Cont_eq α_mono cbrtInv_exp_zero cbrtInv_setup.hloc (N := 0)
    ⟨by simpa using hw, fun s hs => absurd hs (Nat.not_lt_zero s)⟩, mellinTrunc₁Ext_zero]

/-! ### The coefficients -/

theorem natCast_add_one_ne_add_third (n s : ℕ) : (n : ℂ) + 1 ≠ s + 1 / 3 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  have h3 : ((3 * n + 3 : ℕ) : ℝ) = ((3 * s + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have := Nat.cast_injective h3
  omega

/-- `𝓜f(n + 1) = n! (−1)^{n+1} 3^{n+1}/(2·5⋯(3n+2))`. -/
theorem mellinCont_cbrtInv_succ (n : ℕ) :
    mellinCont cbrtInv binomThird (1 / 3) ((n : ℂ) + 1) =
      (n ! : ℂ) * ((-1) ^ (n + 1) * 3 ^ (n + 1) /
        ∏ k ∈ Finset.range (n + 1), ((3 * k + 2 : ℕ) : ℂ)) := by
  rw [mellinCont_cbrtInv_eq (by simp; positivity) (natCast_add_one_ne_add_third n)]
  have hG := Gamma_add_nat_eq_prod_mul (1 / 3 - ((n : ℂ) + 1)) (n + 1) fun j hj h => by
    have := congrArg Complex.re h
    simp at this
    have h3 : ((3 * j + 1 : ℕ) : ℝ) = ((3 * n + 3 : ℕ) : ℝ) := by
      push_cast
      linarith
    have := Nat.cast_injective h3
    omega
  rw [show (1 / 3 : ℂ) - ((n : ℂ) + 1) + ((n + 1 : ℕ) : ℂ) = 1 / 3 by push_cast; ring] at hG
  have hprod : ∏ j ∈ Finset.range (n + 1), ((1 / 3 : ℂ) - ((n : ℂ) + 1) + j) =
      (-1) ^ (n + 1) / 3 ^ (n + 1) * ∏ k ∈ Finset.range (n + 1), ((3 * k + 2 : ℕ) : ℂ) := by
    have : ∀ j ∈ Finset.range (n + 1), (1 / 3 : ℂ) - ((n : ℂ) + 1) + j =
        (-1 / 3) * ((3 * (n + 1 - 1 - j) + 2 : ℕ) : ℂ) := by
      intro j hj
      have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [Nat.add_sub_cancel]
      push_cast [Nat.cast_sub hj']
      ring
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_range_reflect (fun k => ((3 * k + 2 : ℕ) : ℂ)) (n + 1), ← div_pow]
  have hP : (∏ k ∈ Finset.range (n + 1), ((3 * k + 2 : ℕ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => by exact_mod_cast (by omega : 3 * k + 2 ≠ 0)
  have hΓ : Gamma (1 / 3 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hc : ((-1 : ℂ) ^ (n + 1) / 3 ^ (n + 1) * ∏ k ∈ Finset.range (n + 1), ((3 * k + 2 : ℕ) : ℂ))
      ≠ 0 :=
    mul_ne_zero (div_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))) hP
  rw [hprod] at hG
  have hΓ' : Gamma (1 / 3 - ((n : ℂ) + 1)) =
      Gamma (1 / 3) / ((-1) ^ (n + 1) / 3 ^ (n + 1) *
        ∏ k ∈ Finset.range (n + 1), ((3 * k + 2 : ℕ) : ℂ)) := by
    rw [eq_div_iff hc, hG]
    ring
  rw [Gamma_nat_eq_factorial, hΓ']
  rcases neg_one_pow_eq_or ℂ (n + 1) with h | h <;> rw [h] <;> field_simp

/-- DLMF's coefficients `3^{s+1} s!/(2·5⋯(3s+2))` (the index `s + 1` of 2.6.7). -/
noncomputable def dlmfB (s : ℕ) : ℝ :=
  3 ^ (s + 1) * s ! / ∏ k ∈ Finset.range (s + 1), ((3 * k + 2 : ℕ) : ℝ)

/-- `s! c_{s+1} = 3^{s+1} s!/(2·5⋯(3s+2))`. -/
theorem factorial_mul_stieltjesC (s : ℕ) :
    (s ! : ℂ) * stieltjesC cbrtInv binomThird (1 / 3) (s + 1) = (dlmfB s : ℂ) := by
  rw [stieltjesC, Nat.add_sub_cancel, Nat.cast_succ, mellinCont_cbrtInv_succ, dlmfB]
  push_cast
  have hP : (∏ k ∈ Finset.range (s + 1), ((3 * k + 2 : ℕ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => by exact_mod_cast (by omega : 3 * k + 2 ≠ 0)
  have hf : (s ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s)
  rcases neg_one_pow_eq_or ℂ (s + 1) with h | h <;> rw [h] <;> field_simp

/-! ### 2.6.7 -/

/-- `𝓢f(x) = S(x)` for `x > 0`. -/
theorem stieltjesT_cbrtInv {x : ℝ} (hx : 0 < x) : stieltjesT cbrtInv x = (dlmfS x : ℂ) := by
  rw [stieltjesT, dlmfS, show ((∫ t in Ioi (0 : ℝ), 1 / ((1 + t) ^ (1 / 3 : ℝ) * (x + t)) : ℝ) :
    ℂ) = @RCLike.ofReal ℂ _ (∫ t in Ioi (0 : ℝ), 1 / ((1 + t) ^ (1 / 3 : ℝ) * (x + t))) from rfl,
    ← integral_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht : (0 : ℝ) < t := ht
  change cbrtInv t / ((t : ℂ) + x) = ((1 / ((1 + t) ^ (1 / 3 : ℝ) * (x + t)) : ℝ) : ℂ)
  rw [cbrtInv, show (-1 / 3 : ℝ) = -(1 / 3) by norm_num, Real.rpow_neg (by linarith)]
  push_cast
  have h1 : (((1 + t) ^ (1 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by linarith) _).ne'
  have h2 : (t : ℂ) + x ≠ 0 := ofReal_add_ne_zero (ofReal_mem_slitPlane.mpr hx) ht.le
  have h3 : (x : ℂ) + t ≠ 0 := by rw [add_comm]; exact h2
  field_simp
  ring

/-- `π/sin(π/3) = 2π/√3`. -/
theorem pi_div_sin_pi_third : (π : ℂ) / Complex.sin (π * ((1 / 3 : ℝ) : ℂ)) =
    ((2 * π / Real.sqrt 3 : ℝ) : ℂ) := by
  rw [← ofReal_mul, ← ofReal_sin, show π * (1 / 3) = π / 3 by ring, Real.sin_pi_div_three]
  push_cast
  have : Real.sqrt 3 ≠ 0 := by positivity
  field_simp

/-- **DLMF 2.6.7**, the remainder form: for every `n`,
`S(x) = (2π/√3) ∑_{s<n} (−1)^s binom(−1/3, s) x^{−s−1/3} − ∑_{s<n} dlmfB s · x^{−s−1} +
O(x^{−n−1/3})` as `x → +∞`. -/
theorem dlmf_2_6_7_remainder (n : ℕ) :
    (fun x : ℝ => dlmfS x - (2 * π / Real.sqrt 3 *
        ∑ s ∈ Finset.range n, (-1) ^ s * Ring.choose (-1 / 3 : ℝ) s * x ^ (-((s : ℝ) + 1 / 3)) -
      ∑ s ∈ Finset.range n, dlmfB s * x ^ (-((s : ℝ) + 1)))) =O[atTop]
      fun x => x ^ (-((n : ℝ) + 1 / 3)) := by
  have h := cbrtInv_setup.stieltjesR_isBigO (by norm_num) n
  rw [← isBigO_ofReal_left]
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with x hx
  have h27 := cbrtInv_setup.dlmf_2_6_27 (by norm_num) (ofReal_mem_slitPlane.mpr hx) n
  rw [stieltjesT_cbrtInv hx] at h27
  have e : stieltjesR cbrtInv binomThird (1 / 3) n x = (dlmfS x : ℂ) -
      (π / Complex.sin (π * ((1 / 3 : ℝ) : ℂ)) *
        ∑ s ∈ Finset.range n, (-1) ^ s * binomThird s * (x : ℂ) ^ (-((s : ℂ) + ((1 / 3 : ℝ) : ℂ))) -
      ∑ s ∈ Finset.range n, (s ! : ℂ) * stieltjesC cbrtInv binomThird (1 / 3) (s + 1) /
        (x : ℂ) ^ (s + 1)) := by
    rw [h27]
    ring
  have hA : ∀ s : ℕ, (-1 : ℂ) ^ s * binomThird s * (x : ℂ) ^ (-((s : ℂ) + ((1 / 3 : ℝ) : ℂ))) =
      (((-1) ^ s * Ring.choose (-1 / 3 : ℝ) s * x ^ (-((s : ℝ) + 1 / 3)) : ℝ) : ℂ) := fun s => by
    rw [binomThird, show -((s : ℂ) + ((1 / 3 : ℝ) : ℂ)) = ((-((s : ℝ) + 1 / 3) : ℝ) : ℂ) by
      push_cast; ring, ← ofReal_cpow hx.le]
    push_cast
    ring
  have hB : ∀ s : ℕ, (s ! : ℂ) * stieltjesC cbrtInv binomThird (1 / 3) (s + 1) / (x : ℂ) ^ (s + 1) =
      ((dlmfB s * x ^ (-((s : ℝ) + 1)) : ℝ) : ℂ) := fun s => by
    rw [factorial_mul_stieltjesC, show -((s : ℝ) + 1) = -(((s + 1 : ℕ) : ℝ)) by push_cast; ring,
      Real.rpow_neg hx.le, Real.rpow_natCast]
    push_cast
    ring
  rw [e, pi_div_sin_pi_third]
  simp only [hA, hB]
  push_cast
  ring

/-! ### 2.6.7 as a generalized asymptotic expansion -/

/-- The error after `n` pairs of terms of 2.6.7. -/
noncomputable def dlmfE (n : ℕ) (x : ℝ) : ℝ :=
  dlmfS x - (2 * π / Real.sqrt 3 *
      ∑ s ∈ Finset.range n, (-1) ^ s * Ring.choose (-1 / 3 : ℝ) s * x ^ (-((s : ℝ) + 1 / 3)) -
    ∑ s ∈ Finset.range n, dlmfB s * x ^ (-((s : ℝ) + 1)))

theorem dlmfE_isBigO (n : ℕ) : dlmfE n =O[atTop] fun x => x ^ (-((n : ℝ) + 1 / 3)) :=
  dlmf_2_6_7_remainder n

/-- The scale of 2.6.7: `x^{−1/3}, x^{−1}, x^{−4/3}, x^{−2}, …`. -/
noncomputable def dlmfScale (s : ℕ) (x : ℝ) : ℝ :=
  if Even s then x ^ (-(((s / 2 : ℕ) : ℝ) + 1 / 3)) else x ^ (-(((s / 2 : ℕ) : ℝ) + 1))

/-- The terms of 2.6.7, interleaved: `(2π/√3)(−1)^k binom(−1/3, k) x^{−k−1/3}` and
`−3^{k+1} k!/(2·5⋯(3k+2)) x^{−k−1}`. -/
noncomputable def dlmfTerms (s : ℕ) (x : ℝ) : ℝ :=
  if Even s then
    2 * π / Real.sqrt 3 * ((-1) ^ (s / 2) * Ring.choose (-1 / 3 : ℝ) (s / 2) *
      x ^ (-(((s / 2 : ℕ) : ℝ) + 1 / 3)))
  else -(dlmfB (s / 2) * x ^ (-(((s / 2 : ℕ) : ℝ) + 1)))

theorem dlmfScale_even (k : ℕ) (x : ℝ) : dlmfScale (2 * k) x = x ^ (-((k : ℝ) + 1 / 3)) := by
  have : 2 * k / 2 = k := by omega
  simp [dlmfScale, this]

theorem dlmfScale_odd (k : ℕ) (x : ℝ) : dlmfScale (2 * k + 1) x = x ^ (-((k : ℝ) + 1)) := by
  have h1 : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k)
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp [dlmfScale, h1, h2]

theorem dlmfTerms_even (k : ℕ) (x : ℝ) : dlmfTerms (2 * k) x =
    2 * π / Real.sqrt 3 * ((-1) ^ k * Ring.choose (-1 / 3 : ℝ) k * x ^ (-((k : ℝ) + 1 / 3))) := by
  have : 2 * k / 2 = k := by omega
  simp [dlmfTerms, this]

theorem dlmfTerms_odd (k : ℕ) (x : ℝ) :
    dlmfTerms (2 * k + 1) x = -(dlmfB k * x ^ (-((k : ℝ) + 1))) := by
  have h1 : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k)
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp [dlmfTerms, h1, h2]

/-- `dlmfS x − ∑_{s<2n} termsₛ(x) = dlmfE n x`. -/
theorem sub_sum_dlmfTerms_even (n : ℕ) (x : ℝ) :
    dlmfS x - ∑ s ∈ Finset.range (2 * n), dlmfTerms s x = dlmfE n x := by
  rw [dlmfE]
  congr 1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, dlmfTerms_even, dlmfTerms_odd, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- The scale property of `dlmfScale`. -/
theorem isAsympScale_dlmfScale : IsAsympScaleDLMF atTop dlmfScale := by
  intro s
  unfold IsLittleODLMF
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' s
  · refine (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [dlmfScale_odd, dlmfScale_even, ← Real.rpow_sub hx]
    congr 1
    ring
  · refine (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, dlmfScale_even, dlmfScale_odd, ← Real.rpow_sub hx]
    congr 1
    push_cast
    ring

/-- **DLMF 2.6.7**: `S(x) ∼ (2π/√3) ∑ (−1)^s binom(−1/3, s) x^{−s−1/3} − ∑_{s≥1}
3^s (s−1)!/(2·5⋯(3s−1)) x^{−s}` as `x → +∞`, as a generalized asymptotic expansion with respect
to the interleaved scale `x^{−1/3}, x^{−1}, x^{−4/3}, x^{−2}, …`. -/
theorem dlmf_2_6_7 : IsGenAsympExpansionDLMF atTop dlmfScale dlmfS dlmfTerms := by
  refine ⟨isAsympScale_dlmfScale, fun N => ?_⟩
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' N
  · have hne : ∀ᶠ x in atTop, dlmfScale (2 * n) x ≠ 0 := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [dlmfScale_even]
      exact (Real.rpow_pos_of_pos hx _).ne'
    refine (dlmf_2_1_3 hne).mpr ((dlmfE_isBigO n).congr' ?_ ?_)
    · exact Eventually.of_forall fun x => (sub_sum_dlmfTerms_even n x).symm
    · exact Eventually.of_forall fun x => (dlmfScale_even n x).symm
  · have hne : ∀ᶠ x in atTop, dlmfScale (2 * n + 1) x ≠ 0 := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [dlmfScale_odd]
      exact (Real.rpow_pos_of_pos hx _).ne'
    refine (dlmf_2_1_3 hne).mpr ?_
    -- `dlmfS − ∑_{s<2n+1} = dlmfE (n+1) + terms (2n+1)`
    have hE : dlmfE (n + 1) =O[atTop] fun x => x ^ (-((n : ℝ) + 1)) := by
      refine (dlmfE_isBigO (n + 1)).trans (IsBigO.of_bound 1 ?_)
      filter_upwards [eventually_ge_atTop 1] with x hx
      rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
        Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
      refine Real.rpow_le_rpow_of_exponent_le hx ?_
      push_cast
      linarith
    have hT : (fun x => dlmfTerms (2 * n + 1) x) =O[atTop] fun x => x ^ (-((n : ℝ) + 1)) := by
      refine ((isBigO_refl (fun x : ℝ => x ^ (-((n : ℝ) + 1))) atTop).const_mul_left
        (-(dlmfB n))).congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
      dsimp only
      rw [dlmfTerms_odd]
      ring
    refine (hE.add hT).congr' (Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => (dlmfScale_odd n x).symm)
    dsimp only
    rw [← sub_sum_dlmfTerms_even, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ]
    ring

/-! ### The failure of 2.6.6 -/

theorem dlmfB_zero : dlmfB 0 = 3 / 2 := by
  simp [dlmfB]

/-- **The formal expansion 2.6.6 is wrong**: `S(x) ∼ (2π/√3) ∑ (−1)^s binom(−1/3, s) x^{−s−1/3}`
is *not* an asymptotic expansion of `S(x)`, since the remainder after one term is
`−(3/2) x^{−1} + O(x^{−4/3})`. -/
theorem dlmf_2_6_6_false :
    ¬ IsGenAsympExpansionDLMF atTop (fun (s : ℕ) (x : ℝ) => x ^ (-((s : ℝ) + 1 / 3))) dlmfS
      fun s x => 2 * π / Real.sqrt 3 *
        ((-1) ^ s * Ring.choose (-1 / 3 : ℝ) s * x ^ (-((s : ℝ) + 1 / 3))) := by
  intro h
  have hne : ∀ᶠ x : ℝ in atTop, x ^ (-(((1 : ℕ) : ℝ) + 1 / 3)) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact (Real.rpow_pos_of_pos hx _).ne'
  have h1 := (dlmf_2_1_3 hne).mp (h.2 1)
  have h2 : (fun x : ℝ => dlmfB 0 * x ^ (-((0 : ℕ) + 1 : ℝ))) =O[atTop]
      fun x => x ^ (-(((1 : ℕ) : ℝ) + 1 / 3)) := by
    refine ((dlmfE_isBigO 1).sub h1).congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
    simp only [dlmfE, Finset.sum_range_one]
    push_cast
    ring
  have hB : dlmfB 0 ≠ 0 := by rw [dlmfB_zero]; norm_num
  obtain ⟨C, hC⟩ := h2.bound
  have hlim := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually_gt_atTop
    (C / |dlmfB 0|)
  obtain ⟨x, hx0, hCx, hBx⟩ := ((eventually_gt_atTop 0).and (hC.and hlim)).exists
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hCx
  have hx13 : x ^ (-((0 : ℕ) + 1 : ℝ)) = x ^ (1 / 3 : ℝ) * x ^ (-(((1 : ℕ) : ℝ) + 1 / 3)) := by
    rw [← Real.rpow_add hx0]
    congr 1
    push_cast
    ring
  rw [hx13, ← mul_assoc] at hCx
  have hpos : 0 < x ^ (-(((1 : ℕ) : ℝ) + 1 / 3)) := Real.rpow_pos_of_pos hx0 _
  have h3 := le_of_mul_le_mul_right hCx hpos
  rw [div_lt_iff₀ (abs_pos.mpr hB)] at hBx
  linarith [mul_comm (x ^ (1 / 3 : ℝ)) |dlmfB 0|]

end Azurite.DLMF
