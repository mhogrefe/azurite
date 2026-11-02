/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section1Generalized
import Azurite.DLMF.Chapter2.Section5

/-!
# DLMF §2.5(ii) Extensions: truncations and Tables 2.5.1–2.5.2 (2.5.17–2.5.24, 2.5.29–2.5.31)

Handelsman and Lew's extension of the Mellin transform method. The data are `f`, `h` locally
integrable on `(0, ∞)` with

* 2.5.17: `f(t) ∼ ∑ aₛ t^{αₛ}` as `t → 0+`, `ℜαₛ` strictly increasing to `+∞`;
* 2.5.18: `h(t) ∼ e^{iκt^p} ∑ bₛ t^{−βₛ}` as `t → +∞`, `κ` real, `p > 0`, `ℜβₛ` strictly
  increasing to `+∞`;
* 2.5.19: `f(t) = O(t^{−b})` as `t → +∞`, `b + ℜβ₀ > 1`;
* 2.5.20: `h(t) = O(t^c)` as `t → 0+`, `c + ℜα₀ > −1`,

bundled in `HandelsmanLewSetup`. The truncations 2.5.21–2.5.24 are `trunc₁ f = f` on `(0, 1]`
and `0` beyond, `trunc₂ f = f − trunc₁ f`.

* Table 2.5.1 (`mellinConvergent_trunc₁`, `mellinConvergent_trunc₂`, and the setup versions):
  `𝓜f₁` converges for `ℜz > −ℜα₀`, `𝓜f₂` for `ℜz < b`, `𝓜h₁` for `ℜz > −c`, `𝓜h₂` for
  `ℜz < ℜβ₀`, each analytic there (`differentiableAt_mellin_trunc₁/₂`).
* Table 2.5.2 (`dlmf_table_2_5_2_11` … `_22`): `G_{jk}(z) = 𝓜f_j(1 − z) 𝓜h_k(z)` is analytic on
  `D_{jk}`: `−c < ℜz < 1 + ℜα₀`, `ℜz < min(1 + ℜα₀, ℜβ₀)`, `max(−c, 1 − b) < ℜz`,
  `1 − b < ℜz < ℜβ₀`.
* 2.5.29–2.5.30: `I(x) = ∑_{j,k} I_{jk}(x)`, `I_{jk}(x) = ∫₀^∞ f_j(t) h_k(xt) dt`
  (`dlmf_2_5_29`); 2.5.31: `I₂₁(x) = 0` for `x ≥ 1` (`dlmf_2_5_31`).

The continuations 2.5.25–2.5.28 are in `Section5Continuation` (and `Section5Oscillatory` for
`κ ≠ 0`); 2.5.32–2.5.36 in `Section5Expansion`.
-/

open MeasureTheory Filter Topology Set Complex Asymptotics
open scoped Real

namespace Azurite.DLMF

/-! ### Truncations 2.5.21–2.5.24 -/

/-- **DLMF 2.5.21 / 2.5.23**: `f₁(t) = f(t)` for `0 < t ≤ 1`, `0` for `t > 1`. -/
noncomputable def trunc₁ (f : ℝ → ℂ) : ℝ → ℂ := (Ioc 0 1).indicator f

/-- **DLMF 2.5.22 / 2.5.24**: `f₂(t) = f(t) − f₁(t)`. -/
noncomputable def trunc₂ (f : ℝ → ℂ) : ℝ → ℂ := fun t => f t - trunc₁ f t

variable {f : ℝ → ℂ}

theorem trunc₁_apply_of_mem {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : trunc₁ f t = f t :=
  indicator_of_mem (show t ∈ Ioc 0 1 from ⟨ht, ht1⟩) f

theorem trunc₁_apply_of_one_lt {t : ℝ} (ht : 1 < t) : trunc₁ f t = 0 :=
  indicator_of_notMem (fun h => absurd h.2 (not_le.mpr ht)) f

theorem trunc₂_apply_of_mem {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : trunc₂ f t = 0 := by
  simp [trunc₂, trunc₁_apply_of_mem ht ht1]

theorem trunc₂_apply_of_one_lt {t : ℝ} (ht : 1 < t) : trunc₂ f t = f t := by
  simp [trunc₂, trunc₁_apply_of_one_lt ht]

/-- For `t > 0`, `f₂` is `f` on `(1, ∞)` and `0` on `(0, 1]`. -/
theorem trunc₂_eq_indicator {t : ℝ} (ht : 0 < t) : trunc₂ f t = (Ioi 1).indicator f t := by
  rcases le_or_gt t 1 with h | h
  · rw [trunc₂_apply_of_mem ht h]
    exact (indicator_of_notMem (s := Ioi 1) (fun h' => absurd h' (not_lt.mpr h)) f).symm
  · rw [trunc₂_apply_of_one_lt h]
    exact (indicator_of_mem (s := Ioi 1) h f).symm

theorem trunc₁_add_trunc₂ (f : ℝ → ℂ) (t : ℝ) : trunc₁ f t + trunc₂ f t = f t := by
  simp [trunc₂]

theorem locallyIntegrableOn_trunc₁ (hf : LocallyIntegrableOn f (Ioi 0)) :
    LocallyIntegrableOn (trunc₁ f) (Ioi 0) := fun x hx =>
  let ⟨s, hs, hint⟩ := hf x hx
  ⟨s, hs, hint.indicator measurableSet_Ioc⟩

theorem locallyIntegrableOn_trunc₂ (hf : LocallyIntegrableOn f (Ioi 0)) :
    LocallyIntegrableOn (trunc₂ f) (Ioi 0) :=
  hf.sub (locallyIntegrableOn_trunc₁ hf)

/-! ### Order estimates for the truncations -/

/-- `f₁` vanishes beyond `1`, so it is `O(t^{−a})` at `+∞` for every `a`. -/
theorem trunc₁_isBigO_atTop (f : ℝ → ℂ) (a : ℝ) : trunc₁ f =O[atTop] (· ^ (-a)) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  simp [trunc₁_apply_of_one_lt ht]

/-- `f₂` vanishes on `(0, 1]`, so it is `O(t^{−b})` at `0+` for every `b`. -/
theorem trunc₂_isBigO_nhdsGT_zero (f : ℝ → ℂ) (b : ℝ) : trunc₂ f =O[𝓝[>] 0] (· ^ (-b)) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  simp [trunc₂_apply_of_mem ht.1 ht.2.le]

theorem trunc₁_isBigO_nhdsGT_zero {g : ℝ → ℝ} (hf : f =O[𝓝[>] 0] g) :
    trunc₁ f =O[𝓝[>] 0] g := by
  refine hf.congr' ?_ EventuallyEq.rfl
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  exact (trunc₁_apply_of_mem ht.1 ht.2.le).symm

theorem trunc₂_isBigO_atTop {g : ℝ → ℝ} (hf : f =O[atTop] g) : trunc₂ f =O[atTop] g := by
  refine hf.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 1] with t ht
  exact (trunc₂_apply_of_one_lt ht).symm

/-- From DLMF's `O` relative to `t^w` (complex exponent) to Mathlib's `O(t^{ℜw})`, as `t → 0+`. -/
theorem isBigO_rpow_re_of_isBigODLMF_cpow_zero {g : ℝ → ℂ} {w : ℂ}
    (h : IsBigODLMF (𝓝[>] (0 : ℝ)) g fun t => (t : ℂ) ^ w) : g =O[𝓝[>] 0] (· ^ w.re) := by
  have hne : ∀ᶠ t : ℝ in 𝓝[>] 0, (t : ℂ) ^ w ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact cpow_ne_zero_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt ht)) w
  refine ((dlmf_2_1_3 hne).mp h).trans (IsBigO.of_bound 1 ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [norm_cpow_eq_rpow_re_of_pos ht, one_mul, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]

/-- From DLMF's `O` relative to `t^{−w}` to Mathlib's `O(t^{−ℜw})`, as `t → +∞`. -/
theorem isBigO_rpow_re_of_isBigODLMF_cpow_top {g : ℝ → ℂ} {w : ℂ}
    (h : IsBigODLMF atTop g fun t : ℝ => (t : ℂ) ^ (-w)) : g =O[atTop] (· ^ (-w.re)) := by
  have hne : ∀ᶠ t : ℝ in atTop, (t : ℂ) ^ (-w) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact cpow_ne_zero_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt ht)) _
  refine ((dlmf_2_1_3 hne).mp h).trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_cpow_eq_rpow_re_of_pos ht, one_mul, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),
    neg_re]

/-! ### Table 2.5.1 -/

/-- **Table 2.5.1, row `𝓜f₁`**: if `f = O(t^{a₀})` as `t → 0+`, `𝓜f₁(z)` converges for
`ℜz > −a₀`. -/
theorem mellinConvergent_trunc₁ (hloc : LocallyIntegrableOn f (Ioi 0)) {a₀ : ℝ}
    (hf : f =O[𝓝[>] 0] (· ^ a₀)) {z : ℂ} (hz : -a₀ < z.re) : MellinConvergent (trunc₁ f) z :=
  mellinConvergent_of_isBigO_rpow (a := z.re + 1) (b := -a₀) (locallyIntegrableOn_trunc₁ hloc)
    (trunc₁_isBigO_atTop f _) (by linarith)
    (by simpa only [neg_neg] using trunc₁_isBigO_nhdsGT_zero hf) hz

/-- **Table 2.5.1, row `𝓜f₁`**, analyticity. -/
theorem differentiableAt_mellin_trunc₁ (hloc : LocallyIntegrableOn f (Ioi 0)) {a₀ : ℝ}
    (hf : f =O[𝓝[>] 0] (· ^ a₀)) {z : ℂ} (hz : -a₀ < z.re) :
    DifferentiableAt ℂ (mellin (trunc₁ f)) z :=
  mellin_differentiableAt_of_isBigO_rpow (a := z.re + 1) (b := -a₀)
    (locallyIntegrableOn_trunc₁ hloc) (trunc₁_isBigO_atTop f _) (by linarith)
    (by simpa only [neg_neg] using trunc₁_isBigO_nhdsGT_zero hf) hz

/-- **Table 2.5.1, row `𝓜f₂`**: if `f = O(t^{−b})` as `t → +∞`, `𝓜f₂(z)` converges for
`ℜz < b`. -/
theorem mellinConvergent_trunc₂ (hloc : LocallyIntegrableOn f (Ioi 0)) {b : ℝ}
    (hf : f =O[atTop] (· ^ (-b))) {z : ℂ} (hz : z.re < b) : MellinConvergent (trunc₂ f) z :=
  mellinConvergent_of_isBigO_rpow (a := b) (b := z.re - 1) (locallyIntegrableOn_trunc₂ hloc)
    (trunc₂_isBigO_atTop hf) hz (trunc₂_isBigO_nhdsGT_zero f _) (by linarith)

/-- **Table 2.5.1, row `𝓜f₂`**, analyticity. -/
theorem differentiableAt_mellin_trunc₂ (hloc : LocallyIntegrableOn f (Ioi 0)) {b : ℝ}
    (hf : f =O[atTop] (· ^ (-b))) {z : ℂ} (hz : z.re < b) :
    DifferentiableAt ℂ (mellin (trunc₂ f)) z :=
  mellin_differentiableAt_of_isBigO_rpow (a := b) (b := z.re - 1)
    (locallyIntegrableOn_trunc₂ hloc) (trunc₂_isBigO_atTop hf) hz
    (trunc₂_isBigO_nhdsGT_zero f _) (by linarith)

/-! ### The hypotheses of §2.5(ii) -/

/-- The data of DLMF §2.5(ii): `f`, `h` locally integrable on `(0, ∞)` with the expansions
2.5.17 (`f(t) ∼ ∑ aₛ t^{αₛ}`, `t → 0+`) and 2.5.18 (`h(t) ∼ e^{iκt^p} ∑ bₛ t^{−βₛ}`, `t → +∞`),
`ℜαₛ` and `ℜβₛ` strictly increasing to `+∞`, and the order estimates 2.5.19
(`f(t) = O(t^{−b})`, `b + ℜβ₀ > 1`) and 2.5.20 (`h(t) = O(t^c)`, `c + ℜα₀ > −1`). -/
structure HandelsmanLewSetup (f h : ℝ → ℂ) (a α bs β : ℕ → ℂ) (κ p b c : ℝ) : Prop where
  f_loc : LocallyIntegrableOn f (Ioi 0)
  h_loc : LocallyIntegrableOn h (Ioi 0)
  α_mono : StrictMono fun s => (α s).re
  α_tendsto : Tendsto (fun s => (α s).re) atTop atTop
  /-- 2.5.17 -/
  f_exp : IsGenAsympExpansionDLMF (𝓝[>] (0 : ℝ)) (fun s t => (t : ℂ) ^ α s) f
    fun s t => a s * (t : ℂ) ^ α s
  β_mono : StrictMono fun s => (β s).re
  β_tendsto : Tendsto (fun s => (β s).re) atTop atTop
  p_pos : 0 < p
  /-- 2.5.18 -/
  h_exp : IsGenAsympExpansionDLMF atTop (fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ (-β s)) h
    fun s t => bs s * cexp (I * κ * ((t ^ p : ℝ) : ℂ)) * (t : ℂ) ^ (-β s)
  /-- 2.5.19 -/
  f_top : f =O[atTop] (· ^ (-b))
  b_gt : 1 < b + (β 0).re
  /-- 2.5.20 -/
  h_zero : h =O[𝓝[>] 0] (· ^ c)
  c_gt : -1 < c + (α 0).re

namespace HandelsmanLewSetup

variable {h : ℝ → ℂ} {a α bs β : ℕ → ℂ} {κ p b c : ℝ}
  (H : HandelsmanLewSetup f h a α bs β κ p b c)
include H

/-- The leading term of 2.5.17: `f(t) = O(t^{ℜα₀})` as `t → 0+`. -/
theorem f_zero : f =O[𝓝[>] 0] (· ^ (α 0).re) := by
  have := H.f_exp.2 0
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero] at this
  exact isBigO_rpow_re_of_isBigODLMF_cpow_zero this

/-- The leading term of 2.5.18: `h(t) = O(t^{−ℜβ₀})` as `t → +∞`. -/
theorem h_top : h =O[atTop] (· ^ (-(β 0).re)) := by
  have := H.h_exp.2 0
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero] at this
  exact isBigO_rpow_re_of_isBigODLMF_cpow_top this

/-- **Table 2.5.1**: `𝓜f₁(z)` converges for `ℜz > −ℜα₀`. -/
theorem mellinConvergent_f₁ {z : ℂ} (hz : -(α 0).re < z.re) : MellinConvergent (trunc₁ f) z :=
  mellinConvergent_trunc₁ H.f_loc H.f_zero hz

/-- **Table 2.5.1**: `𝓜f₂(z)` converges for `ℜz < b`. -/
theorem mellinConvergent_f₂ {z : ℂ} (hz : z.re < b) : MellinConvergent (trunc₂ f) z :=
  mellinConvergent_trunc₂ H.f_loc H.f_top hz

/-- **Table 2.5.1**: `𝓜h₁(z)` converges for `ℜz > −c`. -/
theorem mellinConvergent_h₁ {z : ℂ} (hz : -c < z.re) : MellinConvergent (trunc₁ h) z :=
  mellinConvergent_trunc₁ H.h_loc H.h_zero hz

/-- **Table 2.5.1**: `𝓜h₂(z)` converges for `ℜz < ℜβ₀`. -/
theorem mellinConvergent_h₂ {z : ℂ} (hz : z.re < (β 0).re) : MellinConvergent (trunc₂ h) z :=
  mellinConvergent_trunc₂ H.h_loc H.h_top hz

theorem differentiableAt_f₁ {z : ℂ} (hz : -(α 0).re < z.re) :
    DifferentiableAt ℂ (mellin (trunc₁ f)) z :=
  differentiableAt_mellin_trunc₁ H.f_loc H.f_zero hz

theorem differentiableAt_f₂ {z : ℂ} (hz : z.re < b) : DifferentiableAt ℂ (mellin (trunc₂ f)) z :=
  differentiableAt_mellin_trunc₂ H.f_loc H.f_top hz

theorem differentiableAt_h₁ {z : ℂ} (hz : -c < z.re) : DifferentiableAt ℂ (mellin (trunc₁ h)) z :=
  differentiableAt_mellin_trunc₁ H.h_loc H.h_zero hz

theorem differentiableAt_h₂ {z : ℂ} (hz : z.re < (β 0).re) :
    DifferentiableAt ℂ (mellin (trunc₂ h)) z :=
  differentiableAt_mellin_trunc₂ H.h_loc H.h_top hz

/-! ### Table 2.5.2 -/

omit H in
/-- `z ↦ 𝓜g(1 − z)` is analytic where `𝓜g` is analytic at `1 − z`. -/
theorem differentiableAt_one_sub {g : ℝ → ℂ} {z : ℂ} (hg : DifferentiableAt ℂ (mellin g) (1 - z)) :
    DifferentiableAt ℂ (fun w => mellin g (1 - w)) z :=
  hg.comp z ((differentiableAt_const _).sub differentiableAt_id)

omit H in
theorem one_sub_re (z : ℂ) : (1 - z).re = 1 - z.re := by simp

/-- **Table 2.5.2, `D₁₁`**: `G₁₁(z) = 𝓜f₁(1 − z) 𝓜h₁(z)` is analytic for
`−c < ℜz < 1 + ℜα₀`. -/
theorem dlmf_table_2_5_2_11 {z : ℂ} (h₁ : -c < z.re) (h₂ : z.re < 1 + (α 0).re) :
    DifferentiableAt ℂ (fun w => mellin (trunc₁ f) (1 - w) * mellin (trunc₁ h) w) z :=
  (differentiableAt_one_sub (H.differentiableAt_f₁ (z := 1 - z) (by
      rw [one_sub_re]; linarith))).mul (H.differentiableAt_h₁ h₁)

/-- **Table 2.5.2, `D₁₂`**: `G₁₂(z) = 𝓜f₁(1 − z) 𝓜h₂(z)` is analytic for
`ℜz < min(1 + ℜα₀, ℜβ₀)`. -/
theorem dlmf_table_2_5_2_12 {z : ℂ} (hz : z.re < min (1 + (α 0).re) (β 0).re) :
    DifferentiableAt ℂ (fun w => mellin (trunc₁ f) (1 - w) * mellin (trunc₂ h) w) z :=
  (differentiableAt_one_sub (H.differentiableAt_f₁ (z := 1 - z) (by
      rw [one_sub_re]; have := lt_min_iff.mp hz; linarith))).mul
    (H.differentiableAt_h₂ (lt_min_iff.mp hz).2)

/-- **Table 2.5.2, `D₂₁`**: `G₂₁(z) = 𝓜f₂(1 − z) 𝓜h₁(z)` is analytic for
`max(−c, 1 − b) < ℜz`. -/
theorem dlmf_table_2_5_2_21 {z : ℂ} (hz : max (-c) (1 - b) < z.re) :
    DifferentiableAt ℂ (fun w => mellin (trunc₂ f) (1 - w) * mellin (trunc₁ h) w) z :=
  (differentiableAt_one_sub (H.differentiableAt_f₂ (z := 1 - z) (by
      rw [one_sub_re]; have := max_lt_iff.mp hz; linarith))).mul
    (H.differentiableAt_h₁ (max_lt_iff.mp hz).1)

/-- **Table 2.5.2, `D₂₂`**: `G₂₂(z) = 𝓜f₂(1 − z) 𝓜h₂(z)` is analytic for
`1 − b < ℜz < ℜβ₀`. -/
theorem dlmf_table_2_5_2_22 {z : ℂ} (h₁ : 1 - b < z.re) (h₂ : z.re < (β 0).re) :
    DifferentiableAt ℂ (fun w => mellin (trunc₂ f) (1 - w) * mellin (trunc₂ h) w) z :=
  (differentiableAt_one_sub (H.differentiableAt_f₂ (z := 1 - z) (by
      rw [one_sub_re]; linarith))).mul (H.differentiableAt_h₂ h₂)

end HandelsmanLewSetup

/-! ### 2.5.29–2.5.31 -/

/-- A product of indicator truncations of `f(t) h(xt)` is integrable when `f(t) h(xt)` is. -/
theorem integrableOn_indicator_mul {h : ℝ → ℂ} {x : ℝ}
    (hint : IntegrableOn (fun t => f t * h (x * t)) (Ioi 0)) {S T : Set ℝ} (hS : MeasurableSet S)
    (hT : MeasurableSet T) :
    IntegrableOn (fun t => S.indicator f t * T.indicator h (x * t)) (Ioi 0) := by
  have heq : ∀ t, S.indicator f t * T.indicator h (x * t) =
      (S ∩ (fun t => x * t) ⁻¹' T).indicator (fun t => f t * h (x * t)) t := fun t => by
    by_cases hs : t ∈ S <;> by_cases ht : x * t ∈ T <;>
      simp [indicator, hs, ht]
  refine (hint.indicator (hS.inter (hT.preimage (by fun_prop)))).congr_fun
    (fun t _ => (heq t).symm) measurableSet_Ioi

variable {h : ℝ → ℂ} {x : ℝ}

theorem integrableOn_trunc₁_trunc₁ (hint : IntegrableOn (fun t => f t * h (x * t)) (Ioi 0)) :
    IntegrableOn (fun t => trunc₁ f t * trunc₁ h (x * t)) (Ioi 0) :=
  integrableOn_indicator_mul hint measurableSet_Ioc measurableSet_Ioc

theorem integrableOn_trunc₁_trunc₂ (hx : 0 < x)
    (hint : IntegrableOn (fun t => f t * h (x * t)) (Ioi 0)) :
    IntegrableOn (fun t => trunc₁ f t * trunc₂ h (x * t)) (Ioi 0) :=
  (integrableOn_indicator_mul hint measurableSet_Ioc measurableSet_Ioi).congr_fun
    (fun t ht => by rw [trunc₂_eq_indicator (mul_pos hx ht)]; rfl) measurableSet_Ioi

theorem integrableOn_trunc₂_trunc₁ (hint : IntegrableOn (fun t => f t * h (x * t)) (Ioi 0)) :
    IntegrableOn (fun t => trunc₂ f t * trunc₁ h (x * t)) (Ioi 0) :=
  (integrableOn_indicator_mul hint measurableSet_Ioi measurableSet_Ioc).congr_fun
    (fun t ht => by rw [trunc₂_eq_indicator ht]; rfl) measurableSet_Ioi

theorem integrableOn_trunc₂_trunc₂ (hx : 0 < x)
    (hint : IntegrableOn (fun t => f t * h (x * t)) (Ioi 0)) :
    IntegrableOn (fun t => trunc₂ f t * trunc₂ h (x * t)) (Ioi 0) :=
  (integrableOn_indicator_mul hint measurableSet_Ioi measurableSet_Ioi).congr_fun
    (fun t ht => by rw [trunc₂_eq_indicator ht, trunc₂_eq_indicator (mul_pos hx ht)])
    measurableSet_Ioi

/-- **DLMF 2.5.30**: `I_{jk}(x) = ∫₀^∞ f_j(t) h_k(xt) dt` is `mellinConvInt` of the truncations. -/
theorem dlmf_2_5_30 (fj hk : ℝ → ℂ) (x : ℝ) :
    mellinConvInt fj hk x = ∫ t in Ioi (0 : ℝ), fj t * hk (x * t) := rfl

/-- **DLMF 2.5.29**: `I(x) = I₁₁(x) + I₁₂(x) + I₂₁(x) + I₂₂(x)` for `x > 0`, when `f(t) h(xt)` is
integrable on `(0, ∞)`. -/
theorem dlmf_2_5_29 (hx : 0 < x) (hint : IntegrableOn (fun t => f t * h (x * t)) (Ioi 0)) :
    mellinConvInt f h x = mellinConvInt (trunc₁ f) (trunc₁ h) x +
      mellinConvInt (trunc₁ f) (trunc₂ h) x + mellinConvInt (trunc₂ f) (trunc₁ h) x +
        mellinConvInt (trunc₂ f) (trunc₂ h) x := by
  simp only [mellinConvInt]
  have i1 := integrableOn_trunc₁_trunc₁ hint
  have i2 := integrableOn_trunc₁_trunc₂ hx hint
  have i3 := integrableOn_trunc₂_trunc₁ hint
  have i4 := integrableOn_trunc₂_trunc₂ hx hint
  have i12 : IntegrableOn (fun t => trunc₁ f t * trunc₁ h (x * t) +
      trunc₁ f t * trunc₂ h (x * t)) (Ioi 0) := i1.add i2
  have i123 : IntegrableOn (fun t => trunc₁ f t * trunc₁ h (x * t) +
      trunc₁ f t * trunc₂ h (x * t) + trunc₂ f t * trunc₁ h (x * t)) (Ioi 0) := i12.add i3
  rw [← integral_add i1 i2, ← integral_add i12 i3, ← integral_add i123 i4]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have h1 := trunc₁_add_trunc₂ f t
  have h2 := trunc₁_add_trunc₂ h (x * t)
  rw [← h1, ← h2]
  ring

/-- **DLMF 2.5.31**: `I₂₁(x) = 0` for `x ≥ 1`: `f₂` lives on `t > 1` and `h₁(xt)` on `xt ≤ 1`. -/
theorem dlmf_2_5_31 (hx : 1 ≤ x) : mellinConvInt (trunc₂ f) (trunc₁ h) x = 0 := by
  simp only [mellinConvInt]
  rw [← integral_zero (μ := volume.restrict (Ioi (0 : ℝ))) (G := ℂ)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rcases le_or_gt t 1 with h1 | h1
  · rw [trunc₂_apply_of_mem ht h1, zero_mul]
  · rw [trunc₁_apply_of_one_lt (by nlinarith), mul_zero]

end Azurite.DLMF
