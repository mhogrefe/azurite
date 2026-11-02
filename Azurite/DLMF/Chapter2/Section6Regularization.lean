/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section6StieltjesExpansion

/-!
# DLMF §2.6(iv): Regularization — 2.6.54–2.6.61

The Mellin-convolution integral `I(x) = ∫₀^∞ f(t) h(xt) dt` (2.6.54, `mellinConvInt` of §2.5) for
`f(t) = ∑_{s<n} aₛ t^{s+α−1} + fₙ(t)`, `fₙ = O(t^{n+α−1})` at `0+` (2.6.55, `MellinZeroSetup`,
with the §2.5(ii) growth condition `f = O(t^{−b})` at `∞`), and
`h(t) = ∑_{s<n} bₛ t^{−s−β} + hₙ(t)`, `hₙ = O(t^{−n−β})` at `∞` (2.6.56, `MellinInfSetup`, with
`h = O(t^c)` at `0+`), `0 < α, β ≤ 1`.

* 2.6.57 (`dlmf_2_6_57`): the algebraic identity for `f(t) h(xt)`.
* 2.6.58–2.6.59 (`dlmf_2_6_59`): the divergent `∫₀^∞ t^λ dt` has regularized value `0`: the
  Mellin transforms of the two halves of `t^λ` are `1/(z+λ)` (`ℜz > −ℜλ`) and `−1/(z+λ)`
  (`ℜz < −ℜλ`) (`mellin_trunc₁_cpow`, `mellin_trunc₂_cpow`), whose continuations cancel
  identically. (For `λ = −1` both have a pole at `z = 1`, the point corresponding to
  `∫₀^∞ t^λ dt`; DLMF's "`λ ∈ ℂ`" should exclude it — `docs/dlmf_errata.md`.)
* 2.6.60 (`MellinZeroSetup.dlmf_2_6_60`): `𝓜f(z) = 𝓜fₙ(z)`, where `𝓜f` is the continued transform
  `mellinTrunc₁Cont f a α' + 𝓜f₂` (2.5.25–2.5.26), on the strip where `𝓜fₙ` converges. The
  analogue for `h` (`MellinInfSetup.mellinCont_eq_mellin_rem`): the continued `𝓜h` of 2.6.18
  equals `𝓜hₘ(z)` for `m − 1 + β < ℜz < m + β`, `ℜz > −c`.
* 2.6.61 (`MellinInfSetup.dlmf_2_6_61`): `𝓜h_x(j+α) = x^{−j−α} 𝓜h(j+α)` for the continued
  transforms, `h_x(t) = h(xt)`, when `α ≠ β` (so that `j + α` is not a pole); `h_x` satisfies the
  hypotheses of 2.6.56 with coefficients `bₛ x^{−s−β}` (`MellinInfSetup.comp_mul_left`).

The expansion 2.6.62 is in `Section6RegularizationExpansion`.
-/

open MeasureTheory Filter Topology Set Complex Asymptotics
open scoped Real Interval

namespace Azurite.DLMF

/-! ### 2.6.55–2.6.56: the hypotheses -/

/-- **DLMF 2.6.55** with the growth condition 2.5.19: `f` locally integrable on `(0, ∞)`,
`f(t) ∼ ∑ aₛ t^{s+α−1}` as `t → 0+` with `0 < α ≤ 1`, and `f = O(t^{−b})` as `t → ∞`. -/
structure MellinZeroSetup (f : ℝ → ℂ) (a : ℕ → ℂ) (α b : ℝ) : Prop where
  f_loc : LocallyIntegrableOn f (Ioi 0)
  α_pos : 0 < α
  α_le : α ≤ 1
  f_exp : IsGenAsympExpansionDLMF (𝓝[>] (0 : ℝ))
    (fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ ((s : ℂ) + α - 1)) f
    fun s t => a s * (t : ℂ) ^ ((s : ℂ) + α - 1)
  f_top : f =O[atTop] (· ^ (-b))

/-- **DLMF 2.6.56** with the growth condition 2.5.20: `h` locally integrable on `(0, ∞)`,
`h(t) ∼ ∑ bₛ t^{−s−β}` as `t → ∞` with `0 < β ≤ 1`, and `h = O(t^c)` as `t → 0+`. -/
structure MellinInfSetup (h : ℝ → ℂ) (bs : ℕ → ℂ) (β c : ℝ) : Prop where
  h_loc : LocallyIntegrableOn h (Ioi 0)
  β_pos : 0 < β
  β_le : β ≤ 1
  h_exp : IsGenAsympExpansionDLMF atTop (fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ (-((s : ℂ) + β))) h
    fun s t => bs s * (t : ℂ) ^ (-((s : ℂ) + β))
  h_zero : h =O[𝓝[>] 0] (· ^ c)

/-- The remainder `fₙ(t) = f(t) − ∑_{s<n} aₛ t^{s+α−1}` of 2.6.55. -/
noncomputable def zeroRem (f : ℝ → ℂ) (a : ℕ → ℂ) (α : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  f t - ∑ s ∈ Finset.range n, a s * (t : ℂ) ^ ((s : ℂ) + α - 1)

/-- The exponents `αₛ = s + α − 1` of 2.6.55 in the notation of 2.5.17. -/
noncomputable def zeroExp (α : ℝ) (s : ℕ) : ℂ := (s : ℂ) + α - 1

theorem zeroExp_mono (α : ℝ) : StrictMono fun s : ℕ => (zeroExp α s).re := by
  intro m n h
  simp only [zeroExp, sub_re, add_re, natCast_re, ofReal_re, one_re]
  have := (Nat.cast_lt (α := ℝ)).mpr h
  linarith

theorem zeroExp_tendsto (α : ℝ) : Tendsto (fun s : ℕ => (zeroExp α s).re) atTop atTop := by
  simp only [zeroExp, sub_re, add_re, natCast_re, ofReal_re, one_re]
  exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _
    tendsto_natCast_atTop_atTop)

theorem truncRem_eq_trunc₁_zeroRem (f : ℝ → ℂ) (a : ℕ → ℂ) (α : ℝ) (n : ℕ) :
    truncRem f a (zeroExp α) n = trunc₁ (zeroRem f a α n) := rfl

/-! ### 2.6.57 -/

/-- **DLMF 2.6.57**: for `t, x > 0`,
`f(t) h(xt) = ∑_j ∑_k a_j b_k t^{j+α−1−k−β} x^{−k−β} + ∑_j a_j t^{j+α−1} hₙ(xt)
  + ∑_k b_k x^{−k−β} t^{−k−β} fₙ(t) + fₙ(t) hₙ(xt)`. -/
theorem dlmf_2_6_57 (f h : ℝ → ℂ) (a bs : ℕ → ℂ) (α β : ℝ) (n : ℕ) {x t : ℝ} (hx : 0 < x)
    (ht : 0 < t) :
    f t * h (x * t) =
      ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, a j * bs k *
          (t : ℂ) ^ ((j : ℂ) + α - 1 - k - β) * (x : ℂ) ^ (-((k : ℂ) + β)) +
        ∑ j ∈ Finset.range n, a j * (t : ℂ) ^ ((j : ℂ) + α - 1) * stieltjesRem h bs β n (x * t) +
        ∑ k ∈ Finset.range n, bs k * (x : ℂ) ^ (-((k : ℂ) + β)) * (t : ℂ) ^ (-((k : ℂ) + β)) *
          zeroRem f a α n t +
        zeroRem f a α n t * stieltjesRem h bs β n (x * t) := by
  have hf : f t = ∑ j ∈ Finset.range n, a j * (t : ℂ) ^ ((j : ℂ) + α - 1) + zeroRem f a α n t := by
    simp [zeroRem]
  have hh : h (x * t) = ∑ k ∈ Finset.range n, bs k * (x : ℂ) ^ (-((k : ℂ) + β)) *
      (t : ℂ) ^ (-((k : ℂ) + β)) + stieltjesRem h bs β n (x * t) := by
    have : ∀ k : ℕ, bs k * ((x * t : ℝ) : ℂ) ^ (-((k : ℂ) + β)) =
        bs k * (x : ℂ) ^ (-((k : ℂ) + β)) * (t : ℂ) ^ (-((k : ℂ) + β)) := fun k => by
      rw [ofReal_mul, mul_cpow_ofReal_nonneg hx.le ht.le, mul_assoc]
    unfold stieltjesRem
    simp only [this]
    ring
  have hpow : ∀ j k : ℕ, (t : ℂ) ^ ((j : ℂ) + α - 1) * (t : ℂ) ^ (-((k : ℂ) + β)) =
      (t : ℂ) ^ ((j : ℂ) + α - 1 - k - β) := fun j k => by
    rw [← cpow_add _ _ (ofReal_ne_zero.mpr ht.ne')]
    congr 1
    ring
  rw [hf, hh, add_mul, mul_add, mul_add]
  have e1 : (∑ j ∈ Finset.range n, a j * (t : ℂ) ^ ((j : ℂ) + α - 1)) *
      (∑ k ∈ Finset.range n, bs k * (x : ℂ) ^ (-((k : ℂ) + β)) * (t : ℂ) ^ (-((k : ℂ) + β))) =
      ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, a j * bs k *
        (t : ℂ) ^ ((j : ℂ) + α - 1 - k - β) * (x : ℂ) ^ (-((k : ℂ) + β)) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
      rw [← hpow j k]; ring
  have e2 : zeroRem f a α n t *
      ∑ k ∈ Finset.range n, bs k * (x : ℂ) ^ (-((k : ℂ) + β)) * (t : ℂ) ^ (-((k : ℂ) + β)) =
      ∑ k ∈ Finset.range n, bs k * (x : ℂ) ^ (-((k : ℂ) + β)) * (t : ℂ) ^ (-((k : ℂ) + β)) *
        zeroRem f a α n t := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1, Finset.sum_mul, e2]
  ring

/-! ### 2.6.58–2.6.59: the regularized `∫₀^∞ t^λ dt` -/

/-- `𝓜(t^λ)₁(z) = 1/(z + λ)` for `ℜz > −ℜλ`. -/
theorem mellin_trunc₁_cpow (lam : ℂ) {z : ℂ} (hz : -lam.re < z.re) :
    mellin (trunc₁ fun t : ℝ => (t : ℂ) ^ lam) z = 1 / (z + lam) :=
  (hasMellin_cpow_Ioc lam (by linarith)).2

/-- `𝓜(t^λ)₂(z) = −1/(z + λ)` for `ℜz < −ℜλ`. -/
theorem mellin_trunc₂_cpow (lam : ℂ) {z : ℂ} (hz : z.re < -lam.re) :
    mellin (trunc₂ fun t : ℝ => (t : ℂ) ^ lam) z = -(1 / (z + lam)) := by
  rw [mellin_trunc₂_eq_inv]
  have hfun : (trunc₁ fun u : ℝ => ((u⁻¹ : ℝ) : ℂ) ^ lam) =
      trunc₁ fun u : ℝ => (u : ℂ) ^ (-lam) := by
    ext u
    simp only [trunc₁, indicator]
    split_ifs with hu
    · rw [← ofReal_inv_cpow_neg hu.1, neg_neg]
    · rfl
  rw [hfun, mellin_trunc₁_cpow (-lam) (by simp; linarith), ← neg_add, div_neg]

/-- **DLMF 2.6.58–2.6.59**: the integral `∫₀^∞ t^λ dt` (2.6.58) diverges for every `λ`, but
the Mellin transforms of its two halves `t^λ 1_{(0,1]}` and `t^λ 1_{(1,∞)}` are `1/(z+λ)` on
`ℜz > −ℜλ` and `−1/(z+λ)` on `ℜz < −ℜλ`; their analytic continuations cancel identically, and
this cancellation (at `z = 1`) is the regularized value `∫₀^∞ t^λ dt = 0` of 2.6.59. -/
theorem dlmf_2_6_59 (lam : ℂ) :
    (∀ z : ℂ, -lam.re < z.re → mellin (trunc₁ fun t : ℝ => (t : ℂ) ^ lam) z = 1 / (z + lam)) ∧
    (∀ z : ℂ, z.re < -lam.re → mellin (trunc₂ fun t : ℝ => (t : ℂ) ^ lam) z = -(1 / (z + lam))) ∧
    ∀ z : ℂ, 1 / (z + lam) + -(1 / (z + lam)) = 0 :=
  ⟨fun _ hz => mellin_trunc₁_cpow lam hz, fun _ hz => mellin_trunc₂_cpow lam hz, fun _ => by ring⟩

/-- **DLMF 2.6.58**: `∫₀^∞ t^λ dt` diverges for every real `λ`. -/
theorem dlmf_2_6_58 (lam : ℝ) : ¬ IntegrableOn (fun t : ℝ => t ^ lam) (Ioi 0) := by
  intro h
  have h1 := (integrableOn_Ioi_rpow_iff one_pos).mp (h.mono_set (Ioi_subset_Ioi zero_le_one))
  have h2 : IntervalIntegrable (fun t : ℝ => t ^ lam) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact h.mono_set Ioc_subset_Ioi_self
  have hsub : [[(0 : ℝ), 1]] \ {0} ⊆ Ioc 0 1 := fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht
    exact ⟨lt_of_le_of_ne ht.1.1 (Ne.symm ht.2), ht.1.2⟩
  have hmem : [[(0 : ℝ), 1]] \ {0} ∈ 𝓝[[[(0 : ℝ), 1]] \ {0}] 0 := self_mem_nhdsWithin
  refine not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton
    (f := fun t : ℝ => Real.log t) (c := 0) zero_ne_one (by simp) ?_ ?_ ?_ h2
  · filter_upwards [hmem] with t ht
    exact (Real.hasDerivAt_log (hsub ht).1.ne').differentiableAt
  · have h1 : Tendsto (fun t : ℝ => ‖Real.log t‖) (𝓝[>] 0) atTop := by
      refine (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      simp only [Function.comp_apply, Real.norm_eq_abs]
      rw [abs_of_neg (Real.log_neg ht.1 ht.2)]
    exact h1.mono_left (nhdsWithin_mono _ fun t ht => (hsub ht).1)
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [hmem] with t ht
    obtain ⟨ht0, ht1⟩ := hsub ht
    rw [(Real.hasDerivAt_log ht0.ne').deriv, Real.norm_of_nonneg (inv_nonneg.mpr ht0.le),
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), one_mul, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge ht0 ht1 h1.le

/-! ### 2.6.60: `𝓜f(z) = 𝓜fₙ(z)` -/

/-- `𝓜(g − ∑_{s<N} cₛ t^{wₛ})₂(z) = 𝓜g₂(z) + ∑_{s<N} cₛ/(z + wₛ)` for `ℜz + ℜwₛ < 0`. -/
theorem mellin_trunc₂_sub_sum {g : ℝ → ℂ} {z : ℂ} (hg : MellinConvergent (trunc₂ g) z) {N : ℕ}
    {c w : ℕ → ℂ} (hw : ∀ s < N, z.re + (w s).re < 0) :
    MellinConvergent (trunc₂ fun t => g t - ∑ s ∈ Finset.range N, c s * (t : ℂ) ^ w s) z ∧
      mellin (trunc₂ fun t => g t - ∑ s ∈ Finset.range N, c s * (t : ℂ) ^ w s) z =
        mellin (trunc₂ g) z + ∑ s ∈ Finset.range N, c s / (z + w s) := by
  induction N with
  | zero => exact ⟨by simpa using hg, by simp⟩
  | succ N ih =>
    obtain ⟨ih1, ih2⟩ := ih fun s hs => hw s (hs.trans (Nat.lt_succ_self N))
    have hpow : MellinConvergent (trunc₂ fun t : ℝ => (t : ℂ) ^ w N) z := by
      have hconv := mellinConvergent_trunc₂ (f := fun t : ℝ => (t : ℂ) ^ w N) (z := z)
        ((continuousOn_ofReal_cpow_Ioi _).locallyIntegrableOn measurableSet_Ioi)
        (b := -(w N).re) ?_ (by linarith [hw N (Nat.lt_succ_self N)])
      · exact hconv
      · refine IsBigO.of_bound 1 ?_
        filter_upwards [eventually_gt_atTop 0] with t ht
        rw [norm_cpow_eq_rpow_re_of_pos ht, one_mul, neg_neg,
          Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
    have hterm : HasMellin (fun t : ℝ => c N * trunc₂ (fun t : ℝ => (t : ℂ) ^ w N) t) z
        (c N * -(1 / (z + w N))) := by
      rw [← mellin_trunc₂_cpow (w N) (by linarith [hw N (Nat.lt_succ_self N)])]
      refine ⟨by simpa only [smul_eq_mul] using hpow.const_smul (c N), ?_⟩
      have := mellin_const_smul (trunc₂ fun t : ℝ => (t : ℂ) ^ w N) z (c N)
      simpa only [smul_eq_mul] using this
    have hsplit : (trunc₂ fun t => g t - ∑ s ∈ Finset.range (N + 1), c s * (t : ℂ) ^ w s) =
        fun t => trunc₂ (fun t => g t - ∑ s ∈ Finset.range N, c s * (t : ℂ) ^ w s) t -
          c N * trunc₂ (fun t : ℝ => (t : ℂ) ^ w N) t := by
      ext t
      simp only [trunc₂, trunc₁, indicator, Finset.sum_range_succ]
      split_ifs <;> ring
    have := hasMellin_sub ih1 hterm.1
    rw [← hsplit, hterm.2] at this
    refine ⟨this.1, ?_⟩
    rw [this.2, ih2, Finset.sum_range_succ]
    ring

namespace MellinZeroSetup

variable {f : ℝ → ℂ} {a : ℕ → ℂ} {α b : ℝ} (F : MellinZeroSetup f a α b)
include F

/-- The continued `𝓜f` of 2.5.26: `mellinTrunc₁Cont f a α' z + 𝓜f₂(z)`. -/
noncomputable def mellinContZero (f : ℝ → ℂ) (a : ℕ → ℂ) (α : ℝ) (z : ℂ) : ℂ :=
  mellinTrunc₁Cont f a (zeroExp α) z + mellin (trunc₂ f) z

omit F in
theorem zeroRem_zero : zeroRem f a α 0 = f := by
  ext t
  simp [zeroRem]

/-- **DLMF 2.6.60**: `𝓜f(z) = 𝓜fₙ(z)` for the continued transform, on the strip
`−(n + α − 1) < ℜz < min(b, 2 − n − α)` where `𝓜fₙ` converges. -/
theorem dlmf_2_6_60 {n : ℕ} {z : ℂ} (hz₁ : -(n + α - 1) < z.re) (hz₂ : z.re < 2 - n - α)
    (hzb : z.re < b) :
    MellinConvergent (zeroRem f a α n) z ∧
      mellinContZero f a α z = mellin (zeroRem f a α n) z := by
  have hmem : z ∈ contDomain (zeroExp α) n := by
    refine ⟨by simp [zeroExp]; linarith, fun s hs h => ?_⟩
    have := congrArg Complex.re h
    simp only [zeroExp, neg_re, sub_re, add_re, natCast_re, ofReal_re, one_re] at this
    have : (s : ℝ) + 1 ≤ n := by exact_mod_cast hs
    linarith
  have hw : ∀ s < n, z.re + (zeroExp α s).re < 0 := fun s hs => by
    have : (s : ℝ) + 1 ≤ n := by exact_mod_cast hs
    simp only [zeroExp, sub_re, add_re, natCast_re, ofReal_re, one_re]
    linarith
  obtain ⟨h₂, e₂⟩ := mellin_trunc₂_sub_sum (mellinConvergent_trunc₂ F.f_loc F.f_top hzb) hw
    (c := a)
  have hrem : (fun t : ℝ => f t - ∑ s ∈ Finset.range n, a s * (t : ℂ) ^ zeroExp α s) =
      zeroRem f a α n := rfl
  rw [hrem] at h₂ e₂
  have h₁ : MellinConvergent (trunc₁ (zeroRem f a α n)) z := by
    rw [← truncRem_eq_trunc₁_zeroRem]
    exact mellinConvergent_truncRem F.f_exp F.f_loc (by simpa [zeroExp] using hz₁)
  refine ⟨?_, ?_⟩
  · have := hasMellin_add h₁ h₂
    simpa only [trunc₁_add_trunc₂] using this.1
  · rw [mellinContZero, mellinTrunc₁Cont_eq (zeroExp_mono α) F.f_exp F.f_loc hmem,
      mellinTrunc₁Ext, truncRem_eq_trunc₁_zeroRem, mellin_eq_trunc_add h₁ h₂]
    linear_combination -e₂

/-- On the strip `1 − α < ℜw < b` the continued transform is the Mellin transform of `f`. -/
theorem mellinContZero_eq_mellin {w : ℂ} (hw₁ : 1 - α < w.re) (hw₂ : w.re < b) :
    MellinConvergent f w ∧ mellinContZero f a α w = mellin f w := by
  have h₁ : MellinConvergent (trunc₁ f) w := by
    rw [← truncRem_zero f a (zeroExp α)]
    exact mellinConvergent_truncRem F.f_exp F.f_loc (by simp; linarith)
  have h₂ : MellinConvergent (trunc₂ f) w := mellinConvergent_trunc₂ F.f_loc F.f_top hw₂
  refine ⟨by simpa only [trunc₁_add_trunc₂] using (hasMellin_add h₁ h₂).1, ?_⟩
  rw [mellinContZero, (dlmf_2_5_25 (zeroExp_mono α) F.f_exp F.f_loc (zeroExp_tendsto α)).1 w
    (by simp [zeroExp]; linarith), ← mellin_eq_trunc_add h₁ h₂]

end MellinZeroSetup

namespace MellinInfSetup

variable {h : ℝ → ℂ} {bs : ℕ → ℂ} {β c : ℝ} (H : MellinInfSetup h bs β c)
include H

/-- `hₘ = O(t^{−m−β})` as `t → ∞`. -/
theorem rem_isBigO (m : ℕ) : stieltjesRem h bs β m =O[atTop] (· ^ (-(m + β))) := by
  have := isBigO_rpow_re_of_isBigODLMF_cpow_top (H.h_exp.2 m)
  simp only [add_re, natCast_re, ofReal_re] at this
  exact this

theorem h_isBigO : h =O[atTop] (· ^ (-β)) := by
  have := H.rem_isBigO 0
  simp only [StieltjesSetup.rem_zero, Nat.cast_zero, zero_add] at this
  exact this

theorem locallyIntegrableOn_rem (m : ℕ) : LocallyIntegrableOn (stieltjesRem h bs β m) (Ioi 0) :=
  H.h_loc.sub ((continuousOn_finsetSum _ fun _ _ =>
    continuousOn_const.mul (continuousOn_ofReal_cpow_Ioi _)).locallyIntegrableOn measurableSet_Ioi)

/-- The explicit continuation of `𝓜h₂` (2.5.27): for `ℜz < n + 1 + β`, `z ≠ s + β` (`s ≤ n`),
`[𝓜h₂]_cont(z) = −∑_{s≤n} bₛ/(z − s − β) + 𝓜(h_{n+1})₂(z)`. -/
theorem mellinTrunc₂ContZero_eq_sum_add {n : ℕ} {z : ℂ} (hz : z.re < n + 1 + β)
    (hz' : ∀ s ≤ n, z ≠ s + β) :
    mellinTrunc₂ContZero h bs (fun s : ℕ => (s : ℂ) + β) z =
      -∑ s ∈ Finset.range (n + 1), bs s / (z - ((s : ℂ) + β)) +
        mellin (trunc₂ (stieltjesRem h bs β (n + 1))) z := by
  have hmem : -z ∈ contDomain (fun s : ℕ => (s : ℂ) + β) (n + 1) := by
    refine ⟨?_, fun s hs h => ?_⟩
    · simp only [add_re, natCast_re, ofReal_re, neg_re, one_re, Nat.cast_add, Nat.cast_one]
      linarith
    · exact hz' s (Nat.lt_succ_iff.mp hs) (neg_injective h)
  rw [mellinTrunc₂ContZero, mellinTrunc₁Cont_eq StieltjesSetup.β_mono
    (isGenAsympExpansion_inv H.h_exp) (locallyIntegrableOn_comp_inv H.h_loc) hmem, mellinTrunc₁Ext,
    mellin_trunc₂_eq_inv]
  have hfun : truncRem (fun t : ℝ => h t⁻¹) bs (fun s : ℕ => (s : ℂ) + β) (n + 1) =
      trunc₁ fun u : ℝ => stieltjesRem h bs β (n + 1) u⁻¹ := by
    ext u
    simp only [truncRem, trunc₁, indicator]
    split_ifs with hu
    · simp only [expPartial, stieltjesRem]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [ofReal_inv_cpow_neg hu.1]
    · rfl
  rw [hfun]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← div_neg, neg_sub, neg_add_eq_sub]

/-- **The `h`-analogue of 2.6.60**: the continued `𝓜h` of 2.6.18 equals `𝓜hₘ(z)` for
`m − 1 + β < ℜz < m + β` and `ℜz > −c` (for `m = 0` only `−c < ℜz < β` is needed). -/
theorem mellinCont_eq_mellin_rem {m : ℕ} {z : ℂ} (hc : -c < z.re)
    (hlo : m = 0 ∨ (m : ℝ) - 1 + β < z.re) (hhi : z.re < m + β) :
    MellinConvergent (stieltjesRem h bs β m) z ∧
      mellinCont h bs β z = mellin (stieltjesRem h bs β m) z := by
  have h₁h : MellinConvergent (trunc₁ h) z := mellinConvergent_trunc₁ H.h_loc H.h_zero hc
  rcases m with _ | n
  · have h₂ : MellinConvergent (trunc₂ h) z :=
      mellinConvergent_trunc₂ H.h_loc H.h_isBigO (by simpa using hhi)
    refine ⟨by simpa [StieltjesSetup.rem_zero] using (hasMellin_add h₁h h₂).1 |>
      fun h => by simpa only [trunc₁_add_trunc₂] using h, ?_⟩
    rw [StieltjesSetup.rem_zero, mellinCont, mellinTrunc₂ContZero_eq H.h_loc StieltjesSetup.β_mono
      StieltjesSetup.β_tendsto H.h_exp (by simpa using hhi), ← mellin_eq_trunc_add h₁h h₂]
  · have hlo' : (n : ℝ) + β < z.re := by
      rcases hlo with h | h
      · exact absurd h (Nat.succ_ne_zero n)
      · push_cast at h
        linarith
    have hw : ∀ s < n + 1, 0 < z.re + (-((s : ℂ) + β)).re := fun s hs => by
      have : (s : ℝ) ≤ n := Nat.cast_le.mpr (Nat.lt_succ_iff.mp hs)
      simp only [neg_re, add_re, natCast_re, ofReal_re]
      linarith
    obtain ⟨h₁, e₁⟩ := StieltjesSetup.mellin_trunc₁_sub_sum h₁h hw (c := bs)
    have h₂ : MellinConvergent (trunc₂ (stieltjesRem h bs β (n + 1))) z :=
      mellinConvergent_trunc₂ (H.locallyIntegrableOn_rem (n + 1)) (H.rem_isBigO (n + 1))
        (by push_cast at hhi ⊢; linarith)
    have hz' : ∀ s ≤ n, z ≠ s + β := fun s hs h => by
      have := congrArg Complex.re h
      simp only [add_re, natCast_re, ofReal_re] at this
      have : (s : ℝ) ≤ n := Nat.cast_le.mpr hs
      linarith
    have hrem : (fun t : ℝ => h t - ∑ s ∈ Finset.range (n + 1), bs s * (t : ℂ) ^ (-((s : ℂ) + β))) =
        stieltjesRem h bs β (n + 1) := rfl
    rw [hrem] at h₁ e₁
    refine ⟨?_, ?_⟩
    · have := hasMellin_add h₁ h₂
      simpa only [trunc₁_add_trunc₂] using this.1
    · rw [mellinCont, H.mellinTrunc₂ContZero_eq_sum_add (by push_cast at hhi ⊢; linarith) hz',
        mellin_eq_trunc_add h₁ h₂, e₁]
      have : ∑ s ∈ Finset.range (n + 1), bs s / (z + -((s : ℂ) + β)) =
          ∑ s ∈ Finset.range (n + 1), bs s / (z - ((s : ℂ) + β)) :=
        Finset.sum_congr rfl fun s _ => by rw [← sub_eq_add_neg]
      rw [this]
      ring

/-! ### 2.6.61 -/

/-- `h_x(t) = h(xt)` satisfies 2.6.56 with coefficients `bₛ x^{−s−β}`. -/
theorem comp_mul_left {x : ℝ} (hx : 0 < x) :
    MellinInfSetup (fun t => h (x * t)) (fun s => bs s * (x : ℂ) ^ (-((s : ℂ) + β))) β c where
  h_loc := LaplaceSmallSetup.locallyIntegrableOn_comp_mul_left H.h_loc hx
  β_pos := H.β_pos
  β_le := H.β_le
  h_exp := by
    refine ⟨H.h_exp.1, fun n => ?_⟩
    obtain ⟨C, hC⟩ := H.h_exp.2 n
    have hxt : Tendsto (fun t : ℝ => x * t) atTop atTop := tendsto_const_mul_atTop_of_pos hx |>.mpr
      tendsto_id
    refine ⟨C * x ^ (-(n + β)), eventually_map.mpr ?_⟩
    filter_upwards [hxt.eventually (eventually_map.mp hC), eventually_gt_atTop 0] with t hCt ht
    have hpow : ∀ s : ℕ, ((x : ℂ) * t) ^ (-((s : ℂ) + β)) =
        (x : ℂ) ^ (-((s : ℂ) + β)) * (t : ℂ) ^ (-((s : ℂ) + β)) := fun s =>
      mul_cpow_ofReal_nonneg hx.le ht.le _
    have hsum : ∑ s ∈ Finset.range n, bs s * ((x : ℂ) * t) ^ (-((s : ℂ) + β)) =
        ∑ s ∈ Finset.range n, bs s * (x : ℂ) ^ (-((s : ℂ) + β)) * (t : ℂ) ^ (-((s : ℂ) + β)) :=
      Finset.sum_congr rfl fun s _ => by rw [hpow s]; ring
    have hxn : ‖(x : ℂ) ^ (-((n : ℂ) + β))‖ = x ^ (-(n + β)) := by
      rw [norm_cpow_eq_rpow_re_of_pos hx]
      simp
    have hT : 0 < ‖(t : ℂ) ^ (-((n : ℂ) + β))‖ := norm_pos_iff.mpr fun h0 =>
      ofReal_ne_zero.mpr ht.ne' ((cpow_eq_zero_iff _ _).mp h0).1
    have hxp : 0 < x ^ (-(n + β)) := Real.rpow_pos_of_pos hx _
    simp only [ofReal_mul] at hCt
    rw [hsum, hpow n, norm_div, norm_mul, hxn, div_le_iff₀ (by positivity)] at hCt
    show ‖(h (x * t) - ∑ s ∈ Finset.range n, bs s * (x : ℂ) ^ (-((s : ℂ) + β)) *
      (t : ℂ) ^ (-((s : ℂ) + β))) / (t : ℂ) ^ (-((n : ℂ) + β))‖ ≤ C * x ^ (-(n + β))
    rw [norm_div, div_le_iff₀ hT]
    linarith
  h_zero := by
    have hxt : Tendsto (fun t : ℝ => x * t) (𝓝[>] 0) (𝓝[>] 0) := by
      have h1 : Tendsto (fun t : ℝ => x * t) (𝓝 0) (𝓝 0) := by
        have : Tendsto (fun t : ℝ => x * t) (𝓝 0) (𝓝 (x * 0)) := tendsto_id.const_mul x
        rwa [mul_zero] at this
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (h1.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos hx ht
    refine (H.h_zero.comp_tendsto hxt).trans (IsBigO.of_bound (x ^ c) ?_)
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht : (0 : ℝ) < t := ht
    simp only [Function.comp_apply]
    rw [Real.mul_rpow hx.le ht.le, Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _)
      (Real.rpow_nonneg ht.le _)), Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]

/-- **DLMF 2.6.61**: `𝓜h_x(j + α) = x^{−j−α} 𝓜h(j + α)` for the continued transforms, when
`α ≠ β` (`0 < α ≤ 1`) and `j + α > −c`. -/
theorem dlmf_2_6_61 {x : ℝ} (hx : 0 < x) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hαβ : α ≠ β)
    {j : ℕ} (hc : -c < j + α) :
    mellinCont (fun t => h (x * t)) (fun s => bs s * (x : ℂ) ^ (-((s : ℂ) + β))) β ((j : ℂ) + α) =
      (x : ℂ) ^ (-((j : ℂ) + α)) * mellinCont h bs β ((j : ℂ) + α) := by
  have hβ0 := H.β_pos
  have hβ1 := H.β_le
  -- the number `m` of poles `s + β` to the left of `j + α`
  obtain ⟨m, hlo, hhi⟩ : ∃ m : ℕ, (m = 0 ∨ (m : ℝ) - 1 + β < j + α) ∧ (j : ℝ) + α < m + β := by
    rcases lt_or_gt_of_ne hαβ with h | h
    · rcases j with _ | j
      · exact ⟨0, Or.inl rfl, by simp; linarith⟩
      · exact ⟨j + 1, Or.inr (by push_cast; linarith), by push_cast; linarith⟩
    · exact ⟨j + 1, Or.inr (by push_cast; linarith), by push_cast; linarith⟩
  have hre : (((j : ℂ) + α)).re = j + α := by simp
  obtain ⟨-, e₁⟩ := (H.comp_mul_left hx).mellinCont_eq_mellin_rem (m := m) (by rw [hre]; exact hc)
    (by rw [hre]; exact hlo) (by rw [hre]; exact hhi)
  obtain ⟨-, e₂⟩ := H.mellinCont_eq_mellin_rem (m := m) (by rw [hre]; exact hc)
    (by rw [hre]; exact hlo) (by rw [hre]; exact hhi)
  rw [e₁, e₂]
  have hrem : stieltjesRem (fun t => h (x * t)) (fun s => bs s * (x : ℂ) ^ (-((s : ℂ) + β))) β m
      =ᵐ[volume.restrict (Ioi 0)] fun t => stieltjesRem h bs β m (x * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht : (0 : ℝ) < t := ht
    simp only [stieltjesRem, ofReal_mul]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_cpow_ofReal_nonneg hx.le ht.le]
    ring
  rw [mellin_congr_ae hrem, mellin_comp_mul_left _ _ hx, smul_eq_mul]

end MellinInfSetup

end Azurite.DLMF
