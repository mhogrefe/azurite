/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14Laplace
import Azurite.DLMF.Chapter2.Section5Expansion
import Azurite.DLMF.Chapter2.Section5Oscillatory

/-!
# DLMF §2.5(iii) Laplace Transforms with Small Parameters (2.5.37–2.5.40)

`h` satisfies 2.5.18 (`h(t) ∼ e^{iκt^p} ∑ bₛ t^{−βₛ}`, `t → +∞`) and 2.5.20 (`h(t) = O(t^c)`,
`t → 0+`) with `c > −1` (`LaplaceSmallSetup`). With `x = 1/ζ` and the truncations 2.5.23–2.5.24,

* 2.5.37: `ℒh(ζ) = ∫₀^∞ h(t) e^{−ζt} dt` (`laplace`, §1.14(iii));
* 2.5.38–2.5.39: `ζ ℒh(ζ) = I₁(x) + I₂(x)`, `I_j(x) = ∫₀^∞ e^{−t} h_j(xt) dt` (`dlmf_2_5_38`);
* 2.5.40: since `𝓜e^{−t}(z) = Γ(z)` (`mellin_expNeg`), Parseval gives
  `I_j(x) = (2πi)⁻¹ ∫_{p_j−i∞}^{p_j+i∞} x^{−z} Γ(1 − z) 𝓜h_j(z) dz` for `−c < p₁ < 1` and
  `p₂ < min(1, ℜβ₀)` (`dlmf_2_5_40_one`, `dlmf_2_5_40_two`).

The Parseval formula needs `Γ(1 − z)` integrable on vertical lines. This follows from the
elementary bound `|Γ(s)| ≤ Γ(ℜs + k) / |ℑs|^k` (`norm_Gamma_le_div_pow_im`, from
`Γ(s + k) = s(s+1)⋯(s+k−1) Γ(s)` and `|Γ(s + k)| ≤ Γ(ℜs + k)`), which also gives the uniform
decay on strips used for the contour shifts of 2.5.41–2.5.43.
-/

open MeasureTheory Filter Topology Set Complex Asymptotics
open scoped Real

namespace Azurite.DLMF

/-! ### Bounds for `Γ` on vertical lines -/

/-- `|Γ(s)| ≤ Γ(ℜs)` for `ℜs > 0`. -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Gamma_eq_integral hs, GammaIntegral, Real.Gamma_eq_integral hs]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re]

/-- `Γ(s + k) = (∏_{j<k} (s + j)) Γ(s)` when no `s + j` vanishes. -/
theorem Gamma_add_nat_eq_prod_mul (s : ℂ) (k : ℕ) (hs : ∀ j < k, s + j ≠ 0) :
    Gamma (s + k) = (∏ j ∈ Finset.range k, (s + j)) * Gamma s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc,
      Gamma_add_one _ (hs k (Nat.lt_succ_self k)),
      ih fun j hj => hs j (hj.trans (Nat.lt_succ_self k))]
    ring

/-- **Decay of `Γ` on vertical lines**: for `ℑs ≠ 0` and `ℜs + k > 0`,
`|Γ(s)| ≤ Γ(ℜs + k) / |ℑs|^k`. -/
theorem norm_Gamma_le_div_pow_im {s : ℂ} {k : ℕ} (hre : 0 < s.re + k) (him : s.im ≠ 0) :
    ‖Gamma s‖ ≤ Real.Gamma (s.re + k) / |s.im| ^ k := by
  have hne : ∀ j < k, s + (j : ℂ) ≠ 0 := fun j _ h => him (by simpa using congrArg Complex.im h)
  have hprod : ∀ j ∈ Finset.range k, |s.im| ≤ ‖s + (j : ℂ)‖ := fun j _ =>
    (abs_im_le_norm _).trans' (le_of_eq (by simp))
  have hP : |s.im| ^ k ≤ ‖∏ j ∈ Finset.range k, (s + (j : ℂ))‖ := by
    rw [norm_prod]
    calc |s.im| ^ k = ∏ _j ∈ Finset.range k, |s.im| := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hprod
  have hP0 : (0 : ℝ) < |s.im| ^ k := pow_pos (abs_pos.mpr him) k
  have hΓ : ‖Gamma (s + k)‖ ≤ Real.Gamma (s.re + k) := by
    have := norm_Gamma_le_Gamma_re (s := s + k) (by simpa using hre)
    simpa using this
  rw [Gamma_add_nat_eq_prod_mul s k hne, norm_mul] at hΓ
  rw [le_div_iff₀ hP0]
  calc ‖Gamma s‖ * |s.im| ^ k ≤ ‖Gamma s‖ * ‖∏ j ∈ Finset.range k, (s + (j : ℂ))‖ :=
        mul_le_mul_of_nonneg_left hP (norm_nonneg _)
    _ = ‖∏ j ∈ Finset.range k, (s + (j : ℂ))‖ * ‖Gamma s‖ := mul_comm _ _
    _ ≤ Real.Gamma (s.re + k) := hΓ

/-- `σ + iy` is never a pole of `Γ` when `σ` is not a non-positive integer. -/
theorem add_mul_I_ne_neg_nat {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n) (y : ℝ) (n : ℕ) :
    (σ : ℂ) + y * I ≠ -n := fun h => by
  have h1 := congrArg Complex.re h
  simp at h1
  exact hσ n h1

theorem continuous_Gamma_vertical {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n) :
    Continuous fun y : ℝ => Gamma (σ + y * I) :=
  continuous_iff_continuousAt.mpr fun y =>
    ContinuousAt.comp (g := Gamma) (f := fun y : ℝ => (σ : ℂ) + y * I) (x := y)
      (continuousAt_Gamma _ (add_mul_I_ne_neg_nat hσ y)) (by fun_prop)

/-- `Γ` is integrable on every vertical line `ℜs = σ` not passing through a pole. -/
theorem integrable_Gamma_vertical {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n) :
    Integrable fun y : ℝ => Gamma (σ + y * I) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_Gamma_vertical hσ).continuousOn
  set k : ℕ := ⌈|σ|⌉₊ + 2
  have hk : 0 < σ + k := by
    have := Nat.le_ceil |σ|
    have := neg_abs_le σ
    simp only [k]
    push_cast
    linarith
  have hG := Real.Gamma_pos_of_pos hk
  set C : ℝ := 2 * (|B| + Real.Gamma (σ + k))
  refine (integrable_inv_one_add_sq.const_mul C).mono'
    (continuous_Gamma_vertical hσ).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rcases le_or_gt |y| 1 with hy | hy
  · have h1 := hB y (abs_le.mp hy)
    have h2 : (1 : ℝ) ≤ 2 / (1 + y ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [abs_le.mp hy]
    calc ‖Gamma (σ + y * I)‖ ≤ |B| := h1.trans (le_abs_self B)
      _ ≤ |B| + Real.Gamma (σ + k) := by linarith
      _ ≤ (|B| + Real.Gamma (σ + k)) * (2 / (1 + y ^ 2)) :=
          le_mul_of_one_le_right (by positivity) h2
      _ = C * (1 + y ^ 2)⁻¹ := by
          simp only [C]
          ring
  · have hy0 : y ≠ 0 := by
      intro h
      rw [h, abs_zero] at hy
      linarith
    have hbound := norm_Gamma_le_div_pow_im (s := σ + y * I) (k := k) (by simpa using hk)
      (by simpa using hy0)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at hbound
    have hyk : y ^ 2 ≤ |y| ^ k := by
      rw [← sq_abs]
      exact pow_le_pow_right₀ hy.le (by simp [k])
    calc ‖Gamma (σ + y * I)‖ ≤ Real.Gamma (σ + k) / |y| ^ k := hbound
      _ ≤ Real.Gamma (σ + k) / y ^ 2 := div_le_div_of_nonneg_left hG.le (by positivity) hyk
      _ ≤ Real.Gamma (σ + k) * (2 / (1 + y ^ 2)) := by
          rw [div_eq_mul_inv]
          refine mul_le_mul_of_nonneg_left ?_ hG.le
          rw [inv_le_iff_one_le_mul₀ (by positivity), div_mul_eq_mul_div,
            le_div_iff₀ (by positivity)]
          nlinarith [sq_abs y]
      _ ≤ C * (1 + y ^ 2)⁻¹ := by
          have e : C * (1 + y ^ 2)⁻¹ =
              Real.Gamma (σ + k) * (2 / (1 + y ^ 2)) + 2 * |B| * (1 + y ^ 2)⁻¹ := by
            simp only [C]
            ring
          have : 0 ≤ 2 * |B| * (1 + y ^ 2)⁻¹ := by positivity
          rw [e]
          linarith

/-! ### `𝓜e^{−t}(z) = Γ(z)` -/

/-- `e^{−t}` as a function `ℝ → ℂ`. -/
noncomputable def expNeg (t : ℝ) : ℂ := ((Real.exp (-t) : ℝ) : ℂ)

theorem mellinConvergent_expNeg {s : ℂ} (hs : 0 < s.re) : MellinConvergent expNeg s :=
  (GammaIntegral_convergent hs).congr_fun (fun t _ => by simp [expNeg, smul_eq_mul, mul_comm])
    measurableSet_Ioi

/-- `𝓜e^{−t}(z) = Γ(z)`, `ℜz > 0`. -/
theorem mellin_expNeg {s : ℂ} (hs : 0 < s.re) : mellin expNeg s = Gamma s := by
  rw [Gamma_eq_integral hs, GammaIntegral_eq_mellin]
  rfl

/-! ### The hypotheses of §2.5(iii) -/

/-- The data of DLMF §2.5(iii): `h` locally integrable on `(0, ∞)` with the expansion 2.5.18 at
`+∞` (`ℜβₛ` strictly increasing to `+∞`, `p > 0`) and `h(t) = O(t^c)` as `t → 0+` with
`c > −1`. -/
structure LaplaceSmallSetup (h : ℝ → ℂ) (bs β : ℕ → ℂ) (κ p c : ℝ) : Prop where
  h_loc : LocallyIntegrableOn h (Ioi 0)
  β_mono : StrictMono fun s => (β s).re
  β_tendsto : Tendsto (fun s => (β s).re) atTop atTop
  p_pos : 0 < p
  /-- 2.5.18 -/
  h_exp : IsGenAsympExpansionDLMF atTop (fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ (-β s)) h
    fun s t => bs s * cexp (I * κ * ((t ^ p : ℝ) : ℂ)) * (t : ℂ) ^ (-β s)
  /-- 2.5.20 -/
  h_zero : h =O[𝓝[>] 0] (· ^ c)
  c_gt : -1 < c

namespace LaplaceSmallSetup

variable {h : ℝ → ℂ} {bs β : ℕ → ℂ} {κ p c : ℝ} (H : LaplaceSmallSetup h bs β κ p c)
include H

theorem h_top : h =O[atTop] (· ^ (-(β 0).re)) := by
  have := H.h_exp.2 0
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero] at this
  exact isBigO_rpow_re_of_isBigODLMF_cpow_top this

theorem mellinConvergent_h₁ {z : ℂ} (hz : -c < z.re) : MellinConvergent (trunc₁ h) z :=
  mellinConvergent_trunc₁ H.h_loc H.h_zero hz

theorem mellinConvergent_h₂ {z : ℂ} (hz : z.re < (β 0).re) : MellinConvergent (trunc₂ h) z :=
  mellinConvergent_trunc₂ H.h_loc H.h_top hz

theorem differentiableAt_h₁ {z : ℂ} (hz : -c < z.re) : DifferentiableAt ℂ (mellin (trunc₁ h)) z :=
  differentiableAt_mellin_trunc₁ H.h_loc H.h_zero hz

theorem differentiableAt_h₂ {z : ℂ} (hz : z.re < (β 0).re) :
    DifferentiableAt ℂ (mellin (trunc₂ h)) z :=
  differentiableAt_mellin_trunc₂ H.h_loc H.h_top hz

omit H in
/-- `t ↦ h(xt)` is locally integrable on `(0, ∞)` when `h` is, `x > 0`. -/
theorem locallyIntegrableOn_comp_mul_left (hloc : LocallyIntegrableOn h (Ioi 0)) {x : ℝ}
    (hx : 0 < x) : LocallyIntegrableOn (fun t => h (x * t)) (Ioi 0) := by
  intro t₀ ht₀
  have ht₀ : (0 : ℝ) < t₀ := ht₀
  refine ⟨Icc (t₀ / 2) (2 * t₀),
    mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)), ?_⟩
  have hint : IntegrableOn h (Icc (x * (t₀ / 2)) (x * (2 * t₀))) :=
    hloc.integrableOn_compact_subset (fun u hu => lt_of_lt_of_le (by positivity) hu.1)
      isCompact_Icc
  have := ((hint.integrable_indicator measurableSet_Icc).comp_mul_left' hx.ne').integrableOn
    (s := Icc (t₀ / 2) (2 * t₀))
  refine this.congr_fun (fun t ht => ?_) measurableSet_Icc
  exact indicator_of_mem (show x * t ∈ Icc (x * (t₀ / 2)) (x * (2 * t₀)) from
    ⟨mul_le_mul_of_nonneg_left ht.1 hx.le, mul_le_mul_of_nonneg_left ht.2 hx.le⟩) h

/-- The integrand `e^{−t} h(xt)` of 2.5.39 is integrable on `(0, ∞)` for `x > 0`. -/
theorem integrableOn_expNeg_mul {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => expNeg t * h (x * t)) (Ioi 0) := by
  -- Mellin convergence at `z = 1`
  have hloc : LocallyIntegrableOn (fun t => expNeg t * h (x * t)) (Ioi 0) :=
    (locallyIntegrableOn_comp_mul_left H.h_loc hx).continuousOn_mul
      (by unfold expNeg; fun_prop) isOpen_Ioi.isLocallyClosed
  have hmul : Tendsto (fun t : ℝ => x * t) atTop atTop := tendsto_id.const_mul_atTop hx
  have hmul0 : Tendsto (fun t : ℝ => x * t) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t : ℝ => x * t) (𝓝 0) (𝓝 (x * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos hx ht
  have htop : (fun t => expNeg t * h (x * t)) =O[atTop] (· ^ (-(2 : ℝ))) := by
    have h1 : expNeg =O[atTop] (· ^ ((β 0).re - 2)) := by
      have := (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one ((β 0).re - 2)).isBigO
      have h1' : (fun t : ℝ => ‖expNeg t‖) =O[atTop] (· ^ ((β 0).re - 2)) :=
        this.congr' (Eventually.of_forall fun t => by
          simp only [expNeg, norm_real, Real.norm_eq_abs, Real.abs_exp, neg_one_mul])
          EventuallyEq.rfl
      exact IsBigO.of_norm_left h1'
    have h2 : (fun t => h (x * t)) =O[atTop] (· ^ (-(β 0).re)) := by
      refine (H.h_top.comp_tendsto hmul).trans (IsBigO.of_bound (x ^ (-(β 0).re)) ?_)
      filter_upwards [eventually_gt_atTop 0] with t ht
      simp only [Function.comp, Real.norm_of_nonneg (Real.rpow_nonneg (mul_pos hx ht).le _),
        Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
      rw [Real.mul_rpow hx.le ht.le]
    refine (h1.mul h2).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have hzero : (fun t => expNeg t * h (x * t)) =O[𝓝[>] 0] (· ^ (-(-c))) := by
    have h1 : expNeg =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [expNeg, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, norm_one, mul_one]
      exact Real.exp_le_one_iff.mpr (by linarith [le_of_lt (show (0:ℝ) < t from ht)])
    have h2 : (fun t => h (x * t)) =O[𝓝[>] 0] (· ^ c) := by
      refine (H.h_zero.comp_tendsto hmul0).trans (IsBigO.of_bound (x ^ c) ?_)
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht : (0 : ℝ) < t := ht
      simp only [Function.comp, Real.norm_of_nonneg (Real.rpow_nonneg (mul_pos hx ht).le _),
        Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
      rw [Real.mul_rpow hx.le ht.le]
    refine (h1.mul h2).congr' EventuallyEq.rfl (Eventually.of_forall fun t => ?_)
    simp
  have hconv : MellinConvergent (fun t => expNeg t * h (x * t)) 1 :=
    mellinConvergent_of_isBigO_rpow (a := 2) (b := -c) hloc htop (by simp) hzero
      (by simp; linarith [H.c_gt])
  refine hconv.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp

/-! ### 2.5.37–2.5.39 -/

omit H in
/-- **DLMF 2.5.37**: `ℒh(ζ) = ∫₀^∞ h(t) e^{−ζt} dt`. -/
theorem dlmf_2_5_37 (h : ℝ → ℂ) (ζ : ℂ) :
    laplace h ζ = ∫ t in Ioi (0 : ℝ), h t * cexp (-(ζ * t)) := by
  simp only [laplace, mul_comm]

omit H in
/-- `ζ ℒh(ζ) = ∫₀^∞ e^{−t} h(t/ζ) dt` for real `ζ > 0` (substitute `t ↦ t/ζ`). -/
theorem mul_laplace_eq_mellinConvInt (h : ℝ → ℂ) {ζ : ℝ} (hζ : 0 < ζ) :
    (ζ : ℂ) * laplace h ζ = mellinConvInt expNeg h (1 / ζ) := by
  rw [laplace, mellinConvInt]
  have e : (∫ t in Ioi (0 : ℝ), cexp (-(ζ * t)) * h t) =
      ∫ t in Ioi (0 : ℝ), expNeg (ζ * t) * h (1 / ζ * (ζ * t)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by
      rw [one_div, inv_mul_cancel_left₀ hζ.ne']
      simp [expNeg, Complex.ofReal_exp]
  have := integral_comp_mul_left_Ioi (fun u : ℝ => expNeg u * h (1 / ζ * u)) 0 hζ
  rw [mul_zero] at this
  rw [e, this, Complex.real_smul, ofReal_inv, mul_inv_cancel_left₀ (ofReal_ne_zero.mpr hζ.ne')]

/-- **DLMF 2.5.38–2.5.39**: `ζ ℒh(ζ) = I₁(x) + I₂(x)` with `x = 1/ζ` and
`I_j(x) = ∫₀^∞ e^{−t} h_j(xt) dt`. -/
theorem dlmf_2_5_38 {ζ : ℝ} (hζ : 0 < ζ) :
    (ζ : ℂ) * laplace h ζ =
      mellinConvInt expNeg (trunc₁ h) (1 / ζ) + mellinConvInt expNeg (trunc₂ h) (1 / ζ) := by
  rw [mul_laplace_eq_mellinConvInt h hζ,
    dlmf_2_5_29 (one_div_pos.mpr hζ) (H.integrableOn_expNeg_mul (one_div_pos.mpr hζ))]
  have h1 : mellinConvInt (trunc₁ expNeg) (trunc₁ h) (1 / ζ) +
      mellinConvInt (trunc₂ expNeg) (trunc₁ h) (1 / ζ) =
        mellinConvInt expNeg (trunc₁ h) (1 / ζ) := by
    simp only [mellinConvInt]
    rw [← integral_add (integrableOn_trunc₁_trunc₁ (H.integrableOn_expNeg_mul (one_div_pos.mpr hζ)))
      (integrableOn_trunc₂_trunc₁ (H.integrableOn_expNeg_mul (one_div_pos.mpr hζ)))]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [← add_mul, trunc₁_add_trunc₂]
  have h2 : mellinConvInt (trunc₁ expNeg) (trunc₂ h) (1 / ζ) +
      mellinConvInt (trunc₂ expNeg) (trunc₂ h) (1 / ζ) =
        mellinConvInt expNeg (trunc₂ h) (1 / ζ) := by
    simp only [mellinConvInt]
    have hi := H.integrableOn_expNeg_mul (one_div_pos.mpr hζ)
    rw [← integral_add (integrableOn_trunc₁_trunc₂ (one_div_pos.mpr hζ) hi)
      (integrableOn_trunc₂_trunc₂ (one_div_pos.mpr hζ) hi)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [← add_mul, trunc₁_add_trunc₂]
  rw [← h1, ← h2]
  ring

/-! ### 2.5.40 -/

omit H in
/-- `Γ(1 − z)` is integrable on the vertical line `ℜz = p` for `p < 1`
(as needed for the Parseval formula with `f = e^{−t}`). -/
theorem integrable_mellin_expNeg_line {p : ℝ} (hp : p < 1) :
    Integrable fun y : ℝ => mellin expNeg (1 - p - y * I) := by
  have hσ : ∀ n : ℕ, (1 - p : ℝ) ≠ -n := fun n h => by
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have := (integrable_Gamma_vertical hσ).comp_mul_left' (R := (-1 : ℝ)) (by norm_num)
  refine this.congr (ae_of_all _ fun y => ?_)
  dsimp only
  rw [mellin_expNeg (by simp; linarith)]
  congr 1
  push_cast
  ring

omit H in
/-- `G(z) = 𝓜e^{−t}(1 − z) 𝓜g(z) = Γ(1 − z) 𝓜g(z)` for `ℜz < 1`. -/
theorem mellinG_expNeg (g : ℝ → ℂ) {z : ℂ} (hz : z.re < 1) :
    mellinG expNeg g z = Gamma (1 - z) * mellin g z := by
  rw [mellinG, mellin_expNeg (by simp; linarith)]

/-- **DLMF 2.5.40**, `j = 1`: for `−c < p₁ < 1`,
`I₁(x) = (2πi)⁻¹ ∫_{p₁−i∞}^{p₁+i∞} x^{−z} Γ(1 − z) 𝓜h₁(z) dz`. -/
theorem dlmf_2_5_40_one {p₁ : ℝ} (hp₁ : -c < p₁) (hp₁' : p₁ < 1) {x : ℝ} (hx : 0 < x) :
    mellinConvInt expNeg (trunc₁ h) x = (2 * π : ℂ)⁻¹ * ∫ y : ℝ,
      (x : ℂ) ^ (-((p₁ : ℂ) + y * I)) *
        (Gamma (1 - (p₁ + y * I)) * mellin (trunc₁ h) (p₁ + y * I)) := by
  rw [dlmf_2_5_33 (mellinConvergent_expNeg (by simp; linarith)) (H.mellinConvergent_h₁ (by simpa))
    (Or.inr (integrable_mellin_expNeg_line hp₁')) hx]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [mellinG_expNeg _ (by simp; linarith)]

/-- **DLMF 2.5.40**, `j = 2`: for `p₂ < min(1, ℜβ₀)`,
`I₂(x) = (2πi)⁻¹ ∫_{p₂−i∞}^{p₂+i∞} x^{−z} Γ(1 − z) 𝓜h₂(z) dz`. -/
theorem dlmf_2_5_40_two {p₂ : ℝ} (hp₂ : p₂ < min 1 (β 0).re) {x : ℝ} (hx : 0 < x) :
    mellinConvInt expNeg (trunc₂ h) x = (2 * π : ℂ)⁻¹ * ∫ y : ℝ,
      (x : ℂ) ^ (-((p₂ : ℂ) + y * I)) *
        (Gamma (1 - (p₂ + y * I)) * mellin (trunc₂ h) (p₂ + y * I)) := by
  have h1 := (lt_min_iff.mp hp₂).1
  have h2 := (lt_min_iff.mp hp₂).2
  rw [dlmf_2_5_33 (mellinConvergent_expNeg (by simp; linarith)) (H.mellinConvergent_h₂ (by simpa))
    (Or.inr (integrable_mellin_expNeg_line h1)) hx]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [mellinG_expNeg _ (by simp; linarith)]

end LaplaceSmallSetup

end Azurite.DLMF
