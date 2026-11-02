/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section5LaplaceStrip

/-!
# DLMF §2.5(iii): growth of the continued Mellin transforms on vertical strips

The contour shifts of 2.5.41–2.5.43 (`shift_Gamma_mul`) need the continued transforms to grow at
most polynomially in `|ℑz|` on vertical strips (`StripData`). This holds for

* `𝓜h₁` on `ℜz > −c` (bounded, `stripData_h₁`);
* the entire continuation of `𝓜h₂` for `κ ≠ 0` (`stripData_mellinTrunc₂Cont`): each term
  `∫₁^∞ t^w e^{iκt^p} dt` continued by `k` integrations by parts is `O((1 + |w|)^k)`
  (`exists_norm_oscExt_le`), and the remainder's transform is bounded;
* the meromorphic continuation of `𝓜h₂` for `κ = 0` (`mellinTrunc₂ContZero`,
  `stripData_mellinTrunc₂ContZero`): away from the poles `βₛ` it is a finite sum of
  `−bₛ/(z − βₛ)` plus a bounded transform.

DLMF does not mention these bounds; they are what makes "by (2.5.14)" (the decay of `Γ`) sufficient
for the shifts.
-/

open MeasureTheory Filter Topology Set Complex Metric Asymptotics
open scoped Real

namespace Azurite.DLMF

/-! ### Bounded Mellin transforms -/

/-- `|𝓜r(z)| ≤ ∫₁^∞ t^{b−1} |r(t)| dt` for `ℜz ≤ b` when `r` vanishes on `(0, 1]`. -/
theorem norm_mellin_le_of_eq_zero_le_one {r : ℝ → ℂ} (hr : ∀ t, t ≤ 1 → r t = 0) {b : ℝ}
    (hconv : MellinConvergent r b) {z : ℂ} (hz : z.re ≤ b) :
    ‖mellin r z‖ ≤ ∫ t in Ioi (0 : ℝ), t ^ (b - 1) * ‖r t‖ := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (b - 1) * ‖r t‖) (Ioi 0) := by
    refine IntegrableOn.congr_fun hconv.norm (fun t ht => ?_) measurableSet_Ioi
    have ht : (0 : ℝ) < t := ht
    simp [norm_cpow_eq_rpow_re_of_pos ht]
  refine norm_integral_le_of_norm_le hint ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht : (0 : ℝ) < t := ht
  rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]
  rcases le_or_gt t 1 with h1 | h1
  · simp [hr t h1]
  · exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h1.le (by linarith))
      (norm_nonneg _)

theorem exists_norm_mellin_le_of_eq_zero_le_one {r : ℝ → ℂ} (hr : ∀ t, t ≤ 1 → r t = 0) {b : ℝ}
    (hconv : MellinConvergent r b) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, z.re ≤ b → ‖mellin r z‖ ≤ M :=
  ⟨_, setIntegral_nonneg measurableSet_Ioi fun _ ht =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (norm_nonneg _),
    fun _ hz => norm_mellin_le_of_eq_zero_le_one hr hconv hz⟩

/-! ### `𝓜h₁` -/

theorem LaplaceSmallSetup.stripData_h₁ {h : ℝ → ℂ} {bs β : ℕ → ℂ} {κ p c : ℝ}
    (H : LaplaceSmallSetup h bs β κ p c) : StripData (mellin (trunc₁ h)) ∅ (-c) where
  diff := fun _ hz _ => H.differentiableAt_h₁ hz
  finite := fun _ _ => by simp
  poly := fun a _ ha => by
    obtain ⟨M, hM0, hM⟩ := exists_norm_mellin_trunc₁_le H.h_loc H.h_zero ha
    exact ⟨M, 0, 1, hM0, le_rfl, le_rfl, fun z hz _ _ => by simpa using hM z hz⟩

/-! ### The entire continuation, `κ ≠ 0` -/

theorem norm_oscInt_le {κ p : ℝ} {w : ℂ} {ε : ℝ} (hε : 0 < ε) (hw : w.re ≤ -1 - ε) :
    ‖oscInt κ p w‖ ≤ 1 / ε := by
  have hw' : w.re < -1 := by linarith
  have h1 : ‖oscInt κ p w‖ ≤ ∫ t in Ioi (1 : ℝ), t ^ w.re := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht : (1 : ℝ) < t := ht
    rw [norm_mul, norm_oscPhase, mul_one, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht)]
  rw [integral_Ioi_rpow_of_lt hw' zero_lt_one, Real.one_rpow] at h1
  refine h1.trans ?_
  have : -(1 : ℝ) / (w.re + 1) = 1 / (-w.re - 1) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]
    ring
  rw [this]
  exact one_div_le_one_div_of_le hε (by linarith)

theorem norm_oscConst {κ : ℝ} {p : ℝ} (hp : 0 < p) :
    ‖cexp (I * κ) / (I * κ * p)‖ = 1 / (|κ| * p) := by
  rw [norm_div, norm_exp, norm_mul, norm_mul, norm_I, one_mul, norm_real, norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp]
  simp

/-- The `k`-fold integration by parts grows at most like `(1 + |w|)^k` on `ℜw ≤ kp − 1 − ε`. -/
theorem exists_norm_oscExt_le {κ p : ℝ} (hκ : κ ≠ 0) (hp : 0 < p) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, w.re ≤ k * p - 1 - ε → ‖oscExt κ p k w‖ ≤ A * (1 + ‖w‖) ^ k := by
  induction k with
  | zero =>
    refine ⟨1 / ε, by positivity, fun w hw => ?_⟩
    simp only [oscExt, pow_zero, mul_one]
    exact norm_oscInt_le hε (by simpa using hw)
  | succ k ih =>
    obtain ⟨A, hA0, hA⟩ := ih
    have hc : ‖(I * κ * p : ℂ)‖ = |κ| * p := by
      rw [norm_mul, norm_mul, norm_I, one_mul, norm_real, norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hp]
    have hc0 : 0 < |κ| * p := mul_pos (abs_pos.mpr hκ) hp
    refine ⟨1 / (|κ| * p) + A * (p + 1) ^ (k + 1) / (|κ| * p), by positivity, fun w hw => ?_⟩
    have hw' : (w - p).re ≤ k * p - 1 - ε := by
      simp only [sub_re, ofReal_re]
      push_cast at hw
      linarith
    have h1 := hA (w - p) hw'
    have hw1 : 0 ≤ 1 + ‖w‖ := by positivity
    have hsub : ‖w - p‖ ≤ ‖w‖ + p := by
      have := norm_sub_le w (p : ℂ)
      rwa [norm_real, Real.norm_eq_abs, abs_of_pos hp] at this
    have hwp : 1 + ‖w - p‖ ≤ (p + 1) * (1 + ‖w‖) := by nlinarith [norm_nonneg w]
    have hwp1 : ‖w - p + 1‖ ≤ (p + 1) * (1 + ‖w‖) := by
      have := norm_add_le (w - p) 1
      rw [norm_one] at this
      nlinarith [norm_nonneg w]
    have hpow : (1 + ‖w - p‖) ^ k ≤ ((p + 1) * (1 + ‖w‖)) ^ k :=
      pow_le_pow_left₀ (by positivity) hwp k
    have hge : (1 : ℝ) ≤ (1 + ‖w‖) ^ (k + 1) := one_le_pow₀ (by linarith [norm_nonneg w])
    calc ‖oscExt κ p (k + 1) w‖
        = ‖-(cexp (I * κ) / (I * κ * p)) - (w - p + 1) / (I * κ * p) * oscExt κ p k (w - p)‖ := rfl
      _ ≤ ‖cexp (I * κ) / (I * κ * p)‖ +
          ‖w - p + 1‖ / ‖(I * κ * p : ℂ)‖ * ‖oscExt κ p k (w - p)‖ := by
          rw [← norm_div, ← norm_mul]
          exact (norm_sub_le _ _).trans_eq (by rw [norm_neg])
      _ ≤ 1 / (|κ| * p) + (p + 1) * (1 + ‖w‖) / (|κ| * p) * (A * ((p + 1) * (1 + ‖w‖)) ^ k) := by
          rw [norm_oscConst hp, hc]
          refine add_le_add le_rfl (mul_le_mul (div_le_div_of_nonneg_right hwp1 hc0.le)
            (h1.trans (mul_le_mul_of_nonneg_left hpow hA0)) (norm_nonneg _) (by positivity))
      _ = 1 / (|κ| * p) + A * (p + 1) ^ (k + 1) / (|κ| * p) * (1 + ‖w‖) ^ (k + 1) := by
          rw [mul_pow]
          ring
      _ ≤ (1 / (|κ| * p) + A * (p + 1) ^ (k + 1) / (|κ| * p)) * (1 + ‖w‖) ^ (k + 1) := by
          rw [add_mul]
          gcongr
          exact le_mul_of_one_le_right (by positivity) hge

section Ne

variable {h : ℝ → ℂ} {bs β : ℕ → ℂ} {κ p : ℝ} (hκ : κ ≠ 0) (hp : 0 < p)
  (hβ : StrictMono fun s => (β s).re) (hβ' : Tendsto (fun s => (β s).re) atTop atTop)
  (hloc : LocallyIntegrableOn h (Ioi 0))
  (hh : IsGenAsympExpansionDLMF atTop (fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ (-β s)) h
    fun s t => bs s * oscPhase κ p t * (t : ℂ) ^ (-β s))
include hκ hp hβ hβ' hloc hh

/-- The entire continuation of `𝓜h₂` (`κ ≠ 0`) grows polynomially on every strip. -/
theorem stripData_mellinTrunc₂Cont (a₀ : ℝ) : StripData (mellinTrunc₂Cont h bs β κ p) ∅ a₀ where
  diff := fun z _ _ => (dlmf_2_5_27_ne hκ hp hβ hloc hh hβ').1 z
  finite := fun _ _ => by simp
  poly := fun a b _ => by
    obtain ⟨N, hN⟩ := (hβ'.eventually_gt_atTop b).exists
    obtain ⟨k, hk⟩ := exists_nat_gt ((b - (β 0).re + 1) / p)
    rw [div_lt_iff₀ hp] at hk
    obtain ⟨A, hA0, hA⟩ := exists_norm_oscExt_le hκ hp k one_pos
    obtain ⟨M₂, hM₂0, hM₂⟩ := exists_norm_mellin_le_of_eq_zero_le_one
      (r := oscRem h bs β κ p N) (fun t ht => indicator_of_notMem (not_lt.mpr ht) _)
      (mellinConvergent_oscRem hp hh hloc (z := (b : ℂ)) (by simpa using hN))
    set D : ℝ := 3 + max |a| |b| + ∑ s ∈ Finset.range N, ‖β s‖ with hD
    have hD1 : 1 ≤ D := by
      have : 0 ≤ ∑ s ∈ Finset.range N, ‖β s‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      rw [hD]
      linarith [le_max_left |a| |b|, abs_nonneg a]
    set B : ℝ := (∑ s ∈ Finset.range N, ‖bs s‖) * (A * D ^ k) + M₂ with hB
    refine ⟨B, k, 1, by positivity, by positivity, le_rfl, fun z hza hzb hzim => ?_⟩
    rw [Real.rpow_natCast, mellinTrunc₂Cont_eq hκ hp hβ hloc hh (N := N) (by linarith),
      mellinTrunc₂Ext]
    have hzre : |z.re| ≤ max |a| |b| := by
      rcases le_total 0 z.re with h0 | h0
      · rw [abs_of_nonneg h0]
        exact (hzb.trans (le_abs_self b)).trans (le_max_right _ _)
      · rw [abs_of_nonpos h0]
        exact (by linarith [neg_abs_le a] : -z.re ≤ |a|).trans (le_max_left _ _)
    have hz1 : (1 : ℝ) ≤ |z.im| ^ k := one_le_pow₀ hzim
    -- each oscillatory term
    have hterm : ∀ s ∈ Finset.range N,
        ‖oscEntire κ p (z - 1 - β s)‖ ≤ A * D ^ k * |z.im| ^ k := fun s hs => by
      have hβs : (β 0).re ≤ (β s).re := hβ.monotone (Nat.zero_le s)
      have hre : (z - 1 - β s).re < k * p - 1 := by
        simp only [sub_re, one_re]
        linarith
      have hre' : (z - 1 - β s).re ≤ k * p - 1 - 1 := by
        simp only [sub_re, one_re]
        linarith
      rw [oscEntire_eq_oscExt hκ hp hre]
      refine (hA _ hre').trans ?_
      have hβs' : ‖β s‖ ≤ ∑ s ∈ Finset.range N, ‖β s‖ :=
        Finset.single_le_sum (fun _ _ => norm_nonneg _) hs
      have hw : 1 + ‖z - 1 - β s‖ ≤ D * |z.im| := by
        have h1 := norm_sub_le (z - 1) (β s)
        have h1' := norm_sub_le z 1
        have h2 := norm_le_abs_re_add_abs_im z
        rw [norm_one] at h1'
        have hc1 : 2 + |z.re| + ‖β s‖ ≤ (2 + |z.re| + ‖β s‖) * |z.im| :=
          le_mul_of_one_le_right (by positivity) hzim
        calc 1 + ‖z - 1 - β s‖ ≤ (2 + |z.re| + ‖β s‖) + |z.im| := by linarith
          _ ≤ (2 + |z.re| + ‖β s‖) * |z.im| + |z.im| := by linarith
          _ = (3 + |z.re| + ‖β s‖) * |z.im| := by ring
          _ ≤ D * |z.im| := by
              rw [hD]
              exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      rw [mul_assoc, ← mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hw k) hA0
    calc ‖∑ s ∈ Finset.range N, bs s * oscEntire κ p (z - 1 - β s) + mellin (oscRem h bs β κ p N) z‖
        ≤ ∑ s ∈ Finset.range N, ‖bs s‖ * (A * D ^ k * |z.im| ^ k) + M₂ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans ?_) (hM₂ z hzb))
          exact Finset.sum_le_sum fun s hs => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hterm s hs) (norm_nonneg _)
      _ = (∑ s ∈ Finset.range N, ‖bs s‖) * (A * D ^ k) * |z.im| ^ k + M₂ := by
          rw [← Finset.sum_mul]
          ring
      _ ≤ B * |z.im| ^ k := by
          rw [hB, add_mul]
          gcongr
          exact le_mul_of_one_le_right hM₂0 hz1

end Ne

/-! ### The meromorphic continuation, `κ = 0` -/

/-- **DLMF 2.5.27**, `κ = 0`: the explicit meromorphic continuation of `𝓜h₂`,
`z ↦ 𝓜(h(1/·))₁`-continued at `−z`. -/
noncomputable def mellinTrunc₂ContZero (h : ℝ → ℂ) (bs β : ℕ → ℂ) (z : ℂ) : ℂ :=
  mellinTrunc₁Cont (fun t => h t⁻¹) bs β (-z)

section Zero

variable {h : ℝ → ℂ} {bs β : ℕ → ℂ} (hloc : LocallyIntegrableOn h (Ioi 0))
  (hβ : StrictMono fun s => (β s).re) (hβ' : Tendsto (fun s => (β s).re) atTop atTop)
  (hh : IsGenAsympExpansionDLMF atTop (fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ (-β s)) h
    fun s t => bs s * (t : ℂ) ^ (-β s))
include hloc hβ hβ' hh

theorem mellinTrunc₂ContZero_eq {z : ℂ} (hz : z.re < (β 0).re) :
    mellinTrunc₂ContZero h bs β z = mellin (trunc₂ h) z := by
  rw [mellinTrunc₂ContZero, mellin_trunc₂_eq_inv]
  exact (dlmf_2_5_25 hβ (isGenAsympExpansion_inv hh) (locallyIntegrableOn_comp_inv hloc)
    hβ').1 (-z) (by simpa using hz)

theorem differentiableAt_mellinTrunc₂ContZero {z : ℂ} (hz : ∀ s, z ≠ β s) :
    DifferentiableAt ℂ (mellinTrunc₂ContZero h bs β) z :=
  ((dlmf_2_5_25 hβ (isGenAsympExpansion_inv hh) (locallyIntegrableOn_comp_inv hloc) hβ').2.1
    (-z) fun s hs => hz s (neg_injective hs)).comp z differentiableAt_id.neg

/-- The principal part `−bₛ/(z − βₛ)` at `βₛ`. -/
theorem mellinTrunc₂ContZero_principal (s : ℕ) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g (β s) ∧
    ∀ᶠ z in 𝓝[≠] (β s), mellinTrunc₂ContZero h bs β z = -bs s / (z - β s) + g z := by
  obtain ⟨g, hg, hgeq⟩ := (dlmf_2_5_25 hβ (isGenAsympExpansion_inv hh)
    (locallyIntegrableOn_comp_inv hloc) hβ').2.2 s
  refine ⟨fun z => g (-z), AnalyticAt.comp_of_eq hg analyticAt_id.neg (by simp), ?_⟩
  have hneg : Tendsto (fun z : ℂ => -z) (𝓝[≠] (β s)) (𝓝[≠] (-β s)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((continuous_neg.tendsto _).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact fun h => hz (neg_injective h)
  filter_upwards [hneg.eventually hgeq] with z hz
  rw [mellinTrunc₂ContZero, hz, neg_div, ← div_neg, neg_sub, neg_add_eq_sub]

omit hloc hh in
/-- Finitely many `βₛ` in every strip. -/
theorem finite_range_β_strip (a b : ℝ) : (range β ∩ {z : ℂ | a ≤ z.re ∧ z.re ≤ b}).Finite := by
  obtain ⟨N, hN⟩ := (hβ'.eventually_gt_atTop b).exists
  refine ((Finset.range N).finite_toSet.image β).subset ?_
  rintro z ⟨⟨s, rfl⟩, -, hb⟩
  refine ⟨s, ?_, rfl⟩
  simp only [Finset.coe_range, mem_Iio]
  by_contra hs
  push Not at hs
  have := hβ.monotone hs
  linarith

/-- The meromorphic continuation of `𝓜h₂` (`κ = 0`) is bounded on every strip for `|ℑz|`
large. -/
theorem stripData_mellinTrunc₂ContZero (a₀ : ℝ) :
    StripData (mellinTrunc₂ContZero h bs β) (range β) a₀ where
  diff := fun z _ hz => differentiableAt_mellinTrunc₂ContZero hloc hβ hβ' hh fun s hs =>
    hz ⟨s, hs.symm⟩
  finite := finite_range_β_strip hβ hβ'
  poly := fun a b _ => by
    obtain ⟨N, hN⟩ := (hβ'.eventually_gt_atTop b).exists
    have hf := isGenAsympExpansion_inv hh
    have hloc' := locallyIntegrableOn_comp_inv hloc
    -- the remainder term is bounded for `ℜ(−z) ≥ −b`
    obtain ⟨M₂, hM₂0, hM₂⟩ := exists_norm_mellin_trunc₁_le (locallyIntegrableOn_sub_expPartial
      (a := bs) (α := β) hloc' N) (sub_expPartial_isBigO hf N) (a := -b) (by simpa using hN)
    set Y : ℝ := 1 + ∑ s ∈ Finset.range N, |(β s).im| with hY
    have hY1 : 1 ≤ Y := by
      rw [hY]
      linarith [Finset.sum_nonneg (fun s _ => abs_nonneg (β s).im) (s := Finset.range N)]
    refine ⟨∑ s ∈ Finset.range N, ‖bs s‖ + M₂, 0, Y, by positivity, le_rfl, hY1,
      fun z hza hzb hzim => ?_⟩
    have hsep : ∀ s ∈ Finset.range N, 1 ≤ ‖-z + β s‖ := fun s hs => by
      have h1 : |(β s).im| ≤ ∑ s ∈ Finset.range N, |(β s).im| :=
        Finset.single_le_sum (f := fun s => |(β s).im|) (fun _ _ => abs_nonneg _) hs
      have h2 := abs_im_le_norm (-z + β s)
      simp only [add_im, neg_im] at h2
      have h3 : |z.im| - |(β s).im| ≤ |-z.im + (β s).im| := by
        have := abs_sub_abs_le_abs_sub (-z.im) (-(β s).im)
        rwa [abs_neg, abs_neg, sub_neg_eq_add] at this
      linarith
    have hdom : -z ∈ contDomain β N := by
      refine ⟨by simp; linarith, fun s hs h => ?_⟩
      have := hsep s (Finset.mem_range.mpr hs)
      rw [h, neg_add_cancel, norm_zero] at this
      linarith
    rw [Real.rpow_zero, mul_one, mellinTrunc₂ContZero, mellinTrunc₁Cont_eq hβ hf hloc' hdom,
      mellinTrunc₁Ext]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans ?_)
      (hM₂ _ (by simp; linarith)))
    refine Finset.sum_le_sum fun s hs => ?_
    rw [norm_div]
    exact div_le_self (norm_nonneg _) (hsep s hs)

end Zero

end Azurite.DLMF
