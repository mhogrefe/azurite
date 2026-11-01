/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section3Bleistein
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# DLMF §2.3(v): Bleistein's quadratic change of variable (2.3.24–2.3.31)

The integral 2.3.24 is `I(α, x) = ∫₀^k e^{−xp(α,t)} q(α,t) t^{λ−1} dt`. For one value of `α`,
the phase `p = p(α, ·)` is given on an open interval `J ∋ 0, α` (`BleisteinPhase p J α`). It is
`C²` on `J`, `p′(α) = 0` and `p″(α) ≠ 0` (as in DLMF), and `(t − α)p′(t) > 0` for `t ≠ α`.

DLMF only asks that the minimum of `p` on `[0, k)` is at `t = α`. That does not make `t ↦ w`
one-to-one, as DLMF claims; strict monotonicity on each side of `α` is needed. Also, for `α < 0`
the point `t = α` is not in `[0, k)`, so `p` must be defined on a larger interval.

* `bleisteinA` is `a` of 2.3.26 and `bleisteinW` is `w` of 2.3.27. For `α < 0`, DLMF's
  `a = (2p(α,0) − 2p(α,α))^{1/2} ≥ 0` is wrong: `t = 0 ↦ w = 0` forces `a < 0`. Here `a` has the
  sign of `α` (`dlmf_2_3_26`); `dlmf_2_3_27_unsigned_ne` shows DLMF's choice gives `w(0) ≠ 0`.
* `dlmf_2_3_25`: `p(t) = ½w² − aw + b` with `b = p(0)`.
* `dlmf_2_3_28`: `dw/dt = ±p′(t)/(2p(t) − 2p(α))^{1/2}` for `t ≠ α`, and `dw/dt = p″(α)^{1/2}` at
  `t = α`. `tendsto_bleisteinDeriv` gives continuity there ("free from singularity"), and
  `strictMonoOn_W` says `t ↦ w` is one-to-one. The proofs use L'Hôpital's rule for
  `(2p(t) − 2p(α))/(t − α)² → p″(α)`.
* `dlmf_2_3_29`: `I = e^{−xp(0)} ∫ exp(−x(½w² − aw)) f(w) w^{λ−1} dw` over the image of the
  `t`-range. `dlmf_2_3_29_Ioo` treats `(0, k) ↦ (0, κ)` with `κ = w(k)`. Integrability is
  transported both ways (`integrableOn_iff`).
* `bleisteinAmp` is `f` of 2.3.30, with `dt/dw = 1/(dw/dt)` evaluated at `t = t(w)`.
* `dlmf_2_3_32_integral`: 2.3.32 for `I(α, x)` itself, uniformly in `α ∈ Λ`. It combines the
  above with `dlmf_2_3_32`. The Taylor expansion 2.3.31 enters only through a uniform remainder
  bound after `n` terms.
-/

open Set Filter Topology MeasureTheory

namespace Azurite.DLMF

/-- The hypotheses on the phase `p = p(α, ·)` near `[0, k)` and `α`. -/
structure BleisteinPhase (p : ℝ → ℝ) (J : Set ℝ) (α : ℝ) : Prop where
  isOpen : IsOpen J
  ordConnected : J.OrdConnected
  zero_mem : (0 : ℝ) ∈ J
  mem : α ∈ J
  contDiffOn : ContDiffOn ℝ 2 p J
  deriv_eq_zero : deriv p α = 0
  sign_deriv : ∀ t ∈ J, t ≠ α → 0 < (t - α) * deriv p t
  deriv2_ne_zero : deriv (deriv p) α ≠ 0

/-- `w − a = ±(2p(t) − 2p(α))^{1/2}`, the sign being that of `t − α`. -/
noncomputable def bleisteinCentered (p : ℝ → ℝ) (α t : ℝ) : ℝ :=
  if α ≤ t then √(2 * p t - 2 * p α) else -√(2 * p t - 2 * p α)

/-- DLMF 2.3.26, `a`, with the sign of `α`. -/
noncomputable def bleisteinA (p : ℝ → ℝ) (α : ℝ) : ℝ := -bleisteinCentered p α 0

/-- DLMF 2.3.27, `w = a ± (2p(t) − 2p(α))^{1/2}`. -/
noncomputable def bleisteinW (p : ℝ → ℝ) (α t : ℝ) : ℝ :=
  bleisteinA p α + bleisteinCentered p α t

/-- DLMF 2.3.28, `dw/dt`. -/
noncomputable def bleisteinDeriv (p : ℝ → ℝ) (α t : ℝ) : ℝ :=
  if t = α then √(deriv (deriv p) α)
  else (if α ≤ t then 1 else -1) * deriv p t / √(2 * p t - 2 * p α)

/-- The inverse `w ↦ t` of `bleisteinW` on `J`. -/
noncomputable def bleisteinInv (p : ℝ → ℝ) (J : Set ℝ) (α : ℝ) : ℝ → ℝ :=
  Function.invFunOn (bleisteinW p α) J

/-- DLMF 2.3.30, `f(α, w) = q(α, t)(t/w)^{λ−1} dt/dw`. -/
noncomputable def bleisteinAmp (lam : ℝ) (p : ℝ → ℝ) (q : ℝ → ℂ) (J : Set ℝ) (α w : ℝ) : ℂ :=
  ((bleisteinInv p J α w / w) ^ (lam - 1) / bleisteinDeriv p α (bleisteinInv p J α w)) •
    q (bleisteinInv p J α w)

theorem bleisteinCentered_self (p : ℝ → ℝ) (α : ℝ) : bleisteinCentered p α α = 0 := by
  simp [bleisteinCentered]

theorem bleisteinW_zero (p : ℝ → ℝ) (α : ℝ) : bleisteinW p α 0 = 0 := by
  simp [bleisteinW, bleisteinA]

theorem bleisteinW_self (p : ℝ → ℝ) (α : ℝ) : bleisteinW p α α = bleisteinA p α := by
  simp [bleisteinW, bleisteinCentered_self]

/-- DLMF 2.3.27: `w = a + (2p(t) − 2p(α))^{1/2}` for `t ≥ α`, `w = a − (…)^{1/2}` for
`t < α`. -/
theorem dlmf_2_3_27 (p : ℝ → ℝ) (α t : ℝ) :
    (α ≤ t → bleisteinW p α t = bleisteinA p α + √(2 * p t - 2 * p α)) ∧
      (t < α → bleisteinW p α t = bleisteinA p α - √(2 * p t - 2 * p α)) := by
  refine ⟨fun h => by simp [bleisteinW, bleisteinCentered, h], fun h => ?_⟩
  simp [bleisteinW, bleisteinCentered, not_le.mpr h, sub_eq_add_neg]

namespace BleisteinPhase

variable {p : ℝ → ℝ} {J : Set ℝ} {α : ℝ}

theorem hasDerivAt (h : BleisteinPhase p J α) {t : ℝ} (ht : t ∈ J) :
    HasDerivAt p (deriv p t) t :=
  ((h.contDiffOn.differentiableOn (by norm_num)).differentiableAt
    (h.isOpen.mem_nhds ht)).hasDerivAt

theorem hasDerivAt_deriv (h : BleisteinPhase p J α) :
    HasDerivAt (deriv p) (deriv (deriv p) α) α :=
  (((h.contDiffOn.deriv_of_isOpen h.isOpen (m := 1) (by norm_num)).differentiableOn
    (by norm_num)).differentiableAt (h.isOpen.mem_nhds h.mem)).hasDerivAt

theorem Icc_subset (h : BleisteinPhase p J α) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    Icc s t ⊆ J :=
  h.ordConnected.out hs ht

theorem lt_p (h : BleisteinPhase p J α) {t : ℝ} (ht : t ∈ J) (hne : t ≠ α) : p α < p t := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨c, hc, hd⟩ := exists_deriv_eq_slope p hlt
      (fun y hy => (h.hasDerivAt (h.Icc_subset ht h.mem hy)).continuousAt.continuousWithinAt)
      (fun y hy => (h.hasDerivAt (h.Icc_subset ht h.mem
        (Ioo_subset_Icc_self hy))).differentiableAt.differentiableWithinAt)
    have hs := h.sign_deriv c (h.Icc_subset ht h.mem (Ioo_subset_Icc_self hc)) hc.2.ne
    have hneg : deriv p c < 0 := by nlinarith [hc.2]
    rw [eq_div_iff (by linarith)] at hd
    nlinarith [hc.2]
  · obtain ⟨c, hc, hd⟩ := exists_deriv_eq_slope p hgt
      (fun y hy => (h.hasDerivAt (h.Icc_subset h.mem ht hy)).continuousAt.continuousWithinAt)
      (fun y hy => (h.hasDerivAt (h.Icc_subset h.mem ht
        (Ioo_subset_Icc_self hy))).differentiableAt.differentiableWithinAt)
    have hs := h.sign_deriv c (h.Icc_subset h.mem ht (Ioo_subset_Icc_self hc)) hc.1.ne'
    have hpos : 0 < deriv p c := by nlinarith [hc.1]
    rw [eq_div_iff (by linarith)] at hd
    nlinarith [hc.1]

theorem p_le (h : BleisteinPhase p J α) {t : ℝ} (ht : t ∈ J) : p α ≤ p t := by
  rcases eq_or_ne t α with rfl | hne
  · exact le_rfl
  · exact (h.lt_p ht hne).le

theorem centered_sq (h : BleisteinPhase p J α) {t : ℝ} (ht : t ∈ J) :
    bleisteinCentered p α t ^ 2 = 2 * p t - 2 * p α := by
  have hX : 0 ≤ 2 * p t - 2 * p α := by linarith [h.p_le ht]
  unfold bleisteinCentered
  split_ifs <;> simp [Real.sq_sqrt hX]

/-- DLMF 2.3.25: `p(t) = ½w² − aw + b`, `b = p(0)`. -/
theorem dlmf_2_3_25 (h : BleisteinPhase p J α) {t : ℝ} (ht : t ∈ J) :
    p t = bleisteinW p α t ^ 2 / 2 - bleisteinA p α * bleisteinW p α t + p 0 := by
  have h1 := h.centered_sq ht
  have h0 := h.centered_sq h.zero_mem
  simp only [bleisteinW, bleisteinA]
  linear_combination (-1 / 2 : ℝ) * h1 + (1 / 2 : ℝ) * h0

/-- DLMF 2.3.26: `a² = 2p(α,0) − 2p(α,α)` (and `b = p(α, 0)`), with `a ≥ 0` for `α ≥ 0` and
`a ≤ 0` for `α < 0`. -/
theorem dlmf_2_3_26 (h : BleisteinPhase p J α) :
    bleisteinA p α ^ 2 = 2 * p 0 - 2 * p α ∧
      (0 ≤ α → bleisteinA p α = √(2 * p 0 - 2 * p α)) ∧
      (α < 0 → bleisteinA p α = -√(2 * p 0 - 2 * p α)) := by
  refine ⟨by rw [bleisteinA, neg_sq, h.centered_sq h.zero_mem], fun hα => ?_, fun hα => ?_⟩
  · rcases hα.lt_or_eq with hα | rfl
    · simp [bleisteinA, bleisteinCentered, not_le.mpr hα]
    · simp [bleisteinA, bleisteinCentered]
  · simp [bleisteinA, bleisteinCentered, hα.le]

/-- DLMF's unsigned `a` in 2.3.26–2.3.27 fails for `α < 0`: at `t = 0 > α` (upper sign) it gives
`w = 2(2p(α,0) − 2p(α,α))^{1/2} ≠ 0`, although `t = 0` should correspond to `w = 0`. -/
theorem dlmf_2_3_27_unsigned_ne (h : BleisteinPhase p J α) (hα : α < 0) :
    √(2 * p 0 - 2 * p α) + √(2 * p 0 - 2 * p α) ≠ 0 := by
  have := h.lt_p h.zero_mem hα.ne'
  have : 0 < √(2 * p 0 - 2 * p α) := Real.sqrt_pos.mpr (by linarith)
  linarith

theorem tendsto_ratio (h : BleisteinPhase p J α) :
    Tendsto (fun t => (2 * p t - 2 * p α) / (t - α) ^ 2) (𝓝[≠] α)
      (𝓝 (deriv (deriv p) α)) := by
  have hJ : ∀ᶠ t in 𝓝[≠] α, t ∈ J := nhdsWithin_le_nhds (h.isOpen.mem_nhds h.mem)
  refine HasDerivAt.lhopital_zero_nhdsNE (f' := fun t => 2 * deriv p t)
    (g' := fun t => 2 * (t - α)) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hJ] with t ht
    exact ((h.hasDerivAt ht).const_mul 2).sub_const _
  · refine Eventually.of_forall fun t => ?_
    convert ((hasDerivAt_id' t).sub_const α).mul ((hasDerivAt_id' t).sub_const α) using 1
    · ext y
      simp only [Pi.mul_apply]
      ring
    · ring
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_ne_zero two_ne_zero (sub_ne_zero.mpr ht)
  · have := (((h.hasDerivAt h.mem).continuousAt.tendsto).const_mul 2).sub_const (2 * p α)
    simpa using this.mono_left nhdsWithin_le_nhds
  · have := ((continuous_id.sub continuous_const).pow 2).tendsto α (f := fun t : ℝ => (t - α) ^ 2)
    simpa using this.mono_left nhdsWithin_le_nhds
  · have := hasDerivAt_iff_tendsto_slope.mp h.hasDerivAt_deriv
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht : t - α ≠ 0 := sub_ne_zero.mpr ht
    rw [slope_def_field, h.deriv_eq_zero, sub_zero]
    field_simp

theorem deriv_div_pos (h : BleisteinPhase p J α) {t : ℝ} (ht : t ∈ J) (hne : t ≠ α) :
    0 < deriv p t / (t - α) := by
  have hs := h.sign_deriv t ht hne
  have h2 : 0 < (t - α) ^ 2 := lt_of_le_of_ne (sq_nonneg _)
    (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hne)))
  have : deriv p t / (t - α) = (t - α) * deriv p t / (t - α) ^ 2 := by
    field_simp [sub_ne_zero.mpr hne]
  rw [this]
  exact div_pos hs h2

theorem deriv2_pos (h : BleisteinPhase p J α) : 0 < deriv (deriv p) α := by
  have hT := hasDerivAt_iff_tendsto_slope.mp h.hasDerivAt_deriv
  have hJ : ∀ᶠ t in 𝓝[≠] α, t ∈ J := nhdsWithin_le_nhds (h.isOpen.mem_nhds h.mem)
  have hge : 0 ≤ deriv (deriv p) α := by
    refine ge_of_tendsto hT ?_
    filter_upwards [hJ, self_mem_nhdsWithin] with t ht hne
    rw [slope_def_field, h.deriv_eq_zero, sub_zero]
    exact (h.deriv_div_pos ht hne).le
  exact lt_of_le_of_ne hge (Ne.symm h.deriv2_ne_zero)

theorem hasDerivAt_W_self (h : BleisteinPhase p J α) :
    HasDerivAt (bleisteinW p α) (√(deriv (deriv p) α)) α := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hT := (Real.continuous_sqrt.tendsto _).comp h.tendsto_ratio
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (h.isOpen.mem_nhds h.mem)] with t ht
    htJ
  have ht : t ≠ α := ht
  have hd : bleisteinW p α t - bleisteinW p α α = bleisteinCentered p α t := by
    simp [bleisteinW, bleisteinCentered_self]
  rw [slope_def_field, hd, Function.comp_apply, Real.sqrt_div' _ (sq_nonneg _),
    Real.sqrt_sq_eq_abs]
  unfold bleisteinCentered
  split_ifs with hle
  · rw [abs_of_pos (lt_of_le_of_ne (sub_nonneg.mpr hle) (sub_ne_zero.mpr ht).symm)]
  · rw [abs_of_neg (by linarith [not_le.mp hle]), div_neg, neg_div]

/-- DLMF 2.3.28: `w` is differentiable on `J` with derivative `bleisteinDeriv`
(`±p′(t)/(2p(t) − 2p(α))^{1/2}` off `α`, `p″(α)^{1/2}` at `α`). -/
theorem dlmf_2_3_28 (h : BleisteinPhase p J α) {t : ℝ} (ht : t ∈ J) :
    HasDerivAt (bleisteinW p α) (bleisteinDeriv p α t) t := by
  rcases eq_or_ne t α with rfl | hne
  · simpa [bleisteinDeriv] using h.hasDerivAt_W_self
  have hX : 0 < 2 * p t - 2 * p α := by linarith [h.lt_p ht hne]
  have hs := (((h.hasDerivAt ht).const_mul 2).sub_const (2 * p α)).sqrt hX.ne'
  have hsq : 0 < √(2 * p t - 2 * p α) := Real.sqrt_pos.mpr hX
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hev : bleisteinW p α =ᶠ[𝓝 t] fun y => bleisteinA p α + -√(2 * p y - 2 * p α) := by
      filter_upwards [Iio_mem_nhds hlt] with y hy
      simp [bleisteinW, bleisteinCentered, not_le.mpr (show y < α from hy)]
    have := (hs.neg.const_add (bleisteinA p α)).congr_of_eventuallyEq hev
    convert this using 1
    simp only [bleisteinDeriv, hne, ↓reduceIte, not_le.mpr hlt]
    field_simp
  · have hev : bleisteinW p α =ᶠ[𝓝 t] fun y => bleisteinA p α + √(2 * p y - 2 * p α) := by
      filter_upwards [Ioi_mem_nhds hgt] with y hy
      simp [bleisteinW, bleisteinCentered, (show α < y from hy).le]
    have := (hs.const_add (bleisteinA p α)).congr_of_eventuallyEq hev
    convert this using 1
    simp only [bleisteinDeriv, hne, ↓reduceIte, hgt.le]
    field_simp

theorem deriv_pos (h : BleisteinPhase p J α) {t : ℝ} (ht : t ∈ J) :
    0 < bleisteinDeriv p α t := by
  unfold bleisteinDeriv
  split_ifs with h1 h2
  · exact Real.sqrt_pos.mpr h.deriv2_pos
  · have hX : 0 < 2 * p t - 2 * p α := by linarith [h.lt_p ht h1]
    have hs := h.sign_deriv t ht h1
    have : 0 < deriv p t := by
      have : 0 < t - α := lt_of_le_of_ne (sub_nonneg.mpr h2) (sub_ne_zero.mpr h1).symm
      nlinarith
    exact div_pos (by linarith) (Real.sqrt_pos.mpr hX)
  · have hX : 0 < 2 * p t - 2 * p α := by linarith [h.lt_p ht h1]
    have hs := h.sign_deriv t ht h1
    have : deriv p t < 0 := by
      have : t - α < 0 := by linarith [not_le.mp h2]
      nlinarith
    exact div_pos (by linarith) (Real.sqrt_pos.mpr hX)

/-- DLMF 2.3.28, "free from singularity at `t = α`": `dw/dt → p″(α)^{1/2}` as `t → α`. -/
theorem tendsto_bleisteinDeriv (h : BleisteinPhase p J α) :
    Tendsto (bleisteinDeriv p α) (𝓝[≠] α) (𝓝 (√(deriv (deriv p) α))) := by
  have hT1 := hasDerivAt_iff_tendsto_slope.mp h.hasDerivAt_deriv
  have hT2 := (Real.continuous_sqrt.tendsto _).comp h.tendsto_ratio
  have hpos := Real.sqrt_pos.mpr h.deriv2_pos
  have hT := hT1.div hT2 hpos.ne'
  rw [Real.div_sqrt] at hT
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (h.isOpen.mem_nhds h.mem)] with t ht
    htJ
  have ht : t ≠ α := ht
  have hX : 0 < 2 * p t - 2 * p α := by linarith [h.lt_p htJ ht]
  have hsq : 0 < √(2 * p t - 2 * p α) := Real.sqrt_pos.mpr hX
  have hta : t - α ≠ 0 := sub_ne_zero.mpr ht
  simp only [Pi.div_apply, Function.comp_apply]
  rw [slope_def_field, h.deriv_eq_zero, sub_zero, Real.sqrt_div' _ (sq_nonneg _),
    Real.sqrt_sq_eq_abs]
  simp only [bleisteinDeriv, ht, ↓reduceIte]
  split_ifs with hle
  · rw [abs_of_pos (lt_of_le_of_ne (sub_nonneg.mpr hle) (sub_ne_zero.mpr ht).symm)]
    field_simp
  · rw [abs_of_neg (by linarith [not_le.mp hle])]
    field_simp

/-- `t ↦ w` is strictly increasing, hence one-to-one, on `J`. -/
theorem strictMonoOn_W (h : BleisteinPhase p J α) : StrictMonoOn (bleisteinW p α) J :=
  strictMonoOn_of_deriv_pos h.ordConnected.convex
    (fun t ht => (h.dlmf_2_3_28 ht).continuousAt.continuousWithinAt)
    (fun t ht => by
      rw [h.isOpen.interior_eq] at ht
      rw [(h.dlmf_2_3_28 ht).deriv]
      exact h.deriv_pos ht)

theorem W_pos (h : BleisteinPhase p J α) {t : ℝ} (ht : t ∈ J ∩ Ioi 0) :
    0 < bleisteinW p α t := by
  rw [← bleisteinW_zero p α]
  exact h.strictMonoOn_W h.zero_mem ht.1 ht.2

theorem inv_W (h : BleisteinPhase p J α) {t : ℝ} (ht : t ∈ J) :
    bleisteinInv p J α (bleisteinW p α t) = t :=
  h.strictMonoOn_W.injOn.leftInvOn_invFunOn ht

/-- `κ = w(k)`: the image of `(0, k)` is `(0, κ)`. -/
theorem image_Ioo (h : BleisteinPhase p J α) {k : ℝ} (hk : k ∈ J) (hk0 : 0 < k) :
    bleisteinW p α '' Ioo 0 k = Ioo 0 (bleisteinW p α k) := by
  have hsub : Icc 0 k ⊆ J := h.Icc_subset h.zero_mem hk
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    have htJ := hsub (Ioo_subset_Icc_self ht)
    exact ⟨h.W_pos ⟨htJ, ht.1⟩, h.strictMonoOn_W htJ hk ht.2⟩
  · have := intermediate_value_Ioo hk0.le
      (fun t ht => (h.dlmf_2_3_28 (hsub ht)).continuousAt.continuousWithinAt)
    rwa [bleisteinW_zero] at this

theorem pointwise (h : BleisteinPhase p J α) (lam x : ℝ) (q : ℝ → ℂ) {t : ℝ}
    (ht : t ∈ J ∩ Ioi 0) :
    |bleisteinDeriv p α t| • (bleisteinWeight lam x (bleisteinA p α) (bleisteinW p α t) •
        bleisteinAmp lam p q J α (bleisteinW p α t)) =
      Real.exp (x * p 0) • ((Real.exp (-(x * p t)) * t ^ (lam - 1)) • q t) := by
  have hw := h.W_pos ht
  have hD := h.deriv_pos ht.1
  have ht0 : (0 : ℝ) < t := ht.2
  simp only [bleisteinAmp, h.inv_W ht.1, smul_smul, bleisteinWeight]
  congr 1
  rw [abs_of_pos hD, Real.div_rpow ht0.le hw.le, h.dlmf_2_3_25 ht.1]
  have he : Real.exp (-(x * (bleisteinW p α t ^ 2 / 2 - bleisteinA p α * bleisteinW p α t +
      p 0))) = Real.exp (-(x * p 0)) *
        Real.exp (-(x * (bleisteinW p α t ^ 2 / 2 - bleisteinA p α * bleisteinW p α t))) := by
    rw [← Real.exp_add]
    ring_nf
  have hwr : 0 < bleisteinW p α t ^ (lam - 1) := Real.rpow_pos_of_pos hw _
  have hE : Real.exp (x * p 0) * Real.exp (-(x * p 0)) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [he]
  field_simp
  linear_combination (-1 : ℝ) * hE

/-- DLMF 2.3.29: the substitution `t ↦ w` turns `∫_S e^{−xp(t)} q(t) t^{λ−1} dt` into
`e^{−xp(0)} ∫_{w(S)} exp(−x(½w² − aw)) f(w) w^{λ−1} dw`. -/
theorem dlmf_2_3_29 (h : BleisteinPhase p J α) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ J ∩ Ioi 0) (lam x : ℝ) (q : ℝ → ℂ) :
    ∫ t in S, (Real.exp (-(x * p t)) * t ^ (lam - 1)) • q t =
      Real.exp (-(x * p 0)) • ∫ w in bleisteinW p α '' S,
        bleisteinWeight lam x (bleisteinA p α) w • bleisteinAmp lam p q J α w := by
  have hd : ∀ t ∈ S, HasDerivWithinAt (bleisteinW p α) (bleisteinDeriv p α t) S t :=
    fun t ht => (h.dlmf_2_3_28 (hS ht).1).hasDerivWithinAt
  have hinj : InjOn (bleisteinW p α) S := h.strictMonoOn_W.injOn.mono fun t ht => (hS ht).1
  rw [integral_image_eq_integral_abs_deriv_smul hSm hd hinj,
    setIntegral_congr_fun hSm fun t ht => h.pointwise lam x q (hS ht), integral_smul, smul_smul,
    ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

/-- Integrability is preserved by the substitution of 2.3.29. -/
theorem integrableOn_iff (h : BleisteinPhase p J α) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ J ∩ Ioi 0) (lam x : ℝ) (q : ℝ → ℂ) :
    IntegrableOn (fun t => (Real.exp (-(x * p t)) * t ^ (lam - 1)) • q t) S ↔
      IntegrableOn (fun w => bleisteinWeight lam x (bleisteinA p α) w •
        bleisteinAmp lam p q J α w) (bleisteinW p α '' S) := by
  have hd : ∀ t ∈ S, HasDerivWithinAt (bleisteinW p α) (bleisteinDeriv p α t) S t :=
    fun t ht => (h.dlmf_2_3_28 (hS ht).1).hasDerivWithinAt
  have hinj : InjOn (bleisteinW p α) S := h.strictMonoOn_W.injOn.mono fun t ht => (hS ht).1
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hSm hd hinj,
    integrableOn_congr_fun (fun t ht => h.pointwise lam x q (hS ht)) hSm]
  exact (integrable_smul_iff (Real.exp_pos _).ne' _).symm

/-- DLMF 2.3.29 for `S = (0, k)`: the `w`-range is `(0, κ)`, `κ = w(k)`. -/
theorem dlmf_2_3_29_Ioo (h : BleisteinPhase p J α) {k : ℝ} (hk : k ∈ J) (hk0 : 0 < k)
    (lam x : ℝ) (q : ℝ → ℂ) :
    ∫ t in Ioo 0 k, (Real.exp (-(x * p t)) * t ^ (lam - 1)) • q t =
      Real.exp (-(x * p 0)) • ∫ w in Ioo 0 (bleisteinW p α k),
        bleisteinWeight lam x (bleisteinA p α) w • bleisteinAmp lam p q J α w := by
  rw [h.dlmf_2_3_29 measurableSet_Ioo (fun t ht => ⟨h.Icc_subset h.zero_mem hk
    (Ioo_subset_Icc_self ht), ht.1⟩) lam x q, h.image_Ioo hk hk0]

theorem measurableSet_image (h : BleisteinPhase p J α) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ J) : MeasurableSet (bleisteinW p α '' S) :=
  measurable_image_of_fderivWithin hSm
    (fun _ ht => (h.dlmf_2_3_28 (hS ht)).hasDerivWithinAt.hasFDerivWithinAt)
    (h.strictMonoOn_W.injOn.mono hS)

end BleisteinPhase

/-- DLMF 2.3.32 for the integral 2.3.24 itself, uniformly for `α ∈ Λ`. For each `α`, the phase
satisfies `BleisteinPhase`, and the `t`-range `S(α)` (DLMF: `(0, k)`) lies in `J(α) ∩ (0, ∞)`.
The amplitude `f(α, ·)` of 2.3.30 has a uniform Taylor remainder bound about `w = a(α)` on the
`w`-range (2.3.31 truncated), and `κ(α) ≥ a(α) + δ`. Then
`‖I(α, x) − e^{−xp(α,0)} ∑_{s<n} φₛ(α) x^{−(λ+s)/2} Fₛ(a√x)‖
  ≤ K e^{−xp(α,0)} x^{−(λ+n)/2} Gₙ(a√x)`. -/
theorem dlmf_2_3_32_integral {Λ : Set ℝ} {p : ℝ → ℝ → ℝ} {q : ℝ → ℝ → ℂ} {J S : ℝ → Set ℝ}
    {φ : ℕ → ℝ → ℂ} {lam δ B C : ℝ} {n : ℕ} (hlam : 0 < lam) (hδ : 0 < δ)
    (hph : ∀ α ∈ Λ, BleisteinPhase (p α) (J α) α)
    (hSm : ∀ α ∈ Λ, MeasurableSet (S α)) (hS : ∀ α ∈ Λ, S α ⊆ J α ∩ Ioi 0)
    (hfar : ∀ α ∈ Λ, ∀ w, 0 < w → w ∉ bleisteinW (p α) α '' S α →
      δ ≤ |w - bleisteinA (p α) α|)
    (hφ : ∀ s < n, ∀ α ∈ Λ, ‖φ s α‖ ≤ B)
    (hT : ∀ α ∈ Λ, ∀ w ∈ bleisteinW (p α) α '' S α,
      ‖bleisteinAmp lam (p α) (q α) (J α) α w -
          ∑ s ∈ Finset.range n, (w - bleisteinA (p α) α) ^ s • φ s α‖ ≤
        C * |w - bleisteinA (p α) α| ^ n)
    (hint : ∀ α ∈ Λ, ∀ x, 0 < x →
      IntegrableOn (fun t => (Real.exp (-(x * p α t)) * t ^ (lam - 1)) • q α t) (S α)) :
    ∃ K, ∀ α ∈ Λ, ∀ x, 0 < x →
      ‖(∫ t in S α, (Real.exp (-(x * p α t)) * t ^ (lam - 1)) • q α t) -
          Real.exp (-(x * p α 0)) • ∑ s ∈ Finset.range n,
            (x ^ (-(lam + s) / 2) * bleisteinF lam s (bleisteinA (p α) α * √x)) • φ s α‖ ≤
        K * Real.exp (-(x * p α 0)) *
          (x ^ (-(lam + n) / 2) * bleisteinG lam n (bleisteinA (p α) α * √x)) := by
  obtain ⟨K, hK⟩ := dlmf_2_3_32 (A := Λ) (U := fun α => bleisteinW (p α.1) α.1 '' S α.1)
    (a := fun α => bleisteinA (p α.1) α.1)
    (f := fun α => bleisteinAmp lam (p α.1) (q α.1) (J α.1) α.1) (φ := fun s α => φ s α.1)
    hlam hδ
    (fun α => by
      rintro _ ⟨t, ht, rfl⟩
      exact (hph α.1 α.2).W_pos (hS α.1 α.2 ht))
    (fun α => (hph α.1 α.2).measurableSet_image (hSm α.1 α.2)
      fun t ht => (hS α.1 α.2 ht).1)
    (fun α => hfar α.1 α.2) (fun s hs α => hφ s hs α.1 α.2) (fun α => hT α.1 α.2)
    (fun α x hx => ((hph α.1 α.2).integrableOn_iff (hSm α.1 α.2) (hS α.1 α.2) lam x
      (q α.1)).mp (hint α.1 α.2 x hx))
  refine ⟨K, fun α hα x hx => ?_⟩
  have hb := hK ⟨α, hα⟩ x hx
  rw [(hph α hα).dlmf_2_3_29 (hSm α hα) (hS α hα), ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-(x * p α 0)) * ‖_‖ ≤ Real.exp (-(x * p α 0)) *
        (K * (x ^ (-(lam + n) / 2) * bleisteinG lam n (bleisteinA (p α) α * √x))) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by ring

end Azurite.DLMF
