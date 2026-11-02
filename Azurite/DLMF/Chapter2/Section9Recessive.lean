/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section9Formal

/-!
# DLMF §2.9(i): Distinct Characteristic Values — solutions 2.9.8, recessive and dominant

* 2.9.8 (`IsDiffAsympDLMF`): `w(n) ∼ ρⁿ n^α ∑ aₛ/nˢ`, i.e. `w(n)/(ρⁿ n^α) ∼ ∑ aₛ/nˢ` (2.9.3 form);
  with `a₀ = 1` it gives the leading behaviour `w(n)/(ρⁿ n^α) → 1` (`HasLeading`).
* Consequences of 2.9.8 for any `w₁`, `w₂` with these leading behaviours and `ρ₁ ≠ ρ₂`:
  * `HasLeading.tendsto_ratio`: `w(n+1)/w(n) → ρ`;
  * `dlmf_2_9_8_independent`: `w₁`, `w₂` are linearly independent (even eventually);
  * `dlmf_2_9_8_recessive`: if `|ρ₂| > |ρ₁|`, or `|ρ₂| = |ρ₁|` and `ℜα₂ > ℜα₁`, then
    `w₁(n)/w₂(n) → 0` (`w₁` recessive, `w₂` dominant);
  * `dlmf_2_9_8_neither`: if `|ρ₂| = |ρ₁|` and `ℜα₂ = ℜα₁`, then `|w₁(n)/w₂(n)| → 1` (neither
    solution is dominant).
* "Recessive solutions are unique and dominant solutions are not": `dlmf_2_9_8_recessive_unique`
  (for solutions of 2.9.1, any solution `v` with `v/w₂ → 0` is eventually a multiple of `w₁`;
  via the Casoratian, `IsDiffSolution.eq_comb`, `exists_casoratian_ne_zero`) and
  `dlmf_2_9_8_dominant_not_unique` (`w₂ + c w₁` is again a solution relative to which `w₁` is
  recessive).

Not formalized: the existence of the solutions `w_j` of 2.9.8 (Wong and Li 1992b), error bounds
(Zhang et al. 1996), inverse factorial series (Olde Daalhuis 2004a), and the informal remark on
numerically satisfactory pairs.
-/

open Filter Topology Asymptotics Finset Complex

namespace Azurite.DLMF

/-- `w(n)/(ρⁿ n^α)`. -/
noncomputable def leadRatio (w : ℕ → ℂ) (ρ α : ℂ) (n : ℕ) : ℂ := w n / (ρ ^ n * (n : ℂ) ^ α)

/-- **DLMF 2.9.8**: `w(n) ∼ ρⁿ n^α ∑_{s=0}^∞ aₛ/nˢ` as `n → ∞`. -/
def IsDiffAsympDLMF (w : ℕ → ℂ) (ρ α : ℂ) (a : ℕ → ℂ) : Prop :=
  IsAsympSeqDLMF (leadRatio w ρ α) a

/-- The leading behaviour `w(n) ∼ ρⁿ n^α`. -/
def HasLeading (w : ℕ → ℂ) (ρ α : ℂ) : Prop :=
  Tendsto (leadRatio w ρ α) atTop (𝓝 1)

variable {w w₁ w₂ v : ℕ → ℂ} {ρ ρ₁ ρ₂ α α₁ α₂ : ℂ}

theorem IsDiffAsympDLMF.hasLeading {a : ℕ → ℂ} (h : IsDiffAsympDLMF w ρ α a) (ha : a 0 = 1) :
    HasLeading w ρ α := by
  have h1 := ((isAsympSeqDLMF_iff _ _).mp h) 1
  have hX : Tendsto (fun n : ℕ => ((n : ℂ)⁻¹) ^ 1) atTop (𝓝 0) := by
    simpa using tendsto_natInv
  have h2 := h1.trans_tendsto hX
  simp only [sum_range_one, pow_zero, mul_one, ha] at h2
  have h3 := h2.add_const 1
  simp only [sub_add_cancel, zero_add] at h3
  exact h3

theorem natCast_cpow_ne_zero {n : ℕ} (hn : 1 ≤ n) (β : ℂ) : (n : ℂ) ^ β ≠ 0 := fun h =>
  (Nat.cast_ne_zero.mpr (by omega : n ≠ 0)) ((cpow_eq_zero_iff _ _).mp h).1

theorem HasLeading.ne_zero (h : HasLeading w ρ α) : ρ ≠ 0 := by
  rintro rfl
  have h0 : Tendsto (leadRatio w 0 α) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [leadRatio, zero_pow (by omega), zero_mul, div_zero]
  exact one_ne_zero (tendsto_nhds_unique h h0)

theorem HasLeading.eventually_lead_ne (h : HasLeading w ρ α) :
    ∀ᶠ n in atTop, leadRatio w ρ α n ≠ 0 :=
  Tendsto.eventually_ne (show Tendsto (leadRatio w ρ α) atTop (𝓝 1) from h) one_ne_zero

theorem HasLeading.eventually_ne (h : HasLeading w ρ α) : ∀ᶠ n in atTop, w n ≠ 0 := by
  filter_upwards [h.eventually_lead_ne] with n hn hw
  exact hn (by rw [leadRatio, hw, zero_div])

theorem HasLeading.eq_mul (h : HasLeading w ρ α) {n : ℕ} (hn : 1 ≤ n) :
    w n = leadRatio w ρ α n * (ρ ^ n * (n : ℂ) ^ α) :=
  (div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero _ h.ne_zero) (natCast_cpow_ne_zero hn α))).symm

/-- `w(n+1)/w(n) → ρ`. -/
theorem HasLeading.tendsto_ratio (h : HasLeading w ρ α) :
    Tendsto (fun n => w (n + 1) / w n) atTop (𝓝 ρ) := by
  have hρ := h.ne_zero
  have hu1 : Tendsto (fun n => leadRatio w ρ α (n + 1)) atTop (𝓝 1) :=
    h.comp (tendsto_add_atTop_nat 1)
  have hq : Tendsto (fun n : ℕ => (1 + (n : ℂ)⁻¹) ^ α) atTop (𝓝 1) := by
    have hc : ContinuousAt (fun z : ℂ => z ^ α) 1 := continuousAt_cpow_const (by simp)
    have h1 : Tendsto (fun n : ℕ => 1 + (n : ℂ)⁻¹) atTop (𝓝 1) := by
      simpa using tendsto_natInv.const_add 1
    have := hc.tendsto.comp h1
    rw [one_cpow] at this
    exact this
  have hlim := (tendsto_const_nhds (x := ρ)).mul ((hu1.div h one_ne_zero).mul hq)
  rw [div_one, mul_one, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1, h.eventually_lead_ne] with n hn hun
  have key := natCast_add_cpow_div α hn 1 0
  simp only [pow_zero, div_one, mul_one, Nat.cast_one, one_mul, CharP.cast_eq_zero, sub_zero]
    at key
  have hw : w n ≠ 0 := fun hw => hun (by rw [leadRatio, hw, zero_div])
  have hP := natCast_cpow_ne_zero hn α
  have hQ : (1 + (n : ℂ)⁻¹) ^ α ≠ 0 := by
    have := natCast_cpow_ne_zero (by omega : 1 ≤ n + 1) α
    rw [key] at this
    exact right_ne_zero_of_mul this
  simp only [Pi.div_apply, leadRatio]
  rw [key, pow_succ]
  field_simp
  exact mul_div_cancel_right₀ _ (by simpa [one_div] using hQ)

/-- **DLMF 2.9.8**: solutions with the leading behaviours `ρⱼⁿ n^{αⱼ}`, `ρ₁ ≠ ρ₂`, are linearly
independent (even as germs at `∞`). -/
theorem dlmf_2_9_8_independent (h₁ : HasLeading w₁ ρ₁ α₁) (h₂ : HasLeading w₂ ρ₂ α₂)
    (hne : ρ₁ ≠ ρ₂) {c₁ c₂ : ℂ} (h : ∀ᶠ n in atTop, c₁ * w₁ n + c₂ * w₂ n = 0) :
    c₁ = 0 ∧ c₂ = 0 := by
  by_cases hc₂ : c₂ = 0
  · subst hc₂
    obtain ⟨n, hn, hw⟩ := (h.and h₁.eventually_ne).exists
    rw [zero_mul, add_zero] at hn
    exact ⟨(mul_eq_zero.mp hn).resolve_right hw, rfl⟩
  · exfalso
    have hr : ∀ᶠ n in atTop, w₁ (n + 1) / w₁ n = w₂ (n + 1) / w₂ n := by
      filter_upwards [h, (tendsto_add_atTop_nat 1).eventually h, h₂.eventually_ne] with n hn hn1 hw
      have k1 : w₂ n = -(c₁ / c₂) * w₁ n := by
        field_simp
        linear_combination hn
      have k2 : w₂ (n + 1) = -(c₁ / c₂) * w₁ (n + 1) := by
        field_simp
        linear_combination hn1
      have hc : -(c₁ / c₂) ≠ 0 := fun h0 => hw (by rw [k1, h0, zero_mul])
      rw [k2, k1, mul_div_mul_left _ _ hc]
    exact hne (tendsto_nhds_unique (h₁.tendsto_ratio.congr' hr) h₂.tendsto_ratio)

/-- `|w₁(n)/w₂(n)| = (|u₁(n)|/|u₂(n)|) (|ρ₁|/|ρ₂|)ⁿ n^{ℜα₁ − ℜα₂}`, `uⱼ = wⱼ/(ρⱼⁿ n^{αⱼ})`. -/
theorem norm_div_eq (h₁ : HasLeading w₁ ρ₁ α₁) (h₂ : HasLeading w₂ ρ₂ α₂) :
    ∀ᶠ n in atTop, ‖leadRatio w₁ ρ₁ α₁ n‖ / ‖leadRatio w₂ ρ₂ α₂ n‖ *
      ((‖ρ₁‖ / ‖ρ₂‖) ^ n * (n : ℝ) ^ (α₁.re - α₂.re)) = ‖w₁ n / w₂ n‖ := by
  filter_upwards [eventually_ge_atTop 1, h₂.eventually_lead_ne] with n hn hu
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ₂ : ‖ρ₂‖ ≠ 0 := norm_ne_zero_iff.mpr h₂.ne_zero
  have hu' : ‖leadRatio w₂ ρ₂ α₂ n‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  rw [h₁.eq_mul hn, h₂.eq_mul hn, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow,
    norm_pow, norm_natCast_cpow_of_pos hn, norm_natCast_cpow_of_pos hn, Real.rpow_sub hn0,
    div_pow]
  have : (n : ℝ) ^ α₂.re ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
  field_simp

/-- **DLMF §2.9(i)**: if `|ρ₂| > |ρ₁|`, or `|ρ₂| = |ρ₁|` and `ℜα₂ > ℜα₁`, then `w₁` is recessive
and `w₂` dominant: `w₁(n)/w₂(n) → 0`. -/
theorem dlmf_2_9_8_recessive (h₁ : HasLeading w₁ ρ₁ α₁) (h₂ : HasLeading w₂ ρ₂ α₂)
    (h : ‖ρ₁‖ < ‖ρ₂‖ ∨ (‖ρ₁‖ = ‖ρ₂‖ ∧ α₁.re < α₂.re)) :
    Tendsto (fun n => w₁ n / w₂ n) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hρ₂ : 0 < ‖ρ₂‖ := norm_pos_iff.mpr h₂.ne_zero
  have hr : Tendsto (fun n : ℕ => (‖ρ₁‖ / ‖ρ₂‖) ^ n * (n : ℝ) ^ (α₁.re - α₂.re)) atTop
      (𝓝 0) := by
    rcases h with h | ⟨h, hre⟩
    · have hr0 : 0 ≤ ‖ρ₁‖ / ‖ρ₂‖ := by positivity
      have hr1 : ‖ρ₁‖ / ‖ρ₂‖ < 1 := (div_lt_one hρ₂).mpr h
      obtain ⟨k, hk⟩ := exists_nat_ge (α₁.re - α₂.re)
      refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
        (tendsto_pow_const_mul_const_pow_of_lt_one k hr0 hr1)
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hle : (n : ℝ) ^ (α₁.re - α₂.re) ≤ (n : ℝ) ^ k := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hk
      calc (‖ρ₁‖ / ‖ρ₂‖) ^ n * (n : ℝ) ^ (α₁.re - α₂.re)
          ≤ (‖ρ₁‖ / ‖ρ₂‖) ^ n * (n : ℝ) ^ k := mul_le_mul_of_nonneg_left hle (by positivity)
        _ = (n : ℝ) ^ k * (‖ρ₁‖ / ‖ρ₂‖) ^ n := mul_comm _ _
    · rw [h, div_self hρ₂.ne']
      simp only [one_pow, one_mul]
      have := (tendsto_rpow_neg_atTop (by linarith : 0 < α₂.re - α₁.re)).comp
        tendsto_natCast_atTop_atTop
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, neg_sub]
  have hu : Tendsto (fun n => ‖leadRatio w₁ ρ₁ α₁ n‖ / ‖leadRatio w₂ ρ₂ α₂ n‖) atTop
      (𝓝 (‖(1 : ℂ)‖ / ‖(1 : ℂ)‖)) := h₁.norm.div h₂.norm (by simp)
  have hlim := hu.mul hr
  rw [mul_zero] at hlim
  exact hlim.congr' (norm_div_eq h₁ h₂)

/-- **DLMF §2.9(i)**: if `|ρ₂| = |ρ₁|` and `ℜα₂ = ℜα₁`, neither solution is dominant:
`|w₁(n)/w₂(n)| → 1`. -/
theorem dlmf_2_9_8_neither (h₁ : HasLeading w₁ ρ₁ α₁) (h₂ : HasLeading w₂ ρ₂ α₂)
    (hρ : ‖ρ₁‖ = ‖ρ₂‖) (hα : α₁.re = α₂.re) :
    Tendsto (fun n => ‖w₁ n / w₂ n‖) atTop (𝓝 1) := by
  have hρ₂ : 0 < ‖ρ₂‖ := norm_pos_iff.mpr h₂.ne_zero
  have hu : Tendsto (fun n => ‖leadRatio w₁ ρ₁ α₁ n‖ / ‖leadRatio w₂ ρ₂ α₂ n‖) atTop
      (𝓝 (‖(1 : ℂ)‖ / ‖(1 : ℂ)‖)) := h₁.norm.div h₂.norm (by simp)
  simp only [norm_one, div_one] at hu
  refine (hu.congr' ?_).congr' (norm_div_eq h₁ h₂)
  filter_upwards with n
  rw [hρ, hα, div_self hρ₂.ne', one_pow, sub_self, Real.rpow_zero, mul_one, mul_one]

/-! ### Recessive solutions are unique, dominant solutions are not -/

/-- The Casoratian `w₁(n) w₂(n+1) − w₁(n+1) w₂(n)`. -/
def casoratian (w₁ w₂ : ℕ → ℂ) (n : ℕ) : ℂ := w₁ n * w₂ (n + 1) - w₁ (n + 1) * w₂ n

/-- Two solutions of 2.9.1 with nonzero Casoratian at `n₀` span all solutions on `n ≥ n₀`. -/
theorem IsDiffSolution.eq_comb {f g : ℕ → ℂ} (h₁ : IsDiffSolution f g w₁)
    (h₂ : IsDiffSolution f g w₂) (hv : IsDiffSolution f g v) {n₀ : ℕ}
    (hC : casoratian w₁ w₂ n₀ ≠ 0) :
    ∃ c₁ c₂ : ℂ, ∀ n, n₀ ≤ n → v n = c₁ * w₁ n + c₂ * w₂ n := by
  refine ⟨(v n₀ * w₂ (n₀ + 1) - v (n₀ + 1) * w₂ n₀) / casoratian w₁ w₂ n₀,
    (w₁ n₀ * v (n₀ + 1) - w₁ (n₀ + 1) * v n₀) / casoratian w₁ w₂ n₀, fun n hn => ?_⟩
  set c₁ := (v n₀ * w₂ (n₀ + 1) - v (n₀ + 1) * w₂ n₀) / casoratian w₁ w₂ n₀ with hc₁
  set c₂ := (w₁ n₀ * v (n₀ + 1) - w₁ (n₀ + 1) * v n₀) / casoratian w₁ w₂ n₀ with hc₂
  have key : ∀ n, n₀ ≤ n → v n = c₁ * w₁ n + c₂ * w₂ n ∧
      v (n + 1) = c₁ * w₁ (n + 1) + c₂ * w₂ (n + 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      rw [hc₁, hc₂]
      constructor
      · field_simp
        simp only [casoratian]
        ring
      · field_simp
        simp only [casoratian]
        ring
    | succ n hn ih =>
      refine ⟨ih.2, ?_⟩
      linear_combination hv n - c₁ * h₁ n - c₂ * h₂ n - f n * ih.2 - g n * ih.1
  exact (key n hn).1

/-- Solutions with distinct leading behaviours have a nonvanishing Casoratian somewhere. -/
theorem exists_casoratian_ne_zero (h₁ : HasLeading w₁ ρ₁ α₁) (h₂ : HasLeading w₂ ρ₂ α₂)
    (hne : ρ₁ ≠ ρ₂) : ∃ n₀, casoratian w₁ w₂ n₀ ≠ 0 := by
  by_contra hC
  push Not at hC
  obtain ⟨N, hN⟩ := eventually_atTop.mp h₂.eventually_ne
  have hR : ∀ n, N ≤ n → w₁ n / w₂ n = w₁ N / w₂ N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rw [← ih]
      have h0 := hC n
      have hw := hN n hn
      have hw1 := hN (n + 1) (by omega)
      simp only [casoratian] at h0
      field_simp
      linear_combination -h0
  have := dlmf_2_9_8_independent h₁ h₂ hne (c₁ := 1) (c₂ := -(w₁ N / w₂ N)) <| by
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [← hR n hn]
    field_simp [hN n hn]
    ring
  exact one_ne_zero this.1

/-- **DLMF §2.9(i)**: "recessive solutions are unique": if `w₁`, `w₂` solve 2.9.1 with distinct
leading behaviours and `w₁/w₂ → 0`, every solution `v` with `v/w₂ → 0` is eventually a constant
multiple of `w₁`. -/
theorem dlmf_2_9_8_recessive_unique {f g : ℕ → ℂ} (hs₁ : IsDiffSolution f g w₁)
    (hs₂ : IsDiffSolution f g w₂) (hsv : IsDiffSolution f g v) (h₁ : HasLeading w₁ ρ₁ α₁)
    (h₂ : HasLeading w₂ ρ₂ α₂) (hne : ρ₁ ≠ ρ₂) (hrec : Tendsto (fun n => w₁ n / w₂ n) atTop (𝓝 0))
    (hv : Tendsto (fun n => v n / w₂ n) atTop (𝓝 0)) :
    ∃ c : ℂ, ∀ᶠ n in atTop, v n = c * w₁ n := by
  obtain ⟨n₀, hC⟩ := exists_casoratian_ne_zero h₁ h₂ hne
  obtain ⟨c₁, c₂, hc⟩ := hs₁.eq_comb hs₂ hsv hC
  have hlim : Tendsto (fun n => v n / w₂ n) atTop (𝓝 (c₁ * 0 + c₂)) := by
    refine ((hrec.const_mul c₁).add_const c₂).congr' ?_
    filter_upwards [eventually_ge_atTop n₀, h₂.eventually_ne] with n hn hw
    rw [hc n hn]
    field_simp
  rw [mul_zero, zero_add] at hlim
  have hc₂ : c₂ = 0 := tendsto_nhds_unique hlim hv
  refine ⟨c₁, ?_⟩
  filter_upwards [eventually_ge_atTop n₀] with n hn
  rw [hc n hn, hc₂, zero_mul, add_zero]

/-- **DLMF §2.9(i)**: "dominant solutions are not [unique]": for every `c`, `w₂ + c w₁` is again a
solution, relative to which `w₁` is still recessive. -/
theorem dlmf_2_9_8_dominant_not_unique {f g : ℕ → ℂ} (hs₁ : IsDiffSolution f g w₁)
    (hs₂ : IsDiffSolution f g w₂) (hw₂ : ∀ᶠ n in atTop, w₂ n ≠ 0)
    (hrec : Tendsto (fun n => w₁ n / w₂ n) atTop (𝓝 0)) (c : ℂ) :
    IsDiffSolution f g (fun n => w₂ n + c * w₁ n) ∧
      Tendsto (fun n => w₁ n / (w₂ n + c * w₁ n)) atTop (𝓝 0) := by
  refine ⟨fun n => by linear_combination hs₂ n + c * hs₁ n, ?_⟩
  have hden : Tendsto (fun n => 1 + c * (w₁ n / w₂ n)) atTop (𝓝 (1 + c * 0)) :=
    (hrec.const_mul c).const_add 1
  rw [mul_zero, add_zero] at hden
  have hlim := hrec.div hden one_ne_zero
  rw [zero_div] at hlim
  refine hlim.congr' ?_
  filter_upwards [hw₂, hden.eventually_ne one_ne_zero] with n hw h1
  have hsum : w₂ n + c * w₁ n ≠ 0 := by
    intro h0
    apply h1
    field_simp
    linear_combination h0
  simp only [Pi.div_apply]
  field_simp

end Azurite.DLMF
