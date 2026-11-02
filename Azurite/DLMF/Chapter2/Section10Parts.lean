/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section10Example

/-!
# DLMF §2.10(ii): Summation by Parts, 2.10.9–2.10.18

* 2.10.9–2.10.10 (`dlmf_2_10_9`, `partialSumU`): `∑_{j=1}^{n−1} uⱼvⱼ = U_{n−1}vₙ +
  ∑_{j=1}^{n−1} Uⱼ(vⱼ − v_{j+1})`, `Uⱼ = u₁ + ⋯ + uⱼ`.
* Example: 2.10.11 (`sumOsc`) `S(α, β, n) = ∑_{j=1}^{n−1} e^{ijβ} j^α`, `e^{iβ} ≠ 1`.
* 2.10.12 (`dlmf_2_10_12`): `|S| ≤ ∑_{j=1}^{n−1} j^α`, which is bounded (`α < −1`), at most
  `1 + ln n` (`α = −1`), or at most `(1 + 1/(α+1)) n^{α+1}` (`α > −1`).
* 2.10.13 (`dlmf_2_10_13`): `Uⱼ = e^{iβ}(e^{ijβ} − 1)/(e^{iβ} − 1)`.
* 2.10.14 (`dlmf_2_10_14`).
* 2.10.15 (`dlmf_2_10_15`): `|j^α − (j+1)^α + αj^{α−1}| ≤ |α(α−1)| C j^{α−2}` for all `j ≥ 1`.
* 2.10.16–2.10.18 (`dlmf_2_10_16`, `dlmf_2_10_17`, `dlmf_2_10_18`), each `O(⋯)` as an explicit bound
  `K(⋯)` valid for all `n ≥ 1`; 2.10.18: `S = e^{inβ}/(e^{iβ} − 1) n^α + O(n^{α−1}) + O(1)`.
-/

open Filter Topology Set Finset Complex
open scoped Real

namespace Azurite.DLMF

/-! ### 2.10.9–2.10.10 -/

/-- **DLMF 2.10.10**: `Uⱼ = u₁ + u₂ + ⋯ + uⱼ`. -/
def partialSumU (u : ℕ → ℂ) (j : ℕ) : ℂ := ∑ k ∈ Finset.Icc 1 j, u k

theorem partialSumU_succ (u : ℕ → ℂ) (j : ℕ) :
    partialSumU u (j + 1) = partialSumU u j + u (j + 1) := by
  simp only [partialSumU]
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- **DLMF 2.10.9** (summation by parts). -/
theorem dlmf_2_10_9 (u v : ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 (n - 1), u j * v j = partialSumU u (n - 1) * v n +
      ∑ j ∈ Finset.Icc 1 (n - 1), partialSumU u j * (v j - v (j + 1)) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  clear hn
  induction N with
  | zero => simp [partialSumU]
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Icc_succ_top (by omega),
      partialSumU_succ]
    ring

theorem sum_Icc_telescope (v : ℕ → ℂ) (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, (v j - v (j + 1)) = v 1 - v (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

/-! ### Power sums (2.10.12) -/

/-- `∑_{j=1}^{n−1} j^γ` is bounded when `γ < −1`. -/
theorem sum_rpow_bdd {γ : ℝ} (hγ : γ < -1) :
    ∃ K, ∀ n : ℕ, ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) ^ γ ≤ K :=
  ⟨∑' j : ℕ, (j : ℝ) ^ γ, fun _ => (Real.summable_nat_rpow.mpr hγ).sum_le_tsum _
    (fun j _ => Real.rpow_nonneg (Nat.cast_nonneg j) γ)⟩

/-- `∑_{j=1}^{n−1} j^{−1} ≤ 1 + ln n`. -/
theorem sum_rpow_neg_one {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) ^ (-1 : ℝ) ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log (n - 1)
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have e : ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) ^ (-1 : ℝ) =
      ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ)⁻¹ :=
    sum_congr rfl fun j _ => Real.rpow_neg_one _
  rw [e]
  refine h.trans ?_
  have hlog : Real.log ((n - 1 : ℕ) : ℝ) ≤ Real.log n := by
    rcases Nat.eq_zero_or_pos (n - 1) with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by exact_mod_cast hn)
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast Nat.sub_le n 1)
  linarith

theorem rpow_le_diff {γ : ℝ} (h1 : -1 < γ) (h0 : γ < 0) {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) ^ γ ≤ ((j : ℝ) ^ (γ + 1) - ((j : ℝ) - 1) ^ (γ + 1)) / (γ + 1) := by
  have hj0 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hγ1 : 0 < γ + 1 := by linarith
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun x : ℝ => x ^ (γ + 1))
    (fun x => (γ + 1) * x ^ (γ + 1 - 1)) (show (j : ℝ) - 1 < j by linarith)
    (fun x _ => (Real.continuousAt_rpow_const x (γ + 1) (Or.inr hγ1.le)).continuousWithinAt)
    (fun x hx => Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1])))
  simp only [show γ + 1 - 1 = γ by ring, sub_sub_cancel, div_one] at hcd
  have hc0 : 0 < c := by linarith [hc.1]
  have hle : (j : ℝ) ^ γ ≤ c ^ γ := Real.rpow_le_rpow_of_nonpos hc0 hc.2.le h0.le
  rw [← hcd, le_div_iff₀ hγ1]
  nlinarith

/-- `∑_{j=1}^{n−1} j^γ ≤ (1 + 1/(γ+1)) n^{γ+1}` when `γ > −1`. -/
theorem sum_rpow_le_of_gt {γ : ℝ} (hγ : -1 < γ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) ^ γ ≤ (1 + 1 / (γ + 1)) * (n : ℝ) ^ (γ + 1) := by
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hγ1 : 0 < γ + 1 := by linarith
  have hpow : 0 ≤ (n : ℝ) ^ (γ + 1) := Real.rpow_nonneg (by linarith) _
  rcases le_or_gt 0 γ with h | h
  · have hb : ∀ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) ^ γ ≤ (n : ℝ) ^ γ := fun j hj =>
      Real.rpow_le_rpow (Nat.cast_nonneg j) (by
        have := (Finset.mem_Icc.mp hj).2; exact_mod_cast (by omega : j ≤ n)) h
    calc ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) ^ γ ≤ ∑ _j ∈ Finset.Icc 1 (n - 1), (n : ℝ) ^ γ :=
          sum_le_sum hb
      _ = ((n - 1 : ℕ) : ℝ) * (n : ℝ) ^ γ := by simp
      _ ≤ (n : ℝ) * (n : ℝ) ^ γ := by
          gcongr
          exact_mod_cast Nat.sub_le n 1
      _ = (n : ℝ) ^ (γ + 1) := by rw [Real.rpow_add_one (by linarith), mul_comm]
      _ ≤ (1 + 1 / (γ + 1)) * (n : ℝ) ^ (γ + 1) := by
          have : 0 ≤ 1 / (γ + 1) := by positivity
          nlinarith
  · have htel : ∀ N : ℕ, ∑ j ∈ Finset.Icc 1 N, ((j : ℝ) ^ (γ + 1) - ((j : ℝ) - 1) ^ (γ + 1)) =
        (N : ℝ) ^ (γ + 1) := by
      intro N
      induction N with
      | zero => simp [Real.zero_rpow hγ1.ne']
      | succ N ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih]
        push_cast
        ring_nf
    calc ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) ^ γ
        ≤ ∑ j ∈ Finset.Icc 1 (n - 1), ((j : ℝ) ^ (γ + 1) - ((j : ℝ) - 1) ^ (γ + 1)) / (γ + 1) :=
          sum_le_sum fun j hj => rpow_le_diff hγ h (Finset.mem_Icc.mp hj).1
      _ = ((n - 1 : ℕ) : ℝ) ^ (γ + 1) / (γ + 1) := by rw [← sum_div, htel]
      _ ≤ (n : ℝ) ^ (γ + 1) / (γ + 1) := by
          gcongr
          exact_mod_cast Nat.sub_le n 1
      _ ≤ (1 + 1 / (γ + 1)) * (n : ℝ) ^ (γ + 1) := by
          rw [div_eq_mul_one_div, mul_comm]
          nlinarith

/-- For `γ ≠ −1`: `∑_{j=1}^{n−1} j^γ ≤ K(n^{γ+1} + 1)`. -/
theorem sum_rpow_le {γ : ℝ} (hγ : γ ≠ -1) :
    ∃ K, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
      ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) ^ γ ≤ K * ((n : ℝ) ^ (γ + 1) + 1) := by
  rcases lt_or_gt_of_ne hγ with h | h
  · obtain ⟨K, hK⟩ := sum_rpow_bdd h
    refine ⟨max K 0, le_max_right _ _, fun n hn => ?_⟩
    have hp : 0 ≤ (n : ℝ) ^ (γ + 1) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    calc _ ≤ K := hK n
      _ ≤ max K 0 := le_max_left _ _
      _ ≤ max K 0 * ((n : ℝ) ^ (γ + 1) + 1) := by
          have := le_max_right K 0
          nlinarith
  · have hγ1 : 0 < γ + 1 := by linarith
    refine ⟨1 + 1 / (γ + 1), by positivity, fun n hn => ?_⟩
    have := sum_rpow_le_of_gt h hn
    have hK : 0 ≤ 1 + 1 / (γ + 1) := by positivity
    nlinarith

/-! ### The example 2.10.11–2.10.18 -/

/-- **DLMF 2.10.11**: `S(α, β, n) = ∑_{j=1}^{n−1} e^{ijβ} j^α`. -/
noncomputable def sumOsc (α β : ℝ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 (n - 1), cexp (I * j * β) * (((j : ℝ) ^ α : ℝ) : ℂ)

theorem norm_cexp_I_nat_mul (j : ℕ) (β : ℝ) : ‖cexp (I * j * β)‖ = 1 := by
  rw [show I * (j : ℂ) * β = ((j * β : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I]

theorem cexp_I_mul_eq_pow (j : ℕ) (β : ℝ) : cexp (I * j * β) = cexp (I * β) ^ j := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem norm_sumOsc_le (α β : ℝ) (n : ℕ) :
    ‖sumOsc α β n‖ ≤ ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) ^ α := by
  refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun j _ => ?_))
  rw [norm_mul, norm_cexp_I_nat_mul, one_mul, norm_real, Real.norm_of_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg j) α)]

/-- **DLMF 2.10.12**: `|S(α, β, n)| ≤ ∑_{j=1}^{n−1} j^α`, which is `O(1)`, `O(ln n)`, or
`O(n^{α+1})` according as `α < −1`, `α = −1`, or `α > −1`. -/
theorem dlmf_2_10_12 (α β : ℝ) :
    (∀ n, ‖sumOsc α β n‖ ≤ ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) ^ α) ∧
    (α < -1 → ∃ K, ∀ n : ℕ, ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) ^ α ≤ K) ∧
    (α = -1 → ∀ n : ℕ, 1 ≤ n → ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) ^ α ≤ 1 + Real.log n) ∧
    (-1 < α → ∀ n : ℕ, 1 ≤ n →
      ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) ^ α ≤ (1 + 1 / (α + 1)) * (n : ℝ) ^ (α + 1)) :=
  ⟨norm_sumOsc_le α β, sum_rpow_bdd, fun h _ hn => h ▸ sum_rpow_neg_one hn,
    fun h _ hn => sum_rpow_le_of_gt h hn⟩

/-- **DLMF 2.10.13**: with `uⱼ = e^{ijβ}`, `Uⱼ = e^{iβ}(e^{ijβ} − 1)/(e^{iβ} − 1)`. -/
theorem dlmf_2_10_13 {β : ℝ} (hβ : cexp (I * β) ≠ 1) (j : ℕ) :
    partialSumU (fun k => cexp (I * k * β)) j =
      cexp (I * β) * (cexp (I * j * β) - 1) / (cexp (I * β) - 1) := by
  have hz : cexp (I * β) - 1 ≠ 0 := sub_ne_zero.mpr hβ
  induction j with
  | zero => simp [partialSumU]
  | succ j ih =>
    rw [partialSumU_succ, ih]
    simp only [cexp_I_mul_eq_pow]
    field_simp
    ring

/-- **DLMF 2.10.14**. -/
theorem dlmf_2_10_14 (α : ℝ) {β : ℝ} (hβ : cexp (I * β) ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    sumOsc α β n = cexp (I * β) / (cexp (I * β) - 1) *
      (cexp (I * (n - 1 : ℕ) * β) * (((n : ℝ) ^ α : ℝ) : ℂ) - 1 +
        ∑ j ∈ Finset.Icc 1 (n - 1), cexp (I * j * β) *
          ((((j : ℝ) ^ α - ((j : ℝ) + 1) ^ α : ℝ)) : ℂ)) := by
  have hz : cexp (I * β) - 1 ≠ 0 := sub_ne_zero.mpr hβ
  set v : ℕ → ℂ := fun j => (((j : ℝ) ^ α : ℝ) : ℂ) with hv
  have h := dlmf_2_10_9 (fun k => cexp (I * k * β)) v hn
  simp only [dlmf_2_10_13 hβ] at h
  rw [sumOsc]
  rw [show (∑ j ∈ Finset.Icc 1 (n - 1), cexp (I * j * β) * (((j : ℝ) ^ α : ℝ) : ℂ)) =
    ∑ j ∈ Finset.Icc 1 (n - 1), cexp (I * j * β) * v j from rfl, h]
  have htel := sum_Icc_telescope v (n - 1)
  rw [Nat.sub_add_cancel hn] at htel
  have hv1 : v 1 = 1 := by simp [hv]
  have hsum : ∑ j ∈ Finset.Icc 1 (n - 1), cexp (I * β) * (cexp (I * j * β) - 1) /
      (cexp (I * β) - 1) * (v j - v (j + 1)) =
      cexp (I * β) / (cexp (I * β) - 1) * (∑ j ∈ Finset.Icc 1 (n - 1), cexp (I * j * β) *
        (v j - v (j + 1)) - ∑ j ∈ Finset.Icc 1 (n - 1), (v j - v (j + 1))) := by
    rw [mul_sub, mul_sum, mul_sum]
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    field_simp
  rw [hsum, htel, hv1]
  have hvn : ∀ j : ℕ, v j - v (j + 1) = ((((j : ℝ) ^ α - ((j : ℝ) + 1) ^ α : ℝ)) : ℂ) := by
    intro j
    simp only [hv]
    push_cast
    ring_nf
  simp only [hvn]
  field_simp
  ring

/-- **DLMF 2.10.15**: `j^α − (j+1)^α = −αj^{α−1} + α(α−1) O(j^{α−2})` uniformly in `j ≥ 1`. -/
theorem dlmf_2_10_15 (α : ℝ) : ∃ C, 0 ≤ C ∧ ∀ j : ℕ, 1 ≤ j →
    |(j : ℝ) ^ α - ((j : ℝ) + 1) ^ α + α * (j : ℝ) ^ (α - 1)| ≤
      |α * (α - 1)| * C * (j : ℝ) ^ (α - 2) := by
  refine ⟨max 1 ((2 : ℝ) ^ (α - 2)), by positivity, fun j hj => ?_⟩
  set C := max 1 ((2 : ℝ) ^ (α - 2))
  have hj0 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjp : (0 : ℝ) < j := by linarith
  -- `ξ^{α−2} ≤ C j^{α−2}` on `[j, j+1]`
  have hξ : ∀ ξ ∈ Icc (j : ℝ) (j + 1), ξ ^ (α - 2) ≤ C * (j : ℝ) ^ (α - 2) := by
    intro ξ hξ
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    rcases le_or_gt (α - 2) 0 with h | h
    · calc ξ ^ (α - 2) ≤ (j : ℝ) ^ (α - 2) := Real.rpow_le_rpow_of_nonpos hjp hξ.1 h
        _ ≤ C * (j : ℝ) ^ (α - 2) := by
          have := le_max_left 1 ((2 : ℝ) ^ (α - 2))
          have : 0 ≤ (j : ℝ) ^ (α - 2) := Real.rpow_nonneg hjp.le _
          nlinarith
    · calc ξ ^ (α - 2) ≤ (2 * (j : ℝ)) ^ (α - 2) :=
            Real.rpow_le_rpow hξ0.le (by linarith [hξ.2]) h.le
        _ = (2 : ℝ) ^ (α - 2) * (j : ℝ) ^ (α - 2) := Real.mul_rpow (by norm_num) hjp.le
        _ ≤ C * (j : ℝ) ^ (α - 2) := by
          have := le_max_right 1 ((2 : ℝ) ^ (α - 2))
          have : 0 ≤ (j : ℝ) ^ (α - 2) := Real.rpow_nonneg hjp.le _
          nlinarith
  set A := |α * (α - 1)| * C * (j : ℝ) ^ (α - 2) with hA
  -- first mean value step: `|α x^{α−1} − α j^{α−1}| ≤ A (x − j)`
  have h1 : ∀ x ∈ Icc (j : ℝ) (j + 1), ‖α * x ^ (α - 1) - α * (j : ℝ) ^ (α - 1)‖ ≤
      A * (x - j) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment' (f := fun x => α * x ^ (α - 1))
      (f' := fun x => α * ((α - 1) * x ^ (α - 1 - 1))) (fun x hx => ?_) (fun x hx => ?_)
    · exact ((Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1]))).const_mul
        α).hasDerivWithinAt
    · rw [show α - 1 - 1 = α - 2 by ring, Real.norm_eq_abs, ← mul_assoc, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1]) _), hA, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hξ x (Ico_subset_Icc_self hx)) (abs_nonneg _)
  -- second mean value step
  have h2 := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun x => x ^ α - (j : ℝ) ^ α - α * (j : ℝ) ^ (α - 1) * (x - j))
    (f' := fun x => α * x ^ (α - 1) - α * (j : ℝ) ^ (α - 1)) (C := A) (a := (j : ℝ))
    (b := j + 1) (fun x hx => ?_) (fun x hx => ?_) (j + 1) ⟨by linarith, le_rfl⟩
  · simp only [sub_self, mul_zero, sub_zero, Real.norm_eq_abs] at h2
    rw [show (j : ℝ) + 1 - j = 1 by ring, mul_one] at h2
    rw [show (j : ℝ) ^ α - ((j : ℝ) + 1) ^ α + α * (j : ℝ) ^ (α - 1) =
      -(((j : ℝ) + 1) ^ α - (j : ℝ) ^ α - α * (j : ℝ) ^ (α - 1)) by ring, abs_neg]
    exact h2.trans_eq (mul_one A)
  · have hd := (((Real.hasDerivAt_rpow_const
      (Or.inl (by linarith [hx.1]) : x ≠ 0 ∨ 1 ≤ α)).sub_const
      ((j : ℝ) ^ α)).sub (((hasDerivAt_id x).sub_const (j : ℝ)).const_mul
        (α * (j : ℝ) ^ (α - 1)))).hasDerivWithinAt (s := Icc (j : ℝ) (j + 1))
    convert hd using 1
    · rfl
    · ring
  · have := h1 x (Ico_subset_Icc_self hx)
    have hxj : x - j ≤ 1 := by linarith [hx.2]
    have hA0 : 0 ≤ A := by rw [hA]; positivity
    calc ‖α * x ^ (α - 1) - α * (j : ℝ) ^ (α - 1)‖ ≤ A * (x - j) := this
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left hxj hA0
      _ = A := mul_one A

section Asymptotics

variable {α β : ℝ}

/-- The bracket remainder of 2.10.16: `−1 + ∑ e^{ijβ}(j^α − (j+1)^α + αj^{α−1})`. -/
noncomputable def sumOscRem (α β : ℝ) (n : ℕ) : ℂ :=
  -1 + ∑ j ∈ Finset.Icc 1 (n - 1), cexp (I * j * β) *
    ((((j : ℝ) ^ α - ((j : ℝ) + 1) ^ α + α * (j : ℝ) ^ (α - 1) : ℝ)) : ℂ)

theorem sumOsc_decomp (hβ : cexp (I * β) ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    sumOsc α β n = cexp (I * β) / (cexp (I * β) - 1) *
      (cexp (I * (n - 1 : ℕ) * β) * (((n : ℝ) ^ α : ℝ) : ℂ) - α * sumOsc (α - 1) β n +
        sumOscRem α β n) := by
  rw [sumOscRem, dlmf_2_10_14 α hβ hn, sumOsc]
  congr 1
  have e : ∑ j ∈ Finset.Icc 1 (n - 1), cexp (I * j * β) *
      ((((j : ℝ) ^ α - ((j : ℝ) + 1) ^ α + α * (j : ℝ) ^ (α - 1) : ℝ)) : ℂ) =
      ∑ j ∈ Finset.Icc 1 (n - 1), cexp (I * j * β) *
        ((((j : ℝ) ^ α - ((j : ℝ) + 1) ^ α : ℝ)) : ℂ) +
      α * ∑ j ∈ Finset.Icc 1 (n - 1), cexp (I * j * β) * (((j : ℝ) ^ (α - 1) : ℝ) : ℂ) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [e]
  ring

/-- **DLMF 2.10.16**: `S(α, β, n) = e^{iβ}/(e^{iβ} − 1) (e^{i(n−1)β} n^α − α S(α − 1, β, n)
+ O(n^{α−1}) + O(1))`, the `O`-terms as one remainder `e` with `|e| ≤ K(n^{α−1} + 1)`. -/
theorem dlmf_2_10_16 (hβ : cexp (I * β) ≠ 1) :
    ∃ K, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n → ∃ e : ℂ, ‖e‖ ≤ K * ((n : ℝ) ^ (α - 1) + 1) ∧
      sumOsc α β n = cexp (I * β) / (cexp (I * β) - 1) *
        (cexp (I * (n - 1 : ℕ) * β) * (((n : ℝ) ^ α : ℝ) : ℂ) - α * sumOsc (α - 1) β n + e) := by
  obtain ⟨C, hC0, hC⟩ := dlmf_2_10_15 α
  obtain ⟨K₁, hK₁0, hK₁⟩ : ∃ K₁, 0 ≤ K₁ ∧ ∀ n : ℕ, 1 ≤ n →
      |α * (α - 1)| * C * ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) ^ (α - 2) ≤
        K₁ * ((n : ℝ) ^ (α - 1) + 1) := by
    by_cases h1 : α = 1
    · refine ⟨0, le_rfl, fun n _ => ?_⟩
      simp [h1]
    · obtain ⟨K, hK0, hK⟩ := sum_rpow_le (γ := α - 2) (by intro h; apply h1; linarith)
      refine ⟨|α * (α - 1)| * C * K, by positivity, fun n hn => ?_⟩
      have := hK n hn
      rw [show α - 2 + 1 = α - 1 by ring] at this
      calc _ ≤ |α * (α - 1)| * C * (K * ((n : ℝ) ^ (α - 1) + 1)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
  refine ⟨1 + K₁, by positivity, fun n hn => ⟨sumOscRem α β n, ?_, sumOsc_decomp hβ hn⟩⟩
  have hr : ‖∑ j ∈ Finset.Icc 1 (n - 1), cexp (I * j * β) *
      ((((j : ℝ) ^ α - ((j : ℝ) + 1) ^ α + α * (j : ℝ) ^ (α - 1) : ℝ)) : ℂ)‖ ≤
      |α * (α - 1)| * C * ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) ^ (α - 2) := by
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun j hj => ?_
    rw [norm_mul, norm_cexp_I_nat_mul, one_mul, norm_real, Real.norm_eq_abs]
    exact hC j (Finset.mem_Icc.mp hj).1
  have hpow : 0 ≤ (n : ℝ) ^ (α - 1) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have h2 := hK₁ n hn
  calc ‖sumOscRem α β n‖ ≤ ‖(-1 : ℂ)‖ + ‖∑ j ∈ Finset.Icc 1 (n - 1), cexp (I * j * β) *
        ((((j : ℝ) ^ α - ((j : ℝ) + 1) ^ α + α * (j : ℝ) ^ (α - 1) : ℝ)) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ 1 + K₁ * ((n : ℝ) ^ (α - 1) + 1) := by
        rw [norm_neg, norm_one]
        linarith
    _ ≤ (1 + K₁) * ((n : ℝ) ^ (α - 1) + 1) := by nlinarith

/-- **DLMF 2.10.17**: `S(α, β, n) = O(n^α) + O(1)`. -/
theorem dlmf_2_10_17 (hβ : cexp (I * β) ≠ 1) :
    ∃ K, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n → ‖sumOsc α β n‖ ≤ K * ((n : ℝ) ^ α + 1) := by
  obtain ⟨K₁, hK₁0, h16⟩ := dlmf_2_10_16 (α := α) hβ
  obtain ⟨K₂, hK₂0, hK₂⟩ : ∃ K₂, 0 ≤ K₂ ∧ ∀ n : ℕ, 1 ≤ n →
      |α| * ‖sumOsc (α - 1) β n‖ ≤ K₂ * ((n : ℝ) ^ α + 1) := by
    by_cases h0 : α = 0
    · exact ⟨0, le_rfl, fun n _ => by simp [h0]⟩
    · obtain ⟨K, hK0, hK⟩ := sum_rpow_le (γ := α - 1) (by intro h; apply h0; linarith)
      refine ⟨|α| * K, by positivity, fun n hn => ?_⟩
      have h1 := (norm_sumOsc_le (α - 1) β n).trans (hK n hn)
      rw [show α - 1 + 1 = α by ring] at h1
      calc |α| * ‖sumOsc (α - 1) β n‖ ≤ |α| * (K * ((n : ℝ) ^ α + 1)) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = _ := by ring
  refine ⟨‖cexp (I * β) / (cexp (I * β) - 1)‖ * (1 + K₂ + K₁), by positivity, fun n hn => ?_⟩
  obtain ⟨e, he, hS⟩ := h16 n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpa : (n : ℝ) ^ (α - 1) ≤ (n : ℝ) ^ α := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hpa0 : 0 ≤ (n : ℝ) ^ (α - 1) := Real.rpow_nonneg (by linarith) _
  have hpn : 0 ≤ (n : ℝ) ^ α := Real.rpow_nonneg (by linarith) _
  have hb : ‖cexp (I * (n - 1 : ℕ) * β) * (((n : ℝ) ^ α : ℝ) : ℂ) - α * sumOsc (α - 1) β n + e‖ ≤
      (n : ℝ) ^ α + |α| * ‖sumOsc (α - 1) β n‖ + K₁ * ((n : ℝ) ^ (α - 1) + 1) := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (le_of_eq ?_)) he)
    rw [norm_mul, norm_cexp_I_nat_mul, one_mul, norm_real, Real.norm_of_nonneg hpn, norm_mul,
      norm_real, Real.norm_eq_abs]
  rw [hS, norm_mul]
  refine (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have := hK₂ n hn
  nlinarith

/-- **DLMF 2.10.18**: `S(α, β, n) = e^{inβ}/(e^{iβ} − 1) n^α + O(n^{α−1}) + O(1)`. -/
theorem dlmf_2_10_18 (hβ : cexp (I * β) ≠ 1) :
    ∃ K, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
      ‖sumOsc α β n - cexp (I * n * β) / (cexp (I * β) - 1) * (((n : ℝ) ^ α : ℝ) : ℂ)‖ ≤
        K * ((n : ℝ) ^ (α - 1) + 1) := by
  obtain ⟨K₁, hK₁0, h16⟩ := dlmf_2_10_16 (α := α) hβ
  obtain ⟨K₃, hK₃0, h17⟩ := dlmf_2_10_17 (α := α - 1) hβ
  have hz : cexp (I * β) - 1 ≠ 0 := sub_ne_zero.mpr hβ
  refine ⟨‖cexp (I * β) / (cexp (I * β) - 1)‖ * (|α| * K₃ + K₁), by positivity,
    fun n hn => ?_⟩
  obtain ⟨e, he, hS⟩ := h16 n hn
  have hzn : cexp (I * β) * cexp (I * (n - 1 : ℕ) * β) = cexp (I * n * β) := by
    rw [cexp_I_mul_eq_pow, cexp_I_mul_eq_pow, ← pow_succ', Nat.sub_add_cancel hn]
  have hA : cexp (I * β) / (cexp (I * β) - 1) * (cexp (I * (n - 1 : ℕ) * β) *
      (((n : ℝ) ^ α : ℝ) : ℂ)) = cexp (I * n * β) / (cexp (I * β) - 1) *
        (((n : ℝ) ^ α : ℝ) : ℂ) := by
    rw [← hzn]
    field_simp
  rw [hS, show cexp (I * β) / (cexp (I * β) - 1) * (cexp (I * (n - 1 : ℕ) * β) *
      (((n : ℝ) ^ α : ℝ) : ℂ) - α * sumOsc (α - 1) β n + e) -
      cexp (I * n * β) / (cexp (I * β) - 1) * (((n : ℝ) ^ α : ℝ) : ℂ) =
      cexp (I * β) / (cexp (I * β) - 1) * (-(α * sumOsc (α - 1) β n) + e) by
    rw [← hA]; ring, norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 := h17 n hn
  have hpa0 : 0 ≤ (n : ℝ) ^ (α - 1) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc ‖-(α * sumOsc (α - 1) β n) + e‖ ≤ |α| * ‖sumOsc (α - 1) β n‖ + ‖e‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_neg, norm_mul, norm_real, Real.norm_eq_abs]
    _ ≤ |α| * (K₃ * ((n : ℝ) ^ (α - 1) + 1)) + K₁ * ((n : ℝ) ^ (α - 1) + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) he
    _ = (|α| * K₃ + K₁) * ((n : ℝ) ^ (α - 1) + 1) := by ring

end Asymptotics

end Azurite.DLMF
