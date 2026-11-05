/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section9
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-!
# DLMF §3.9(ii): Euler's transformation of series

* 3.9.3 (`dlmf_3_9_3`): `Δᵏa₀ = Δᵏ⁻¹a₁ − Δᵏ⁻¹a₀` for Mathlib's forward difference `Δ = fwdDiff 1`.
* 3.9.4 (`dlmf_3_9_4`): `Δᵏa₀ = ∑_{m=0}^{k} (−1)^m C(k, m) a_{k−m}`.
* 3.9.2 (`dlmf_3_9_2`): if `S = ∑ (−1)ᵏ aₖ` converges, then `S = ∑ (−1)ᵏ 2^{−k−1} Δᵏa₀`. The
  partial sums of the transformed series are the binomial means
  `2^{−N} ∑_{j<N} C(N, j + 1) s_j` of the partial sums `s_j` (`euler_partial_eq`), and these
  converge to `S` by a Toeplitz argument (`toeplitz_tendsto`). So the right-hand side always
  converges: DLMF's proviso "provided that the right-hand side converges" is automatically
  satisfied.
* 3.9.5 (`dlmf_3_9_5`): `ln 2 = 1 − 1/2 + 1/3 − ⋯ = ∑ 1/(k 2ᵏ)`, from
  `Δᵏ(1/(n + 1)) = (−1)ᵏ k!/((n + 1)⋯(n + k + 1))` (`fwdDiff_iter_inv_affine`).
* 3.9.6 (`dlmf_3_9_6`): `π/4 = 1 − 1/3 + 1/5 − ⋯ = ½(1 + 1!/(1·3) + 2!/(1·3·5) + ⋯)`.
-/

open Filter Topology Finset

namespace Azurite.DLMF

/-! ### Forward differences, 3.9.3–3.9.4 -/

section Diff

variable {𝕜 : Type*} [Field 𝕜]

/-- **DLMF 3.9.3**: `Δᵏa₀ = Δᵏ⁻¹a₁ − Δᵏ⁻¹a₀`. -/
theorem dlmf_3_9_3 (a : ℕ → 𝕜) (k : ℕ) :
    (fwdDiff 1)^[k + 1] a 0 = (fwdDiff 1)^[k] a 1 - (fwdDiff 1)^[k] a 0 := by
  rw [Function.iterate_succ_apply']
  rfl

/-- **DLMF 3.9.4**: `Δᵏa₀ = ∑_{m=0}^{k} (−1)^m C(k, m) a_{k−m}`. -/
theorem dlmf_3_9_4 (a : ℕ → 𝕜) (k : ℕ) :
    (fwdDiff 1)^[k] a 0 = ∑ m ∈ range (k + 1), (-1) ^ m * (k.choose m : 𝕜) * a (k - m) := by
  rw [fwdDiff_iter_eq_sum_shift, ← sum_range_reflect]
  refine sum_congr rfl fun m hm => ?_
  have hm' : m ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hm)
  rw [zsmul_eq_mul, show k + 1 - 1 - m = k - m by omega, Nat.choose_symm hm',
    show k - (k - m) = m by omega, zero_add, nsmul_one]
  push_cast
  ring

/-- `(−1)ᵏ Δᵏa₀ = ∑_{m ≤ k} C(k, m) (−1)^m a_m`. -/
theorem neg_one_pow_fwdDiff (a : ℕ → 𝕜) (k : ℕ) :
    (-1) ^ k * (fwdDiff 1)^[k] a 0 =
      ∑ m ∈ range (k + 1), (k.choose m : 𝕜) * ((-1) ^ m * a m) := by
  rw [fwdDiff_iter_eq_sum_shift, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hm' : m ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hm)
  rw [zsmul_eq_mul, zero_add, nsmul_one]
  push_cast
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm'
  rw [show m + d - m = d by omega, pow_add]
  ring_nf
  rw [pow_mul', neg_one_sq, one_pow, mul_one]

end Diff

/-! ### The binomial means -/

section Means

variable {𝕜 : Type*} [Field 𝕜]

/-- The `k`-th term `(−1)ᵏ 2^{−k−1} Δᵏa₀` of Euler's transformation. -/
def eulerTerm (a : ℕ → 𝕜) (k : ℕ) : 𝕜 := (-1) ^ k / 2 ^ (k + 1) * (fwdDiff 1)^[k] a 0

/-- Abel summation against binomial coefficients. -/
theorem choose_abel (s : ℕ → 𝕜) (N : ℕ) :
    ∑ m ∈ range (N + 1), (N.choose m : 𝕜) * (s m - if m = 0 then 0 else s (m - 1)) =
      ∑ j ∈ range (N + 1), (N.choose j : 𝕜) * s j -
        ∑ j ∈ range N, (N.choose (j + 1) : 𝕜) * s j := by
  rw [sum_range_succ' _ N, sum_range_succ' (fun j => (N.choose j : 𝕜) * s j) N]
  simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, sub_zero]
  rw [add_sub_right_comm, ← sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun j _ => by ring

/-- The partial sums of Euler's transformation are binomial means of the partial sums
`s_j = ∑_{m ≤ j} (−1)^m a_m`. -/
theorem euler_partial_eq (a : ℕ → 𝕜) (h2 : (2 : 𝕜) ≠ 0) (N : ℕ) :
    ∑ k ∈ range N, eulerTerm a k = (2 ^ N)⁻¹ * ∑ j ∈ range N, (N.choose (j + 1) : 𝕜) *
      ∑ m ∈ range (j + 1), (-1) ^ m * a m := by
  set s : ℕ → 𝕜 := fun j => ∑ m ∈ range (j + 1), (-1) ^ m * a m
  have hb : ∀ m, (-1) ^ m * a m = s m - if m = 0 then 0 else s (m - 1) := fun m => by
    rcases m with _ | m
    · simp [s]
    · simp [s, sum_range_succ]
  have hterm : ∀ k, eulerTerm a k =
      (2 ^ (k + 1))⁻¹ * ∑ m ∈ range (k + 1), (k.choose m : 𝕜) * ((-1) ^ m * a m) := fun k => by
    rw [eulerTerm, ← neg_one_pow_fwdDiff, div_eq_inv_mul, mul_assoc]
  induction N with
  | zero => simp
  | succ N ih =>
    have hab : ∑ m ∈ range (N + 1), (N.choose m : 𝕜) * ((-1) ^ m * a m) =
        ∑ m ∈ range (N + 1), (N.choose m : 𝕜) * (s m - if m = 0 then 0 else s (m - 1)) :=
      sum_congr rfl fun m _ => by rw [hb]
    rw [sum_range_succ, ih, hterm, hab, choose_abel]
    have hlast : ∑ j ∈ range N, (N.choose (j + 1) : 𝕜) * s j =
        ∑ j ∈ range (N + 1), (N.choose (j + 1) : 𝕜) * s j := by
      rw [sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
    have hpas : ∑ j ∈ range (N + 1), ((N + 1).choose (j + 1) : 𝕜) * s j =
        ∑ j ∈ range (N + 1), (N.choose j : 𝕜) * s j +
          ∑ j ∈ range N, (N.choose (j + 1) : 𝕜) * s j := by
      rw [hlast, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => ?_
      rw [Nat.choose_succ_succ', Nat.cast_add]
      ring
    rw [hpas, pow_succ]
    field_simp
    ring

end Means

/-! ### Toeplitz -/

/-- A Toeplitz lemma: if `s_j → S`, the weights `λ_N(j) ≥ 0` satisfy `∑_{j<N} λ_N(j) → 1` and
`λ_N(j) → 0` for each `j`, then `∑_{j<N} λ_N(j) s_j → S`. -/
theorem toeplitz_tendsto {𝕜 : Type*} [RCLike 𝕜] {s : ℕ → 𝕜} {S : 𝕜} {w : ℕ → ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝 S)) (hw0 : ∀ N j, 0 ≤ w N j)
    (hw1 : Tendsto (fun N => ∑ j ∈ range N, w N j) atTop (𝓝 1))
    (hwj : ∀ j, Tendsto (fun N => w N j) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ j ∈ range N, (w N j : 𝕜) * s j) atTop (𝓝 S) := by
  have hsplit : ∀ N, ∑ j ∈ range N, (w N j : 𝕜) * s j =
      ∑ j ∈ range N, (w N j : 𝕜) * (s j - S) + ((∑ j ∈ range N, w N j : ℝ) : 𝕜) * S := by
    intro N
    push_cast
    rw [sum_mul, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  simp_rw [hsplit]
  have h2 : Tendsto (fun N => ((∑ j ∈ range N, w N j : ℝ) : 𝕜) * S) atTop (𝓝 S) := by
    have := ((RCLike.continuous_ofReal.tendsto 1).comp hw1).mul_const S
    simpa using this
  suffices h1 : Tendsto (fun N => ∑ j ∈ range N, (w N j : 𝕜) * (s j - S)) atTop (𝓝 0) by
    simpa using h1.add h2
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hS := Metric.tendsto_atTop.mp hs (ε / 4) (by positivity)
  obtain ⟨J, hJ⟩ := hS
  -- the head `j < J`
  have hhead : Tendsto (fun N => ∑ j ∈ range J, w N j * ‖s j - S‖) atTop (𝓝 0) := by
    have := tendsto_finsetSum (range J) fun j _ => (hwj j).mul_const ‖s j - S‖
    simpa using this
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hhead (ε / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hw1 1 one_pos
  refine ⟨max J (max N₁ N₂), fun N hN => ?_⟩
  have hJN : J ≤ N := le_trans (le_max_left _ _) hN
  have h1N := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
  have h2N := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sum_nonneg fun j _ =>
    mul_nonneg (hw0 N j) (norm_nonneg _))] at h1N
  rw [Real.dist_eq] at h2N
  have hsum2 : ∑ j ∈ range N, w N j < 2 := by linarith [(abs_lt.mp h2N).2]
  rw [dist_eq_norm, sub_zero]
  calc ‖∑ j ∈ range N, (w N j : 𝕜) * (s j - S)‖
      ≤ ∑ j ∈ range N, w N j * ‖s j - S‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun j _ => ?_))
        rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (hw0 N j)]
    _ = ∑ j ∈ range J, w N j * ‖s j - S‖ + ∑ j ∈ Ico J N, w N j * ‖s j - S‖ :=
        (sum_range_add_sum_Ico _ hJN).symm
    _ ≤ ε / 2 + ∑ j ∈ Ico J N, w N j * (ε / 4) := by
        refine add_le_add h1N.le (sum_le_sum fun j hj => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (hw0 N j)
        have := hJ j (mem_Ico.mp hj).1
        rw [dist_eq_norm] at this
        exact this.le
    _ ≤ ε / 2 + ∑ j ∈ range N, w N j * (ε / 4) :=
        add_le_add le_rfl (sum_le_sum_of_subset_of_nonneg
          (fun j hj => mem_range.mpr (mem_Ico.mp hj).2)
          fun j _ _ => mul_nonneg (hw0 N j) (by positivity))
    _ = ε / 2 + (∑ j ∈ range N, w N j) * (ε / 4) := by rw [sum_mul]
    _ < ε / 2 + 2 * (ε / 4) := by gcongr
    _ = ε := by ring

/-! ### 3.9.2 -/

/-- The binomial weights `C(N, j + 1)/2^N`. -/
theorem euler_weights :
    (∀ N j, (0 : ℝ) ≤ (N.choose (j + 1) : ℝ) / 2 ^ N) ∧
      Tendsto (fun N => ∑ j ∈ range N, (N.choose (j + 1) : ℝ) / 2 ^ N) atTop (𝓝 1) ∧
      ∀ j, Tendsto (fun N => (N.choose (j + 1) : ℝ) / 2 ^ N) atTop (𝓝 0) := by
  refine ⟨fun N j => by positivity, ?_, fun j => ?_⟩
  · have hsum : ∀ N, ∑ j ∈ range N, (N.choose (j + 1) : ℝ) / 2 ^ N = 1 - (2 ^ N)⁻¹ := by
      intro N
      have h := Nat.sum_range_choose N
      rw [sum_range_succ'] at h
      have h' : (∑ j ∈ range N, (N.choose (j + 1) : ℝ)) = 2 ^ N - 1 := by
        have := congrArg (fun x : ℕ => (x : ℝ)) h
        push_cast at this
        simp only [Nat.choose_zero_right, Nat.cast_one] at this
        linarith
      rw [← sum_div, h']
      field_simp
    simp_rw [hsum]
    have : Tendsto (fun N : ℕ => ((2 : ℝ) ^ N)⁻¹) atTop (𝓝 0) := by
      exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    simpa using this.const_sub 1
  · have h := tendsto_pow_const_div_const_pow_of_one_lt (j + 1) (one_lt_two (α := ℝ))
    refine squeeze_zero (fun N => by positivity) (fun N => ?_) h
    gcongr
    exact_mod_cast Nat.choose_le_pow N (j + 1)

/-- **DLMF 3.9.2**: if `S = ∑ (−1)ᵏ aₖ` converges, then Euler's transformed series
`∑ (−1)ᵏ 2^{−k−1} Δᵏa₀` converges to `S` (its convergence is automatic). -/
theorem dlmf_3_9_2 {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) {S : 𝕜}
    (h : Tendsto (fun n => ∑ k ∈ range n, (-1) ^ k * a k) atTop (𝓝 S)) :
    Tendsto (fun n => ∑ k ∈ range n, eulerTerm a k) atTop (𝓝 S) := by
  obtain ⟨hw0, hw1, hwj⟩ := euler_weights
  have hs : Tendsto (fun j => ∑ m ∈ range (j + 1), (-1) ^ m * a m) atTop (𝓝 S) :=
    h.comp (tendsto_add_atTop_nat 1)
  have key := toeplitz_tendsto (𝕜 := 𝕜) hs hw0 hw1 hwj
  refine key.congr fun N => ?_
  rw [euler_partial_eq a two_ne_zero, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  push_cast
  ring

/-! ### Examples -/

/-- `Δᵏ (1/(cn + 1)) = (−1)ᵏ cᵏ k!/((cn + 1)(c(n + 1) + 1)⋯(c(n + k) + 1))`. -/
theorem fwdDiff_iter_inv_affine {c : ℝ} (hc : 0 < c) (k n : ℕ) :
    (fwdDiff 1)^[k] (fun n : ℕ => ((c * n + 1 : ℝ))⁻¹) n =
      (-1) ^ k * c ^ k * k.factorial / ∏ i ∈ range (k + 1), (c * (n + i) + 1) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show (fwdDiff 1)^[k] _ (n + 1) - (fwdDiff 1)^[k] _ n = _
    rw [ih, ih]
    have hpos : ∀ m : ℕ, 0 < c * m + 1 := fun m => by positivity
    set Q := ∏ i ∈ range k, (c * ((n : ℝ) + (i + 1)) + 1)
    have hQ : 0 < Q := prod_pos fun i _ => by positivity
    have e1 : ∏ i ∈ range (k + 1), (c * (((n + 1 : ℕ) : ℝ) + i) + 1) =
        Q * (c * (n + (k + 1)) + 1) := by
      rw [prod_range_succ]
      congr 1
      · exact prod_congr rfl fun i _ => by push_cast; ring_nf
      · push_cast; ring
    have e2 : ∏ i ∈ range (k + 1), (c * ((n : ℝ) + i) + 1) = Q * (c * n + 1) := by
      rw [prod_range_succ']
      congr 1
      · exact prod_congr rfl fun i _ => by push_cast; ring_nf
      · simp
    have e3 : ∏ i ∈ range (k + 1 + 1), (c * ((n : ℝ) + i) + 1) =
        Q * (c * n + 1) * (c * (n + (k + 1)) + 1) := by
      rw [prod_range_succ, e2]
      push_cast; ring
    rw [e1, e2, e3, Nat.factorial_succ]
    have h1 : 0 < c * (n : ℝ) + 1 := by positivity
    have h2 : 0 < c * ((n : ℝ) + (k + 1)) + 1 := by positivity
    field_simp
    push_cast
    ring

/-- **DLMF 3.9.5**: `ln 2 = 1 − 1/2 + 1/3 − 1/4 + ⋯ = 1/(1·2¹) + 1/(2·2²) + 1/(3·2³) + ⋯`. -/
theorem dlmf_3_9_5 :
    Tendsto (fun n => ∑ k ∈ range n, (-1 : ℝ) ^ k / (k + 1)) atTop (𝓝 (Real.log 2)) ∧
      Tendsto (fun n => ∑ k ∈ range n, 1 / ((k + 1) * (2 : ℝ) ^ (k + 1))) atTop
        (𝓝 (Real.log 2)) ∧
      ∀ k, eulerTerm (fun n : ℕ => ((n : ℝ) + 1)⁻¹) k = 1 / ((k + 1) * (2 : ℝ) ^ (k + 1)) := by
  have hterm : ∀ k, eulerTerm (fun n : ℕ => ((n : ℝ) + 1)⁻¹) k =
      1 / ((k + 1) * (2 : ℝ) ^ (k + 1)) := fun k => by
    have h := fwdDiff_iter_inv_affine (c := 1) one_pos k 0
    simp only [one_mul, one_pow, Nat.cast_zero, zero_add, mul_one] at h
    rw [eulerTerm, h, prod_range_succ, show ∏ x ∈ range k, ((x : ℝ) + 1) = k.factorial by
      exact_mod_cast prod_range_add_one_eq_factorial k]
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    rw [show ((-1 : ℝ) ^ k) ^ 2 = 1 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  -- the right-hand side: `−ln(1 − 1/2)`
  have hR : Tendsto (fun n => ∑ k ∈ range n, 1 / ((k + 1) * (2 : ℝ) ^ (k + 1))) atTop
      (𝓝 (Real.log 2)) := by
    have h := (Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / 2) (by norm_num)).tendsto_sum_nat
    rw [show -Real.log (1 - 1 / 2) = Real.log 2 by
      rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv, neg_neg]] at h
    refine h.congr fun n => sum_congr rfl fun k _ => ?_
    rw [div_pow, one_pow]
    field_simp
  -- the left-hand side converges (Leibniz), and Euler's transformation identifies its sum
  obtain ⟨l, hl⟩ : ∃ l, Tendsto (fun n => ∑ k ∈ range n, (-1 : ℝ) ^ k / (k + 1)) atTop (𝓝 l) := by
    apply Antitone.tendsto_alternating_series_of_tendsto_zero
    · exact antitone_iff_forall_lt.mpr fun _ _ _ => by gcongr
    · exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hE := dlmf_3_9_2 (𝕜 := ℝ) (fun n : ℕ => ((n : ℝ) + 1)⁻¹) (S := l)
    (hl.congr fun n => sum_congr rfl fun k _ => by rw [div_eq_mul_inv])
  simp_rw [hterm] at hE
  rw [tendsto_nhds_unique hE hR] at hl
  exact ⟨hl, hR, hterm⟩

/-- **DLMF 3.9.6**: `π/4 = 1 − 1/3 + 1/5 − 1/7 + ⋯ = ½(1 + 1!/(1·3) + 2!/(1·3·5) + 3!/(1·3·5·7)
+ ⋯)`, the `k`-th term being `½ k!/(1·3⋯(2k + 1))`. -/
theorem dlmf_3_9_6 :
    Tendsto (fun n => ∑ k ∈ range n, (-1 : ℝ) ^ k / (2 * k + 1)) atTop (𝓝 (Real.pi / 4)) ∧
      Tendsto (fun n => ∑ k ∈ range n,
        1 / 2 * (k.factorial / ∏ i ∈ range (k + 1), (2 * (i : ℝ) + 1))) atTop
        (𝓝 (Real.pi / 4)) := by
  have hterm : ∀ k, eulerTerm (fun n : ℕ => ((2 * n + 1 : ℝ))⁻¹) k =
      1 / 2 * (k.factorial / ∏ i ∈ range (k + 1), (2 * (i : ℝ) + 1)) := fun k => by
    have h := fwdDiff_iter_inv_affine (c := 2) two_pos k 0
    simp only [Nat.cast_zero, zero_add] at h
    rw [eulerTerm, h]
    have hP : 0 < ∏ i ∈ range (k + 1), (2 * (i : ℝ) + 1) := prod_pos fun i _ => by positivity
    field_simp
    rw [show ((-1 : ℝ) ^ k) ^ 2 = 1 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    ring
  have hL := Real.tendsto_sum_pi_div_four
  have hE := dlmf_3_9_2 (𝕜 := ℝ) (fun n : ℕ => ((2 * n + 1 : ℝ))⁻¹) (S := Real.pi / 4)
    (hL.congr fun n => sum_congr rfl fun k _ => by rw [div_eq_mul_inv])
  simp_rw [hterm] at hE
  exact ⟨hL, hE⟩

end Azurite.DLMF
