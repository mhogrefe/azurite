/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section7Rank

/-!
# DLMF §2.7(ii): Irregular Singularities of Rank 1 — formal solutions 2.7.8, 2.7.11

For data 2.7.7 (`RankOneData f g a fc gc`), a root `λ` of the characteristic equation 2.7.9 with
`f₀ + 2λ ≠ 0` (that is, `λ₁ ≠ λ₂`) and `μ` given by 2.7.10:

* 2.7.11 (`rankOneCoeff`, `dlmf_2_7_11`): the coefficients `a₀ = 1`,
  `(f₀ + 2λ) s aₛ = (s − μ)(s − 1 − μ) a_{s−1}
    + ∑_{r=1}^{s} (λ f_{r+1} + g_{r+1} − (s − r − μ) fᵣ) a_{s−r}`.
* 2.7.8 (`RankOneData.dlmf_2_7_8`): `e^{λz} z^μ ∑ aₛ z^{−s}` is a *formal solution* of 2.7.1:
  every truncation `w_N(z) = e^{λz} z^μ ∑_{s≤N} aₛ z^{−s}` (`rankOneTrunc`, principal branch of
  `z^μ`) satisfies `w_N″ + f w_N′ + g w_N = e^{λz} z^μ B_N(z)` for `|z| > a`, `z ∉ (−∞, 0]`, with
  `B_N(z) = O(z^{−N−2})` as `z → ∞`.

The proof expands `B_N(z) = ∑ cₙ z^{−n}` (`bracketSeq`, a convergent series for `|z| > a`) and shows
`cₙ = 0` for `n ≤ N + 1` (`bracketSeq_zero`, `bracketSeq_one`, `bracketSeq_add_two`): the
coefficient of `z⁰` is 2.7.9, that of `z^{−1}` is 2.7.10, and that of `z^{−s−1}` is 2.7.11.
-/

open Filter Topology Set Complex Metric Finset Asymptotics Bornology

namespace Azurite.DLMF

/-! ### Sequence operations -/

/-- The Cauchy-product coefficients `(a ⋆ b)ₙ = ∑_{j ≤ n} a_{n−j} b_j`. -/
def seqConv (a b : ℕ → ℂ) (n : ℕ) : ℂ := ∑ j ∈ range (n + 1), a (n - j) * b j

/-- The truncation `bₙ` for `n ≤ N`, `0` beyond. -/
def truncSeq (a : ℕ → ℂ) (N n : ℕ) : ℂ := if n ≤ N then a n else 0

theorem truncSeq_of_le {a : ℕ → ℂ} {N n : ℕ} (h : n ≤ N) : truncSeq a N n = a n := by
  simp [truncSeq, h]

theorem truncSeq_of_lt {a : ℕ → ℂ} {N n : ℕ} (h : N < n) : truncSeq a N n = 0 := by
  simp [truncSeq, not_le.mpr h]

theorem hasRadiusGE_of_support {b : ℕ → ℂ} {M : ℕ} (hb : ∀ n, M < n → b n = 0) (R : ℝ) :
    HasRadiusGE b R := by
  intro ρ hρ _
  refine ⟨∑ n ∈ range (M + 1), ‖b n‖ * ρ ^ n, fun s => ?_⟩
  by_cases hs : s ≤ M
  · exact single_le_sum (f := fun n => ‖b n‖ * ρ ^ n) (fun _ _ => by positivity)
      (mem_range.mpr (by omega))
  · rw [hb s (by omega), norm_zero, zero_mul]
    exact sum_nonneg fun _ _ => by positivity

theorem HasRadiusGE.add {a b : ℕ → ℂ} {R : ℝ} (ha : HasRadiusGE a R) (hb : HasRadiusGE b R) :
    HasRadiusGE (a + b) R := by
  intro ρ hρ hρR
  obtain ⟨K₁, h₁⟩ := ha ρ hρ hρR
  obtain ⟨K₂, h₂⟩ := hb ρ hρ hρR
  refine ⟨K₁ + K₂, fun s => ?_⟩
  rw [Pi.add_apply]
  calc ‖a s + b s‖ * ρ ^ s ≤ (‖a s‖ + ‖b s‖) * ρ ^ s :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
    _ = ‖a s‖ * ρ ^ s + ‖b s‖ * ρ ^ s := add_mul _ _ _
    _ ≤ K₁ + K₂ := add_le_add (h₁ s) (h₂ s)

theorem sum_antidiagonal_mul_pow (a b : ℕ → ℂ) (x : ℂ) (n : ℕ) :
    ∑ kl ∈ antidiagonal n, a kl.1 * x ^ kl.1 * (b kl.2 * x ^ kl.2) = seqConv a b n * x ^ n := by
  rw [← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, seqConv, sum_mul]
  refine sum_congr rfl fun r hr => ?_
  have hr' : r ≤ n := mem_range_succ_iff.mp hr
  dsimp only
  rw [← pow_sub_mul_pow x hr']
  ring

theorem HasRadiusGE.conv {a b : ℕ → ℂ} {R : ℝ} (ha : HasRadiusGE a R) (hb : HasRadiusGE b R) :
    HasRadiusGE (seqConv a b) R :=
  hasRadiusGE_of_summable (z₀ := 0) fun _ hζ => by
    simpa only [sum_antidiagonal_mul_pow] using
      summable_norm_sum_mul_antidiagonal_of_summable_norm (ha.summable_norm hζ)
        (hb.summable_norm hζ)

/-- A power series whose first `m` coefficients vanish is `O(ζ^m)` at `0`. -/
theorem HasRadiusGE.isBigO_pow {c : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE c R) (hR : 0 < R) {m : ℕ}
    (hc : ∀ n < m, c n = 0) : (powerSeriesSum c 0) =O[𝓝 0] (fun ζ : ℂ => ζ ^ m) := by
  set ρ := R / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρR : ρ < R := by linarith
  have hsum : Summable fun n => ‖c n‖ * ρ ^ n := by
    have hb : (ρ : ℂ) ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_zero_right, norm_real, Real.norm_of_nonneg hρ0.le]
      exact hρR
    refine (h.summable_norm hb).congr fun n => ?_
    rw [sub_zero, norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hρ0.le]
  refine IsBigO.of_bound ((∑' n, ‖c n‖ * ρ ^ n) / ρ ^ m) ?_
  filter_upwards [ball_mem_nhds (0 : ℂ) hρ0] with ζ hζ
  have hζ' : ‖ζ‖ < ρ := by rwa [mem_ball, dist_zero_right] at hζ
  have hzR : ζ ∈ ball (0 : ℂ) R := ball_subset_ball hρR.le hζ
  have hterm : ∀ n, ‖c n * (ζ - 0) ^ n‖ ≤ ‖ζ‖ ^ m / ρ ^ m * (‖c n‖ * ρ ^ n) := by
    intro n
    rw [sub_zero, norm_mul, norm_pow]
    by_cases hn : n < m
    · rw [hc n hn, norm_zero, zero_mul]
      positivity
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hn)
      have hj : ‖ζ‖ ^ j ≤ ρ ^ j := pow_le_pow_left₀ (norm_nonneg _) hζ'.le j
      calc ‖c (m + j)‖ * ‖ζ‖ ^ (m + j) = ‖c (m + j)‖ * ‖ζ‖ ^ m * ‖ζ‖ ^ j := by ring
        _ ≤ ‖c (m + j)‖ * ‖ζ‖ ^ m * ρ ^ j := mul_le_mul_of_nonneg_left hj (by positivity)
        _ = ‖ζ‖ ^ m / ρ ^ m * (‖c (m + j)‖ * ρ ^ (m + j)) := by
          rw [pow_add]
          field_simp
  rw [powerSeriesSum]
  calc ‖∑' n, c n * (ζ - 0) ^ n‖ ≤ ∑' n, ‖c n * (ζ - 0) ^ n‖ :=
        norm_tsum_le_tsum_norm (h.summable_norm hzR)
    _ ≤ ∑' n, ‖ζ‖ ^ m / ρ ^ m * (‖c n‖ * ρ ^ n) :=
        Summable.tsum_le_tsum hterm (h.summable_norm hzR) (hsum.mul_left _)
    _ = (∑' n, ‖c n‖ * ρ ^ n) / ρ ^ m * ‖ζ ^ m‖ := by
        rw [tsum_mul_left, norm_pow]
        ring

/-! ### The operator `w ↦ w′` on `e^{λz} z^μ ∑ bₙ z^{−n}` -/

/-- The coefficients of `d/dz` on `e^{λz} z^μ ∑ bₙ z^{−n}`: `(T b)₀ = λ b₀`,
`(T b)_{k+1} = λ b_{k+1} + (μ − k) b_k`. -/
def frobT (lam mu : ℂ) (b : ℕ → ℂ) : ℕ → ℂ
  | 0 => lam * b 0
  | k + 1 => lam * b (k + 1) + (mu - k) * b k

theorem frobT_support {lam mu : ℂ} {b : ℕ → ℂ} {M : ℕ} (hb : ∀ n, M < n → b n = 0) :
    ∀ n, M + 1 < n → frobT lam mu b n = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [frobT, hb (k + 1) (by omega), hb k (by omega), mul_zero, add_zero]

theorem HasRadiusGE.powerSeriesSum_frobT {b : ℕ → ℂ} {R : ℝ} (hb : HasRadiusGE b R)
    (lam mu : ℂ) {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) R) :
    powerSeriesSum (frobT lam mu b) 0 ζ = lam * powerSeriesSum b 0 ζ +
      mu * ζ * powerSeriesSum b 0 ζ - ζ ^ 2 * powerSeriesSum (shiftDeriv b) 0 ζ := by
  have hS : HasSum (fun n => b n * (ζ - 0) ^ n) (powerSeriesSum b 0 ζ) := (hb.summable hζ).hasSum
  have h1 := hb.hasSum_natCast_mul hζ
  simp only [sub_zero] at hS h1
  have h0 := (hasSum_nat_add_iff' 1).mpr hS
  simp only [sum_range_one, pow_zero, mul_one] at h0
  have key : HasSum (fun n => frobT lam mu b n * ζ ^ n) (lam * powerSeriesSum b 0 ζ +
      mu * ζ * powerSeriesSum b 0 ζ - ζ ^ 2 * powerSeriesSum (shiftDeriv b) 0 ζ) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [sum_range_one, pow_zero, mul_one]
    convert ((h0.mul_left lam).add (hS.mul_left (mu * ζ))).sub (h1.mul_left ζ) using 1
    · funext n
      simp only [frobT]
      ring
    · simp only [frobT]
      ring
  rw [powerSeriesSum]
  simp only [sub_zero]
  exact key.tsum_eq

/-- `e^{λz} z^μ ∑ bₙ z^{−n}` (principal branch of `z^μ`). -/
noncomputable def frobW (lam mu : ℂ) (b : ℕ → ℂ) (z : ℂ) : ℂ :=
  cexp (lam * z) * z ^ mu * powerSeriesSum b 0 z⁻¹

/-- `d/dz (e^{λz} z^μ ∑ bₙ z^{−n}) = e^{λz} z^μ ∑ (T b)ₙ z^{−n}`. -/
theorem HasRadiusGE.hasDerivAt_frobW {b : ℕ → ℂ} {R : ℝ} (hb : HasRadiusGE b R) (lam mu : ℂ)
    {z : ℂ} (hz : z ∈ slitPlane) (hzR : z⁻¹ ∈ ball (0 : ℂ) R) :
    HasDerivAt (frobW lam mu b) (frobW lam mu (frobT lam mu b) z) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hS : HasDerivAt (fun z => powerSeriesSum b 0 z⁻¹)
      (powerSeriesSum (shiftDeriv b) 0 z⁻¹ * -(z ^ 2)⁻¹) z :=
    (hb.hasDerivAt hzR).comp z (hasDerivAt_inv hz0)
  have he : HasDerivAt (fun z => cexp (lam * z)) (cexp (lam * z) * (lam * 1)) z :=
    ((hasDerivAt_id z).const_mul lam).cexp
  have hp : HasDerivAt (fun z => z ^ mu) (mu * z ^ (mu - 1) * 1) z :=
    (hasDerivAt_id z).cpow_const hz
  refine ((he.mul hp).mul hS).congr_deriv ?_
  rw [frobW, hb.powerSeriesSum_frobT lam mu hzR, cpow_sub _ _ hz0, cpow_one]
  simp only [Pi.mul_apply]
  field_simp
  ring

/-! ### 2.7.11: the coefficients -/

/-- **DLMF 2.7.11**: `a₀ = 1` and, for `s ≥ 0`,
`(f₀ + 2λ)(s + 1) a_{s+1} = (s + 1 − μ)(s − μ) aₛ
  + ∑_{i ≤ s} (λ f_{s+2−i} + g_{s+2−i} − (i − μ) f_{s+1−i}) aᵢ`
(2.7.11 with `i = s + 1 − r`). -/
noncomputable def rankOneCoeff (fc gc : ℕ → ℂ) (lam mu : ℂ) : ℕ → ℂ
  | 0 => 1
  | s + 1 => ((((s + 1 : ℕ) : ℂ) - mu) * ((s : ℂ) - mu) * rankOneCoeff fc gc lam mu s +
      ∑ i : Fin (s + 1), (lam * fc (s + 2 - i) + gc (s + 2 - i) -
        (((i : ℕ) : ℂ) - mu) * fc (s + 1 - i)) * rankOneCoeff fc gc lam mu i) /
      ((fc 0 + 2 * lam) * ((s + 1 : ℕ) : ℂ))

theorem rankOneCoeff_zero (fc gc : ℕ → ℂ) (lam mu : ℂ) : rankOneCoeff fc gc lam mu 0 = 1 := by
  rw [rankOneCoeff]

theorem rankOneCoeff_succ (fc gc : ℕ → ℂ) {lam : ℂ} (mu : ℂ) (hne : fc 0 + 2 * lam ≠ 0)
    (s : ℕ) :
    (fc 0 + 2 * lam) * ((s + 1 : ℕ) : ℂ) * rankOneCoeff fc gc lam mu (s + 1) =
      (((s + 1 : ℕ) : ℂ) - mu) * ((s : ℂ) - mu) * rankOneCoeff fc gc lam mu s +
        ∑ i ∈ range (s + 1), (lam * fc (s + 2 - i) + gc (s + 2 - i) -
          ((i : ℂ) - mu) * fc (s + 1 - i)) * rankOneCoeff fc gc lam mu i := by
  have hd : (fc 0 + 2 * lam) * ((s + 1 : ℕ) : ℂ) ≠ 0 :=
    mul_ne_zero hne (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero s))
  rw [rankOneCoeff, Finset.sum_range, mul_div_assoc', mul_div_cancel_left₀ _ hd]

theorem sum_Icc_one_eq_sum_range (F : ℕ → ℂ) (n : ℕ) :
    ∑ r ∈ Icc 1 n, F r = ∑ i ∈ range n, F (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- **DLMF 2.7.11**, in DLMF's form: for `s ≥ 1`,
`(f₀ + 2λ) s aₛ = (s − μ)(s − 1 − μ) a_{s−1}
  + ∑_{r=1}^{s} (λ f_{r+1} + g_{r+1} − (s − r − μ) fᵣ) a_{s−r}`.
-/
theorem dlmf_2_7_11 (fc gc : ℕ → ℂ) {lam : ℂ} (mu : ℂ) (hne : fc 0 + 2 * lam ≠ 0) {s : ℕ}
    (hs : 1 ≤ s) :
    (fc 0 + 2 * lam) * s * rankOneCoeff fc gc lam mu s =
      ((s : ℂ) - mu) * ((s : ℂ) - 1 - mu) * rankOneCoeff fc gc lam mu (s - 1) +
        ∑ r ∈ Icc 1 s, (lam * fc (r + 1) + gc (r + 1) - ((s : ℂ) - r - mu) * fc r) *
          rankOneCoeff fc gc lam mu (s - r) := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  rw [rankOneCoeff_succ fc gc mu hne k, sum_Icc_one_eq_sum_range,
    ← sum_range_reflect _ (k + 1)]
  simp only [Nat.add_sub_cancel]
  congr 1
  · push_cast
    ring
  · refine sum_congr rfl fun j hj => ?_
    have hj' : j < k + 1 := mem_range.mp hj
    rw [show k + 2 - (k - j) = j + 1 + 1 by omega,
      show k + 1 - (k - j) = j + 1 by omega, show k + 1 - (j + 1) = k - j by omega,
      Nat.cast_sub (by omega : j ≤ k)]
    push_cast
    ring

/-! ### The coefficients of `B_N` -/

/-- The coefficients of `B(z) = ∑ cₙ z^{−n}` with
`(e^{λz} z^μ ∑ bₙ z^{−n})″ + f (…)′ + g (…) = e^{λz} z^μ B(z)`: `c = T(T b) + f ⋆ T b + g ⋆ b`. -/
def bracketSeq (fc gc : ℕ → ℂ) (lam mu : ℂ) (b : ℕ → ℂ) : ℕ → ℂ :=
  frobT lam mu (frobT lam mu b) + seqConv fc (frobT lam mu b) + seqConv gc b

variable {fc gc : ℕ → ℂ} {lam mu : ℂ} {b : ℕ → ℂ}

/-- The coefficient of `z⁰`: 2.7.9. -/
theorem bracketSeq_zero : bracketSeq fc gc lam mu b 0 = rankOneChar fc gc lam * b 0 := by
  simp only [bracketSeq, Pi.add_apply, frobT, seqConv, rankOneChar, zero_add, range_one,
    sum_singleton, Nat.sub_zero]
  ring

/-- The coefficient of `z^{−1}`: 2.7.10. -/
theorem bracketSeq_one : bracketSeq fc gc lam mu b 1 = rankOneChar fc gc lam * b 1 +
    ((fc 0 + 2 * lam) * mu + fc 1 * lam + gc 1) * b 0 := by
  simp only [bracketSeq, Pi.add_apply, frobT, seqConv, rankOneChar, sum_range_succ, range_zero,
    sum_empty, Nat.cast_zero]
  norm_num
  ring

/-- The coefficient of `z^{−k−2}`: 2.7.11 with `s = k + 1`. -/
theorem bracketSeq_add_two (k : ℕ) : bracketSeq fc gc lam mu b (k + 2) =
    rankOneChar fc gc lam * b (k + 2) +
      ((fc 0 + 2 * lam) * mu + fc 1 * lam + gc 1 - (fc 0 + 2 * lam) * ((k + 1 : ℕ) : ℂ)) *
        b (k + 1) +
      ((((k + 1 : ℕ) : ℂ) - mu) * ((k : ℂ) - mu) * b k +
        ∑ i ∈ range (k + 1), (lam * fc (k + 2 - i) + gc (k + 2 - i) -
          ((i : ℂ) - mu) * fc (k + 1 - i)) * b i) := by
  -- the `f`-convolution, peeled at both ends
  have e₁ : seqConv fc (frobT lam mu b) (k + 2) =
      fc 0 * (lam * b (k + 2) + (mu - ((k + 1 : ℕ) : ℂ)) * b (k + 1)) +
        lam * ∑ i ∈ range (k + 1), fc (k + 1 - i) * b (i + 1) +
        ∑ i ∈ range (k + 1), fc (k + 1 - i) * ((mu - i) * b i) + fc (k + 2) * (lam * b 0) := by
    have : ∀ i ∈ range (k + 1), fc (k + 2 - (i + 1)) * frobT lam mu b (i + 1) =
        lam * (fc (k + 1 - i) * b (i + 1)) + fc (k + 1 - i) * ((mu - i) * b i) := by
      intro i _
      rw [show k + 2 - (i + 1) = k + 1 - i by omega]
      simp only [frobT]
      ring
    rw [seqConv, sum_range_succ' _ (k + 2), sum_range_succ _ (k + 1), sum_congr rfl this,
      sum_add_distrib, mul_sum]
    simp only [frobT, Nat.sub_zero, show k + 2 - (k + 1 + 1) = 0 by omega,
      show k + 1 + 1 = k + 2 from rfl]
    ring
  -- reindexing `∑ f_{k+1−i} b_{i+1}`
  have e₂ : ∑ i ∈ range (k + 1), fc (k + 1 - i) * b (i + 1) + fc (k + 2) * b 0 =
      ∑ i ∈ range (k + 1), fc (k + 2 - i) * b i + fc 1 * b (k + 1) := by
    have h₁ := sum_range_succ' (fun j => fc (k + 2 - j) * b j) (k + 1)
    have h₂ := sum_range_succ (fun j => fc (k + 2 - j) * b j) (k + 1)
    simp only [Nat.sub_zero, show k + 2 - (k + 1) = 1 by omega] at h₁ h₂
    rw [← h₂, h₁]
    congr 1
    exact sum_congr rfl fun i _ => by rw [show k + 2 - (i + 1) = k + 1 - i by omega]
  -- the `g`-convolution
  have e₃ : seqConv gc b (k + 2) =
      ∑ i ∈ range (k + 1), gc (k + 2 - i) * b i + gc 1 * b (k + 1) + gc 0 * b (k + 2) := by
    rw [seqConv, sum_range_succ, sum_range_succ]
    simp only [show k + 2 - (k + 1) = 1 by omega, Nat.sub_self]
  have e₄ : frobT lam mu (frobT lam mu b) (k + 2) =
      lam * (lam * b (k + 2) + (mu - ((k + 1 : ℕ) : ℂ)) * b (k + 1)) +
        (mu - ((k + 1 : ℕ) : ℂ)) * (lam * b (k + 1) + (mu - k) * b k) := by
    simp only [frobT]
  have e₅ : ∑ i ∈ range (k + 1), (lam * fc (k + 2 - i) + gc (k + 2 - i) -
      ((i : ℂ) - mu) * fc (k + 1 - i)) * b i =
        lam * ∑ i ∈ range (k + 1), fc (k + 2 - i) * b i +
          ∑ i ∈ range (k + 1), gc (k + 2 - i) * b i +
          ∑ i ∈ range (k + 1), fc (k + 1 - i) * ((mu - i) * b i) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  simp only [bracketSeq, Pi.add_apply]
  rw [e₁, e₃, e₄, e₅, rankOneChar]
  linear_combination lam * e₂

/-! ### 2.7.8: formal solutions -/

/-- The truncated formal solution `w_N(z) = e^{λz} z^μ ∑_{s≤N} aₛ z^{−s}` (2.7.8 with
the coefficients 2.7.10–2.7.11). -/
noncomputable def rankOneTrunc (fc gc : ℕ → ℂ) (lam : ℂ) (N : ℕ) : ℂ → ℂ :=
  frobW lam (rankOneMu fc gc lam) (truncSeq (rankOneCoeff fc gc lam (rankOneMu fc gc lam)) N)

theorem powerSeriesSum_truncSeq (a : ℕ → ℂ) (N : ℕ) (ζ : ℂ) :
    powerSeriesSum (truncSeq a N) 0 ζ = ∑ s ∈ range (N + 1), a s * ζ ^ s := by
  rw [powerSeriesSum, tsum_eq_sum (s := range (N + 1)) fun n hn => by
    rw [truncSeq_of_lt (by simpa using hn), zero_mul]]
  exact sum_congr rfl fun n hn => by
    rw [truncSeq_of_le (Nat.lt_succ_iff.mp (mem_range.mp hn)), sub_zero]

theorem rankOneTrunc_eq (fc gc : ℕ → ℂ) (lam : ℂ) (N : ℕ) (z : ℂ) :
    rankOneTrunc fc gc lam N z = cexp (lam * z) * z ^ rankOneMu fc gc lam *
      ∑ s ∈ range (N + 1), rankOneCoeff fc gc lam (rankOneMu fc gc lam) s / z ^ s := by
  rw [rankOneTrunc, frobW, powerSeriesSum_truncSeq]
  congr 1
  exact sum_congr rfl fun s _ => by rw [inv_pow, div_eq_mul_inv]

/-- The first `N + 2` coefficients of the bracket vanish for the truncated series. -/
theorem bracketSeq_truncSeq_eq_zero (hchar : rankOneChar fc gc lam = 0)
    (hne : fc 0 + 2 * lam ≠ 0) (N : ℕ) {n : ℕ} (hn : n < N + 2) :
    bracketSeq fc gc lam (rankOneMu fc gc lam)
      (truncSeq (rankOneCoeff fc gc lam (rankOneMu fc gc lam)) N) n = 0 := by
  set mu := rankOneMu fc gc lam with hmu_def
  have hmu := rankOneMu_mul (gc := gc) hne
  rw [← hmu_def] at hmu
  rcases n with _ | _ | k
  · rw [bracketSeq_zero, hchar, zero_mul]
  · rw [bracketSeq_one, hchar, hmu]
    ring
  · rw [bracketSeq_add_two, hchar, hmu]
    have hk : k + 1 ≤ N := by omega
    have hrec := rankOneCoeff_succ fc gc mu hne k
    have hs : ∑ i ∈ range (k + 1), (lam * fc (k + 2 - i) + gc (k + 2 - i) -
        ((i : ℂ) - mu) * fc (k + 1 - i)) * truncSeq (rankOneCoeff fc gc lam mu) N i =
        ∑ i ∈ range (k + 1), (lam * fc (k + 2 - i) + gc (k + 2 - i) -
        ((i : ℂ) - mu) * fc (k + 1 - i)) * rankOneCoeff fc gc lam mu i :=
      sum_congr rfl fun i hi => by
        rw [truncSeq_of_le (by have := mem_range.mp hi; omega : i ≤ N)]
    rw [truncSeq_of_le hk, truncSeq_of_le (by omega : k ≤ N), hs]
    linear_combination -hrec

/-- **DLMF 2.7.8**: under 2.7.7, for a root `λ` of 2.7.9 with `f₀ + 2λ ≠ 0` (`λ₁ ≠ λ₂`) and `μ`,
`aₛ` from 2.7.10–2.7.11, `e^{λz} z^μ ∑ aₛ z^{−s}` is a formal solution of 2.7.1: each truncation
`w_N = rankOneTrunc` satisfies, for `|z| > a` off the branch cut,
`w_N″ + f w_N′ + g w_N = e^{λz} z^μ B_N(z)` with `B_N(z) = O(z^{−N−2})` as `z → ∞`. -/
theorem RankOneData.dlmf_2_7_8 {f g : ℂ → ℂ} {a : ℝ} (D : RankOneData f g a fc gc)
    (hchar : rankOneChar fc gc lam = 0) (hne : fc 0 + 2 * lam ≠ 0) (N : ℕ) :
    ∃ w' B : ℂ → ℂ, B =O[cobounded ℂ] (fun z => z⁻¹ ^ (N + 2)) ∧
      ∀ z ∈ slitPlane, a < ‖z‖ →
        HasDerivAt (rankOneTrunc fc gc lam N) (w' z) z ∧
        HasDerivAt w' (-(f z * w' z + g z * rankOneTrunc fc gc lam N z) +
          cexp (lam * z) * z ^ rankOneMu fc gc lam * B z) z := by
  set mu := rankOneMu fc gc lam with hmu_def
  set r := truncSeq (rankOneCoeff fc gc lam mu) N with hr_def
  have hr0 : ∀ n, N < n → r n = 0 := fun n hn => truncSeq_of_lt hn
  have hr1 := frobT_support (lam := lam) (mu := mu) hr0
  have hr2 := frobT_support (lam := lam) (mu := mu) hr1
  set c := bracketSeq fc gc lam mu r with hc_def
  have hR : (0 : ℝ) < a⁻¹ := inv_pos.mpr D.a_pos
  have hcR : HasRadiusGE c a⁻¹ :=
    ((hasRadiusGE_of_support hr2 _).add (D.f_radius.conv (hasRadiusGE_of_support hr1 _))).add
      (D.g_radius.conv (hasRadiusGE_of_support hr0 _))
  refine ⟨frobW lam mu (frobT lam mu r), fun z => powerSeriesSum c 0 z⁻¹, ?_, fun z hz hza => ?_⟩
  · have := (hcR.isBigO_pow hR fun n hn => bracketSeq_truncSeq_eq_zero hchar hne N hn).comp_tendsto
      tendsto_inv₀_cobounded
    exact this
  have hζ := D.inv_mem_ball hza
  have hbig : z⁻¹ ∈ ball (0 : ℂ) (‖z⁻¹‖ + 1) := by
    rw [mem_ball, dist_zero_right]
    linarith
  refine ⟨(hasRadiusGE_of_support hr0 _).hasDerivAt_frobW lam mu hz hbig,
    ((hasRadiusGE_of_support hr1 _).hasDerivAt_frobW lam mu hz hbig).congr_deriv ?_⟩
  -- `∑ cₙ ζⁿ = ∑ (TTr)ₙ ζⁿ + F(ζ) ∑ (Tr)ₙ ζⁿ + G(ζ) ∑ rₙ ζⁿ`
  have hsum : powerSeriesSum c 0 z⁻¹ = powerSeriesSum (frobT lam mu (frobT lam mu r)) 0 z⁻¹ +
      powerSeriesSum fc 0 z⁻¹ * powerSeriesSum (frobT lam mu r) 0 z⁻¹ +
      powerSeriesSum gc 0 z⁻¹ * powerSeriesSum r 0 z⁻¹ := by
    have h₁ := ((hasRadiusGE_of_support hr2 a⁻¹).summable hζ).hasSum
    have h₂ := hasSum_mul_powerSeriesSum (D.f_radius.summable_norm hζ)
      ((hasRadiusGE_of_support hr1 a⁻¹).summable_norm hζ)
    have h₃ := hasSum_mul_powerSeriesSum (D.g_radius.summable_norm hζ)
      ((hasRadiusGE_of_support hr0 a⁻¹).summable_norm hζ)
    refine ((h₁.add h₂).add h₃).tsum_eq ▸ ?_
    rw [powerSeriesSum]
    refine tsum_congr fun n => ?_
    simp only [hc_def, bracketSeq, Pi.add_apply, seqConv]
    ring
  rw [show rankOneTrunc fc gc lam N z = frobW lam mu r z from rfl]
  simp only [frobW]
  rw [hsum, D.f_eq z hza, D.g_eq z hza]
  ring

end Azurite.DLMF
