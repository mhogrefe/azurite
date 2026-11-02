/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section1
import Azurite.DLMF.Chapter2.Section7Formal
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Analytic.Binomial

/-!
# DLMF §2.9(i): Distinct Characteristic Values — 2.9.1–2.9.3

* 2.9.1 (`IsDiffSolution`): `w(n+2) + f(n) w(n+1) + g(n) w(n) = 0`, `n = 0, 1, 2, …`.
* 2.9.2 (`dlmf_2_9_2`, `dlmf_2_9_1_iff_2_9_2`): the equivalent form
  `Δ²w(n) + (2 + f(n)) Δw(n) + (1 + f(n) + g(n)) w(n) = 0` with Mathlib's forward difference
  `Δ = fwdDiff 1` (§3.6(i)).
* 2.9.3 (`IsAsympSeqDLMF`): `f(n) ∼ ∑ fₛ/nˢ` as `n → ∞` (Poincaré, 2.1.13–2.1.14 along the
  integers).

Toolkit for the formal solutions of §2.9: `HasAsympSeries l X φ c` (`φ − ∑_{s<M} cₛ Xˢ = O(X^M)`
for every `M`, along a filter on which `X → 0`), closed under sums (`HasAsympSeries.add`,
`HasAsympSeries.sum`), products (`HasAsympSeries.mul`, Cauchy product `seqConv`), multiplication
by `Xˢ` (`HasAsympSeries.pow_mul`), with the binomial series of `(1 + kX)^β`
(`hasAsympSeries_one_add_cpow`). `IsAsympSeqDLMF f c ↔ HasAsympSeries atTop (n ↦ 1/n) f c`
(`isAsympSeqDLMF_iff`).
-/

open Filter Topology Asymptotics Finset

namespace Azurite.DLMF

/-! ### 2.9.1–2.9.2 -/

/-- **DLMF 2.9.1**: `w(n+2) + f(n) w(n+1) + g(n) w(n) = 0` for `n = 0, 1, 2, …`. -/
def IsDiffSolution (f g w : ℕ → ℂ) : Prop :=
  ∀ n, w (n + 2) + f n * w (n + 1) + g n * w n = 0

/-- **DLMF 2.9.2**: `Δ²w(n) + (2 + f(n)) Δw(n) + (1 + f(n) + g(n)) w(n)` is the left side of 2.9.1,
`Δ` the forward difference. -/
theorem dlmf_2_9_2 (f g w : ℕ → ℂ) (n : ℕ) :
    fwdDiff 1 (fwdDiff 1 w) n + (2 + f n) * fwdDiff 1 w n + (1 + f n + g n) * w n =
      w (n + 2) + f n * w (n + 1) + g n * w n := by
  rw [show n + 2 = n + 1 + 1 from rfl]
  simp only [fwdDiff]
  ring

/-- **DLMF 2.9.1 ⟺ 2.9.2**. -/
theorem dlmf_2_9_1_iff_2_9_2 (f g w : ℕ → ℂ) :
    IsDiffSolution f g w ↔ ∀ n, fwdDiff 1 (fwdDiff 1 w) n + (2 + f n) * fwdDiff 1 w n +
      (1 + f n + g n) * w n = 0 := by
  simp only [dlmf_2_9_2, IsDiffSolution]

/-! ### Asymptotic series along a filter -/

section Series

variable {α : Type*} {l : Filter α} {X : α → ℂ}

/-- `φ ∼ ∑ cₛ Xˢ`: for every `M`, `φ − ∑_{s<M} cₛ Xˢ = O(X^M)` along `l`. -/
def HasAsympSeries (l : Filter α) (X : α → ℂ) (φ : α → ℂ) (c : ℕ → ℂ) : Prop :=
  ∀ M : ℕ, (fun t => φ t - ∑ s ∈ range M, c s * X t ^ s) =O[l] fun t => X t ^ M

theorem isBigO_pow_of_le (hX : Tendsto X l (𝓝 0)) {M K : ℕ} (h : M ≤ K) :
    (fun t => X t ^ K) =O[l] fun t => X t ^ M := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hX (Metric.closedBall_mem_nhds (0 : ℂ) one_pos)] with t ht
  rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at ht
  rw [one_mul, norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) ht h

theorem isBigO_poly_one (hX : Tendsto X l (𝓝 0)) (c : ℕ → ℂ) (M : ℕ) :
    (fun t => ∑ s ∈ range M, c s * X t ^ s) =O[l] fun _ => (1 : ℂ) := by
  have h : ∀ s ∈ range M, (fun t => c s * X t ^ s) =O[l] fun _ => (1 : ℂ) := fun s _ =>
    ((isBigO_pow_of_le hX (Nat.zero_le s)).const_mul_left (c s)).congr_right fun t => pow_zero _
  exact (IsBigO.sum h).congr_left fun t => Finset.sum_apply t _ _

theorem HasAsympSeries.isBigO_one {φ : α → ℂ} {c : ℕ → ℂ} (h : HasAsympSeries l X φ c) :
    φ =O[l] fun _ => (1 : ℂ) :=
  (h 0).congr (fun t => by simp) (fun t => by simp)

theorem HasAsympSeries.congr_coeff {φ : α → ℂ} {c d : ℕ → ℂ} (h : HasAsympSeries l X φ c)
    (hcd : ∀ s, c s = d s) : HasAsympSeries l X φ d := by
  rwa [show d = c from funext fun s => (hcd s).symm]

theorem HasAsympSeries.congr_fun {φ ψ : α → ℂ} {c : ℕ → ℂ} (h : HasAsympSeries l X φ c)
    (hφψ : ∀ᶠ t in l, φ t = ψ t) : HasAsympSeries l X ψ c := fun M =>
  (h M).congr' (hφψ.mono fun t ht => by simp only [ht]) EventuallyEq.rfl

theorem HasAsympSeries.add {φ ψ : α → ℂ} {c d : ℕ → ℂ} (h₁ : HasAsympSeries l X φ c)
    (h₂ : HasAsympSeries l X ψ d) :
    HasAsympSeries l X (fun t => φ t + ψ t) (fun s => c s + d s) := fun M => by
  refine ((h₁ M).add (h₂ M)).congr_left fun t => ?_
  simp only [add_mul, sum_add_distrib]
  ring

theorem HasAsympSeries.const_mul {φ : α → ℂ} {c : ℕ → ℂ} (a : ℂ) (h : HasAsympSeries l X φ c) :
    HasAsympSeries l X (fun t => a * φ t) (fun s => a * c s) := fun M => by
  refine ((h M).const_mul_left a).congr_left fun t => ?_
  simp only [mul_sub, mul_sum, mul_assoc]

theorem HasAsympSeries.sum {ι : Type*} (S : Finset ι) {φ : ι → α → ℂ} {c : ι → ℕ → ℂ}
    (h : ∀ i ∈ S, HasAsympSeries l X (φ i) (c i)) :
    HasAsympSeries l X (fun t => ∑ i ∈ S, φ i t) (fun s => ∑ i ∈ S, c i s) := fun M => by
  have hS : ∀ i ∈ S, (fun t => φ i t - ∑ s ∈ range M, c i s * X t ^ s) =O[l]
      fun t => X t ^ M := fun i hi => h i hi M
  refine (IsBigO.sum hS).congr_left fun t => ?_
  rw [Finset.sum_apply]
  simp only [sum_sub_distrib, sum_mul]
  congr 1
  exact sum_comm

/-- The product of two truncations minus the truncated Cauchy product is the sum of the terms of
total degree `≥ M`. -/
theorem poly_mul_sub_conv (c d : ℕ → ℂ) (M : ℕ) (x : ℂ) :
    (∑ i ∈ range M, c i * x ^ i) * (∑ j ∈ range M, d j * x ^ j) -
        ∑ m ∈ range M, seqConv c d m * x ^ m =
      ∑ p ∈ (range M ×ˢ range M).filter (fun p => M ≤ p.1 + p.2),
        c p.1 * x ^ p.1 * (d p.2 * x ^ p.2) := by
  rw [sum_mul_sum, ← sum_product', ← sum_filter_add_sum_filter_not (range M ×ˢ range M)
    (fun p => M ≤ p.1 + p.2)]
  have hmaps : ∀ p ∈ (range M ×ˢ range M).filter (fun p => ¬M ≤ p.1 + p.2),
      p.1 + p.2 ∈ range M := fun p hp => by
    simp only [mem_filter, mem_product, mem_range] at hp ⊢
    omega
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ m ∈ range M, ∑ p ∈ ((range M ×ˢ range M).filter
      (fun p => ¬M ≤ p.1 + p.2)).filter (fun p => p.1 + p.2 = m),
        c p.1 * x ^ p.1 * (d p.2 * x ^ p.2) = seqConv c d m * x ^ m := by
    intro m hm
    rw [← sum_antidiagonal_mul_pow]
    refine sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [mem_filter, mem_product, mem_range, mem_antidiagonal] at hm ⊢
    omega
  rw [sum_congr rfl hfib]
  ring

theorem HasAsympSeries.mul (hX : Tendsto X l (𝓝 0)) {φ ψ : α → ℂ} {c d : ℕ → ℂ}
    (h₁ : HasAsympSeries l X φ c) (h₂ : HasAsympSeries l X ψ d) :
    HasAsympSeries l X (fun t => φ t * ψ t) (seqConv c d) := by
  intro M
  have a₁ : (fun t => (φ t - ∑ s ∈ range M, c s * X t ^ s) * ψ t) =O[l] fun t => X t ^ M :=
    ((h₁ M).mul h₂.isBigO_one).congr_right fun t => mul_one _
  have a₂ : (fun t => (∑ s ∈ range M, c s * X t ^ s) * (ψ t - ∑ s ∈ range M, d s * X t ^ s))
      =O[l] fun t => X t ^ M :=
    ((isBigO_poly_one hX c M).mul (h₂ M)).congr_right fun t => one_mul _
  have a₃ : (fun t => (∑ s ∈ range M, c s * X t ^ s) * (∑ s ∈ range M, d s * X t ^ s) -
      ∑ m ∈ range M, seqConv c d m * X t ^ m) =O[l] fun t => X t ^ M := by
    simp only [poly_mul_sub_conv]
    have hS : ∀ p ∈ (range M ×ˢ range M).filter (fun p => M ≤ p.1 + p.2),
        (fun t => c p.1 * X t ^ p.1 * (d p.2 * X t ^ p.2)) =O[l] fun t => X t ^ M := by
      intro p hp
      have hp' : M ≤ p.1 + p.2 := (mem_filter.mp hp).2
      refine ((isBigO_pow_of_le hX hp').const_mul_left (c p.1 * d p.2)).congr_left fun t => ?_
      rw [pow_add]
      ring
    exact (IsBigO.sum hS).congr_left fun t => Finset.sum_apply t _ _
  refine ((a₁.add a₂).add a₃).congr_left fun t => ?_
  ring

/-- `Xˢ ∼ Xˢ`. -/
theorem hasAsympSeries_pow (hX : Tendsto X l (𝓝 0)) (s : ℕ) :
    HasAsympSeries l X (fun t => X t ^ s) (fun d => if d = s then 1 else 0) := by
  intro M
  by_cases hs : s < M
  · refine (isBigO_zero _ _).congr_left fun t => ?_
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range, hs, ↓reduceIte, sub_self]
  · refine (isBigO_pow_of_le hX (not_lt.mp hs)).congr_left fun t => ?_
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range, hs, ↓reduceIte, sub_zero]

theorem seqConv_indicator (s : ℕ) (c : ℕ → ℂ) (d : ℕ) :
    seqConv (fun d => if d = s then 1 else 0) c d = if s ≤ d then c (d - s) else 0 := by
  rw [seqConv]
  split_ifs with h
  · rw [sum_eq_single (d - s)]
    · simp only [show d - (d - s) = s by omega, ↓reduceIte, one_mul]
    · intro j hj hne
      simp only [show d - j ≠ s by have := mem_range.mp hj; omega, ↓reduceIte, zero_mul]
    · intro hn
      exact absurd (mem_range.mpr (by omega)) hn
  · refine sum_eq_zero fun j hj => ?_
    simp only [show d - j ≠ s by have := mem_range.mp hj; omega, ↓reduceIte, zero_mul]

/-- `Xˢ φ ∼ ∑_{d ≥ s} c_{d−s} X^d`. -/
theorem HasAsympSeries.pow_mul (hX : Tendsto X l (𝓝 0)) {φ : α → ℂ} {c : ℕ → ℂ} (s : ℕ)
    (h : HasAsympSeries l X φ c) :
    HasAsympSeries l X (fun t => X t ^ s * φ t) (fun d => if s ≤ d then c (d - s) else 0) :=
  ((hasAsympSeries_pow hX s).mul hX h).congr_coeff fun d => seqConv_indicator s c d

/-- The binomial series: `(1 + kX)^β ∼ ∑ binom(β, j) kʲ Xʲ`. -/
theorem hasAsympSeries_one_add_cpow (hX : Tendsto X l (𝓝 0)) (k β : ℂ) :
    HasAsympSeries l X (fun t => (1 + k * X t) ^ β) (fun j => Ring.choose β j * k ^ j) := by
  intro M
  have h := (Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := β)).isBigO_sub_partialSum_pow M
  have hk : Tendsto (fun t => k * X t) l (𝓝 0) := by simpa using hX.const_mul k
  have h₂ := h.comp_tendsto hk
  refine (h₂.trans (IsBigO.of_bound (‖k‖ ^ M) (Eventually.of_forall fun t => ?_))).congr_left
    fun t => ?_
  · rw [Function.comp_apply, Real.norm_of_nonneg (by positivity), norm_mul, mul_pow, norm_pow]
  · simp only [Function.comp_apply, zero_add, FormalMultilinearSeries.partialSum,
      binomialSeries_apply, List.prod_ofFn, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    congr 1
    exact sum_congr rfl fun j _ => by ring

end Series

/-! ### 2.9.3 -/

/-- **DLMF 2.9.3**: `f(n) ∼ ∑_{s=0}^∞ fₛ/nˢ` as `n → ∞`: for each positive integer `M`,
`f(n) = ∑_{s<M} fₛ/nˢ + O(n^{−M})` (2.1.13–2.1.14 along the integers). -/
def IsAsympSeqDLMF (f c : ℕ → ℂ) : Prop :=
  ∀ M : ℕ, 0 < M → IsBigODLMF atTop (fun n : ℕ => f n - ∑ s ∈ range M, c s / (n : ℂ) ^ s)
    fun n => ((n : ℂ) ^ M)⁻¹

/-- `1/n → 0`. -/
theorem tendsto_natInv : Tendsto (fun n : ℕ => (n : ℂ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_nhds_zero_nat

theorem eventually_natPow_inv_ne_zero (M : ℕ) : ∀ᶠ n : ℕ in atTop, ((n : ℂ) ^ M)⁻¹ ≠ 0 := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega)))

theorem isAsympSeqDLMF_iff (f c : ℕ → ℂ) :
    IsAsympSeqDLMF f c ↔ HasAsympSeries atTop (fun n : ℕ => (n : ℂ)⁻¹) f c := by
  have e : ∀ M (n : ℕ), f n - ∑ s ∈ range M, c s / (n : ℂ) ^ s =
      f n - ∑ s ∈ range M, c s * ((n : ℂ)⁻¹) ^ s := fun M n => by
    simp only [div_eq_mul_inv, inv_pow]
  constructor
  · intro h
    have hpos : ∀ M, 0 < M → (fun n : ℕ => f n - ∑ s ∈ range M, c s * ((n : ℂ)⁻¹) ^ s)
        =O[atTop] fun n : ℕ => ((n : ℂ)⁻¹) ^ M := fun M hM => by
      have := (dlmf_2_1_3 (eventually_natPow_inv_ne_zero M)).mp (h M hM)
      simp only [e, ← inv_pow] at this
      exact this
    intro M
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · have h1 := (hpos 1 one_pos).trans (isBigO_pow_of_le tendsto_natInv (Nat.zero_le 1))
      have h2 : (fun n : ℕ => c 0 * ((n : ℂ)⁻¹) ^ 0) =O[atTop] fun n : ℕ => ((n : ℂ)⁻¹) ^ 0 :=
        (isBigO_refl _ _).const_mul_left _
      refine (h1.add h2).congr_left fun n => ?_
      simp
    · exact hpos M hM
  · intro h M hM
    refine (dlmf_2_1_3 (eventually_natPow_inv_ne_zero M)).mpr ?_
    simp only [e, ← inv_pow]
    exact h M

end Azurite.DLMF
