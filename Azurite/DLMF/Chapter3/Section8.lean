/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section10
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# DLMF §3.8(i): nonlinear equations — introduction

* 3.8.1–3.8.2: roots, zeros of multiplicity `m` (`IsZeroOfMultiplicity`; simple zeros
  `isZeroOfMultiplicity_one_iff`), and the comparison with §1.10(i)
  (`isZeroOfMultiplicity_iff_isZeroOfOrder`, `isZeroOfMultiplicity_iff_analyticOrderAt`). Fixed
  points of `φ` are the roots of `z − φ(z)` (`dlmf_3_8_2`).
* 3.8.3: convergence of order `p` (`HasConvOrder`, the index set `convIndices`): linear,
  quadratic and cubic convergence (`IsLinearConv`, `IsQuadraticConv`, `IsCubicConv`). The index
  set is closed downwards for convergent sequences (`HasConvOrder.mono`), and linear convergence
  is geometric (`IsLinearConv.tendsto`).
* Imprecisions: with the strict inequality in 3.8.3 a sequence that reaches `ζ` has no order
  (`not_mem_convIndices_const`). "The largest of the possible set of indices" need not exist: for
  `eₙ = exp(−2ⁿ/(n + 1))` every `q < 2` is an index but `2` is not (`slowSeq_hasConvOrder`,
  `slowSeq_not_two`, `dlmf_3_8_3_no_largest`).
* Local convergence of an iteration (`ConvergesLocally`). A map contracting distances to `ζ`
  converges locally, geometrically (`convergesLocally_of_contract`).
-/

open Filter Topology

namespace Azurite.DLMF

/-! ### Roots, multiplicity, fixed points (3.8.1–3.8.2) -/

section Zeros

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- **DLMF §3.8(i)**: `z₀` is a zero of `f` of multiplicity `m`:
`f(z₀) = f′(z₀) = ⋯ = f^{(m−1)}(z₀) = 0` and `f^{(m)}(z₀) ≠ 0`. -/
def IsZeroOfMultiplicity (f : 𝕜 → 𝕜) (z₀ : 𝕜) (m : ℕ) : Prop :=
  (∀ k < m, iteratedDeriv k f z₀ = 0) ∧ iteratedDeriv m f z₀ ≠ 0

/-- A simple zero (`f(z₀) = 0`, `f′(z₀) ≠ 0`) is a zero of multiplicity `1`. -/
theorem isZeroOfMultiplicity_one_iff {f : 𝕜 → 𝕜} {z₀ : 𝕜} :
    IsZeroOfMultiplicity f z₀ 1 ↔ f z₀ = 0 ∧ deriv f z₀ ≠ 0 := by
  simp [IsZeroOfMultiplicity, iteratedDeriv_one]

/-- A zero of multiplicity `m ≥ 1` is a root of 3.8.1. -/
theorem IsZeroOfMultiplicity.root {f : 𝕜 → 𝕜} {z₀ : 𝕜} {m : ℕ} (h : IsZeroOfMultiplicity f z₀ m)
    (hm : 1 ≤ m) : f z₀ = 0 := by
  simpa using h.1 0 hm

/-- Fixed points of `φ` (3.8.2) are the roots of `z − φ(z)` (3.8.1). -/
theorem dlmf_3_8_2 (φ : 𝕜 → 𝕜) (z : 𝕜) : Function.IsFixedPt φ z ↔ z - φ z = 0 := by
  rw [Function.IsFixedPt, sub_eq_zero, eq_comm]

end Zeros

/-- **DLMF §3.8(i)**, "compare §1.10(i)": for `m ≥ 1` the multiplicity agrees with the order of
the zero of §1.10(i), and for analytic `f` with Mathlib's `analyticOrderAt`. -/
theorem isZeroOfMultiplicity_iff_isZeroOfOrder {f : ℂ → ℂ} {z₀ : ℂ} {m : ℕ} (hm : 1 ≤ m) :
    IsZeroOfMultiplicity f z₀ m ↔ IsZeroOfOrder f z₀ m := by
  have hfac : ∀ k : ℕ, (k.factorial : ℂ) ≠ 0 := fun k => Nat.cast_ne_zero.mpr k.factorial_ne_zero
  simp [IsZeroOfMultiplicity, IsZeroOfOrder, hm, div_eq_zero_iff, hfac]

theorem isZeroOfMultiplicity_iff_analyticOrderAt {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    {m : ℕ} (hm : 1 ≤ m) : IsZeroOfMultiplicity f z₀ m ↔ analyticOrderAt f z₀ = m := by
  rw [isZeroOfMultiplicity_iff_isZeroOfOrder hm, isZeroOfOrder_iff_analyticOrderAt hf hm]

/-! ### Order of convergence (3.8.3) -/

section Order

variable {E : Type*} [NormedAddCommGroup E]

/-- **DLMF 3.8.3**: `|z_{n+1} − ζ| < A |zₙ − ζ|^p` for all sufficiently large `n`. -/
def HasConvOrder (z : ℕ → E) (ζ : E) (A p : ℝ) : Prop :=
  ∀ᶠ n in atTop, ‖z (n + 1) - ζ‖ < A * ‖z n - ζ‖ ^ p

/-- The set of indices `p` for which 3.8.3 holds with some `A`. -/
def convIndices (z : ℕ → E) (ζ : E) : Set ℝ := {p | ∃ A, HasConvOrder z ζ A p}

/-- Linear (geometric) convergence: 3.8.3 with `p = 1` and `A < 1`. -/
def IsLinearConv (z : ℕ → E) (ζ : E) : Prop := ∃ A < 1, HasConvOrder z ζ A 1

/-- Quadratic convergence: 3.8.3 with `p = 2`. -/
def IsQuadraticConv (z : ℕ → E) (ζ : E) : Prop := 2 ∈ convIndices z ζ

/-- Cubic convergence: 3.8.3 with `p = 3`. -/
def IsCubicConv (z : ℕ → E) (ζ : E) : Prop := 3 ∈ convIndices z ζ

/-- The set of indices is closed downwards (in `(0, ∞)`) for convergent sequences: if 3.8.3 holds
with `p` and `zₙ → ζ`, it holds with every `0 < q ≤ p` and the same `A`. -/
theorem HasConvOrder.mono {z : ℕ → E} {ζ : E} {A p q : ℝ} (h : HasConvOrder z ζ A p)
    (hz : Tendsto z atTop (𝓝 ζ)) (hq : 0 < q) (hqp : q ≤ p) : HasConvOrder z ζ A q := by
  have h1 : ∀ᶠ n in atTop, ‖z n - ζ‖ ≤ 1 := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hz).eventually (gt_mem_nhds one_pos)
    exact this.mono fun n hn => hn.le
  filter_upwards [h, h1] with n hn h1n
  have hA : 0 < A := by
    by_contra hA; push Not at hA
    have : A * ‖z n - ζ‖ ^ p ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hA (Real.rpow_nonneg (norm_nonneg _) _)
    linarith [norm_nonneg (z (n + 1) - ζ)]
  refine hn.trans_le (mul_le_mul_of_nonneg_left ?_ hA.le)
  exact Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) h1n hq.le hqp

/-- Linear convergence implies convergence, geometrically: `|zₙ − ζ| ≤ C Aⁿ`. -/
theorem IsLinearConv.tendsto {z : ℕ → E} {ζ : E} (h : IsLinearConv z ζ) :
    Tendsto z atTop (𝓝 ζ) := by
  obtain ⟨A, hA1, hA⟩ := h
  obtain ⟨N, hN⟩ := eventually_atTop.mp hA
  have hA0 : 0 ≤ A := by
    have := hN N le_rfl
    by_contra h0; push Not at h0
    have : A * ‖z N - ζ‖ ^ (1 : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h0.le (Real.rpow_nonneg (norm_nonneg _) _)
    linarith [norm_nonneg (z (N + 1) - ζ)]
  have hbound : ∀ k, ‖z (N + k) - ζ‖ ≤ A ^ k * ‖z N - ζ‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hN (N + k) (by omega)
      rw [Real.rpow_one] at this
      calc ‖z (N + (k + 1)) - ζ‖ ≤ A * ‖z (N + k) - ζ‖ := this.le
        _ ≤ A * (A ^ k * ‖z N - ζ‖) := mul_le_mul_of_nonneg_left ih hA0
        _ = A ^ (k + 1) * ‖z N - ζ‖ := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun k => A ^ k * ‖z N - ζ‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hA0 hA1).mul_const ‖z N - ζ‖
  have hg' : Tendsto (fun n => A ^ (n - N) * ‖z N - ζ‖) atTop (𝓝 0) :=
    hg.comp (tendsto_sub_atTop_nat N)
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hg'
  filter_upwards [eventually_ge_atTop N] with n hn
  have := hbound (n - N)
  rwa [Nat.add_sub_cancel' hn] at this

/-- **DLMF §3.8(i), imprecision in 3.8.3**: with the strict inequality, a sequence that reaches
`ζ` exactly has no order of convergence `p ≠ 0` at all (only the degenerate `p = 0`, where
`0⁰ = 1`). -/
theorem not_mem_convIndices_const (ζ : E) {p : ℝ} (hp : p ≠ 0) :
    p ∉ convIndices (fun _ => ζ) ζ := by
  rintro ⟨A, h⟩
  obtain ⟨n, hn⟩ := h.exists
  simp only [sub_self, norm_zero] at hn
  rw [Real.zero_rpow hp, mul_zero] at hn
  exact lt_irrefl 0 hn

end Order

/-! ### "`p` is the largest of the possible set of indices" need not exist -/

section NoLargest

/-- `eₙ = exp(−2ⁿ/(n + 1))`. -/
noncomputable def slowSeq (n : ℕ) : ℝ := Real.exp (-(2 ^ n / (n + 1)))

theorem slowSeq_pos (n : ℕ) : 0 < slowSeq n := Real.exp_pos _

theorem norm_slowSeq (n : ℕ) : ‖slowSeq n - 0‖ = slowSeq n := by
  rw [sub_zero, Real.norm_eq_abs, abs_of_pos (slowSeq_pos n)]

theorem slowSeq_rpow (n : ℕ) (q : ℝ) : slowSeq n ^ q = Real.exp (-(2 ^ n / (n + 1)) * q) := by
  rw [slowSeq, ← Real.exp_mul]

theorem tendsto_slowSeq : Tendsto slowSeq atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (2 : ℝ) ^ n / (n + 1)) atTop atTop := by
    have := (tendsto_pow_const_div_const_pow_of_one_lt 1 (one_lt_two (α := ℝ)))
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / 2 ^ n) atTop (𝓝 0) := by
      have h3 := (tendsto_pow_const_div_const_pow_of_one_lt 0 (one_lt_two (α := ℝ)))
      simpa [add_div] using (this.add h3)
    have hpos : ∀ᶠ n : ℕ in atTop, 0 < ((n : ℝ) + 1) / 2 ^ n :=
      Eventually.of_forall fun n => by positivity
    have := (tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨h2, hpos⟩))
    refine this.congr fun n => ?_
    simp [Function.comp]
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h)

/-- Every index `q < 2` works for `eₙ` (with `A = 1`). -/
theorem slowSeq_hasConvOrder {q : ℝ} (hq : q < 2) : HasConvOrder slowSeq 0 1 q := by
  unfold HasConvOrder
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 * q - 2) / (2 - q))
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [norm_slowSeq, norm_slowSeq, one_mul, slowSeq_rpow, slowSeq, Real.exp_lt_exp]
  have hn' : ((2 * q - 2) / (2 - q)) < n := hN.trans_le (by exact_mod_cast hn)
  rw [div_lt_iff₀ (by linarith)] at hn'
  have h1 : (0 : ℝ) < n + 1 := by positivity
  have h2 : (0 : ℝ) < n + 2 := by positivity
  have h3 : (0 : ℝ) < 2 ^ n := by positivity
  push_cast
  rw [pow_succ]
  rw [show -((2 : ℝ) ^ n * 2 / (n + 1 + 1)) = -((2 : ℝ) ^ n * 2 / (n + 2)) by ring]
  rw [neg_mul, neg_lt_neg_iff, div_mul_eq_mul_div, div_lt_div_iff₀ h1 h2]
  nlinarith

/-- The index `2` does not work for `eₙ`, with any `A`. -/
theorem slowSeq_not_two : 2 ∉ convIndices slowSeq 0 := by
  rintro ⟨A, hA⟩
  have h : Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1) / ((n + 1) * (n + 2))) atTop atTop := by
    have h2 := (tendsto_pow_const_div_const_pow_of_one_lt 2 (one_lt_two (α := ℝ)))
    have h3 := (tendsto_pow_const_div_const_pow_of_one_lt 1 (one_lt_two (α := ℝ)))
    have h4 := (tendsto_pow_const_div_const_pow_of_one_lt 0 (one_lt_two (α := ℝ)))
    have hs : Tendsto (fun n : ℕ => (((n : ℝ) + 1) * (n + 2)) / 2 ^ (n + 1)) atTop (𝓝 0) := by
      have := ((h2.add (h3.const_mul 3)).add (h4.const_mul 2)).div_const 2
      simp only [mul_zero, add_zero, zero_div] at this
      refine this.congr fun n => ?_
      rw [pow_succ]; field_simp; ring
    have hpos : ∀ᶠ n : ℕ in atTop, 0 < (((n : ℝ) + 1) * (n + 2)) / 2 ^ (n + 1) :=
      Eventually.of_forall fun n => by positivity
    have := (tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hs, hpos⟩))
    refine this.congr fun n => ?_
    simp [Function.comp]
  obtain ⟨n, hn1, hn2⟩ := (hA.and (h.eventually_gt_atTop A)).exists
  rw [norm_slowSeq, norm_slowSeq, slowSeq_rpow, slowSeq] at hn1
  have hle : A ≤ Real.exp ((2 : ℝ) ^ (n + 1) / ((n + 1) * (n + 2))) :=
    hn2.le.trans (by linarith [Real.add_one_le_exp ((2 : ℝ) ^ (n + 1) / ((n + 1) * (n + 2)))])
  have hA0 : 0 < A := by
    by_contra h0; push Not at h0
    have := mul_nonpos_of_nonpos_of_nonneg h0 (Real.exp_pos (-(2 ^ n / (↑n + 1)) * 2)).le
    linarith [Real.exp_pos (-((2 : ℝ) ^ (n + 1) / ((↑(n + 1) : ℝ) + 1)))]
  have key : Real.exp (-((2 : ℝ) ^ (n + 1) / ((↑(n + 1) : ℝ) + 1))) =
      Real.exp ((2 : ℝ) ^ (n + 1) / ((n + 1) * (n + 2))) *
        Real.exp (-(2 ^ n / (↑n + 1)) * 2) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [key] at hn1
  have := mul_le_mul_of_nonneg_right hle (Real.exp_pos (-(2 ^ n / (↑n + 1)) * 2)).le
  linarith

/-- **DLMF §3.8(i), imprecision**: "`p` is the largest of the possible set of indices for 3.8.3"
need not exist. For `eₙ = exp(−2ⁿ/(n + 1)) → 0`, every `q < 2` is an index but `2` is not, so
the set of indices has no largest element. -/
theorem dlmf_3_8_3_no_largest : ¬ ∃ p, IsGreatest (convIndices slowSeq 0) p := by
  rintro ⟨p, hp, hmax⟩
  rcases lt_or_ge p 2 with h | h
  · have := hmax ⟨1, slowSeq_hasConvOrder (q := (p + 2) / 2) (by linarith)⟩
    linarith
  · obtain ⟨A, hA⟩ := hp
    exact slowSeq_not_two ⟨A, hA.mono tendsto_slowSeq two_pos h⟩

end NoLargest

/-! ### Local convergence -/

section Local

variable {E : Type*} [NormedAddCommGroup E]

/-- **DLMF §3.8(i)**: the iteration `z_{n+1} = T(zₙ)` converges locally to `ζ` if `zₙ → ζ` for
every `z₀` in some neighbourhood of `ζ`. -/
def ConvergesLocally (T : E → E) (ζ : E) : Prop :=
  ∃ N ∈ 𝓝 ζ, ∀ z₀ ∈ N, Tendsto (fun n => T^[n] z₀) atTop (𝓝 ζ)

/-- A map that contracts distances to `ζ` on a ball, `|T(z) − ζ| ≤ A |z − ζ|` with `A < 1`,
converges locally to `ζ`, with `|zₙ − ζ| ≤ Aⁿ |z₀ − ζ|`. -/
theorem convergesLocally_of_contract {T : E → E} {ζ : E} {r A : ℝ} (hr : 0 < r) (hA0 : 0 ≤ A)
    (hA1 : A < 1) (hT : ∀ z ∈ Metric.ball ζ r, ‖T z - ζ‖ ≤ A * ‖z - ζ‖) :
    ConvergesLocally T ζ ∧ ∀ z₀ ∈ Metric.ball ζ r, ∀ n, ‖T^[n] z₀ - ζ‖ ≤ A ^ n * ‖z₀ - ζ‖ := by
  have hb : ∀ z₀ ∈ Metric.ball ζ r, ∀ n,
      T^[n] z₀ ∈ Metric.ball ζ r ∧ ‖T^[n] z₀ - ζ‖ ≤ A ^ n * ‖z₀ - ζ‖ := by
    intro z₀ hz n
    induction n with
    | zero => simpa using hz
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have h1 := hT _ ih.1
      have h2 : ‖T (T^[n] z₀) - ζ‖ ≤ A ^ (n + 1) * ‖z₀ - ζ‖ := by
        calc ‖T (T^[n] z₀) - ζ‖ ≤ A * ‖T^[n] z₀ - ζ‖ := h1
          _ ≤ A * (A ^ n * ‖z₀ - ζ‖) := mul_le_mul_of_nonneg_left ih.2 hA0
          _ = A ^ (n + 1) * ‖z₀ - ζ‖ := by ring
      refine ⟨?_, h2⟩
      rw [Metric.mem_ball, dist_eq_norm]
      have := Metric.mem_ball.mp ih.1
      rw [dist_eq_norm] at this
      calc ‖T (T^[n] z₀) - ζ‖ ≤ A * ‖T^[n] z₀ - ζ‖ := h1
        _ ≤ 1 * ‖T^[n] z₀ - ζ‖ := mul_le_mul_of_nonneg_right hA1.le (norm_nonneg _)
        _ < r := by linarith
  refine ⟨⟨Metric.ball ζ r, Metric.ball_mem_nhds ζ hr, fun z₀ hz => ?_⟩,
    fun z₀ hz n => (hb z₀ hz n).2⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun n => A ^ n * ‖z₀ - ζ‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hA0 hA1).mul_const ‖z₀ - ζ‖
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hb z₀ hz n).2) hg

end Local

end Azurite.DLMF
