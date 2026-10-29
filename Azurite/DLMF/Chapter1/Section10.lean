/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section9PowerSeries
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# DLMF §1.10: Functions of a Complex Variable

Formalizations of <https://dlmf.nist.gov/1.10>.

## §1.10(i) Taylor's theorem for complex variables

* 1.10.1: `dlmf_1_10_1` (Taylor expansion on `|z − z₀| < R`, `R ∈ (0, ∞]`, via Mathlib's
  `Complex.hasSum_taylorSeries_on_eball`), `dlmf_1_10_1_radius` (radius of the Taylor series
  `≥ R`, in terms of `pradius` from `Section9PowerSeries`).
* Examples: `dlmf_1_10_2` (`eᶻ`), `dlmf_1_10_3` (`ln(1 + z)`, `|z| < 1`), `dlmf_1_10_4`
  (`(1 − z)^{−α} = ∑ (α)ₙ zⁿ/n!` with `(α)ₙ = (ascPochhammer ℂ n).eval α`, from Mathlib's
  binomial series and `ringChoose_eq_ascPochhammer`).
* Zeros: `IsZeroOfOrder`, `IsSimpleZero`; `isZeroOfOrder_iff_analyticOrderAt` (agrees with
  Mathlib's `analyticOrderAt`), `isZeroOfOrder_iff_exists` (`f = (z − z₀)ᵐ g`, `g(z₀) ≠ 0`),
  `isSimpleZero_iff` (`f(z₀) = 0`, `f′(z₀) ≠ 0`).
-/

open Filter Topology Set Metric Complex
open scoped NNReal ENNReal Nat

namespace Azurite.DLMF

/-! ### §1.10(i) Taylor's theorem -/

/-- **DLMF 1.10.1** (Taylor's theorem): for `f` analytic on `|z − z₀| < R`,
`f(z) = ∑ f⁽ⁿ⁾(z₀)/n! (z − z₀)ⁿ` there (as a convergent series in DLMF's sense). -/
theorem dlmf_1_10_1 {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (eball z₀ R)) {z : ℂ} (hz : z ∈ eball z₀ R) :
    HasSum (fun n => iteratedDeriv n f z₀ / n ! * (z - z₀) ^ n) (f z) ∧
      SeriesConverges (fun n => iteratedDeriv n f z₀ / n ! * (z - z₀) ^ n) (f z) := by
  have h := Complex.hasSum_taylorSeries_on_eball hf hz
  have h' : HasSum (fun n => iteratedDeriv n f z₀ / n ! * (z - z₀) ^ n) (f z) := by
    convert h using 1
    funext n
    simp only [smul_eq_mul]
    ring
  exact ⟨h', seriesConverges_iff.mpr h'.tendsto_sum_nat⟩

/-- DLMF §1.10(i): the radius of convergence of the Taylor series is at least `R`. -/
theorem dlmf_1_10_1_radius {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (eball z₀ R)) :
    R ≤ pradius fun n => iteratedDeriv n f z₀ / n ! := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  have hz : z₀ + r ∈ eball z₀ R := by
    rw [mem_eball, edist_eq_enorm_sub, add_sub_cancel_left]
    simpa [enorm_eq_nnnorm] using hr
  have h0 := (tendsto_norm_zero.comp (dlmf_1_10_1 hf hz).2.tendsto_zero)
  refine le_pradius_of_tendsto (l := 0) ?_
  simpa only [Function.comp_def, add_sub_cancel_left, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, NNReal.abs_eq] using h0

/-- **DLMF 1.10.2**: `eᶻ = 1 + z/1! + z²/2! + ⋯`, `|z| < ∞`. -/
theorem dlmf_1_10_2 (z : ℂ) :
    HasSum (fun n => z ^ n / n !) (exp z) ∧ SeriesConverges (fun n => z ^ n / n !) (exp z) := by
  have h : HasSum (fun n => z ^ n / n !) (exp z) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  exact ⟨h, seriesConverges_iff.mpr h.tendsto_sum_nat⟩

/-- **DLMF 1.10.3**: `ln(1 + z) = z − z²/2 + z³/3 − ⋯`, `|z| < 1` (principal value). -/
theorem dlmf_1_10_3 {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (-1) ^ (n + 1) * z ^ n / n) (log (1 + z)) ∧
      SeriesConverges (fun n : ℕ => (-1) ^ (n + 1) * z ^ n / n) (log (1 + z)) :=
  ⟨hasSum_taylorSeries_log hz, seriesConverges_iff.mpr (hasSum_taylorSeries_log hz).tendsto_sum_nat⟩

theorem ringChoose_eq_ascPochhammer (α : ℂ) (n : ℕ) :
    Ring.choose (α + n - 1) n = (ascPochhammer ℂ n).eval α / n ! := by
  rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval,
    show α + n - 1 - n + 1 = α by ring, smul_eq_mul, div_eq_inv_mul]

/-- **DLMF 1.10.4**: `(1 − z)^{−α} = 1 + αz + α(α+1)/2! z² + ⋯ = ∑ (α)ₙ/n! zⁿ`, `|z| < 1`
(principal value). -/
theorem dlmf_1_10_4 (α : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => (ascPochhammer ℂ n).eval α / n ! * z ^ n) ((1 - z) ^ (-α)) ∧
      SeriesConverges (fun n => (ascPochhammer ℂ n).eval α / n ! * z ^ n) ((1 - z) ^ (-α)) := by
  have hmem : z ∈ eball (0 : ℂ) 1 := by
    rw [mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
      ← NNReal.coe_lt_coe]
    simpa using hz
  have h := (one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero α).hasSum hmem
  have h' : HasSum (fun n => (ascPochhammer ℂ n).eval α / n ! * z ^ n) ((1 - z) ^ (-α)) := by
    convert h using 1
    · funext n
      rw [FormalMultilinearSeries.ofScalars_apply_eq, ← ringChoose_eq_ascPochhammer,
        smul_eq_mul]
    · simp [cpow_neg]
  exact ⟨h', seriesConverges_iff.mpr h'.tendsto_sum_nat⟩

/-! ### Zeros -/

/-- `f` has a zero of order (multiplicity) `m ≥ 1` at `z₀`: the first nonzero coefficient of its
Taylor series at `z₀` is that of `(z − z₀)ᵐ`. -/
def IsZeroOfOrder (f : ℂ → ℂ) (z₀ : ℂ) (m : ℕ) : Prop :=
  1 ≤ m ∧ (∀ k < m, iteratedDeriv k f z₀ / k ! = 0) ∧ iteratedDeriv m f z₀ / m ! ≠ 0

/-- A simple zero is a zero of order `1`. -/
def IsSimpleZero (f : ℂ → ℂ) (z₀ : ℂ) : Prop := IsZeroOfOrder f z₀ 1

/-- DLMF §1.10(i): for analytic `f`, a zero of order `m` is a point of analytic order `m`
(Mathlib's `analyticOrderAt`). -/
theorem isZeroOfOrder_iff_analyticOrderAt {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    {m : ℕ} (hm : 1 ≤ m) : IsZeroOfOrder f z₀ m ↔ analyticOrderAt f z₀ = m := by
  have hfac : ∀ k : ℕ, (k ! : ℂ) ≠ 0 := fun k => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hiff := fun n => natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := n) hf
  simp only [IsZeroOfOrder, div_eq_zero_iff, hfac, or_false, ne_eq, div_eq_zero_iff, hm,
    true_and]
  constructor
  · rintro ⟨h0, h1⟩
    refine le_antisymm ?_ ((hiff m).mpr h0)
    by_contra hlt
    push Not at hlt
    have := (hiff (m + 1)).mp (Order.add_one_le_of_lt hlt) m (Nat.lt_succ_self m)
    exact h1 this
  · intro h
    refine ⟨(hiff m).mp h.ge, fun h0 => ?_⟩
    have : ((m + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f z₀ := (hiff (m + 1)).mpr fun i hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact (hiff m).mp h.ge i hi
      · exact h0
    rw [h] at this
    exact absurd this (by norm_cast; omega)

/-- A zero of order `m` is a factorization `f(z) = (z − z₀)ᵐ g(z)` with `g` analytic and
`g(z₀) ≠ 0`. -/
theorem isZeroOfOrder_iff_exists {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) {m : ℕ}
    (hm : 1 ≤ m) : IsZeroOfOrder f z₀ m ↔ ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ m * g z := by
  rw [isZeroOfOrder_iff_analyticOrderAt hf hm, hf.analyticOrderAt_eq_natCast]
  simp only [smul_eq_mul]

/-- DLMF §1.10(i): a zero is simple iff `f(z₀) = 0` and `f′(z₀) ≠ 0`. -/
theorem isSimpleZero_iff {f : ℂ → ℂ} {z₀ : ℂ} :
    IsSimpleZero f z₀ ↔ f z₀ = 0 ∧ deriv f z₀ ≠ 0 := by
  simp [IsSimpleZero, IsZeroOfOrder, iteratedDeriv_one]

end Azurite.DLMF
