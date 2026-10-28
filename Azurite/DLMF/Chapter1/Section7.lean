/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section2
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# DLMF §1.7: Inequalities

Formalizations of <https://dlmf.nist.gov/1.7>, one theorem per equation, named `dlmf_1_7_N`;
statements made in the prose get suffixed names (`_eq_iff`, `_converse`, `_reverse`).
Finite sequences `a₁, …, aₙ` are functions `Fin n → ℝ`.

## §1.7(i) Finite Sums

* **Cauchy–Schwarz** 1.7.1 `dlmf_1_7_1`, via Lagrange's identity `lagrange_identity`.
  Equality case `dlmf_1_7_1_eq_iff`; converse `dlmf_1_7_1_converse`.
* **Hölder** 1.7.2 `dlmf_1_7_2` (Mathlib).  Equality case `dlmf_1_7_2_eq_iff`, from the equality
  case of the weighted AM–GM inequality; converse `dlmf_1_7_2_converse`.
* **Minkowski** 1.7.3 `dlmf_1_7_3` (Mathlib).  Equality case `dlmf_1_7_3_eq_iff`; the reversed
  inequality for `0 < p < 1`, `dlmf_1_7_3_reverse`, with its equality case
  `dlmf_1_7_3_reverse_eq_iff`.  Both equality cases come from one argument
  (`lpSum_add_eq_iff`): writing `a + b = (α + β)(λ a/α + μ b/β)`, strict convexity
  (`p > 1`) or strict concavity (`0 < p < 1`) of `t ↦ tᵖ` forces `a/α = b/β`.

DLMF states each equality case as "iff `aⱼ = c bⱼ` (resp. `aⱼᵖ = c bⱼ^q`) for all `j`".  That
fails when every `bⱼ = 0` but some `aⱼ ≠ 0`, since equality then holds trivially.  The
`_eq_iff` theorems add the alternative "`b = 0`"; the `_eq_iff_of_ne` theorems give DLMF's
wording under the hypothesis `b ≠ 0`.

## §1.7(ii) Integrals

The interval `(a, b)` has endpoints in `[−∞, +∞]` (`eIoo`), and "the integrals converge" becomes
integrability hypotheses.  Each result is first proved for an arbitrary measure.
* **Cauchy–Schwarz** 1.7.4 `dlmf_1_7_4` (general: `sq_integral_mul_le`, from
  `∫ (f − t g)² ≥ 0`).
* **Hölder** 1.7.5 `dlmf_1_7_5` (general: `integral_mul_le_and_eq_iff`, Young's inequality
  `young_rpow` applied to `f/‖f‖_p`, `g/‖g‖_q` and integrated).
* **Minkowski** 1.7.6 `dlmf_1_7_6` and its reverse for `0 < p < 1`, `dlmf_1_7_6_reverse`
  (general: `lpInt_add_le`, `lpInt_add_ge`, from `minkowski_integral_aux`, the pointwise form of
  the strict-convexity argument of §1.7(i)).
* **Equality cases** `dlmf_1_7_4_eq_iff`, `dlmf_1_7_5_eq_iff`, `dlmf_1_7_6_eq_iff`,
  `dlmf_1_7_6_reverse_eq_iff`: iff `A f = B g` (resp. `A fᵖ = B g^q`) for constants `A`, `B` not
  both zero.  DLMF says "for all `x`"; for integrable functions this holds almost everywhere on
  `(a, b)`.  For continuous `f`, `g` it holds for every `x` in `(a, b)`
  (`_eq_iff_of_continuousOn`, via `ae_eIoo_iff_forall`).

## §1.7(iii) Means

The means of §1.2(iv) (`Section2`).  `powerMean p a r` is the weighted mean `M(r)` for every real
`r`: `weightedMean` for `r ≠ 0` and the weighted geometric mean `∏ aⱼ^{pⱼ}` for `r = 0`.
* 1.7.9 `dlmf_1_7_9`, `dlmf_1_7_9_eq_iff` (`M(r) ≤ M(s)` for `r < s`; equality iff all `aⱼ`
  are equal, or `s ≤ 0` and some `aⱼ = 0`).  Proof (`powerMean_mono`): strict Jensen for
  `x ↦ x^{s/r}` when `0 < r < s` (`powerMean_le_of_pos`), weighted AM–GM against `M(0)`
  (`powerMean_zero_le`), reciprocals for negative exponents (`powerMean_neg`), zeros separately.
* 1.7.8 `dlmf_1_7_8` (`min ≤ M(r) ≤ max`, `r ≠ 0`), with `dlmf_1_7_8_eq_sup'_iff`,
  `dlmf_1_7_8_eq_inf'_iff` and DLMF's combined `dlmf_1_7_8_eq_iff`: monotonicity and the limits
  1.2.23, 1.2.24.
* 1.7.7 `dlmf_1_7_7` (`H ≤ G ≤ A`), `dlmf_1_7_7_harmMean_eq_iff`, `dlmf_1_7_7_geomMean_eq_iff`:
  1.7.9 at `r = −1, 0, 1` with equal weights (1.2.25).

## §1.7(iv) Jensen's Inequality

* 1.7.10 `dlmf_1_7_10`: `φ(∫₀¹ f) ≤ ∫₀¹ φ(f)` for `a < f < b` (`−∞ ≤ a`, `b ≤ +∞`) and `φ`
  convex on `(a, b)`, with `φ ∘ f` integrable.  Mathlib's integral Jensen needs a closed set;
  here a convex function on an open set has a supporting line (`exists_affine_le_of_convexOn`,
  slope `sup` of left difference quotients), and `∫₀¹ f ∈ (a, b)` because `f` takes values on
  both sides of its integral (`exists_mem_Icc_le_intervalIntegral`).
* 1.7.11 `dlmf_1_7_11` (`exp(∫₀¹ ln f) ≤ ∫₀¹ f`), `dlmf_1_7_11_lt` (strict unless `f` is a.e.
  constant), `dlmf_1_7_11_eq_iff`.  DLMF prints `<`, which fails for constant `f`.
-/

namespace Azurite.DLMF

open Finset Set

variable {n : ℕ}

/-! ### Cauchy–Schwarz -/

/-- **Lagrange's identity**:
`∑ᵢ ∑ⱼ (aᵢ bⱼ − aⱼ bᵢ)² = 2 ((∑ aⱼ²)(∑ bⱼ²) − (∑ aⱼ bⱼ)²)`. -/
theorem lagrange_identity (a b : Fin n → ℝ) :
    ∑ i, ∑ j, (a i * b j - a j * b i) ^ 2 =
      2 * ((∑ j, a j ^ 2) * (∑ j, b j ^ 2) - (∑ j, a j * b j) ^ 2) := by
  have h1 : ∑ i, ∑ j, a i ^ 2 * b j ^ 2 = (∑ j, a j ^ 2) * ∑ j, b j ^ 2 :=
    (sum_mul_sum _ _ _ _).symm
  have h2 : ∑ i, ∑ j, a j ^ 2 * b i ^ 2 = (∑ j, a j ^ 2) * ∑ j, b j ^ 2 := by
    rw [sum_comm]; exact h1
  have h3 : ∑ i, ∑ j, 2 * (a i * b i) * (a j * b j) = 2 * (∑ j, a j * b j) ^ 2 := by
    rw [← sum_mul_sum, ← mul_sum]; ring
  calc ∑ i, ∑ j, (a i * b j - a j * b i) ^ 2
      = ∑ i, ∑ j, (a i ^ 2 * b j ^ 2 + a j ^ 2 * b i ^ 2 - 2 * (a i * b i) * (a j * b j)) :=
        sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    _ = _ := by
        simp only [sum_add_distrib, sum_sub_distrib]
        rw [h1, h2, h3]
        ring

/-- **DLMF 1.7.1** (Cauchy–Schwarz inequality):
`(∑ aⱼ bⱼ)² ≤ (∑ aⱼ²)(∑ bⱼ²)`. -/
theorem dlmf_1_7_1 (a b : Fin n → ℝ) :
    (∑ j, a j * b j) ^ 2 ≤ (∑ j, a j ^ 2) * (∑ j, b j ^ 2) := by
  have h := lagrange_identity a b
  have h0 : 0 ≤ ∑ i, ∑ j, (a i * b j - a j * b i) ^ 2 :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _
  linarith

/-- **DLMF §1.7(i)**: equality holds in Cauchy–Schwarz iff `aⱼ = c bⱼ` for all `j`, or `b = 0`. -/
theorem dlmf_1_7_1_eq_iff (a b : Fin n → ℝ) :
    (∑ j, a j * b j) ^ 2 = (∑ j, a j ^ 2) * (∑ j, b j ^ 2) ↔
      (∃ c : ℝ, ∀ j, a j = c * b j) ∨ ∀ j, b j = 0 := by
  constructor
  · intro h
    have h0 : ∑ i, ∑ j, (a i * b j - a j * b i) ^ 2 = 0 := by
      rw [lagrange_identity, h, sub_self, mul_zero]
    have hij : ∀ i j, a i * b j = a j * b i := fun i j => by
      have hi := (sum_eq_zero_iff_of_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _).mp h0
        i (mem_univ _)
      have hj := (sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).mp hi j (mem_univ _)
      exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hj)
    by_cases hb : ∀ j, b j = 0
    · exact Or.inr hb
    · push Not at hb
      obtain ⟨k, hk⟩ := hb
      refine Or.inl ⟨a k / b k, fun j => ?_⟩
      rw [div_mul_eq_mul_div, eq_div_iff hk, hij j k]
  · rintro (⟨c, hc⟩ | hb)
    · have e1 : ∑ j, a j * b j = c * ∑ j, b j ^ 2 := by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by rw [hc]; ring
      have e2 : ∑ j, a j ^ 2 = c ^ 2 * ∑ j, b j ^ 2 := by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by rw [hc]; ring
      rw [e1, e2]; ring
    · simp [hb]

/-- **DLMF §1.7(i)**, in DLMF's wording: for `b ≠ 0`, equality holds in Cauchy–Schwarz iff
`aⱼ = c bⱼ` for all `j`. -/
theorem dlmf_1_7_1_eq_iff_of_ne {a b : Fin n → ℝ} (hb : b ≠ 0) :
    (∑ j, a j * b j) ^ 2 = (∑ j, a j ^ 2) * (∑ j, b j ^ 2) ↔ ∃ c : ℝ, ∀ j, a j = c * b j := by
  rw [dlmf_1_7_1_eq_iff, or_iff_left fun h : ∀ j, b j = 0 => hb (funext h)]

/-- **DLMF §1.7(i)** (converse of Cauchy–Schwarz): for `A, B > 0`, if `(∑ aⱼ bⱼ)² ≤ AB` for all
`b` with `∑ bⱼ² ≤ B`, then `∑ aⱼ² ≤ A`. -/
theorem dlmf_1_7_1_converse (a : Fin n → ℝ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h : ∀ b : Fin n → ℝ, ∑ j, b j ^ 2 ≤ B → (∑ j, a j * b j) ^ 2 ≤ A * B) :
    ∑ j, a j ^ 2 ≤ A := by
  set S := ∑ j, a j ^ 2 with hS
  have hS0 : 0 ≤ S := sum_nonneg fun j _ => sq_nonneg _
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact hA.le
  set t := √(B / S)
  have ht : t ^ 2 = B / S := Real.sq_sqrt (div_nonneg hB.le hS0)
  have e1 : ∑ j, (t * a j) ^ 2 = t ^ 2 * S := by
    rw [hS, mul_sum]; exact sum_congr rfl fun j _ => by ring
  have e2 : ∑ j, a j * (t * a j) = t * S := by
    rw [hS, mul_sum]; exact sum_congr rfl fun j _ => by ring
  have key := h (fun j => t * a j) (by
    rw [e1, ht, div_mul_cancel₀ _ hpos.ne'])
  rw [e2, mul_pow, ht, sq, ← mul_assoc, div_mul_cancel₀ _ hpos.ne'] at key
  nlinarith

/-! ### Hölder -/

theorem holderConjugate_of_one_div {p q : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) :
    p.HolderConjugate q :=
  Real.holderConjugate_iff.mpr ⟨hp, by simpa [one_div] using hpq⟩

/-- **DLMF 1.7.2** (Hölder's inequality): for `p > 1`, `1/p + 1/q = 1`, `aⱼ, bⱼ ≥ 0`,
`∑ aⱼ bⱼ ≤ (∑ aⱼᵖ)^{1/p} (∑ bⱼ^q)^{1/q}`. -/
theorem dlmf_1_7_2 {p q : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) {a b : Fin n → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    ∑ j, a j * b j ≤ (∑ j, a j ^ p) ^ (1 / p) * (∑ j, b j ^ q) ^ (1 / q) :=
  Real.inner_le_Lp_mul_Lq_of_nonneg univ (holderConjugate_of_one_div hp hpq)
    (fun j _ => ha j) (fun j _ => hb j)

theorem sum_rpow_nonneg {p : ℝ} {a : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) : 0 ≤ ∑ j, a j ^ p :=
  sum_nonneg fun j _ => Real.rpow_nonneg (ha j) p

theorem sum_rpow_eq_zero_iff {p : ℝ} (hp : p ≠ 0) {a : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) :
    ∑ j, a j ^ p = 0 ↔ ∀ j, a j = 0 := by
  rw [sum_eq_zero_iff_of_nonneg fun j _ => Real.rpow_nonneg (ha j) p]
  simp [Real.rpow_eq_zero (ha _) hp]

/-- **DLMF §1.7(i)**: for `p > 1`, `1/p + 1/q = 1`, `aⱼ, bⱼ ≥ 0`, equality holds in Hölder's
inequality iff `aⱼᵖ = c bⱼ^q` for all `j`, or `b = 0`. -/
theorem dlmf_1_7_2_eq_iff {p q : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) {a b : Fin n → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    ∑ j, a j * b j = (∑ j, a j ^ p) ^ (1 / p) * (∑ j, b j ^ q) ^ (1 / q) ↔
      (∃ c : ℝ, ∀ j, a j ^ p = c * b j ^ q) ∨ ∀ j, b j = 0 := by
  have hpqc := holderConjugate_of_one_div hp hpq
  have hp0 : 0 < p := hpqc.pos
  have hq0 : 0 < q := hpqc.symm.pos
  have h1p : 0 < 1 / p := one_div_pos.mpr hp0
  have h1q : 0 < 1 / q := one_div_pos.mpr hq0
  set S := ∑ j, a j ^ p with hS
  set T := ∑ j, b j ^ q with hT
  have hS0 : 0 ≤ S := sum_rpow_nonneg ha
  have hT0 : 0 ≤ T := sum_rpow_nonneg hb
  rcases hT0.eq_or_lt with hT' | hTpos
  · have hb0 : ∀ j, b j = 0 := (sum_rpow_eq_zero_iff hq0.ne' hb).mp hT'.symm
    refine iff_of_true ?_ (Or.inr hb0)
    rw [← hT', Real.zero_rpow h1q.ne', mul_zero]
    simp [hb0]
  rcases hS0.eq_or_lt with hS' | hSpos
  · have ha0 : ∀ j, a j = 0 := (sum_rpow_eq_zero_iff hp0.ne' ha).mp hS'.symm
    refine iff_of_true ?_ (Or.inl ⟨0, fun j => by simp [ha0, Real.zero_rpow hp0.ne']⟩)
    rw [← hS', Real.zero_rpow h1p.ne', zero_mul]
    simp [ha0]
  set α := S ^ (1 / p)
  set β := T ^ (1 / q)
  have hα : 0 < α := Real.rpow_pos_of_pos hSpos _
  have hβ : 0 < β := Real.rpow_pos_of_pos hTpos _
  set X : Fin n → ℝ := fun j => a j ^ p / S
  set Y : Fin n → ℝ := fun j => b j ^ q / T
  have hX0 : ∀ j, 0 ≤ X j := fun j => div_nonneg (Real.rpow_nonneg (ha j) _) hS0
  have hY0 : ∀ j, 0 ≤ Y j := fun j => div_nonneg (Real.rpow_nonneg (hb j) _) hT0
  have hXY : ∀ j, X j ^ (1 / p) * Y j ^ (1 / q) = a j * b j / (α * β) := by
    intro j
    simp only [X, Y]
    rw [Real.div_rpow (Real.rpow_nonneg (ha j) _) hS0, Real.div_rpow (Real.rpow_nonneg (hb j) _)
      hT0, ← Real.rpow_mul (ha j), ← Real.rpow_mul (hb j), mul_one_div_cancel hp0.ne',
      mul_one_div_cancel hq0.ne', Real.rpow_one, Real.rpow_one, div_mul_div_comm]
  have hsumX : ∑ j, X j = 1 := by
    simp only [X]; rw [← sum_div, ← hS, div_self hSpos.ne']
  have hsumY : ∑ j, Y j = 1 := by
    simp only [Y]; rw [← sum_div, ← hT, div_self hTpos.ne']
  set d : Fin n → ℝ := fun j => 1 / p * X j + 1 / q * Y j - X j ^ (1 / p) * Y j ^ (1 / q)
  have hd0 : ∀ j, 0 ≤ d j := fun j => sub_nonneg.mpr
    (Real.geom_mean_le_arith_mean2_weighted h1p.le h1q.le (hX0 j) (hY0 j) hpq)
  have hsumd : ∑ j, d j = 1 - (∑ j, a j * b j) / (α * β) := by
    simp only [d, sum_sub_distrib, sum_add_distrib, ← mul_sum, hsumX, hsumY, hXY, ← sum_div]
    linear_combination hpq
  have hdeq : ∀ j, d j = 0 ↔ X j = Y j := fun j => by
    rw [← Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos h1p h1q (hX0 j) (hY0 j) hpq]
    simp only [d]
    constructor <;> intro h <;> linarith
  constructor
  · intro h
    have hsum0 : ∑ j, d j = 0 := by
      rw [hsumd, h, div_self (mul_pos hα hβ).ne', sub_self]
    have hdj := (sum_eq_zero_iff_of_nonneg fun j _ => hd0 j).mp hsum0
    refine Or.inl ⟨S / T, fun j => ?_⟩
    have hXYj := (hdeq j).mp (hdj j (mem_univ _))
    simp only [X, Y] at hXYj
    rw [div_eq_div_iff hSpos.ne' hTpos.ne'] at hXYj
    rw [div_mul_eq_mul_div, eq_div_iff hTpos.ne']
    linear_combination hXYj
  · rintro (⟨c, hc⟩ | hb0)
    · have hcT : S = c * T := by
        rw [hS, hT, mul_sum]; exact sum_congr rfl fun j _ => hc j
      have hc0 : c ≠ 0 := by
        rintro rfl; rw [zero_mul] at hcT; exact hSpos.ne' hcT
      have hsum0 : ∑ j, d j = 0 := sum_eq_zero fun j _ => (hdeq j).mpr (by
        simp only [X, Y]; rw [hc j, hcT, mul_div_mul_left _ _ hc0])
      rw [hsumd, sub_eq_zero, eq_comm, div_eq_one_iff_eq (mul_pos hα hβ).ne'] at hsum0
      exact hsum0
    · have : T = 0 := by
        rw [hT]; simp [hb0, Real.zero_rpow hq0.ne']
      exact absurd this hTpos.ne'

/-- **DLMF §1.7(i)**, in DLMF's wording: for `b ≠ 0`, equality holds in Hölder's inequality iff
`aⱼᵖ = c bⱼ^q` for all `j`. -/
theorem dlmf_1_7_2_eq_iff_of_ne {p q : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1)
    {a b : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (hb' : b ≠ 0) :
    ∑ j, a j * b j = (∑ j, a j ^ p) ^ (1 / p) * (∑ j, b j ^ q) ^ (1 / q) ↔
      ∃ c : ℝ, ∀ j, a j ^ p = c * b j ^ q := by
  rw [dlmf_1_7_2_eq_iff hp hpq ha hb, or_iff_left fun h : ∀ j, b j = 0 => hb' (funext h)]

/-- **DLMF §1.7(i)** (converse of Hölder): for `p > 1`, `1/p + 1/q = 1`, `aⱼ ≥ 0` and
`A, B > 0`, if `∑ aⱼ bⱼ ≤ A^{1/p} B^{1/q}` for all `bⱼ ≥ 0` with `∑ bⱼ^q ≤ B`, then
`∑ aⱼᵖ ≤ A`. -/
theorem dlmf_1_7_2_converse {p q : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1)
    {a : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h : ∀ b : Fin n → ℝ, (∀ j, 0 ≤ b j) → ∑ j, b j ^ q ≤ B →
      ∑ j, a j * b j ≤ A ^ (1 / p) * B ^ (1 / q)) :
    ∑ j, a j ^ p ≤ A := by
  have hpqc := holderConjugate_of_one_div hp hpq
  have hp0 : 0 < p := hpqc.pos
  have hq0 : 0 < q := hpqc.symm.pos
  set S := ∑ j, a j ^ p with hS
  rcases (show 0 ≤ S from sum_rpow_nonneg ha).eq_or_lt with h0 | hSpos
  · rw [← h0]; exact hA.le
  have hBS : 0 ≤ B / S := div_nonneg hB.le hSpos.le
  set t := (B / S) ^ (1 / q)
  have ht : 0 ≤ t := Real.rpow_nonneg hBS _
  set b : Fin n → ℝ := fun j => t * a j ^ (p - 1)
  have hb0 : ∀ j, 0 ≤ b j := fun j => mul_nonneg ht (Real.rpow_nonneg (ha j) _)
  have hbq : ∀ j, b j ^ q = B / S * a j ^ p := fun j => by
    simp only [b]
    rw [Real.mul_rpow ht (Real.rpow_nonneg (ha j) _), ← Real.rpow_mul hBS,
      one_div_mul_cancel hq0.ne', Real.rpow_one, ← Real.rpow_mul (ha j), hpqc.sub_one_mul_conj]
  have hab : ∀ j, a j * b j = t * a j ^ p := fun j => by
    have e : a j ^ p = a j ^ (p - 1) * a j := by
      rw [← Real.rpow_add_one' (ha j) (by rw [sub_add_cancel]; exact hp0.ne'), sub_add_cancel]
    simp only [b]; rw [e]; ring
  have hbB : ∑ j, b j ^ q = B := by
    rw [sum_congr rfl fun j _ => hbq j, ← mul_sum, ← hS, div_mul_cancel₀ _ hSpos.ne']
  have key := h b hb0 hbB.le
  rw [sum_congr rfl fun j _ => hab j, ← mul_sum, ← hS] at key
  have hsplit : S = S ^ (1 / p) * S ^ (1 / q) := by
    rw [← Real.rpow_add hSpos, hpq, Real.rpow_one]
  have htS : t * S = B ^ (1 / q) * S ^ (1 / p) := by
    have hq' : 0 < S ^ (1 / q) := Real.rpow_pos_of_pos hSpos _
    calc t * S = B ^ (1 / q) / S ^ (1 / q) * (S ^ (1 / p) * S ^ (1 / q)) := by
          rw [← hsplit, show t = (B / S) ^ (1 / q) from rfl, Real.div_rpow hB.le hSpos.le]
      _ = B ^ (1 / q) * S ^ (1 / p) := by field_simp
  rw [htS] at key
  have hBq : 0 < B ^ (1 / q) := Real.rpow_pos_of_pos hB _
  have hle : S ^ (1 / p) ≤ A ^ (1 / p) := by nlinarith
  exact (Real.rpow_le_rpow_iff hSpos.le hA.le (one_div_pos.mpr hp0)).mp hle

/-! ### Minkowski -/

/-- **DLMF 1.7.3** (Minkowski's inequality): for `p > 1`, `aⱼ, bⱼ ≥ 0`,
`(∑ (aⱼ + bⱼ)ᵖ)^{1/p} ≤ (∑ aⱼᵖ)^{1/p} + (∑ bⱼᵖ)^{1/p}`. -/
theorem dlmf_1_7_3 {p : ℝ} (hp : 1 < p) {a b : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hb : ∀ j, 0 ≤ b j) :
    (∑ j, (a j + b j) ^ p) ^ (1 / p) ≤ (∑ j, a j ^ p) ^ (1 / p) + (∑ j, b j ^ p) ^ (1 / p) :=
  Real.Lp_add_le_of_nonneg univ hp.le (fun j _ => ha j) (fun j _ => hb j)

/-- `(∑ aⱼᵖ)^{1/p}`. -/
noncomputable def lpSum (p : ℝ) (a : Fin n → ℝ) : ℝ := (∑ j, a j ^ p) ^ (1 / p)

theorem lpSum_nonneg {p : ℝ} {a : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) : 0 ≤ lpSum p a :=
  Real.rpow_nonneg (sum_rpow_nonneg ha) _

theorem rpow_one_div_eq_iff {x y p : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : 0 < p) :
    x ^ (1 / p) = y ↔ x = y ^ p := by
  constructor
  · rintro rfl; rw [← Real.rpow_mul hx, one_div_mul_cancel hp.ne', Real.rpow_one]
  · rintro rfl; rw [← Real.rpow_mul hy, mul_one_div_cancel hp.ne', Real.rpow_one]

theorem lpSum_rpow {p : ℝ} (hp : 0 < p) {a : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) :
    lpSum p a ^ p = ∑ j, a j ^ p := by
  rw [lpSum, ← Real.rpow_mul (sum_rpow_nonneg ha), one_div_mul_cancel hp.ne', Real.rpow_one]

theorem lpSum_eq_zero_iff {p : ℝ} (hp : 0 < p) {a : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) :
    lpSum p a = 0 ↔ ∀ j, a j = 0 := by
  rw [lpSum, rpow_one_div_eq_iff (sum_rpow_nonneg ha) le_rfl hp, Real.zero_rpow hp.ne',
    sum_rpow_eq_zero_iff hp.ne' ha]

theorem sum_div_lpSum_rpow {p : ℝ} (hp : 0 < p) {a : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hα : 0 < lpSum p a) : ∑ j, (a j / lpSum p a) ^ p = 1 := by
  rw [sum_congr rfl fun j _ => Real.div_rpow (ha j) hα.le p, ← sum_div, ← lpSum_rpow hp ha,
    div_self (Real.rpow_pos_of_pos hα p).ne']

theorem lpSum_const_mul {p : ℝ} (hp : 0 < p) {c : ℝ} (hc : 0 ≤ c) {b : Fin n → ℝ}
    (hb : ∀ j, 0 ≤ b j) : lpSum p (fun j => c * b j) = c * lpSum p b := by
  simp only [lpSum]
  rw [sum_congr rfl fun j _ => Real.mul_rpow hc (hb j), ← mul_sum,
    Real.mul_rpow (Real.rpow_nonneg hc p) (sum_rpow_nonneg hb), ← Real.rpow_mul hc,
    mul_one_div_cancel hp.ne', Real.rpow_one]

/-- Jensen for a strictly convex function, termwise, with its equality case. -/
theorem sum_strictConvexOn {g : ℝ → ℝ} (hg : StrictConvexOn ℝ (Ici 0) g) {u v : Fin n → ℝ}
    (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) {l m : ℝ} (hl : 0 < l) (hm : 0 < m)
    (hlm : l + m = 1) :
    ∑ j, g (l * u j + m * v j) ≤ ∑ j, (l * g (u j) + m * g (v j)) ∧
      (∑ j, g (l * u j + m * v j) = ∑ j, (l * g (u j) + m * g (v j)) ↔ ∀ j, u j = v j) := by
  have hle : ∀ j, g (l * u j + m * v j) ≤ l * g (u j) + m * g (v j) := fun j =>
    hg.convexOn.2 (hu j) (hv j) hl.le hm.le hlm
  refine ⟨sum_le_sum fun j _ => hle j, ?_⟩
  rw [sum_eq_sum_iff_of_le fun j _ => hle j]
  refine ⟨fun h j => ?_, fun h j _ => ?_⟩
  · by_contra hne
    exact (hg.2 (hu j) (hv j) hne hl hm hlm).ne (h j (mem_univ _))
  · simp only [h j, ← add_mul, hlm, one_mul]

/-- The core of Minkowski's inequality and its reverse: if `x ↦ σ xᵖ` is strictly convex then
`σ ∑ (aⱼ + bⱼ)ᵖ ≤ σ (α + β)ᵖ`, with equality iff `a/α = b/β`. -/
theorem minkowski_aux {p σ : ℝ} (hp : 0 < p) (hσ : σ ≠ 0)
    (hg : StrictConvexOn ℝ (Ici 0) fun x : ℝ => σ * x ^ p) {a b : Fin n → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (hα : 0 < lpSum p a) (hβ : 0 < lpSum p b) :
    σ * ∑ j, (a j + b j) ^ p ≤ σ * (lpSum p a + lpSum p b) ^ p ∧
      (∑ j, (a j + b j) ^ p = (lpSum p a + lpSum p b) ^ p ↔
        ∀ j, a j / lpSum p a = b j / lpSum p b) := by
  set α := lpSum p a
  set β := lpSum p b
  have hαβ : 0 < α + β := add_pos hα hβ
  set l := α / (α + β)
  set m := β / (α + β)
  have hl : 0 < l := div_pos hα hαβ
  have hm : 0 < m := div_pos hβ hαβ
  have hlm : l + m = 1 := by simp only [l, m]; rw [← add_div, div_self hαβ.ne']
  set u : Fin n → ℝ := fun j => a j / α
  set v : Fin n → ℝ := fun j => b j / β
  have hu : ∀ j, 0 ≤ u j := fun j => div_nonneg (ha j) hα.le
  have hv : ∀ j, 0 ≤ v j := fun j => div_nonneg (hb j) hβ.le
  have hsu : ∑ j, u j ^ p = 1 := sum_div_lpSum_rpow hp ha hα
  have hsv : ∑ j, v j ^ p = 1 := sum_div_lpSum_rpow hp hb hβ
  have hpow : 0 < (α + β) ^ p := Real.rpow_pos_of_pos hαβ p
  have hdec : ∑ j, (a j + b j) ^ p = (α + β) ^ p * ∑ j, (l * u j + m * v j) ^ p := by
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    have e : l * u j + m * v j = (a j + b j) / (α + β) := by
      simp only [l, m, u, v]; field_simp
    rw [e, Real.div_rpow (add_nonneg (ha j) (hb j)) hαβ.le, mul_div_cancel₀ _ hpow.ne']
  obtain ⟨hle, heq⟩ := sum_strictConvexOn hg hu hv hl hm hlm
  simp only [sum_add_distrib, ← mul_sum, hsu, hsv] at hle heq
  have hmid : l * (σ * 1) + m * (σ * 1) = σ := by linear_combination σ * hlm
  rw [hmid] at hle heq
  set W := ∑ j, (l * u j + m * v j) ^ p
  refine ⟨?_, ?_⟩
  · rw [hdec]
    calc σ * ((α + β) ^ p * W) = (α + β) ^ p * (σ * W) := by ring
      _ ≤ (α + β) ^ p * σ := mul_le_mul_of_nonneg_left hle hpow.le
      _ = σ * (α + β) ^ p := by ring
  · have hc : (α + β) ^ p * W = (α + β) ^ p ↔ σ * W = σ := by
      constructor <;> intro h
      · rw [mul_left_cancel₀ hpow.ne' (h.trans (mul_one _).symm), mul_one]
      · rw [mul_left_cancel₀ hσ (h.trans (mul_one _).symm), mul_one]
    rw [hdec, hc, heq]

/-- Equality in Minkowski's inequality or its reverse. -/
theorem lpSum_add_eq_iff {p σ : ℝ} (hp : 0 < p) (hσ : σ ≠ 0)
    (hg : StrictConvexOn ℝ (Ici 0) fun x : ℝ => σ * x ^ p) {a b : Fin n → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    lpSum p (fun j => a j + b j) = lpSum p a + lpSum p b ↔
      (∃ c : ℝ, ∀ j, a j = c * b j) ∨ ∀ j, b j = 0 := by
  by_cases hb0 : ∀ j, b j = 0
  · refine iff_of_true ?_ (Or.inr hb0)
    rw [(lpSum_eq_zero_iff hp hb).mpr hb0, add_zero]
    congr 1; funext j; simp [hb0]
  by_cases ha0 : ∀ j, a j = 0
  · refine iff_of_true ?_ (Or.inl ⟨0, fun j => by simp [ha0]⟩)
    rw [(lpSum_eq_zero_iff hp ha).mpr ha0, zero_add]
    congr 1; funext j; simp [ha0]
  have hα : 0 < lpSum p a := (lpSum_nonneg ha).lt_of_ne fun h =>
    ha0 ((lpSum_eq_zero_iff hp ha).mp h.symm)
  have hβ : 0 < lpSum p b := (lpSum_nonneg hb).lt_of_ne fun h =>
    hb0 ((lpSum_eq_zero_iff hp hb).mp h.symm)
  rw [show lpSum p (fun j => a j + b j) = (∑ j, (a j + b j) ^ p) ^ (1 / p) from rfl,
    rpow_one_div_eq_iff (sum_rpow_nonneg fun j => add_nonneg (ha j) (hb j))
      (add_pos hα hβ).le hp, (minkowski_aux hp hσ hg ha hb hα hβ).2]
  constructor
  · intro h
    refine Or.inl ⟨lpSum p a / lpSum p b, fun j => ?_⟩
    have e := h j
    rw [div_eq_div_iff hα.ne' hβ.ne'] at e
    rw [div_mul_eq_mul_div, eq_div_iff hβ.ne']
    linear_combination e
  · rintro (⟨c, hc⟩ | hb0')
    · push Not at hb0
      obtain ⟨k, hk⟩ := hb0
      have hbk : 0 < b k := (hb k).lt_of_ne' hk
      have hc0 : 0 ≤ c := by
        have := ha k
        rw [hc k] at this
        by_contra hneg
        push Not at hneg
        nlinarith
      have hαc : lpSum p a = c * lpSum p b := by
        rw [show a = fun j => c * b j from funext hc]; exact lpSum_const_mul hp hc0 hb
      have hcpos : c ≠ 0 := by
        rintro rfl; rw [zero_mul] at hαc; exact hα.ne' hαc
      intro j
      rw [hc j, hαc, mul_div_mul_left _ _ hcpos]
    · exact absurd hb0' hb0

/-- **DLMF §1.7(i)**: for `p > 1`, `aⱼ, bⱼ ≥ 0`, equality holds in Minkowski's inequality iff
`aⱼ = c bⱼ` for all `j`, or `b = 0`. -/
theorem dlmf_1_7_3_eq_iff {p : ℝ} (hp : 1 < p) {a b : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hb : ∀ j, 0 ≤ b j) :
    (∑ j, (a j + b j) ^ p) ^ (1 / p) = (∑ j, a j ^ p) ^ (1 / p) + (∑ j, b j ^ p) ^ (1 / p) ↔
      (∃ c : ℝ, ∀ j, a j = c * b j) ∨ ∀ j, b j = 0 :=
  lpSum_add_eq_iff (by linarith) one_ne_zero (by simpa using strictConvexOn_rpow hp) ha hb

/-- **DLMF §1.7(i)**, in DLMF's wording: for `p > 1`, `aⱼ, bⱼ ≥ 0` and `b ≠ 0`, equality holds
in Minkowski's inequality iff `aⱼ = c bⱼ` for all `j`. -/
theorem dlmf_1_7_3_eq_iff_of_ne {p : ℝ} (hp : 1 < p) {a b : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hb : ∀ j, 0 ≤ b j) (hb' : b ≠ 0) :
    (∑ j, (a j + b j) ^ p) ^ (1 / p) = (∑ j, a j ^ p) ^ (1 / p) + (∑ j, b j ^ p) ^ (1 / p) ↔
      ∃ c : ℝ, ∀ j, a j = c * b j := by
  rw [dlmf_1_7_3_eq_iff hp ha hb, or_iff_left fun h : ∀ j, b j = 0 => hb' (funext h)]

theorem strictConvexOn_neg_rpow {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    StrictConvexOn ℝ (Ici 0) fun x : ℝ => -1 * x ^ p := by
  convert (Real.strictConcaveOn_rpow hp0 hp1).neg using 1
  funext x
  simp

/-- **DLMF §1.7(i)** (reverse Minkowski): for `0 < p < 1`, `aⱼ, bⱼ ≥ 0`,
`(∑ (aⱼ + bⱼ)ᵖ)^{1/p} ≥ (∑ aⱼᵖ)^{1/p} + (∑ bⱼᵖ)^{1/p}`. -/
theorem dlmf_1_7_3_reverse {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {a b : Fin n → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    (∑ j, a j ^ p) ^ (1 / p) + (∑ j, b j ^ p) ^ (1 / p) ≤ (∑ j, (a j + b j) ^ p) ^ (1 / p) := by
  show lpSum p a + lpSum p b ≤ lpSum p fun j => a j + b j
  rcases (lpSum_nonneg ha).eq_or_lt with hα | hα
  · have ha0 := (lpSum_eq_zero_iff hp0 ha).mp hα.symm
    rw [← hα, zero_add]
    exact le_of_eq (by congr 1; funext j; simp [ha0])
  rcases (lpSum_nonneg hb).eq_or_lt with hβ | hβ
  · have hb0 := (lpSum_eq_zero_iff hp0 hb).mp hβ.symm
    rw [← hβ, add_zero]
    exact le_of_eq (by congr 1; funext j; simp [hb0])
  have h := (minkowski_aux hp0 (by norm_num) (strictConvexOn_neg_rpow hp0 hp1) ha hb hα hβ).1
  have h' : (lpSum p a + lpSum p b) ^ p ≤ ∑ j, (a j + b j) ^ p := by linarith
  have hαβ : 0 ≤ lpSum p a + lpSum p b := (add_pos hα hβ).le
  calc lpSum p a + lpSum p b = ((lpSum p a + lpSum p b) ^ p) ^ (1 / p) := by
        rw [← Real.rpow_mul hαβ, mul_one_div_cancel hp0.ne', Real.rpow_one]
    _ ≤ (∑ j, (a j + b j) ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hαβ _) h' (one_div_pos.mpr hp0).le

/-- **DLMF §1.7(i)**: for `0 < p < 1`, `aⱼ, bⱼ ≥ 0`, equality holds in the reverse Minkowski
inequality iff `aⱼ = c bⱼ` for all `j`, or `b = 0`. -/
theorem dlmf_1_7_3_reverse_eq_iff {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {a b : Fin n → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    (∑ j, (a j + b j) ^ p) ^ (1 / p) = (∑ j, a j ^ p) ^ (1 / p) + (∑ j, b j ^ p) ^ (1 / p) ↔
      (∃ c : ℝ, ∀ j, a j = c * b j) ∨ ∀ j, b j = 0 :=
  lpSum_add_eq_iff hp0 (by norm_num) (strictConvexOn_neg_rpow hp0 hp1) ha hb

/-- **DLMF §1.7(i)**, in DLMF's wording: for `0 < p < 1`, `aⱼ, bⱼ ≥ 0` and `b ≠ 0`, equality
holds in the reverse Minkowski inequality iff `aⱼ = c bⱼ` for all `j`. -/
theorem dlmf_1_7_3_reverse_eq_iff_of_ne {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {a b : Fin n → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (hb' : b ≠ 0) :
    (∑ j, (a j + b j) ^ p) ^ (1 / p) = (∑ j, a j ^ p) ^ (1 / p) + (∑ j, b j ^ p) ^ (1 / p) ↔
      ∃ c : ℝ, ∀ j, a j = c * b j := by
  rw [dlmf_1_7_3_reverse_eq_iff hp0 hp1 ha hb, or_iff_left fun h : ∀ j, b j = 0 => hb' (funext h)]

/-! ### Integrals: Cauchy–Schwarz -/

section Integrals

open MeasureTheory Filter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}

theorem integrable_mul_of_integrable_sq (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) : Integrable (fun x => f x * g x) μ :=
  Integrable.mono' ((hf2.add hg2).div_const 2) (hf.mul hg) (ae_of_all _ fun x => by
    show ‖f x * g x‖ ≤ (f x ^ 2 + g x ^ 2) / 2
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)])

theorem integrable_sub_mul_sq (hfg : Integrable (fun x => f x * g x) μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hg2 : Integrable (fun x => g x ^ 2) μ) (t : ℝ) :
    Integrable (fun x => (f x - t * g x) ^ 2) μ :=
  ((hf2.sub (hfg.const_mul (2 * t))).add (hg2.const_mul (t ^ 2))).congr
    (ae_of_all _ fun x => by simp only [Pi.add_apply, Pi.sub_apply]; ring)

theorem integral_sub_mul_sq (hfg : Integrable (fun x => f x * g x) μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hg2 : Integrable (fun x => g x ^ 2) μ) (t : ℝ) :
    ∫ x, (f x - t * g x) ^ 2 ∂μ =
      ∫ x, f x ^ 2 ∂μ - 2 * t * ∫ x, f x * g x ∂μ + t ^ 2 * ∫ x, g x ^ 2 ∂μ := by
  have e : ∀ x, (f x - t * g x) ^ 2 = f x ^ 2 - 2 * t * (f x * g x) + t ^ 2 * g x ^ 2 :=
    fun x => by ring
  simp_rw [e]
  have h1 : Integrable (fun x => f x ^ 2 - 2 * t * (f x * g x)) μ := hf2.sub (hfg.const_mul _)
  have h2 : Integrable (fun x => t ^ 2 * g x ^ 2) μ := hg2.const_mul _
  have h3 : Integrable (fun x => 2 * t * (f x * g x)) μ := hfg.const_mul _
  rw [integral_add h1 h2, integral_sub hf2 h3, integral_const_mul, integral_const_mul]

theorem ae_eq_zero_of_integral_sq_eq_zero (hf2 : Integrable (fun x => f x ^ 2) μ)
    (h : ∫ x, f x ^ 2 ∂μ = 0) : ∀ᵐ x ∂μ, f x = 0 := by
  have := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x)) hf2).mp h
  filter_upwards [this] with x hx
  simpa using hx

/-- The Cauchy–Schwarz inequality for integrals against any measure. -/
theorem sq_integral_mul_le (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hg2 : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have hfg := integrable_mul_of_integrable_sq hf hg hf2 hg2
  set F := ∫ x, f x ^ 2 ∂μ
  set G := ∫ x, g x ^ 2 ∂μ
  set P := ∫ x, f x * g x ∂μ
  have hG0 : 0 ≤ G := integral_nonneg fun x => sq_nonneg _
  rcases hG0.eq_or_lt with hG | hG
  · have hg0 := ae_eq_zero_of_integral_sq_eq_zero hg2 hG.symm
    have hP : P = 0 := integral_eq_zero_of_ae (by filter_upwards [hg0] with x hx; simp [hx])
    rw [hP, ← hG]; simp
  have h := integral_sub_mul_sq hfg hf2 hg2 (P / G)
  have h0 : 0 ≤ ∫ x, (f x - P / G * g x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have key : F - 2 * (P / G) * P + (P / G) ^ 2 * G = F - P ^ 2 / G := by
    field_simp; ring
  rw [h, key] at h0
  have := (div_le_iff₀ hG).mp (by linarith : P ^ 2 / G ≤ F)
  linarith

/-- Equality in the Cauchy–Schwarz inequality for integrals: iff `A f = B g` almost everywhere
for constants `A`, `B` not both zero. -/
theorem sq_integral_mul_eq_iff (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hg2 : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 = (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ᵐ x ∂μ, A * f x = B * g x := by
  have hfg := integrable_mul_of_integrable_sq hf hg hf2 hg2
  set F := ∫ x, f x ^ 2 ∂μ
  set G := ∫ x, g x ^ 2 ∂μ
  set P := ∫ x, f x * g x ∂μ
  have hG0 : 0 ≤ G := integral_nonneg fun x => sq_nonneg _
  constructor
  · intro h
    rcases hG0.eq_or_lt with hG | hG
    · have hg0 := ae_eq_zero_of_integral_sq_eq_zero hg2 hG.symm
      exact ⟨0, 1, Or.inr one_ne_zero, by filter_upwards [hg0] with x hx; simp [hx]⟩
    have h0 : ∫ x, (f x - P / G * g x) ^ 2 ∂μ = 0 := by
      rw [integral_sub_mul_sq hfg hf2 hg2]
      field_simp
      linear_combination -G * h
    have hz := ae_eq_zero_of_integral_sq_eq_zero (integrable_sub_mul_sq hfg hf2 hg2 _) h0
    exact ⟨1, P / G, Or.inl one_ne_zero, by
      filter_upwards [hz] with x hx; linarith⟩
  · rintro ⟨A, B, hAB, hfg'⟩
    by_cases hA : A = 0
    · have hB : B ≠ 0 := hAB.resolve_left (not_not.mpr hA)
      have hg0 : ∀ᵐ x ∂μ, g x = 0 := by
        filter_upwards [hfg'] with x hx
        rw [hA, zero_mul] at hx
        exact (mul_eq_zero.mp hx.symm).resolve_left hB
      have hP : P = 0 := integral_eq_zero_of_ae (by filter_upwards [hg0] with x hx; simp [hx])
      have hG : G = 0 := integral_eq_zero_of_ae (by filter_upwards [hg0] with x hx; simp [hx])
      rw [hP, hG]; ring
    · have hfc : ∀ᵐ x ∂μ, f x = B / A * g x := by
        filter_upwards [hfg'] with x hx
        field_simp
        linarith
      have hP : P = B / A * G := by
        rw [← integral_const_mul]
        exact integral_congr_ae (by filter_upwards [hfc] with x hx; rw [hx]; ring)
      have hF : F = (B / A) ^ 2 * G := by
        rw [← integral_const_mul]
        exact integral_congr_ae (by filter_upwards [hfc] with x hx; rw [hx]; ring)
      rw [hP, hF]; ring

/-! ### Integrals: Hölder -/

/-- Young's inequality `xy ≤ xᵖ/p + y^q/q`, with equality iff `xᵖ = y^q`. -/
theorem young_rpow {p q x y : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    x * y ≤ 1 / p * x ^ p + 1 / q * y ^ q ∧
      (x * y = 1 / p * x ^ p + 1 / q * y ^ q ↔ x ^ p = y ^ q) := by
  have hpqc := holderConjugate_of_one_div hp hpq
  have h1p : 0 < 1 / p := one_div_pos.mpr hpqc.pos
  have h1q : 0 < 1 / q := one_div_pos.mpr hpqc.symm.pos
  have e : (x ^ p) ^ (1 / p) * (y ^ q) ^ (1 / q) = x * y := by
    rw [← Real.rpow_mul hx, mul_one_div_cancel hpqc.pos.ne', Real.rpow_one, ← Real.rpow_mul hy,
      mul_one_div_cancel hpqc.symm.pos.ne', Real.rpow_one]
  rw [← e]
  exact ⟨Real.geom_mean_le_arith_mean2_weighted h1p.le h1q.le (Real.rpow_nonneg hx p)
      (Real.rpow_nonneg hy q) hpq,
    Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos h1p h1q (Real.rpow_nonneg hx p)
      (Real.rpow_nonneg hy q) hpq⟩

theorem ae_eq_zero_of_integral_rpow_eq_zero {p : ℝ} (hp : p ≠ 0) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hfp : Integrable (fun x => f x ^ p) μ) (h : ∫ x, f x ^ p ∂μ = 0) : ∀ᵐ x ∂μ, f x = 0 := by
  have := (integral_eq_zero_iff_of_nonneg_ae
    (hf0.mono fun _ hx => Real.rpow_nonneg hx p) hfp).mp h
  filter_upwards [this, hf0] with x hx hx0
  exact (Real.rpow_eq_zero hx0 hp).mp hx

theorem integral_rpow_nonneg {p : ℝ} (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) : 0 ≤ ∫ x, f x ^ p ∂μ :=
  integral_nonneg_of_ae (hf0.mono fun _ hx => Real.rpow_nonneg hx p)

theorem rpow_one_div_rpow {x p : ℝ} (hx : 0 ≤ x) (hp : p ≠ 0) : (x ^ (1 / p)) ^ p = x := by
  rw [← Real.rpow_mul hx, one_div_mul_cancel hp, Real.rpow_one]

/-- Hölder's inequality for integrals of nonnegative functions, with integrability of `fg` and
the equality case. -/
theorem integral_mul_le_and_eq_iff {p q : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hfp : Integrable (fun x => f x ^ p) μ)
    (hgq : Integrable (fun x => g x ^ q) μ) :
    Integrable (fun x => f x * g x) μ ∧
      ∫ x, f x * g x ∂μ ≤ (∫ x, f x ^ p ∂μ) ^ (1 / p) * (∫ x, g x ^ q ∂μ) ^ (1 / q) ∧
      (∫ x, f x * g x ∂μ = (∫ x, f x ^ p ∂μ) ^ (1 / p) * (∫ x, g x ^ q ∂μ) ^ (1 / q) ↔
        ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ᵐ x ∂μ, A * f x ^ p = B * g x ^ q) := by
  have hpqc := holderConjugate_of_one_div hp hpq
  have hp0 : 0 < p := hpqc.pos
  have hq0 : 0 < q := hpqc.symm.pos
  have hfg : Integrable (fun x => f x * g x) μ :=
    Integrable.mono' ((hfp.const_mul (1 / p)).add (hgq.const_mul (1 / q))) (hf.mul hg) (by
      filter_upwards [hf0, hg0] with x hx hy
      show ‖f x * g x‖ ≤ 1 / p * f x ^ p + 1 / q * g x ^ q
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx hy)]
      exact (young_rpow hp hpq hx hy).1)
  refine ⟨hfg, ?_⟩
  set S := ∫ x, f x ^ p ∂μ
  set T := ∫ x, g x ^ q ∂μ
  set P := ∫ x, f x * g x ∂μ
  have hS0 : 0 ≤ S := integral_rpow_nonneg hf0
  have hT0 : 0 ≤ T := integral_rpow_nonneg hg0
  rcases hT0.eq_or_lt with hT | hTpos
  · have hgz := ae_eq_zero_of_integral_rpow_eq_zero hq0.ne' hg0 hgq hT.symm
    have hP : P = 0 := integral_eq_zero_of_ae (by filter_upwards [hgz] with x hx; simp [hx])
    rw [hP, ← hT, Real.zero_rpow (one_div_pos.mpr hq0).ne', mul_zero]
    exact ⟨le_rfl, iff_of_true rfl ⟨0, 1, Or.inr one_ne_zero, by
      filter_upwards [hgz] with x hx; simp [hx, Real.zero_rpow hq0.ne']⟩⟩
  rcases hS0.eq_or_lt with hS | hSpos
  · have hfz := ae_eq_zero_of_integral_rpow_eq_zero hp0.ne' hf0 hfp hS.symm
    have hP : P = 0 := integral_eq_zero_of_ae (by filter_upwards [hfz] with x hx; simp [hx])
    rw [hP, ← hS, Real.zero_rpow (one_div_pos.mpr hp0).ne', zero_mul]
    exact ⟨le_rfl, iff_of_true rfl ⟨1, 0, Or.inl one_ne_zero, by
      filter_upwards [hfz] with x hx; simp [hx, Real.zero_rpow hp0.ne']⟩⟩
  set a := S ^ (1 / p)
  set b := T ^ (1 / q)
  have ha : 0 < a := Real.rpow_pos_of_pos hSpos _
  have hb : 0 < b := Real.rpow_pos_of_pos hTpos _
  have hap : a ^ p = S := rpow_one_div_rpow hS0 hp0.ne'
  have hbq : b ^ q = T := rpow_one_div_rpow hT0 hq0.ne'
  set D : α → ℝ := fun x => 1 / p * (f x ^ p / S) + 1 / q * (g x ^ q / T) - f x * g x / (a * b)
  -- pointwise: `D x` is the gap in Young's inequality for `f x / a`, `g x / b`
  have hpt : ∀ x, 0 ≤ f x → 0 ≤ g x → 0 ≤ D x ∧ (D x = 0 ↔ T * f x ^ p = S * g x ^ q) := by
    intro x hx hy
    have e1 : (f x / a) ^ p = f x ^ p / S := by rw [Real.div_rpow hx ha.le, hap]
    have e2 : (g x / b) ^ q = g x ^ q / T := by rw [Real.div_rpow hy hb.le, hbq]
    have e3 : f x * g x / (a * b) = f x / a * (g x / b) := by rw [div_mul_div_comm]
    obtain ⟨hle, heq⟩ := young_rpow hp hpq (div_nonneg hx ha.le) (div_nonneg hy hb.le)
    rw [e1, e2] at hle heq
    have hD : D x = 1 / p * (f x ^ p / S) + 1 / q * (g x ^ q / T) - f x / a * (g x / b) := by
      simp only [D, e3]
    refine ⟨by rw [hD]; exact sub_nonneg.mpr hle, ?_⟩
    rw [hD, sub_eq_zero, eq_comm, heq, div_eq_div_iff hSpos.ne' hTpos.ne']
    constructor <;> intro h <;> linear_combination h
  have hD0 : ∀ᵐ x ∂μ, 0 ≤ D x := by
    filter_upwards [hf0, hg0] with x hx hy; exact (hpt x hx hy).1
  have hDint : Integrable D μ :=
    (((hfp.div_const S).const_mul (1 / p)).add ((hgq.div_const T).const_mul (1 / q))).sub
      (hfg.div_const (a * b))
  have hDsum : ∫ x, D x ∂μ = 1 - P / (a * b) := by
    have i1 : Integrable (fun x => 1 / p * (f x ^ p / S)) μ := (hfp.div_const S).const_mul _
    have i2 : Integrable (fun x => 1 / q * (g x ^ q / T)) μ := (hgq.div_const T).const_mul _
    have i3 : Integrable (fun x => 1 / p * (f x ^ p / S) + 1 / q * (g x ^ q / T)) μ := i1.add i2
    have i4 : Integrable (fun x => f x * g x / (a * b)) μ := hfg.div_const _
    simp only [D]
    rw [integral_sub i3 i4, integral_add i1 i2,
      integral_const_mul, integral_const_mul, integral_div, integral_div, integral_div,
      div_self hSpos.ne', div_self hTpos.ne']
    linear_combination hpq
  have hab : 0 < a * b := mul_pos ha hb
  refine ⟨?_, ?_⟩
  · have := integral_nonneg_of_ae hD0
    rw [hDsum] at this
    exact (div_le_one hab).mp (sub_nonneg.mp this)
  have hiff : P = a * b ↔ ∀ᵐ x ∂μ, T * f x ^ p = S * g x ^ q := by
    calc P = a * b ↔ ∫ x, D x ∂μ = 0 := by
          rw [hDsum, sub_eq_zero, eq_comm (a := (1 : ℝ)), div_eq_one_iff_eq hab.ne']
      _ ↔ ∀ᵐ x ∂μ, D x = 0 := integral_eq_zero_iff_of_nonneg_ae hD0 hDint
      _ ↔ ∀ᵐ x ∂μ, T * f x ^ p = S * g x ^ q := eventually_congr (by
          filter_upwards [hf0, hg0] with x hx hy; exact (hpt x hx hy).2)
  rw [hiff]
  constructor
  · intro h
    exact ⟨T, S, Or.inl hTpos.ne', h⟩
  · rintro ⟨A, B, hAB, h⟩
    have hAS : A * S = B * T := by
      rw [← integral_const_mul, ← integral_const_mul]
      exact integral_congr_ae h
    have hA : A ≠ 0 := by
      rintro rfl
      rw [zero_mul, eq_comm, mul_eq_zero] at hAS
      exact hAB.elim (fun h => h rfl) fun hB => hTpos.ne' (hAS.resolve_left hB)
    filter_upwards [h] with x hx
    apply mul_left_cancel₀ hA
    linear_combination T * hx - g x ^ q * hAS

/-! ### Integrals: Minkowski -/

theorem rpow_add_le_two_rpow_mul {p x y : ℝ} (hp : 0 < p) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ p ≤ 2 ^ p * (x ^ p + y ^ p) := by
  have hxp := Real.rpow_nonneg hx p
  have hyp := Real.rpow_nonneg hy p
  have h2 : (0 : ℝ) < 2 ^ p := Real.rpow_pos_of_pos two_pos p
  rcases le_total x y with h | h
  · calc (x + y) ^ p ≤ (2 * y) ^ p := Real.rpow_le_rpow (add_nonneg hx hy) (by linarith) hp.le
      _ = 2 ^ p * y ^ p := Real.mul_rpow zero_le_two hy
      _ ≤ 2 ^ p * (x ^ p + y ^ p) := mul_le_mul_of_nonneg_left (by linarith) h2.le
  · calc (x + y) ^ p ≤ (2 * x) ^ p := Real.rpow_le_rpow (add_nonneg hx hy) (by linarith) hp.le
      _ = 2 ^ p * x ^ p := Real.mul_rpow zero_le_two hx
      _ ≤ 2 ^ p * (x ^ p + y ^ p) := mul_le_mul_of_nonneg_left (by linarith) h2.le

theorem integrable_rpow_add {p : ℝ} (hp : 0 < p) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfp : Integrable (fun x => f x ^ p) μ) (hgp : Integrable (fun x => g x ^ p) μ) :
    Integrable (fun x => (f x + g x) ^ p) μ :=
  Integrable.mono' ((hfp.add hgp).const_mul (2 ^ p))
    ((hf.add hg).aemeasurable.pow_const p).aestronglyMeasurable (by
      filter_upwards [hf0, hg0] with x hx hy
      show ‖(f x + g x) ^ p‖ ≤ 2 ^ p * (f x ^ p + g x ^ p)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (add_nonneg hx hy) p)]
      exact rpow_add_le_two_rpow_mul hp hx hy)

/-- `(∫ fᵖ)^{1/p}`. -/
noncomputable def lpInt (p : ℝ) (μ : Measure α) (f : α → ℝ) : ℝ := (∫ x, f x ^ p ∂μ) ^ (1 / p)

/-- Termwise strict convexity, with its equality case. -/
theorem strictConvexOn_le_and_eq_iff {g : ℝ → ℝ} (hg : StrictConvexOn ℝ (Ici 0) g)
    {u v l m : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hl : 0 < l) (hm : 0 < m) (hlm : l + m = 1) :
    g (l * u + m * v) ≤ l * g u + m * g v ∧ (g (l * u + m * v) = l * g u + m * g v ↔ u = v) :=
  ⟨hg.convexOn.2 hu hv hl.le hm.le hlm, fun h => by_contra fun hne =>
    (hg.2 hu hv hne hl hm hlm).ne h, fun h => by simp only [h, ← add_mul, hlm, one_mul]⟩

/-- The core of Minkowski's inequality for integrals and its reverse: if `x ↦ σ xᵖ` is strictly
convex then `σ ∫ (f + g)ᵖ ≤ σ (α + β)ᵖ`, with equality iff `β f = α g` almost everywhere. -/
theorem minkowski_integral_aux {p σ : ℝ} (hp : 0 < p) (hσ : σ ≠ 0)
    (hcvx : StrictConvexOn ℝ (Ici 0) fun x : ℝ => σ * x ^ p) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfp : Integrable (fun x => f x ^ p) μ) (hgp : Integrable (fun x => g x ^ p) μ)
    (hS : 0 < ∫ x, f x ^ p ∂μ) (hT : 0 < ∫ x, g x ^ p ∂μ) :
    σ * ∫ x, (f x + g x) ^ p ∂μ ≤ σ * (lpInt p μ f + lpInt p μ g) ^ p ∧
      (∫ x, (f x + g x) ^ p ∂μ = (lpInt p μ f + lpInt p μ g) ^ p ↔
        ∀ᵐ x ∂μ, lpInt p μ g * f x = lpInt p μ f * g x) := by
  set S := ∫ x, f x ^ p ∂μ
  set T := ∫ x, g x ^ p ∂μ
  set I := ∫ x, (f x + g x) ^ p ∂μ
  set a := lpInt p μ f
  set b := lpInt p μ g
  have ha : 0 < a := Real.rpow_pos_of_pos hS _
  have hb : 0 < b := Real.rpow_pos_of_pos hT _
  have hap : a ^ p = S := rpow_one_div_rpow hS.le hp.ne'
  have hbp : b ^ p = T := rpow_one_div_rpow hT.le hp.ne'
  have hab : 0 < a + b := add_pos ha hb
  set K := (a + b) ^ p
  have hK : 0 < K := Real.rpow_pos_of_pos hab p
  set l := a / (a + b)
  set m := b / (a + b)
  have hl : 0 < l := div_pos ha hab
  have hm : 0 < m := div_pos hb hab
  have hlm : l + m = 1 := by simp only [l, m]; rw [← add_div, div_self hab.ne']
  set D : α → ℝ := fun x => σ * (l * (f x ^ p / S) + m * (g x ^ p / T) - (f x + g x) ^ p / K)
  have hpt : ∀ x, 0 ≤ f x → 0 ≤ g x → 0 ≤ D x ∧ (D x = 0 ↔ b * f x = a * g x) := by
    intro x hx hy
    have e1 : (f x / a) ^ p = f x ^ p / S := by rw [Real.div_rpow hx ha.le, hap]
    have e2 : (g x / b) ^ p = g x ^ p / T := by rw [Real.div_rpow hy hb.le, hbp]
    have e3 : (l * (f x / a) + m * (g x / b)) ^ p = (f x + g x) ^ p / K := by
      have : l * (f x / a) + m * (g x / b) = (f x + g x) / (a + b) := by
        simp only [l, m]; field_simp
      rw [this, Real.div_rpow (add_nonneg hx hy) hab.le]
    obtain ⟨hle, heq⟩ := strictConvexOn_le_and_eq_iff hcvx (div_nonneg hx ha.le)
      (div_nonneg hy hb.le) hl hm hlm
    simp only [e1, e2, e3] at hle heq
    have hD : D x = l * (σ * (f x ^ p / S)) + m * (σ * (g x ^ p / T)) -
        σ * ((f x + g x) ^ p / K) := by simp only [D]; ring
    refine ⟨by rw [hD]; exact sub_nonneg.mpr hle, ?_⟩
    rw [hD, sub_eq_zero, eq_comm, heq, div_eq_div_iff ha.ne' hb.ne']
    constructor <;> intro h <;> linear_combination h
  have hfgp := integrable_rpow_add hp hf0 hg0 hf hg hfp hgp
  have hD0 : ∀ᵐ x ∂μ, 0 ≤ D x := by
    filter_upwards [hf0, hg0] with x hx hy; exact (hpt x hx hy).1
  have j1 : Integrable (fun x => l * (f x ^ p / S)) μ := (hfp.div_const S).const_mul l
  have j2 : Integrable (fun x => m * (g x ^ p / T)) μ := (hgp.div_const T).const_mul m
  have j3 : Integrable (fun x => (f x + g x) ^ p / K) μ := hfgp.div_const K
  have hint1 : Integrable (fun x => l * (f x ^ p / S) + m * (g x ^ p / T)) μ := j1.add j2
  have hDint : Integrable D μ := (hint1.sub (hfgp.div_const K)).const_mul σ
  have hDsum : ∫ x, D x ∂μ = σ * (1 - I / K) := by
    simp only [D]
    rw [integral_const_mul, integral_sub hint1 j3, integral_add j1 j2,
      integral_const_mul, integral_const_mul, integral_div, integral_div, integral_div,
      div_self hS.ne', div_self hT.ne', mul_one, mul_one, hlm]
  refine ⟨?_, ?_⟩
  · have h0 := integral_nonneg_of_ae hD0
    rw [hDsum] at h0
    have e : σ * K - σ * I = K * (σ * (1 - I / K)) := by field_simp
    nlinarith
  calc I = K ↔ ∫ x, D x ∂μ = 0 := by
        rw [hDsum, mul_eq_zero, or_iff_right hσ, sub_eq_zero, eq_comm (a := (1 : ℝ)),
          div_eq_one_iff_eq hK.ne']
    _ ↔ ∀ᵐ x ∂μ, D x = 0 := integral_eq_zero_iff_of_nonneg_ae hD0 hDint
    _ ↔ ∀ᵐ x ∂μ, b * f x = a * g x := eventually_congr (by
        filter_upwards [hf0, hg0] with x hx hy; exact (hpt x hx hy).2)

theorem lpInt_add_of_ae_zero_left {p : ℝ} (hp : 0 < p) (hf : ∀ᵐ x ∂μ, f x = 0) :
    lpInt p μ (fun x => f x + g x) = lpInt p μ g ∧ lpInt p μ f = 0 := by
  refine ⟨congrArg (· ^ (1 / p)) (integral_congr_ae (by
    filter_upwards [hf] with x hx; simp [hx])), ?_⟩
  have : ∫ x, f x ^ p ∂μ = 0 := integral_eq_zero_of_ae (by
    filter_upwards [hf] with x hx; simp [hx, Real.zero_rpow hp.ne'])
  simp only [lpInt]; rw [this, Real.zero_rpow (one_div_pos.mpr hp).ne']

theorem lpInt_add_of_ae_zero_right {p : ℝ} (hp : 0 < p) (hg : ∀ᵐ x ∂μ, g x = 0) :
    lpInt p μ (fun x => f x + g x) = lpInt p μ f ∧ lpInt p μ g = 0 := by
  refine ⟨congrArg (· ^ (1 / p)) (integral_congr_ae (by
    filter_upwards [hg] with x hx; simp [hx])), ?_⟩
  have : ∫ x, g x ^ p ∂μ = 0 := integral_eq_zero_of_ae (by
    filter_upwards [hg] with x hx; simp [hx, Real.zero_rpow hp.ne'])
  simp only [lpInt]; rw [this, Real.zero_rpow (one_div_pos.mpr hp).ne']

theorem rpow_rpow_one_div {x p : ℝ} (hx : 0 ≤ x) (hp : p ≠ 0) : (x ^ p) ^ (1 / p) = x := by
  rw [← Real.rpow_mul hx, mul_one_div_cancel hp, Real.rpow_one]

/-- Minkowski's inequality for integrals of nonnegative functions, `p > 1`. -/
theorem lpInt_add_le {p : ℝ} (hp : 1 < p) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfp : Integrable (fun x => f x ^ p) μ) (hgp : Integrable (fun x => g x ^ p) μ) :
    lpInt p μ (fun x => f x + g x) ≤ lpInt p μ f + lpInt p μ g := by
  have hp0 : 0 < p := by linarith
  rcases (integral_rpow_nonneg (p := p) hf0).eq_or_lt with hS | hS
  · obtain ⟨h1, h2⟩ := lpInt_add_of_ae_zero_left (g := g) hp0
      (ae_eq_zero_of_integral_rpow_eq_zero hp0.ne' hf0 hfp hS.symm)
    rw [h1, h2, zero_add]
  rcases (integral_rpow_nonneg (p := p) hg0).eq_or_lt with hT | hT
  · obtain ⟨h1, h2⟩ := lpInt_add_of_ae_zero_right (f := f) hp0
      (ae_eq_zero_of_integral_rpow_eq_zero hp0.ne' hg0 hgp hT.symm)
    rw [h1, h2, add_zero]
  have h := (minkowski_integral_aux hp0 one_ne_zero (by simpa using strictConvexOn_rpow hp)
    hf0 hg0 hf hg hfp hgp hS hT).1
  rw [one_mul, one_mul] at h
  have hab : 0 ≤ lpInt p μ f + lpInt p μ g :=
    add_nonneg (Real.rpow_nonneg hS.le _) (Real.rpow_nonneg hT.le _)
  calc lpInt p μ (fun x => f x + g x) ≤ ((lpInt p μ f + lpInt p μ g) ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (integral_rpow_nonneg ((hf0.and hg0).mono fun _ h => add_nonneg h.1 h.2))
          h (one_div_pos.mpr hp0).le
    _ = lpInt p μ f + lpInt p μ g := rpow_rpow_one_div hab hp0.ne'

/-- The reverse Minkowski inequality for integrals of nonnegative functions, `0 < p < 1`. -/
theorem lpInt_add_ge {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfp : Integrable (fun x => f x ^ p) μ) (hgp : Integrable (fun x => g x ^ p) μ) :
    lpInt p μ f + lpInt p μ g ≤ lpInt p μ (fun x => f x + g x) := by
  rcases (integral_rpow_nonneg (p := p) hf0).eq_or_lt with hS | hS
  · obtain ⟨h1, h2⟩ := lpInt_add_of_ae_zero_left (g := g) hp0
      (ae_eq_zero_of_integral_rpow_eq_zero hp0.ne' hf0 hfp hS.symm)
    rw [h1, h2, zero_add]
  rcases (integral_rpow_nonneg (p := p) hg0).eq_or_lt with hT | hT
  · obtain ⟨h1, h2⟩ := lpInt_add_of_ae_zero_right (f := f) hp0
      (ae_eq_zero_of_integral_rpow_eq_zero hp0.ne' hg0 hgp hT.symm)
    rw [h1, h2, add_zero]
  have h := (minkowski_integral_aux hp0 (by norm_num) (strictConvexOn_neg_rpow hp0 hp1)
    hf0 hg0 hf hg hfp hgp hS hT).1
  have h' : (lpInt p μ f + lpInt p μ g) ^ p ≤ ∫ x, (f x + g x) ^ p ∂μ := by linarith
  have hab : 0 ≤ lpInt p μ f + lpInt p μ g :=
    add_nonneg (Real.rpow_nonneg hS.le _) (Real.rpow_nonneg hT.le _)
  calc lpInt p μ f + lpInt p μ g = ((lpInt p μ f + lpInt p μ g) ^ p) ^ (1 / p) :=
        (rpow_rpow_one_div hab hp0.ne').symm
    _ ≤ lpInt p μ (fun x => f x + g x) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hab _) h' (one_div_pos.mpr hp0).le

/-- Equality in Minkowski's inequality for integrals or its reverse: iff `A f = B g` almost
everywhere for constants `A`, `B` not both zero. -/
theorem lpInt_add_eq_iff {p σ : ℝ} (hp : 0 < p) (hσ : σ ≠ 0)
    (hcvx : StrictConvexOn ℝ (Ici 0) fun x : ℝ => σ * x ^ p) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfp : Integrable (fun x => f x ^ p) μ) (hgp : Integrable (fun x => g x ^ p) μ) :
    lpInt p μ (fun x => f x + g x) = lpInt p μ f + lpInt p μ g ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ᵐ x ∂μ, A * f x = B * g x := by
  rcases (integral_rpow_nonneg (p := p) hg0).eq_or_lt with hT | hT
  · have hgz := ae_eq_zero_of_integral_rpow_eq_zero hp.ne' hg0 hgp hT.symm
    obtain ⟨h1, h2⟩ := lpInt_add_of_ae_zero_right (f := f) hp hgz
    exact iff_of_true (by rw [h1, h2, add_zero])
      ⟨0, 1, Or.inr one_ne_zero, by filter_upwards [hgz] with x hx; simp [hx]⟩
  rcases (integral_rpow_nonneg (p := p) hf0).eq_or_lt with hS | hS
  · have hfz := ae_eq_zero_of_integral_rpow_eq_zero hp.ne' hf0 hfp hS.symm
    obtain ⟨h1, h2⟩ := lpInt_add_of_ae_zero_left (g := g) hp hfz
    exact iff_of_true (by rw [h1, h2, zero_add])
      ⟨1, 0, Or.inl one_ne_zero, by filter_upwards [hfz] with x hx; simp [hx]⟩
  have ha : 0 < lpInt p μ f := Real.rpow_pos_of_pos hS _
  have hb : 0 < lpInt p μ g := Real.rpow_pos_of_pos hT _
  have hI0 : 0 ≤ ∫ x, (f x + g x) ^ p ∂μ :=
    integral_rpow_nonneg ((hf0.and hg0).mono fun _ h => add_nonneg h.1 h.2)
  rw [show lpInt p μ (fun x => f x + g x) = (∫ x, (f x + g x) ^ p ∂μ) ^ (1 / p) from rfl,
    rpow_one_div_eq_iff hI0 (add_pos ha hb).le hp,
    (minkowski_integral_aux hp hσ hcvx hf0 hg0 hf hg hfp hgp hS hT).2]
  constructor
  · intro h
    exact ⟨lpInt p μ g, lpInt p μ f, Or.inl hb.ne', h⟩
  · rintro ⟨A, B, hAB, h⟩
    have hA : A ≠ 0 := by
      rintro rfl
      have hB := hAB.resolve_left (not_not.mpr rfl)
      have hgz : ∀ᵐ x ∂μ, g x = 0 := by
        filter_upwards [h] with x hx
        rw [zero_mul] at hx
        exact (mul_eq_zero.mp hx.symm).resolve_left hB
      exact hT.ne' (integral_eq_zero_of_ae (by
        filter_upwards [hgz] with x hx; simp [hx, Real.zero_rpow hp.ne']))
    set c := B / A
    have hfc : ∀ᵐ x ∂μ, f x = c * g x := by
      filter_upwards [h] with x hx
      simp only [c]
      field_simp
      linear_combination hx
    have hc : 0 ≤ c := by
      by_contra hneg
      push Not at hneg
      have hfz : ∀ᵐ x ∂μ, f x = 0 := by
        filter_upwards [hfc, hf0, hg0] with x h1 h2 h3
        exact le_antisymm (by nlinarith) h2
      exact hS.ne' (integral_eq_zero_of_ae (by
        filter_upwards [hfz] with x hx; simp [hx, Real.zero_rpow hp.ne']))
    have hSc : ∫ x, f x ^ p ∂μ = c ^ p * ∫ x, g x ^ p ∂μ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (by
        filter_upwards [hfc, hg0] with x hx hy; rw [hx, Real.mul_rpow hc hy])
    have hac : lpInt p μ f = c * lpInt p μ g := by
      simp only [lpInt]
      rw [hSc, Real.mul_rpow (Real.rpow_nonneg hc p) hT.le, rpow_rpow_one_div hc hp.ne']
    filter_upwards [hfc] with x hx
    rw [hx, hac]; ring

end Integrals

/-! ### DLMF 1.7.4–1.7.6 on intervals -/

section Intervals

open MeasureTheory Filter

/-- The interval `(a, b)` with endpoints in `[−∞, +∞]`. -/
def eIoo (a b : EReal) : Set ℝ := {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}

theorem isOpen_eIoo (a b : EReal) : IsOpen (eIoo a b) :=
  (isOpen_lt continuous_const continuous_coe_real_ereal).inter
    (isOpen_lt continuous_coe_real_ereal continuous_const)

theorem measurableSet_eIoo (a b : EReal) : MeasurableSet (eIoo a b) :=
  (isOpen_eIoo a b).measurableSet

theorem ae_eIoo_iff_forall {a b : EReal} {F G : ℝ → ℝ} (hF : ContinuousOn F (eIoo a b))
    (hG : ContinuousOn G (eIoo a b)) :
    (∀ᵐ x ∂volume.restrict (eIoo a b), F x = G x) ↔ ∀ x ∈ eIoo a b, F x = G x :=
  ⟨fun h => Measure.eqOn_open_of_ae_eq h (isOpen_eIoo a b) hF hG,
    fun h => ae_restrict_of_forall_mem (measurableSet_eIoo a b) h⟩

variable {a b : EReal} {f g : ℝ → ℝ}

/-- **DLMF 1.7.4** (Cauchy–Schwarz inequality for integrals over `(a, b)`, `−∞ ≤ a`,
`b ≤ +∞`). -/
theorem dlmf_1_7_4 (hf : AEStronglyMeasurable f (volume.restrict (eIoo a b)))
    (hg : AEStronglyMeasurable g (volume.restrict (eIoo a b)))
    (hf2 : IntegrableOn (fun x => f x ^ 2) (eIoo a b))
    (hg2 : IntegrableOn (fun x => g x ^ 2) (eIoo a b)) :
    (∫ x in eIoo a b, f x * g x) ^ 2 ≤ (∫ x in eIoo a b, f x ^ 2) * ∫ x in eIoo a b, g x ^ 2 :=
  sq_integral_mul_le hf hg hf2 hg2

/-- **DLMF §1.7(ii)**: equality holds in 1.7.4 iff `A f(x) = B g(x)` for almost every `x` in
`(a, b)`, for constants `A`, `B` not both zero. -/
theorem dlmf_1_7_4_eq_iff (hf : AEStronglyMeasurable f (volume.restrict (eIoo a b)))
    (hg : AEStronglyMeasurable g (volume.restrict (eIoo a b)))
    (hf2 : IntegrableOn (fun x => f x ^ 2) (eIoo a b))
    (hg2 : IntegrableOn (fun x => g x ^ 2) (eIoo a b)) :
    (∫ x in eIoo a b, f x * g x) ^ 2 = (∫ x in eIoo a b, f x ^ 2) * ∫ x in eIoo a b, g x ^ 2 ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ᵐ x ∂volume.restrict (eIoo a b), A * f x = B * g x :=
  sq_integral_mul_eq_iff hf hg hf2 hg2

/-- **DLMF §1.7(ii)**, for continuous `f`, `g`: equality holds in 1.7.4 iff `A f(x) = B g(x)` for
all `x` in `(a, b)`, for constants `A`, `B` not both zero. -/
theorem dlmf_1_7_4_eq_iff_of_continuousOn (hf : ContinuousOn f (eIoo a b))
    (hg : ContinuousOn g (eIoo a b)) (hf2 : IntegrableOn (fun x => f x ^ 2) (eIoo a b))
    (hg2 : IntegrableOn (fun x => g x ^ 2) (eIoo a b)) :
    (∫ x in eIoo a b, f x * g x) ^ 2 = (∫ x in eIoo a b, f x ^ 2) * ∫ x in eIoo a b, g x ^ 2 ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ x ∈ eIoo a b, A * f x = B * g x := by
  rw [dlmf_1_7_4_eq_iff (hf.aestronglyMeasurable (measurableSet_eIoo a b))
    (hg.aestronglyMeasurable (measurableSet_eIoo a b)) hf2 hg2]
  exact exists_congr fun A => exists_congr fun B => and_congr_right fun _ =>
    ae_eIoo_iff_forall (continuousOn_const.mul hf) (continuousOn_const.mul hg)

/-- **DLMF 1.7.5** (Hölder's inequality for integrals over `(a, b)`): for `p > 1`,
`1/p + 1/q = 1`, `f, g ≥ 0`. -/
theorem dlmf_1_7_5 {p q : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1)
    (hf0 : ∀ x ∈ eIoo a b, 0 ≤ f x) (hg0 : ∀ x ∈ eIoo a b, 0 ≤ g x)
    (hf : AEStronglyMeasurable f (volume.restrict (eIoo a b)))
    (hg : AEStronglyMeasurable g (volume.restrict (eIoo a b)))
    (hfp : IntegrableOn (fun x => f x ^ p) (eIoo a b))
    (hgq : IntegrableOn (fun x => g x ^ q) (eIoo a b)) :
    ∫ x in eIoo a b, f x * g x ≤
      (∫ x in eIoo a b, f x ^ p) ^ (1 / p) * (∫ x in eIoo a b, g x ^ q) ^ (1 / q) :=
  (integral_mul_le_and_eq_iff hp hpq (ae_restrict_of_forall_mem (measurableSet_eIoo a b) hf0)
    (ae_restrict_of_forall_mem (measurableSet_eIoo a b) hg0) hf hg hfp hgq).2.1

/-- **DLMF §1.7(ii)**: equality holds in 1.7.5 iff `A f(x)ᵖ = B g(x)^q` for almost every `x` in
`(a, b)`, for constants `A`, `B` not both zero. -/
theorem dlmf_1_7_5_eq_iff {p q : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1)
    (hf0 : ∀ x ∈ eIoo a b, 0 ≤ f x) (hg0 : ∀ x ∈ eIoo a b, 0 ≤ g x)
    (hf : AEStronglyMeasurable f (volume.restrict (eIoo a b)))
    (hg : AEStronglyMeasurable g (volume.restrict (eIoo a b)))
    (hfp : IntegrableOn (fun x => f x ^ p) (eIoo a b))
    (hgq : IntegrableOn (fun x => g x ^ q) (eIoo a b)) :
    ∫ x in eIoo a b, f x * g x =
        (∫ x in eIoo a b, f x ^ p) ^ (1 / p) * (∫ x in eIoo a b, g x ^ q) ^ (1 / q) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧
        ∀ᵐ x ∂volume.restrict (eIoo a b), A * f x ^ p = B * g x ^ q :=
  (integral_mul_le_and_eq_iff hp hpq (ae_restrict_of_forall_mem (measurableSet_eIoo a b) hf0)
    (ae_restrict_of_forall_mem (measurableSet_eIoo a b) hg0) hf hg hfp hgq).2.2

/-- **DLMF §1.7(ii)**, for continuous `f`, `g`: equality holds in 1.7.5 iff
`A f(x)ᵖ = B g(x)^q` for all `x` in `(a, b)`, for constants `A`, `B` not both zero. -/
theorem dlmf_1_7_5_eq_iff_of_continuousOn {p q : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1)
    (hf0 : ∀ x ∈ eIoo a b, 0 ≤ f x) (hg0 : ∀ x ∈ eIoo a b, 0 ≤ g x)
    (hf : ContinuousOn f (eIoo a b)) (hg : ContinuousOn g (eIoo a b))
    (hfp : IntegrableOn (fun x => f x ^ p) (eIoo a b))
    (hgq : IntegrableOn (fun x => g x ^ q) (eIoo a b)) :
    ∫ x in eIoo a b, f x * g x =
        (∫ x in eIoo a b, f x ^ p) ^ (1 / p) * (∫ x in eIoo a b, g x ^ q) ^ (1 / q) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ x ∈ eIoo a b, A * f x ^ p = B * g x ^ q := by
  have hpqc := holderConjugate_of_one_div hp hpq
  rw [dlmf_1_7_5_eq_iff hp hpq hf0 hg0 (hf.aestronglyMeasurable (measurableSet_eIoo a b))
    (hg.aestronglyMeasurable (measurableSet_eIoo a b)) hfp hgq]
  exact exists_congr fun A => exists_congr fun B => and_congr_right fun _ =>
    ae_eIoo_iff_forall (continuousOn_const.mul (hf.rpow_const fun _ _ => Or.inr hpqc.pos.le))
      (continuousOn_const.mul (hg.rpow_const fun _ _ => Or.inr hpqc.symm.pos.le))

/-- **DLMF 1.7.6** (Minkowski's inequality for integrals over `(a, b)`): for `p > 1`,
`f, g ≥ 0`. -/
theorem dlmf_1_7_6 {p : ℝ} (hp : 1 < p) (hf0 : ∀ x ∈ eIoo a b, 0 ≤ f x)
    (hg0 : ∀ x ∈ eIoo a b, 0 ≤ g x) (hf : AEStronglyMeasurable f (volume.restrict (eIoo a b)))
    (hg : AEStronglyMeasurable g (volume.restrict (eIoo a b)))
    (hfp : IntegrableOn (fun x => f x ^ p) (eIoo a b))
    (hgp : IntegrableOn (fun x => g x ^ p) (eIoo a b)) :
    (∫ x in eIoo a b, (f x + g x) ^ p) ^ (1 / p) ≤
      (∫ x in eIoo a b, f x ^ p) ^ (1 / p) + (∫ x in eIoo a b, g x ^ p) ^ (1 / p) :=
  lpInt_add_le hp (ae_restrict_of_forall_mem (measurableSet_eIoo a b) hf0)
    (ae_restrict_of_forall_mem (measurableSet_eIoo a b) hg0) hf hg hfp hgp

/-- **DLMF §1.7(ii)**: for `p > 1`, equality holds in 1.7.6 iff `A f(x) = B g(x)` for almost
every `x` in `(a, b)`, for constants `A`, `B` not both zero. -/
theorem dlmf_1_7_6_eq_iff {p : ℝ} (hp : 1 < p) (hf0 : ∀ x ∈ eIoo a b, 0 ≤ f x)
    (hg0 : ∀ x ∈ eIoo a b, 0 ≤ g x) (hf : AEStronglyMeasurable f (volume.restrict (eIoo a b)))
    (hg : AEStronglyMeasurable g (volume.restrict (eIoo a b)))
    (hfp : IntegrableOn (fun x => f x ^ p) (eIoo a b))
    (hgp : IntegrableOn (fun x => g x ^ p) (eIoo a b)) :
    (∫ x in eIoo a b, (f x + g x) ^ p) ^ (1 / p) =
        (∫ x in eIoo a b, f x ^ p) ^ (1 / p) + (∫ x in eIoo a b, g x ^ p) ^ (1 / p) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ᵐ x ∂volume.restrict (eIoo a b), A * f x = B * g x :=
  lpInt_add_eq_iff (by linarith) one_ne_zero (by simpa using strictConvexOn_rpow hp)
    (ae_restrict_of_forall_mem (measurableSet_eIoo a b) hf0)
    (ae_restrict_of_forall_mem (measurableSet_eIoo a b) hg0) hf hg hfp hgp

/-- **DLMF §1.7(ii)**, for continuous `f`, `g`: for `p > 1`, equality holds in 1.7.6 iff
`A f(x) = B g(x)` for all `x` in `(a, b)`, for constants `A`, `B` not both zero. -/
theorem dlmf_1_7_6_eq_iff_of_continuousOn {p : ℝ} (hp : 1 < p)
    (hf0 : ∀ x ∈ eIoo a b, 0 ≤ f x) (hg0 : ∀ x ∈ eIoo a b, 0 ≤ g x)
    (hf : ContinuousOn f (eIoo a b)) (hg : ContinuousOn g (eIoo a b))
    (hfp : IntegrableOn (fun x => f x ^ p) (eIoo a b))
    (hgp : IntegrableOn (fun x => g x ^ p) (eIoo a b)) :
    (∫ x in eIoo a b, (f x + g x) ^ p) ^ (1 / p) =
        (∫ x in eIoo a b, f x ^ p) ^ (1 / p) + (∫ x in eIoo a b, g x ^ p) ^ (1 / p) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ x ∈ eIoo a b, A * f x = B * g x := by
  rw [dlmf_1_7_6_eq_iff hp hf0 hg0 (hf.aestronglyMeasurable (measurableSet_eIoo a b))
    (hg.aestronglyMeasurable (measurableSet_eIoo a b)) hfp hgp]
  exact exists_congr fun A => exists_congr fun B => and_congr_right fun _ =>
    ae_eIoo_iff_forall (continuousOn_const.mul hf) (continuousOn_const.mul hg)

/-- **DLMF §1.7(ii)** (reverse Minkowski for integrals): for `0 < p < 1`, `f, g ≥ 0`, the
inequality 1.7.6 is reversed. -/
theorem dlmf_1_7_6_reverse {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hf0 : ∀ x ∈ eIoo a b, 0 ≤ f x)
    (hg0 : ∀ x ∈ eIoo a b, 0 ≤ g x) (hf : AEStronglyMeasurable f (volume.restrict (eIoo a b)))
    (hg : AEStronglyMeasurable g (volume.restrict (eIoo a b)))
    (hfp : IntegrableOn (fun x => f x ^ p) (eIoo a b))
    (hgp : IntegrableOn (fun x => g x ^ p) (eIoo a b)) :
    (∫ x in eIoo a b, f x ^ p) ^ (1 / p) + (∫ x in eIoo a b, g x ^ p) ^ (1 / p) ≤
      (∫ x in eIoo a b, (f x + g x) ^ p) ^ (1 / p) :=
  lpInt_add_ge hp0 hp1 (ae_restrict_of_forall_mem (measurableSet_eIoo a b) hf0)
    (ae_restrict_of_forall_mem (measurableSet_eIoo a b) hg0) hf hg hfp hgp

/-- **DLMF §1.7(ii)**: for `0 < p < 1`, equality holds in the reversed 1.7.6 iff `A f(x) = B g(x)`
for almost every `x` in `(a, b)`, for constants `A`, `B` not both zero. -/
theorem dlmf_1_7_6_reverse_eq_iff {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hf0 : ∀ x ∈ eIoo a b, 0 ≤ f x) (hg0 : ∀ x ∈ eIoo a b, 0 ≤ g x)
    (hf : AEStronglyMeasurable f (volume.restrict (eIoo a b)))
    (hg : AEStronglyMeasurable g (volume.restrict (eIoo a b)))
    (hfp : IntegrableOn (fun x => f x ^ p) (eIoo a b))
    (hgp : IntegrableOn (fun x => g x ^ p) (eIoo a b)) :
    (∫ x in eIoo a b, (f x + g x) ^ p) ^ (1 / p) =
        (∫ x in eIoo a b, f x ^ p) ^ (1 / p) + (∫ x in eIoo a b, g x ^ p) ^ (1 / p) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ᵐ x ∂volume.restrict (eIoo a b), A * f x = B * g x :=
  lpInt_add_eq_iff hp0 (by norm_num) (strictConvexOn_neg_rpow hp0 hp1)
    (ae_restrict_of_forall_mem (measurableSet_eIoo a b) hf0)
    (ae_restrict_of_forall_mem (measurableSet_eIoo a b) hg0) hf hg hfp hgp

/-- **DLMF §1.7(ii)**, for continuous `f`, `g`: for `0 < p < 1`, equality holds in the reversed
1.7.6 iff `A f(x) = B g(x)` for all `x` in `(a, b)`, for constants `A`, `B` not both zero. -/
theorem dlmf_1_7_6_reverse_eq_iff_of_continuousOn {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hf0 : ∀ x ∈ eIoo a b, 0 ≤ f x) (hg0 : ∀ x ∈ eIoo a b, 0 ≤ g x)
    (hf : ContinuousOn f (eIoo a b)) (hg : ContinuousOn g (eIoo a b))
    (hfp : IntegrableOn (fun x => f x ^ p) (eIoo a b))
    (hgp : IntegrableOn (fun x => g x ^ p) (eIoo a b)) :
    (∫ x in eIoo a b, (f x + g x) ^ p) ^ (1 / p) =
        (∫ x in eIoo a b, f x ^ p) ^ (1 / p) + (∫ x in eIoo a b, g x ^ p) ^ (1 / p) ↔
      ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ x ∈ eIoo a b, A * f x = B * g x := by
  rw [dlmf_1_7_6_reverse_eq_iff hp0 hp1 hf0 hg0 (hf.aestronglyMeasurable
    (measurableSet_eIoo a b)) (hg.aestronglyMeasurable (measurableSet_eIoo a b)) hfp hgp]
  exact exists_congr fun A => exists_congr fun B => and_congr_right fun _ =>
    ae_eIoo_iff_forall (continuousOn_const.mul hf) (continuousOn_const.mul hg)

end Intervals

/-! ### §1.7(iii) Means -/

section Means

open Filter Topology

variable {n : ℕ}

theorem IsWeights.univ_nonempty {p : Fin n → ℝ} (hp : IsWeights p) :
    (univ : Finset (Fin n)).Nonempty := by
  rcases (univ : Finset (Fin n)).eq_empty_or_nonempty with h | h
  · have := hp.2
    rw [h, sum_empty] at this
    exact absurd this zero_ne_one
  · exact h

/-- The weighted mean `M(r)` of §1.2(iv) for every real `r`: `weightedMean` for `r ≠ 0`, and the
weighted geometric mean `a₁^{p₁} ⋯ aₙ^{pₙ}` for `r = 0` (its limit as `r → 0`; DLMF 1.2.26 for
equal weights). -/
noncomputable def powerMean (p a : Fin n → ℝ) (r : ℝ) : ℝ :=
  if r = 0 then ∏ i, a i ^ p i else weightedMean p a r

theorem powerMean_of_ne_zero {p a : Fin n → ℝ} {r : ℝ} (hr : r ≠ 0) :
    powerMean p a r = weightedMean p a r := by simp [powerMean, hr]

theorem powerMean_zero (p a : Fin n → ℝ) : powerMean p a 0 = ∏ i, a i ^ p i := by
  simp [powerMean]

theorem powerMean_nonneg {p a : Fin n → ℝ} (hp : IsWeights p) (ha : ∀ i, 0 ≤ a i) (r : ℝ) :
    0 ≤ powerMean p a r := by
  by_cases hr : r = 0
  · subst hr; rw [powerMean_zero]; exact prod_nonneg fun i _ => Real.rpow_nonneg (ha i) _
  · rw [powerMean_of_ne_zero hr]
    unfold weightedMean
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg
        (sum_nonneg fun i _ => mul_nonneg (hp.1 i).le (Real.rpow_nonneg (ha i) r)) _

theorem powerMean_pos {p a : Fin n → ℝ} (hp : IsWeights p) (ha : ∀ i, 0 < a i) (r : ℝ) :
    0 < powerMean p a r := by
  by_cases hr : r = 0
  · subst hr; rw [powerMean_zero]; exact prod_pos fun i _ => Real.rpow_pos_of_pos (ha i) _
  · rw [powerMean_of_ne_zero hr, dlmf_1_2_21 p a r fun h => (ha _).ne' h.2.choose_spec]
    exact Real.rpow_pos_of_pos (sum_pos (fun i _ => mul_pos (hp.1 i)
      (Real.rpow_pos_of_pos (ha i) r)) hp.univ_nonempty) _

theorem powerMean_const {p : Fin n → ℝ} (hp : IsWeights p) {c : ℝ} (hc : 0 ≤ c) (r : ℝ) :
    powerMean p (fun _ => c) r = c := by
  by_cases hr : r = 0
  · subst hr
    rw [powerMean_zero, ← Real.rpow_sum_of_nonneg hc (fun i _ => (hp.1 i).le), hp.2,
      Real.rpow_one]
  · rw [powerMean_of_ne_zero hr]
    unfold weightedMean
    split_ifs with h
    · exact h.2.choose_spec.symm
    · show (∑ i, p i * c ^ r) ^ (1 / r) = c
      rw [← sum_mul, hp.2, one_mul, rpow_rpow_one_div hc hr]

/-- `M(−r)` is the reciprocal of `M(r)` for the reciprocals. -/
theorem powerMean_neg {p a : Fin n → ℝ} (hp : IsWeights p) (ha : ∀ i, 0 < a i) (r : ℝ) :
    powerMean p a (-r) = (powerMean p (fun i => (a i)⁻¹) r)⁻¹ := by
  by_cases hr : r = 0
  · subst hr
    rw [neg_zero, powerMean_zero, powerMean_zero, ← prod_inv_distrib]
    exact prod_congr rfl fun i _ => by rw [Real.inv_rpow (ha i).le, inv_inv]
  · have hno : ∀ i, a i ≠ 0 := fun i => (ha i).ne'
    rw [powerMean_of_ne_zero (neg_ne_zero.mpr hr), powerMean_of_ne_zero hr,
      dlmf_1_2_21 p a (-r) (fun h => hno _ h.2.choose_spec),
      dlmf_1_2_21 p _ r (fun h => by
        obtain ⟨-, i, hi⟩ := h
        exact inv_ne_zero (hno i) hi)]
    have hterm : ∀ i, (a i)⁻¹ ^ r = a i ^ (-r) := fun i => by
      rw [Real.inv_rpow (ha i).le, Real.rpow_neg (ha i).le]
    simp only [hterm]
    rw [show 1 / -r = -(1 / r) by ring, Real.rpow_neg (sum_nonneg fun i _ =>
      mul_nonneg (hp.1 i).le (Real.rpow_nonneg (ha i).le _))]

theorem forall_eq_wsum_iff {p : Fin n → ℝ} (hp : IsWeights p) (z : Fin n → ℝ) :
    (∀ j, z j = ∑ i, p i * z i) ↔ ∀ i j, z i = z j := by
  refine ⟨fun h i j => (h i).trans (h j).symm, fun h j => ?_⟩
  rw [sum_congr rfl fun i _ => by rw [h i j], ← sum_mul, hp.2, one_mul]

/-- `M(r) ≤ M(s)` for `0 < r < s`, with equality iff all `aⱼ` are equal (strict Jensen for
`x ↦ x^{s/r}`). -/
theorem powerMean_le_of_pos {p a : Fin n → ℝ} (hp : IsWeights p) (ha : ∀ i, 0 ≤ a i) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) :
    powerMean p a r ≤ powerMean p a s ∧
      (powerMean p a r = powerMean p a s ↔ ∀ i j, a i = a j) := by
  have hs : 0 < s := hr.trans hrs
  rw [powerMean_of_ne_zero hr.ne', powerMean_of_ne_zero hs.ne',
    dlmf_1_2_21 p a r (fun h => lt_asymm hr h.1), dlmf_1_2_21 p a s (fun h => lt_asymm hs h.1)]
  set t := s / r
  have ht : 1 < t := (one_lt_div hr).mpr hrs
  set z : Fin n → ℝ := fun i => a i ^ r
  have hz : ∀ i, 0 ≤ z i := fun i => Real.rpow_nonneg (ha i) r
  have hzt : ∀ i, z i ^ t = a i ^ s := fun i => by
    simp only [z, t]; rw [← Real.rpow_mul (ha i), mul_div_cancel₀ _ hr.ne']
  set X := ∑ i, p i * z i
  have hX : 0 ≤ X := sum_nonneg fun i _ => mul_nonneg (hp.1 i).le (hz i)
  have hY : 0 ≤ ∑ i, p i * a i ^ s :=
    sum_nonneg fun i _ => mul_nonneg (hp.1 i).le (Real.rpow_nonneg (ha i) s)
  have hcv := strictConvexOn_rpow ht
  have hJ : X ^ t ≤ ∑ i, p i * a i ^ s := by
    have := hcv.convexOn.map_sum_le (t := univ) (w := p) (p := z) (fun i _ => (hp.1 i).le) hp.2
      (fun i _ => hz i)
    simp only [smul_eq_mul, hzt] at this
    exact this
  have hJeq : X ^ t = ∑ i, p i * a i ^ s ↔ ∀ j, z j = X := by
    have := hcv.map_sum_eq_iff (t := univ) (w := p) (p := z) (fun i _ => hp.1 i) hp.2
      (fun i _ => hz i)
    simp only [smul_eq_mul, hzt, Finset.mem_univ, true_implies] at this
    exact this
  have hXr : X ^ (1 / r) = (X ^ t) ^ (1 / s) := by
    rw [← Real.rpow_mul hX]; congr 1; simp only [t]; field_simp
  rw [hXr]
  refine ⟨Real.rpow_le_rpow (Real.rpow_nonneg hX t) hJ (one_div_pos.mpr hs).le, ?_⟩
  rw [Real.rpow_left_inj (Real.rpow_nonneg hX t) hY (one_div_pos.mpr hs).ne', hJeq,
    forall_eq_wsum_iff hp z]
  exact forall_congr' fun i => forall_congr' fun j => Real.rpow_left_inj (ha i) (ha j) hr.ne'

/-- `M(0) ≤ M(s)` for `s > 0`, with equality iff all `aⱼ` are equal (weighted AM–GM for
`aⱼ^s`). -/
theorem powerMean_zero_le {p a : Fin n → ℝ} (hp : IsWeights p) (ha : ∀ i, 0 ≤ a i) {s : ℝ}
    (hs : 0 < s) :
    powerMean p a 0 ≤ powerMean p a s ∧
      (powerMean p a 0 = powerMean p a s ↔ ∀ i j, a i = a j) := by
  rw [powerMean_zero, powerMean_of_ne_zero hs.ne', dlmf_1_2_21 p a s (fun h => lt_asymm hs h.1)]
  set z : Fin n → ℝ := fun i => a i ^ s
  have hz : ∀ i, 0 ≤ z i := fun i => Real.rpow_nonneg (ha i) s
  have hG0 : 0 ≤ ∏ i, a i ^ p i := prod_nonneg fun i _ => Real.rpow_nonneg (ha i) _
  have hG : (∏ i, a i ^ p i) ^ s = ∏ i, z i ^ p i := by
    rw [← Real.finsetProd_rpow univ _ (fun i _ => Real.rpow_nonneg (ha i) _)]
    exact prod_congr rfl fun i _ => by
      simp only [z]; rw [← Real.rpow_mul (ha i), ← Real.rpow_mul (ha i), mul_comm]
  have hZ0 : 0 ≤ ∏ i, z i ^ p i := prod_nonneg fun i _ => Real.rpow_nonneg (hz i) _
  have hY : 0 ≤ ∑ i, p i * z i := sum_nonneg fun i _ => mul_nonneg (hp.1 i).le (hz i)
  have hAM := Real.geom_mean_le_arith_mean_weighted univ p z (fun i _ => (hp.1 i).le) hp.2
    (fun i _ => hz i)
  have hAMeq := Real.geom_mean_eq_arith_mean_weighted_iff_of_pos univ p z (fun i _ => hp.1 i)
    hp.2 (fun i _ => hz i)
  simp only [Finset.mem_univ, true_implies] at hAMeq
  rw [← rpow_rpow_one_div hG0 hs.ne', hG]
  refine ⟨Real.rpow_le_rpow hZ0 hAM (one_div_pos.mpr hs).le, ?_⟩
  rw [Real.rpow_left_inj hZ0 hY (one_div_pos.mpr hs).ne', hAMeq]
  exact forall_congr' fun i => forall_congr' fun j => Real.rpow_left_inj (ha i) (ha j) hs.ne'

theorem powerMean_mono_of_nonneg {p a : Fin n → ℝ} (hp : IsWeights p) (ha : ∀ i, 0 ≤ a i)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) :
    powerMean p a r ≤ powerMean p a s ∧
      (powerMean p a r = powerMean p a s ↔ ∀ i j, a i = a j) := by
  rcases hr.eq_or_lt with rfl | hr
  · exact powerMean_zero_le hp ha hrs
  · exact powerMean_le_of_pos hp ha hr hrs

/-- Monotonicity of `M(r)` for positive `aⱼ`, with equality iff all `aⱼ` are equal. -/
theorem powerMean_mono_of_pos {p a : Fin n → ℝ} (hp : IsWeights p) (ha : ∀ i, 0 < a i)
    {r s : ℝ} (hrs : r < s) :
    powerMean p a r ≤ powerMean p a s ∧
      (powerMean p a r = powerMean p a s ↔ ∀ i j, a i = a j) := by
  have hb : ∀ i, 0 ≤ (a i)⁻¹ := fun i => (inv_pos.mpr (ha i)).le
  have hbpos : ∀ i, 0 < (a i)⁻¹ := fun i => inv_pos.mpr (ha i)
  have hallb : (∀ i j, (a i)⁻¹ = (a j)⁻¹) ↔ ∀ i j, a i = a j :=
    forall_congr' fun i => forall_congr' fun j => inv_inj
  have hneg : ∀ {r s : ℝ}, r < s → s ≤ 0 → powerMean p a r ≤ powerMean p a s ∧
      (powerMean p a r = powerMean p a s ↔ ∀ i j, a i = a j) := by
    intro r s hrs hs
    have key := powerMean_mono_of_nonneg hp hb (r := -s) (s := -r) (by linarith) (by linarith)
    rw [show powerMean p a r = (powerMean p (fun i => (a i)⁻¹) (-r))⁻¹ by
        rw [← powerMean_neg hp ha, neg_neg],
      show powerMean p a s = (powerMean p (fun i => (a i)⁻¹) (-s))⁻¹ by
        rw [← powerMean_neg hp ha, neg_neg]]
    refine ⟨inv_anti₀ (powerMean_pos hp hbpos _) key.1, ?_⟩
    rw [inv_inj, eq_comm, key.2, hallb]
  rcases le_or_gt 0 r with hr | hr
  · exact powerMean_mono_of_nonneg hp (fun i => (ha i).le) hr hrs
  rcases le_or_gt s 0 with hs | hs
  · exact hneg hrs hs
  have h1 := hneg hr le_rfl
  have h2 := powerMean_zero_le hp (fun i => (ha i).le) hs
  refine ⟨h1.1.trans h2.1, fun h => h1.2.mp (le_antisymm h1.1 (h2.1.trans_eq h.symm)),
    fun h => ?_⟩
  rw [h1.2.mpr h, h2.2.mpr h]

theorem powerMean_eq_zero_of_nonpos {p a : Fin n → ℝ} (hp : IsWeights p) (hz : ∃ j, a j = 0)
    {t : ℝ} (ht : t ≤ 0) : powerMean p a t = 0 := by
  obtain ⟨j, hj⟩ := hz
  rcases ht.eq_or_lt with rfl | ht
  · rw [powerMean_zero]
    exact prod_eq_zero (mem_univ j) (by rw [hj, Real.zero_rpow (hp.1 j).ne'])
  · rw [powerMean_of_ne_zero ht.ne]
    unfold weightedMean
    rw [ite_eq_left ⟨ht, j, hj⟩]

theorem powerMean_eq_zero_iff_of_pos {p a : Fin n → ℝ} (hp : IsWeights p) (ha : ∀ i, 0 ≤ a i)
    {s : ℝ} (hs : 0 < s) : powerMean p a s = 0 ↔ ∀ i, a i = 0 := by
  rw [powerMean_of_ne_zero hs.ne', dlmf_1_2_21 p a s (fun h => lt_asymm hs h.1),
    rpow_one_div_eq_iff (sum_nonneg fun i _ => mul_nonneg (hp.1 i).le (Real.rpow_nonneg (ha i) s))
      le_rfl hs, Real.zero_rpow hs.ne',
    sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hp.1 i).le (Real.rpow_nonneg (ha i) s)]
  simp [(hp.1 _).ne', Real.rpow_eq_zero (ha _) hs.ne']

/-- **DLMF 1.7.9** with its equality case, for `M(r)` extended to all real `r` (`powerMean`). -/
theorem powerMean_mono {p a : Fin n → ℝ} (hp : IsWeights p) (ha : ∀ i, 0 ≤ a i) {r s : ℝ}
    (hrs : r < s) :
    powerMean p a r ≤ powerMean p a s ∧ (powerMean p a r = powerMean p a s ↔
      (∀ i j, a i = a j) ∨ (s ≤ 0 ∧ ∃ j, a j = 0)) := by
  by_cases hz : ∃ j, a j = 0
  · obtain ⟨j, hj⟩ := hz
    rcases le_or_gt s 0 with hs | hs
    · rw [powerMean_eq_zero_of_nonpos hp ⟨j, hj⟩ (hrs.le.trans hs),
        powerMean_eq_zero_of_nonpos hp ⟨j, hj⟩ hs]
      exact ⟨le_rfl, iff_of_true rfl (Or.inr ⟨hs, j, hj⟩)⟩
    rw [or_iff_left fun h => not_le.mpr hs h.1]
    rcases le_or_gt r 0 with hr | hr
    · rw [powerMean_eq_zero_of_nonpos hp ⟨j, hj⟩ hr]
      refine ⟨powerMean_nonneg hp ha s, ?_⟩
      rw [eq_comm, powerMean_eq_zero_iff_of_pos hp ha hs]
      exact ⟨fun h i k => by rw [h i, h k], fun h i => by rw [h i j, hj]⟩
    · exact powerMean_le_of_pos hp ha hr hrs
  · push Not at hz
    rw [or_iff_left fun h => hz _ h.2.choose_spec]
    exact powerMean_mono_of_pos hp (fun i => (ha i).lt_of_ne (hz i).symm) hrs

/-- **DLMF 1.7.9**: `M(r) ≤ M(s)` for `r < s` (nonnegative `aⱼ`, weights `pⱼ`; `M(0)` is the
weighted geometric mean). -/
theorem dlmf_1_7_9 {p a : Fin n → ℝ} (hp : IsWeights p) (ha : ∀ i, 0 ≤ a i) {r s : ℝ}
    (hrs : r < s) : powerMean p a r ≤ powerMean p a s :=
  (powerMean_mono hp ha hrs).1

/-- **DLMF §1.7(iii)**: equality holds in 1.7.9 iff `a₁ = a₂ = ⋯ = aₙ`, or `s ≤ 0` and some
`aⱼ = 0`. -/
theorem dlmf_1_7_9_eq_iff {p a : Fin n → ℝ} (hp : IsWeights p) (ha : ∀ i, 0 ≤ a i) {r s : ℝ}
    (hrs : r < s) : powerMean p a r = powerMean p a s ↔
      (∀ i j, a i = a j) ∨ (s ≤ 0 ∧ ∃ j, a j = 0) :=
  (powerMean_mono hp ha hrs).2

theorem tendsto_powerMean_atTop [NeZero n] {p a : Fin n → ℝ} (hp : IsWeights p)
    (ha : ∀ i, 0 ≤ a i) :
    Tendsto (powerMean p a) atTop (𝓝 (univ.sup' univ_nonempty a)) :=
  (dlmf_1_2_23 hp a ha).congr'
    ((eventually_gt_atTop 0).mono fun _ hr => (powerMean_of_ne_zero hr.ne').symm)

theorem tendsto_powerMean_atBot [NeZero n] {p a : Fin n → ℝ} (hp : IsWeights p)
    (ha : ∀ i, 0 ≤ a i) :
    Tendsto (powerMean p a) atBot (𝓝 (univ.inf' univ_nonempty a)) :=
  (dlmf_1_2_24 hp a ha).congr'
    ((eventually_lt_atBot 0).mono fun _ hr => (powerMean_of_ne_zero hr.ne).symm)

theorem powerMean_le_sup' [NeZero n] {p a : Fin n → ℝ} (hp : IsWeights p) (ha : ∀ i, 0 ≤ a i)
    (s : ℝ) : powerMean p a s ≤ univ.sup' univ_nonempty a :=
  ge_of_tendsto (tendsto_powerMean_atTop hp ha)
    ((eventually_gt_atTop s).mono fun _ ht => (powerMean_mono hp ha ht).1)

theorem inf'_le_powerMean [NeZero n] {p a : Fin n → ℝ} (hp : IsWeights p) (ha : ∀ i, 0 ≤ a i)
    (s : ℝ) : univ.inf' univ_nonempty a ≤ powerMean p a s :=
  le_of_tendsto (tendsto_powerMean_atBot hp ha)
    ((eventually_lt_atBot s).mono fun _ ht => (powerMean_mono hp ha ht).1)

theorem powerMean_of_allEq [NeZero n] {p a : Fin n → ℝ} (hp : IsWeights p) (ha : ∀ i, 0 ≤ a i)
    (h : ∀ i j, a i = a j) (r : ℝ) (i₀ : Fin n) : powerMean p a r = a i₀ := by
  have hac : a = fun _ => a i₀ := funext fun i => h i i₀
  have := powerMean_const hp (ha i₀) r
  rwa [← hac] at this

/-- **DLMF 1.7.8**: `min(a₁, …, aₙ) ≤ M(r) ≤ max(a₁, …, aₙ)` (nonnegative `aⱼ`, weights `pⱼ`,
`r ≠ 0`). -/
theorem dlmf_1_7_8 [NeZero n] {p a : Fin n → ℝ} (hp : IsWeights p) (ha : ∀ i, 0 ≤ a i) {r : ℝ}
    (hr : r ≠ 0) :
    univ.inf' univ_nonempty a ≤ weightedMean p a r ∧
      weightedMean p a r ≤ univ.sup' univ_nonempty a := by
  rw [← powerMean_of_ne_zero hr]
  exact ⟨inf'_le_powerMean hp ha r, powerMean_le_sup' hp ha r⟩

/-- **DLMF §1.7(iii)**: `M(r) = max(a₁, …, aₙ)` iff `a₁ = a₂ = ⋯ = aₙ`. -/
theorem dlmf_1_7_8_eq_sup'_iff [NeZero n] {p a : Fin n → ℝ} (hp : IsWeights p)
    (ha : ∀ i, 0 ≤ a i) {r : ℝ} (hr : r ≠ 0) :
    weightedMean p a r = univ.sup' univ_nonempty a ↔ ∀ i j, a i = a j := by
  rw [← powerMean_of_ne_zero hr]
  obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  constructor
  · intro h
    have h1 := (powerMean_mono hp ha (lt_add_one r)).1
    have h2 := powerMean_le_sup' hp ha (r + 1)
    rcases (powerMean_mono hp ha (lt_add_one r)).2.mp (le_antisymm h1 (h2.trans_eq h.symm)) with
      h' | ⟨hr1, hz⟩
    · exact h'
    · have h0 : powerMean p a r = 0 := powerMean_eq_zero_of_nonpos hp hz (by linarith)
      have hle : ∀ i, a i = 0 := fun i =>
        le_antisymm ((le_sup' a (mem_univ i)).trans (h.symm.trans h0).le) (ha i)
      exact fun i j => by rw [hle i, hle j]
  · intro h
    rw [powerMean_of_allEq hp ha h r i₀]
    exact le_antisymm (le_sup' a (mem_univ i₀)) (sup'_le _ _ fun i _ => (h i i₀).le)

/-- **DLMF §1.7(iii)**: `M(r) = min(a₁, …, aₙ)` iff `a₁ = a₂ = ⋯ = aₙ`, or `r < 0` and some
`aⱼ = 0`. -/
theorem dlmf_1_7_8_eq_inf'_iff [NeZero n] {p a : Fin n → ℝ} (hp : IsWeights p)
    (ha : ∀ i, 0 ≤ a i) {r : ℝ} (hr : r ≠ 0) :
    weightedMean p a r = univ.inf' univ_nonempty a ↔
      (∀ i j, a i = a j) ∨ (r < 0 ∧ ∃ j, a j = 0) := by
  rw [← powerMean_of_ne_zero hr]
  obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  constructor
  · intro h
    have h1 := (powerMean_mono hp ha (sub_one_lt r)).1
    have h2 := inf'_le_powerMean hp ha (r - 1)
    rcases (powerMean_mono hp ha (sub_one_lt r)).2.mp (le_antisymm h1 (h.trans_le h2).ge) with
      h' | ⟨hr0, hz⟩
    · exact Or.inl h'
    · exact Or.inr ⟨lt_of_le_of_ne hr0 hr, hz⟩
  · rintro (h | ⟨hr0, j, hj⟩)
    · rw [powerMean_of_allEq hp ha h r i₀]
      exact le_antisymm (le_inf' _ _ fun i _ => (h i₀ i).le) (inf'_le a (mem_univ i₀))
    · rw [powerMean_eq_zero_of_nonpos hp ⟨j, hj⟩ hr0.le]
      exact le_antisymm (le_inf' _ _ fun i _ => ha i) (hj ▸ inf'_le a (mem_univ j))

/-- **DLMF §1.7(iii)**, as stated: equality holds in 1.7.8 iff `a₁ = a₂ = ⋯ = aₙ`, or `r < 0`
and some `aⱼ = 0`. -/
theorem dlmf_1_7_8_eq_iff [NeZero n] {p a : Fin n → ℝ} (hp : IsWeights p) (ha : ∀ i, 0 ≤ a i)
    {r : ℝ} (hr : r ≠ 0) :
    (weightedMean p a r = univ.inf' univ_nonempty a ∨
        weightedMean p a r = univ.sup' univ_nonempty a) ↔
      (∀ i j, a i = a j) ∨ (r < 0 ∧ ∃ j, a j = 0) := by
  rw [dlmf_1_7_8_eq_inf'_iff hp ha hr, dlmf_1_7_8_eq_sup'_iff hp ha hr]
  exact ⟨fun h => h.elim id Or.inl, Or.inl⟩

theorem powerMean_uniform_zero [NeZero n] {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) :
    powerMean (fun _ => (1 / n : ℝ)) a 0 = geomMean a := by
  rw [powerMean_zero, geomMean, Real.finsetProd_rpow univ a (fun i _ => ha i)]

/-- **DLMF 1.7.7**: `H ≤ G ≤ A` for positive `a₁, …, aₙ`. -/
theorem dlmf_1_7_7 [NeZero n] {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) :
    harmMean a ≤ geomMean a ∧ geomMean a ≤ arithMean a := by
  have hw := isWeights_const (n := n)
  have ha0 : ∀ i, 0 ≤ a i := fun i => (ha i).le
  rw [← dlmf_1_2_25_harm a ha, ← powerMean_uniform_zero ha0, ← dlmf_1_2_25_arith a,
    ← powerMean_of_ne_zero (by norm_num : (-1 : ℝ) ≠ 0), ← powerMean_of_ne_zero one_ne_zero]
  exact ⟨dlmf_1_7_9 hw ha0 (by norm_num), dlmf_1_7_9 hw ha0 zero_lt_one⟩

/-- **DLMF §1.7(iii)**: `H = G` iff `a₁ = a₂ = ⋯ = aₙ`. -/
theorem dlmf_1_7_7_harmMean_eq_iff [NeZero n] {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) :
    harmMean a = geomMean a ↔ ∀ i j, a i = a j := by
  have ha0 : ∀ i, 0 ≤ a i := fun i => (ha i).le
  rw [← dlmf_1_2_25_harm a ha, ← powerMean_uniform_zero ha0,
    ← powerMean_of_ne_zero (by norm_num : (-1 : ℝ) ≠ 0),
    dlmf_1_7_9_eq_iff isWeights_const ha0 (by norm_num),
    or_iff_left fun h => (ha _).ne' h.2.choose_spec]

/-- **DLMF §1.7(iii)**: `G = A` iff `a₁ = a₂ = ⋯ = aₙ`. -/
theorem dlmf_1_7_7_geomMean_eq_iff [NeZero n] {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) :
    geomMean a = arithMean a ↔ ∀ i j, a i = a j := by
  have ha0 : ∀ i, 0 ≤ a i := fun i => (ha i).le
  rw [← powerMean_uniform_zero ha0, ← dlmf_1_2_25_arith a, ← powerMean_of_ne_zero one_ne_zero,
    dlmf_1_7_9_eq_iff isWeights_const ha0 zero_lt_one,
    or_iff_left fun h => (ha _).ne' h.2.choose_spec]

end Means

/-! ### §1.7(iv) Jensen's inequality -/

section Jensen

open MeasureTheory Filter

/-- A convex function on an open subset of `ℝ` has a supporting line at every point: the
supremum of the left difference quotients is a valid slope. -/
theorem exists_affine_le_of_convexOn {s : Set ℝ} {φ : ℝ → ℝ} (hφ : ConvexOn ℝ s φ) (hs : IsOpen s)
    {m : ℝ} (hm : m ∈ s) : ∃ c : ℝ, ∀ y ∈ s, φ m + c * (y - m) ≤ φ y := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs m hm
  have hz : m + ε / 2 ∈ s := hball (by
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
    linarith)
  have hx : m - ε / 2 ∈ s := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos (half_pos hε)]
    linarith)
  set L := (fun x => (φ m - φ x) / (m - x)) '' (s ∩ Iio m)
  have hLne : L.Nonempty := ⟨_, m - ε / 2, ⟨hx, show m - ε / 2 < m by linarith⟩, rfl⟩
  have hbdd : BddAbove L := ⟨(φ (m + ε / 2) - φ m) / (m + ε / 2 - m), by
    rintro _ ⟨x, ⟨hxs, hxm⟩, rfl⟩
    exact hφ.slope_mono_adjacent hxs hz hxm (by linarith)⟩
  refine ⟨sSup L, fun y hy => ?_⟩
  rcases lt_trichotomy y m with hym | rfl | hmy
  · have h1 : (φ m - φ y) / (m - y) ≤ sSup L := le_csSup hbdd ⟨y, ⟨hy, hym⟩, rfl⟩
    rw [div_le_iff₀ (by linarith)] at h1
    linarith
  · simp
  · have h1 : sSup L ≤ (φ y - φ m) / (y - m) := csSup_le hLne (by
      rintro _ ⟨x, ⟨hxs, hxm⟩, rfl⟩
      exact hφ.slope_mono_adjacent hxs hy hxm hmy)
    rw [le_div_iff₀ (by linarith)] at h1
    linarith

/-- An integrable function on `[0, 1]` takes a value `≤` its integral. -/
theorem exists_mem_Icc_le_intervalIntegral {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1) :
    ∃ x ∈ Icc (0 : ℝ) 1, f x ≤ ∫ x in (0 : ℝ)..1, f x := by
  by_contra h
  push Not at h
  set m := ∫ x in (0 : ℝ)..1, f x
  have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on (hf.sub intervalIntegrable_const)
    (fun x hx => sub_pos.mpr (h x (Ioo_subset_Icc_self hx))) zero_lt_one
  rw [intervalIntegral.integral_sub hf intervalIntegrable_const, intervalIntegral.integral_const,
    sub_zero, one_smul, sub_self] at hpos
  exact lt_irrefl _ hpos

/-- **Jensen's inequality** on `[0, 1]` for a convex function on an open set. -/
theorem convexOn_intervalIntegral_le {s : Set ℝ} (hs : IsOpen s) {φ f : ℝ → ℝ}
    (hφ : ConvexOn ℝ s φ) (hfs : ∀ x ∈ Icc (0 : ℝ) 1, f x ∈ s)
    (hf : IntervalIntegrable f volume 0 1)
    (hφf : IntervalIntegrable (fun x => φ (f x)) volume 0 1) :
    φ (∫ x in (0 : ℝ)..1, f x) ≤ ∫ x in (0 : ℝ)..1, φ (f x) := by
  set m := ∫ x in (0 : ℝ)..1, f x
  obtain ⟨x₁, hx₁, h₁⟩ := exists_mem_Icc_le_intervalIntegral hf
  obtain ⟨x₂, hx₂, h₂⟩ := exists_mem_Icc_le_intervalIntegral hf.neg
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at h₂
  have hm : m ∈ s :=
    (convex_iff_ordConnected.mp hφ.1).out (hfs x₁ hx₁) (hfs x₂ hx₂) ⟨h₁, by linarith⟩
  obtain ⟨c, hc⟩ := exists_affine_le_of_convexOn hφ hs hm
  have i1 : IntervalIntegrable (fun x => c * (f x - m)) volume 0 1 :=
    (hf.sub intervalIntegrable_const).const_mul c
  have i2 : IntervalIntegrable (fun x => φ m + c * (f x - m)) volume 0 1 :=
    intervalIntegrable_const.add i1
  have i3 : IntervalIntegrable (fun _ : ℝ => m) volume 0 1 := intervalIntegrable_const
  calc φ m = ∫ x in (0 : ℝ)..1, (φ m + c * (f x - m)) := by
        rw [intervalIntegral.integral_add intervalIntegrable_const i1,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hf i3]
        simp [m]
    _ ≤ ∫ x in (0 : ℝ)..1, φ (f x) :=
        intervalIntegral.integral_mono_on zero_le_one i2 hφf fun x hx => hc (f x) (hfs x hx)

/-- **DLMF 1.7.10** (Jensen's inequality): for `f` integrable on `[0, 1]` with
`a < f(x) < b` (`−∞ ≤ a`, `b ≤ +∞`) and `φ` convex on `(a, b)`,
`φ(∫₀¹ f) ≤ ∫₀¹ φ(f)` (provided `φ ∘ f` is integrable). -/
theorem dlmf_1_7_10 {a b : EReal} {φ f : ℝ → ℝ} (hφ : ConvexOn ℝ (eIoo a b) φ)
    (hfab : ∀ x ∈ Icc (0 : ℝ) 1, f x ∈ eIoo a b) (hf : IntervalIntegrable f volume 0 1)
    (hφf : IntervalIntegrable (fun x => φ (f x)) volume 0 1) :
    φ (∫ x in (0 : ℝ)..1, f x) ≤ ∫ x in (0 : ℝ)..1, φ (f x) :=
  convexOn_intervalIntegral_le (isOpen_eIoo a b) hφ hfab hf hφf

instance isProbabilityMeasure_restrict_Ioc_zero_one :
    IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; simp⟩

/-- **DLMF 1.7.11**, non-strict: `exp(∫₀¹ ln f) ≤ ∫₀¹ f` for positive `f` with `f` and `ln f`
integrable. -/
theorem dlmf_1_7_11 {f : ℝ → ℝ} (hf0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 < f x)
    (hf : IntervalIntegrable f volume 0 1)
    (hlog : IntervalIntegrable (fun x => Real.log (f x)) volume 0 1) :
    Real.exp (∫ x in (0 : ℝ)..1, Real.log (f x)) ≤ ∫ x in (0 : ℝ)..1, f x := by
  have heq : EqOn (fun x => Real.exp (Real.log (f x))) f (uIcc 0 1) := fun x hx => by
    rw [Set.uIcc_of_le zero_le_one] at hx; exact Real.exp_log (hf0 x hx)
  have hexp : IntervalIntegrable (fun x => Real.exp (Real.log (f x))) volume 0 1 :=
    hf.congr fun x hx => (heq (uIoc_subset_uIcc hx)).symm
  have h := convexOn_intervalIntegral_le isOpen_univ convexOn_exp (fun x _ => mem_univ _) hlog
    hexp
  rwa [intervalIntegral.integral_congr heq] at h

/-- **DLMF 1.7.11**, strict: `exp(∫₀¹ ln f) < ∫₀¹ f` unless `f` is almost everywhere constant on
`(0, 1]`.  (DLMF states `<` unconditionally; for constant `f` both sides are equal.) -/
theorem dlmf_1_7_11_lt {f : ℝ → ℝ} (hf0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 < f x)
    (hf : IntervalIntegrable f volume 0 1)
    (hlog : IntervalIntegrable (fun x => Real.log (f x)) volume 0 1)
    (hnc : ¬ ∃ c : ℝ, ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), f x = c) :
    Real.exp (∫ x in (0 : ℝ)..1, Real.log (f x)) < ∫ x in (0 : ℝ)..1, f x := by
  set μ := volume.restrict (Ioc (0 : ℝ) 1)
  have hpos : ∀ x ∈ Ioc (0 : ℝ) 1, 0 < f x := fun x hx => hf0 x (Ioc_subset_Icc_self hx)
  have hlogI : Integrable (fun x => Real.log (f x)) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hlog
  have hexpI : Integrable (Real.exp ∘ fun x => Real.log (f x)) μ :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hf).congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      simp [Real.exp_log (hpos x hx)])
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  rcases strictConvexOn_exp.ae_eq_const_or_map_average_lt Real.continuous_exp.continuousOn
    isClosed_univ (ae_of_all _ fun _ => mem_univ _) hlogI hexpI with h | h
  · refine absurd ⟨Real.exp (⨍ x, Real.log (f x) ∂μ), ?_⟩ hnc
    filter_upwards [h, ae_restrict_mem measurableSet_Ioc] with x hx hxI
    simp only [Function.const_apply] at hx
    rw [← hx, Real.exp_log (hpos x hxI)]
  · simp only [average_eq_integral] at h
    calc Real.exp (∫ x, Real.log (f x) ∂μ) < ∫ x, Real.exp (Real.log (f x)) ∂μ := h
      _ = ∫ x, f x ∂μ := setIntegral_congr_fun measurableSet_Ioc fun x hx =>
          Real.exp_log (hpos x hx)

/-- **DLMF §1.7(iv)**: equality holds in 1.7.11 iff `f` is almost everywhere constant on
`(0, 1]`. -/
theorem dlmf_1_7_11_eq_iff {f : ℝ → ℝ} (hf0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 < f x)
    (hf : IntervalIntegrable f volume 0 1)
    (hlog : IntervalIntegrable (fun x => Real.log (f x)) volume 0 1) :
    Real.exp (∫ x in (0 : ℝ)..1, Real.log (f x)) = ∫ x in (0 : ℝ)..1, f x ↔
      ∃ c : ℝ, ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), f x = c := by
  refine ⟨fun h => by_contra fun hnc => (dlmf_1_7_11_lt hf0 hf hlog hnc).ne h, ?_⟩
  rintro ⟨c, hc⟩
  have hpos : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), 0 < f x :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hf0 x (Ioc_subset_Icc_self hx)
  obtain ⟨x, hx, hx0⟩ := (hc.and hpos).exists
  have hc0 : 0 < c := hx ▸ hx0
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    integral_congr_ae (hc.mono fun x hx => by rw [hx]), integral_congr_ae hc]
  simp [Real.exp_log hc0]

end Jensen

end Azurite.DLMF
