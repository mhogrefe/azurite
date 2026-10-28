/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalities

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

end Azurite.DLMF
