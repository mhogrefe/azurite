/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.AsymptoticExpansion

/-!
# Brent–Zimmermann §4.5 (continued): the `e^(1/(12n))` refinement of Stirling's formula

The two-sided Stirling bound quoted in §4.5,

  `√(2πn) (n/e)^n ≤ n! ≤ √(2πn) (n/e)^n e^(1/(12n))`,

whose lower half is Mathlib's `Stirling.le_factorial_stirling`.  The upper half
(`factorial_le_stirling_refined`) comes from Mathlib's exact series for the differences of
`log (stirlingSeq n)`: each term `1/(2k+3) · r^(k+1)` with `r = 1/(2n+3)²` is at most
`r^(k+1)/3`, so `log s_{n+1} − log s_{n+2} ≤ (1/3) r/(1 − r) = 1/(12(n+1)(n+2))`
(`log_stirlingSeq_sdiff_le_telescoping`); telescoping and `s_n → √π` give
`log s_{n+1} − log √π ≤ 1/(12(n+1))` (`log_stirlingSeq_sub_log_sqrt_pi_le`).
-/

namespace Azurite

namespace BZ

open Real Filter Topology Finset

/-- `log s_{n+1} − log s_{n+2} ≤ 1/(12(n+1)) − 1/(12(n+2))` for the Stirling sequence
`s_n = n!/(√(2n) (n/e)^n)`. -/
theorem log_stirlingSeq_sdiff_le_telescoping (n : ℕ) :
    Real.log (Stirling.stirlingSeq (n + 1)) - Real.log (Stirling.stirlingSeq (n + 2))
      ≤ 1 / (12 * ((n : ℝ) + 1)) - 1 / (12 * ((n : ℝ) + 2)) := by
  have h := Stirling.log_stirlingSeq_sdiff_hasSum n
  set r : ℝ := (1 / (2 * ((n + 1 : ℕ) : ℝ) + 1)) ^ 2 with hr
  have hq : (0 : ℝ) < 2 * ((n + 1 : ℕ) : ℝ) + 1 := by positivity
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr]
    refine pow_lt_one₀ (by positivity) ?_ two_ne_zero
    rw [div_lt_one hq]
    push_cast
    linarith
  have hgeo : HasSum (fun k : ℕ => 1 / 3 * r ^ (k + 1)) (1 / 3 * r * (1 - r)⁻¹) := by
    have := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (1 / 3 * r)
    convert this using 1
    funext k
    ring
  refine (hasSum_le (fun k => ?_) h hgeo).trans (le_of_eq ?_)
  · apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 _)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    push_cast
    linarith
  · have h1r : (1 : ℝ) - r
        = ((2 * ((n + 1 : ℕ) : ℝ) + 1) ^ 2 - 1) / (2 * ((n + 1 : ℕ) : ℝ) + 1) ^ 2 := by
      rw [hr]
      field_simp
    have hnum : (2 * ((n + 1 : ℕ) : ℝ) + 1) ^ 2 - 1 ≠ 0 := by
      push_cast
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [h1r, hr]
    field_simp
    push_cast
    ring

/-- `log s_{n+1} − log √π ≤ 1/(12(n+1))`. -/
theorem log_stirlingSeq_sub_log_sqrt_pi_le (n : ℕ) :
    Real.log (Stirling.stirlingSeq (n + 1)) - Real.log (Real.sqrt π)
      ≤ 1 / (12 * ((n : ℝ) + 1)) := by
  have hfin : ∀ M : ℕ, Real.log (Stirling.stirlingSeq (n + 1))
      - Real.log (Stirling.stirlingSeq (n + 1 + M))
      ≤ 1 / (12 * ((n : ℝ) + 1)) - 1 / (12 * (((n + 1 + M : ℕ) : ℝ))) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      have := log_stirlingSeq_sdiff_le_telescoping (n + M)
      rw [show n + M + 1 = n + 1 + M by omega, show n + M + 2 = n + 1 + (M + 1) by omega] at this
      push_cast at this ih ⊢
      ring_nf at this ih ⊢
      linarith
  have hlim : Tendsto (fun M : ℕ => Real.log (Stirling.stirlingSeq (n + 1))
      - Real.log (Stirling.stirlingSeq (n + 1 + M))) atTop
      (𝓝 (Real.log (Stirling.stirlingSeq (n + 1)) - Real.log (Real.sqrt π))) := by
    refine tendsto_const_nhds.sub ?_
    have hc : ContinuousAt Real.log (Real.sqrt π) :=
      Real.continuousAt_log (Real.sqrt_pos.mpr pi_pos).ne'
    have := hc.tendsto.comp
      (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat (n + 1)))
    refine this.congr fun M => ?_
    simp only [Function.comp_apply]
    rw [add_comm M (n + 1)]
  refine le_of_tendsto hlim (Eventually.of_forall fun M => ?_)
  have : 0 ≤ 1 / (12 * (((n + 1 + M : ℕ) : ℝ))) := by positivity
  linarith [hfin M]

/-- Stirling's formula with the `e^(1/(12n))` refinement: `n! ≤ √(2πn) (n/e)^n e^(1/(12n))` for
`n ≥ 1` (the matching lower bound is Mathlib's `Stirling.le_factorial_stirling`). -/
theorem factorial_le_stirling_refined {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ Real.sqrt (2 * π * n) * (n / exp 1) ^ n * exp (1 / (12 * n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := log_stirlingSeq_sub_log_sqrt_pi_le m
  have hs : 0 < Stirling.stirlingSeq (m + 1) := Stirling.stirlingSeq'_pos m
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr pi_pos
  rw [← Real.log_div hs.ne' hpi.ne', Real.log_le_iff_le_exp (by positivity),
    Stirling.stirlingSeq, div_div, div_le_iff₀ (by positivity)] at h
  have hsplit : Real.sqrt (2 * π * ((m + 1 : ℕ) : ℝ))
      = Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) * Real.sqrt π := by
    rw [← Real.sqrt_mul (by positivity)]
    ring_nf
  rw [hsplit]
  push_cast at h ⊢
  refine h.trans (le_of_eq ?_)
  ring

end BZ

end Azurite
