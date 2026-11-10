/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section4
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The psi function on the real line: recurrence, reflection, bounds, and its limit formula

Tools for DLMF 5.4.19 (`Section4Gauss.lean`) and 5.4.20 (`Section4Zeros.lean`).  `psiR x` is
`ψ(x)` for real `x` (`digamma_ofReal`: `ψ` is real there, §5.3).

* `psiR_add_one`, `psiR_add_nat` (the recurrence), `psiR_nat_add_one` (`ψ(n + 1) = Hₙ − γ`),
  `psiR_one_sub` (the reflection formula), `psiR_mono` (nondecreasing on `(0, ∞)`, §5.3),
  `continuousAt_psiR`.
* Bounds `ln n < ψ(n + 1) < ln(n + 1)` (`log_lt_psiR_nat_add_one`, `psiR_nat_add_one_lt_log`,
  from Mathlib's Euler–Mascheroni sequences), hence `psiR_bracket`.
* `tendsto_psiR_series`: `ψ(x) = lim_{N→∞} (ln N − ∑_{k<N} 1/(x + k))` for `x > 0` (the limit form
  of 5.7.6), from the recurrence and `ψ(x + N) − ln N → 0`.
-/

open Complex Filter Topology Set Finset
open scoped Real

namespace Azurite.DLMF

/-- `ψ(x)` for real `x`. -/
noncomputable def psiR (x : ℝ) : ℝ := (digamma (x : ℂ)).re

theorem digamma_ofReal (x : ℝ) : digamma (x : ℂ) = (psiR x : ℂ) :=
  Complex.ext (by simp [psiR]) (by simp [dlmf_5_3_F3_real])

theorem ofReal_not_mem_gammaPoles {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) : (x : ℂ) ∉ gammaPoles := by
  rw [not_mem_gammaPoles]
  intro m h
  exact hx m (by exact_mod_cast h)

/-- `ψ(x + 1) = ψ(x) + 1/x`. -/
theorem psiR_add_one {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) : psiR (x + 1) = psiR x + 1 / x := by
  have h := congrArg re
    (digamma_apply_add_one (x : ℂ) (not_mem_gammaPoles.mp (ofReal_not_mem_gammaPoles hx)))
  simp only [psiR]
  push_cast
  rw [h, add_re, ← ofReal_inv, ofReal_re, one_div]

/-- `ψ(x + n) = ψ(x) + ∑_{k<n} 1/(x + k)`. -/
theorem psiR_add_nat {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) (n : ℕ) :
    psiR (x + n) = psiR x + ∑ k ∈ range n, 1 / (x + k) := by
  have h := congrArg re
    (digamma_apply_add_nat (not_mem_gammaPoles.mp (ofReal_not_mem_gammaPoles hx)) n)
  simp only [psiR]
  push_cast
  rw [h, add_re, re_sum]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [show (x : ℂ) + k = ((x + k : ℝ) : ℂ) by push_cast; rfl, ← ofReal_inv, ofReal_re, one_div]

/-- `ψ(n + 1) = Hₙ − γ`. -/
theorem psiR_nat_add_one (n : ℕ) :
    psiR (n + 1) = (harmonic n : ℝ) - Real.eulerMascheroniConstant := by
  simp only [psiR]
  push_cast
  rw [digamma_nat_add_one]
  simp

theorem log_lt_psiR_nat_add_one {n : ℕ} (hn : n ≠ 0) : Real.log n < psiR (n + 1) := by
  rw [psiR_nat_add_one]
  have := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  simp only [Real.eulerMascheroniSeq', hn, ↓reduceIte] at this
  linarith

theorem psiR_nat_add_one_lt_log (n : ℕ) : psiR (n + 1) < Real.log (n + 1) := by
  rw [psiR_nat_add_one]
  have := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  simp only [Real.eulerMascheroniSeq] at this
  linarith

/-- `ψ` is nondecreasing on `(0, ∞)` (§5.3). -/
theorem psiR_mono : MonotoneOn psiR (Ioi 0) := dlmf_5_3_F3_mono

/-- For `n + 1 ≤ y ≤ n + 1 + m`, `n ≥ 1`: `ln n ≤ ψ(y) ≤ ln(n + 1 + m)`. -/
theorem psiR_bracket {n m : ℕ} (hn : n ≠ 0) {y : ℝ} (h1 : (n : ℝ) + 1 ≤ y)
    (h2 : y ≤ n + 1 + m) : Real.log n ≤ psiR y ∧ psiR y ≤ Real.log (n + 1 + m) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  constructor
  · exact (log_lt_psiR_nat_add_one hn).le.trans
      (psiR_mono (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr (by linarith)) h1)
  · have hu := psiR_nat_add_one_lt_log (n + m)
    push_cast at hu
    rw [show (n : ℝ) + 1 + m = n + m + 1 by ring]
    refine le_trans (psiR_mono (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr (by linarith))
      (by linarith)) hu.le

theorem log_sub_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log a - Real.log b ≤ (a - b) / b := by
  rw [← Real.log_div ha.ne' hb.ne']
  have := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [sub_div, div_self hb.ne']
  exact this

theorem continuousAt_psiR {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) : ContinuousAt psiR x :=
  continuous_re.continuousAt.comp
    ((dlmf_5_2_2_analytic _ (ofReal_not_mem_gammaPoles hx)).continuousAt.comp
      continuous_ofReal.continuousAt)

/-- The reflection formula on the real line: `ψ(1 − x) = ψ(x) + π cot(πx)`, `x ∉ ℤ`. -/
theorem psiR_one_sub {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) :
    psiR (1 - x) = psiR x + π * Real.cot (π * x) := by
  have hx' : ∀ n : ℤ, (x : ℂ) ≠ n := fun n h => hx n (by exact_mod_cast h)
  have h := congrArg re (digamma_one_sub hx')
  simp only [psiR]
  push_cast
  rw [h, add_re, show (π : ℂ) * cot (π * x) = ((π * Real.cot (π * x) : ℝ) : ℂ) by
    push_cast; rfl, ofReal_re]

/-- **The limit form of 5.7.6**: `ψ(x) = lim_{N→∞} (ln N − ∑_{k<N} 1/(x + k))`, `x > 0`. -/
theorem tendsto_psiR_series {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ => Real.log N - ∑ k ∈ range N, 1 / (x + k)) atTop (𝓝 (psiR x)) := by
  have hxp : ∀ m : ℕ, x ≠ -m := fun m h => by
    have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  set m := ⌈x⌉₊ with hm
  have hxm : x ≤ m := Nat.le_ceil x
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have key : ∀ n : ℕ, 1 ≤ n →
      ‖Real.log ((n + 1 : ℕ) : ℝ) - psiR (x + ((n + 1 : ℕ) : ℝ))‖ ≤ (m + 1) / n := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    obtain ⟨hl, hu⟩ := psiR_bracket (m := m) hn0 (y := x + ((n + 1 : ℕ) : ℝ))
      (by push_cast; linarith) (by push_cast; linarith)
    push_cast at hl hu ⊢
    have e1 := log_sub_log_le (a := (n : ℝ) + 1) (b := n) (by linarith) (by linarith)
    have e2 := log_sub_log_le (a := (n : ℝ) + 1 + m) (b := (n : ℝ) + 1) (by linarith)
      (by linarith)
    have e3 : ((n : ℝ) + 1 - n) / n ≤ (m + 1) / n := by
      apply div_le_div_of_nonneg_right _ (by linarith); linarith
    have e4 : ((n : ℝ) + 1 + m - (n + 1)) / (n + 1) ≤ (m + 1) / n := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hrec : ∀ N : ℕ, Real.log N - ∑ k ∈ range N, 1 / (x + k)
      = psiR x + (Real.log N - psiR (x + N)) := by
    intro N; rw [psiR_add_nat hxp N]; ring
  have hg : Tendsto (fun N : ℕ => Real.log N - psiR (x + N)) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat ((m : ℝ) + 1))
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact key n hn
  have h := (tendsto_const_nhds (x := psiR x)).add hg
  rw [add_zero] at h
  exact h.congr fun N => (hrec N).symm

end Azurite.DLMF
