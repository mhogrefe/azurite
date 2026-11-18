/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section3
import Azurite.DLMF.Chapter5.Section4Zeros
import Azurite.DLMF.Chapter5.Section6

/-!
# The zeros of `ψ` on the real line: enclosures from a residual

The real zeros of `ψ` (DLMF §5.4(iii), Table 5.4.1) are `x₀ = 1.4616…`, the minimum of `Γ` on
`(0, ∞)` (`psiZeroPos`, from `DLMF.dlmf_5_3_F1_min`: `1 < x₀ < 3/2`), and for `n ≥ 1` the zero
`xₙ = DLMF.psiZero n` in `(−n, −n + 1)`.  `psiZeroAt n` is `xₙ` for every `n`.

The facts behind `AzFloat.psiZeroPrecRound` are lower bounds of the slope of `ψ` that need no
derivative:

* `psiR_sub_ge_pos`: `1/a − 1/b ≤ ψ(b) − ψ(a)` for `0 < a ≤ b` (the first term of
  `ψ(b) − ψ(a) = ∑ (1/(a + k) − 1/(b + k))`);
* `psiR_sub_ge_neg`: `y − x ≤ ψ(y) − ψ(x)` for `x ≤ y` in `(−n, −n + 1)` (the term `k = n − 1`
  of the recurrence, where `x + k` and `y + k` lie in `(−1, 0)`).

So a point `x` with a small residual is near the zero: `|x₀ − x| ≤ 4 |ψ(x)|` for `0 < x ≤ 2`
(`abs_psiZeroAt_zero_sub_le`) and `|xₙ − x| ≤ |ψ(x)|` for `x` in `(−n, −n + 1)`
(`abs_psiZeroAt_sub_le`).
-/

open Finset Set Filter Topology

namespace Azurite

open DLMF

theorem exists_psiZeroPos : ∃ x : ℝ, 1 < x ∧ x < 3 / 2 ∧ psiR x = 0 := by
  obtain ⟨x₀, h1, h2, -, -, hψ⟩ := dlmf_5_3_F1_min
  refine ⟨x₀, h1, h2, ?_⟩
  rw [digamma_ofReal] at hψ
  exact_mod_cast hψ

/-- The positive zero `x₀ = 1.4616…` of `ψ`, where `Γ` has its minimum on `(0, ∞)`. -/
noncomputable def psiZeroPos : ℝ := Classical.choose exists_psiZeroPos

theorem psiZeroPos_spec : 1 < psiZeroPos ∧ psiZeroPos < 3 / 2 ∧ psiR psiZeroPos = 0 :=
  Classical.choose_spec exists_psiZeroPos

/-- The `n`-th real zero of `ψ` (DLMF Table 5.4.1): `x₀ = 1.4616…`, and `xₙ ∈ (−n, −n + 1)` for
`n ≥ 1`. -/
noncomputable def psiZeroAt (n : ℕ) : ℝ := if n = 0 then psiZeroPos else psiZero n

theorem psiZeroAt_zero : psiZeroAt 0 = psiZeroPos := by simp [psiZeroAt]

theorem psiZeroAt_of_pos {n : ℕ} (hn : 1 ≤ n) : psiZeroAt n = psiZero n := by
  rw [psiZeroAt, ite_eq_right (by omega)]

/-- `1/a − 1/b ≤ ψ(b) − ψ(a)` for `0 < a ≤ b`. -/
theorem psiR_sub_ge_pos {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) :
    1 / a - 1 / b ≤ psiR b - psiR a := by
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  set S : ℕ → ℝ := fun N => ∑ k ∈ range N, (1 / (a + k) - 1 / (b + k)) with hS
  have hlim : Tendsto S atTop (𝓝 (psiR b - psiR a)) := by
    refine ((tendsto_psiR_series hb0).sub (tendsto_psiR_series ha0)).congr fun N => ?_
    simp only [hS, sum_sub_distrib]
    ring
  have hterm : ∀ k : ℕ, 0 ≤ 1 / (a + k) - 1 / (b + k) := fun k => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hmono : Monotone S := monotone_nat_of_le_succ fun N => by
    simp only [hS, sum_range_succ]
    linarith [hterm N]
  have h1 := hmono.ge_of_tendsto hlim 1
  simpa only [hS, sum_range_one, Nat.cast_zero, add_zero] using h1

/-- `y − x ≤ ψ(y) − ψ(x)` for `x ≤ y` in `(−n, −n + 1)`, `n ≥ 1`. -/
theorem psiR_sub_ge_neg {n : ℕ} (hn : 1 ≤ n) {x y : ℝ}
    (hx : x ∈ Ioo (-(n : ℝ)) (-(n : ℝ) + 1)) (hy : y ∈ Ioo (-(n : ℝ)) (-(n : ℝ) + 1))
    (hxy : x ≤ y) : y - x ≤ psiR y - psiR x := by
  have ex := psiR_add_nat (not_neg_nat_of_mem_Ioo hx) n
  have ey := psiR_add_nat (not_neg_nat_of_mem_Ioo hy) n
  have hmono : psiR (x + n) ≤ psiR (y + n) :=
    psiR_mono (mem_Ioi.mpr (by linarith [hx.1])) (mem_Ioi.mpr (by linarith [hy.1]))
      (by linarith)
  have hterm : ∀ k ∈ range n, 0 ≤ 1 / (x + k) - 1 / (y + k) := fun k hk => by
    have hk1 : (k : ℝ) + 1 ≤ n := by exact_mod_cast mem_range.mp hk
    rw [sub_nonneg]
    exact one_div_le_one_div_of_neg_of_le (by linarith [hy.2]) (by linarith)
  -- the term `k = n − 1`
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hlast : y - x ≤ 1 / (x + (j : ℕ)) - 1 / (y + (j : ℕ)) := by
    have hx1 := hx.1
    have hx2 := hx.2
    have hy1 := hy.1
    have hy2 := hy.2
    push_cast at hx1 hx2 hy1 hy2
    have hxj : x + j < 0 := by linarith
    have hyj : y + j < 0 := by linarith
    have hxj' : -1 < x + j := by linarith
    have hyj' : -1 < y + j := by linarith
    rw [div_sub_div _ _ hxj.ne hyj.ne, le_div_iff₀ (mul_pos_of_neg_of_neg hxj hyj)]
    have hp : (x + j) * (y + j) ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hxy)]
  have hsum : y - x ≤ ∑ k ∈ range (j + 1), (1 / (x + k) - 1 / (y + k)) := by
    rw [sum_range_succ]
    have : 0 ≤ ∑ k ∈ range j, (1 / (x + (k : ℕ)) - 1 / (y + (k : ℕ))) :=
      sum_nonneg fun k hk => hterm k (mem_range.mpr (by have := mem_range.mp hk; omega))
    linarith
  rw [sum_sub_distrib] at hsum
  linarith

/-- **A point near the positive zero**: `|x₀ − x| ≤ 4 δ` when `0 < x ≤ 2` and `|ψ(x)| ≤ δ`. -/
theorem abs_psiZeroAt_zero_sub_le {x δ : ℝ} (hx0 : 0 < x) (hx2 : x ≤ 2) (hδ : |psiR x| ≤ δ) :
    |psiZeroAt 0 - x| ≤ 4 * δ := by
  rw [psiZeroAt_zero]
  obtain ⟨h1, h2, hz⟩ := psiZeroPos_spec
  set z := psiZeroPos
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hδ
  obtain ⟨hl, hu⟩ := abs_le.mp hδ
  have hz0 : 0 < z := by linarith
  have hxz : 0 < x * z := mul_pos hx0 hz0
  have hprod : x * z ≤ 4 := by nlinarith
  rw [abs_le]
  rcases le_total x z with h | h
  · have hs := psiR_sub_ge_pos hx0 h
    rw [hz, div_sub_div _ _ hx0.ne' hz0.ne', div_le_iff₀ hxz] at hs
    constructor <;> nlinarith
  · have hs := psiR_sub_ge_pos hz0 h
    rw [hz, div_sub_div _ _ hz0.ne' hx0.ne', div_le_iff₀ (mul_pos hz0 hx0)] at hs
    constructor <;> nlinarith

/-- **A point near a negative zero**: `|xₙ − x| ≤ δ` when `x ∈ (−n, −n + 1)` and
`|ψ(x)| ≤ δ`. -/
theorem abs_psiZeroAt_sub_le {n : ℕ} (hn : 1 ≤ n) {x δ : ℝ}
    (hx : x ∈ Ioo (-(n : ℝ)) (-(n : ℝ) + 1)) (hδ : |psiR x| ≤ δ) : |psiZeroAt n - x| ≤ δ := by
  rw [psiZeroAt_of_pos hn]
  obtain ⟨hmem, hz⟩ := psiZero_spec hn
  obtain ⟨hl, hu⟩ := abs_le.mp hδ
  rw [abs_le]
  rcases le_total x (psiZero n) with h | h
  · have hs := psiR_sub_ge_neg hn hx hmem h
    rw [hz] at hs
    constructor <;> linarith
  · have hs := psiR_sub_ge_neg hn hmem hx h
    rw [hz] at hs
    constructor <;> linarith

end Azurite
