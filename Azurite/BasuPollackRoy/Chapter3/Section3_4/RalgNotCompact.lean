/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_4.NotCompact
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_11
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

/-! # BPR §3.4 — `[0, 1] ⊆ ℝ_alg` is not compact

The closed bounded interval `[0, 1]` over the real algebraic numbers `ℝ_alg` is **not compact**: the
family `{[0, r) ∪ (s, 1] | 0 < r < c < s < 1}` is an open cover with no finite subcover, where `c` is
a transcendental real (BPR uses `π/4`; since `π`'s transcendence is not in Mathlib we use the
fractional part of a Liouville number, an explicit transcendental in `(0, 1)`). The gap at `c` cannot
be reached by `ℝ_alg`, so no finite subfamily covers `[0, 1]`. -/

namespace Azurite.BPR

open Azurite.BPR.Exercise2_11

/-- There is an explicit transcendental real in `(0, 1)`: the fractional part of a Liouville number.
(It is `∉ ℝ_alg` because adding back the integer part would otherwise make the Liouville number
algebraic.) -/
theorem exists_transcendental_R_alg_mem_Ioo01 : ∃ g : ℝ, g ∉ R_alg ∧ 0 < g ∧ g < 1 := by
  set c : ℝ := liouvilleNumber ((2 : ℕ) : ℝ) with hcdef
  have hc : c ∉ R_alg := by
    rw [mem_R_alg_iff_isAlgebraic_int]
    exact transcendental_liouvilleNumber (by norm_num)
  have hfloor_mem : ((⌊c⌋ : ℤ) : ℝ) ∈ R_alg := intCast_mem R_alg ⌊c⌋
  refine ⟨Int.fract c, ?_, ?_, Int.fract_lt_one c⟩
  · intro hg
    exact hc (by rw [← Int.fract_add_floor c]; exact add_mem hg hfloor_mem)
  · rcases lt_or_eq_of_le (Int.fract_nonneg c) with h | h
    · exact h
    · exfalso
      apply hc
      have h2 := Int.floor_add_fract c
      rw [← h, add_zero] at h2
      rw [← h2]
      exact hfloor_mem

/-- **BPR §3.4, example: `[0, 1] ⊆ ℝ_alg` is not compact.** The closed bounded unit interval over the
real algebraic numbers is not compact, witnessed by the transcendental-gap cover. -/
theorem not_isCompact_unitIcc_R_alg :
    ¬ IsCompact (unitIcc : Set (Fin 1 → R_alg)) := by
  obtain ⟨g, hg_nmem, hg_pos, hg_lt1⟩ := exists_transcendental_R_alg_mem_Ioo01
  apply not_isCompact_unitIcc_of_cover
    {p : R_alg × R_alg | 0 < p.1 ∧ (↑p.1 : ℝ) < g ∧ g < (↑p.2 : ℝ) ∧ p.2 < 1}
  · -- cover
    intro u hu0 hu1
    have hu0R : (0 : ℝ) ≤ (↑(u 0) : ℝ) := by exact_mod_cast hu0
    have hu1R : (↑(u 0) : ℝ) ≤ 1 := by exact_mod_cast hu1
    have hne : (↑(u 0) : ℝ) ≠ g := fun h => hg_nmem (h ▸ (u 0).2)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `↑(u 0) < g`: cover `u` by `[0, r)`.
      obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hlt
      obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn hg_lt1
      have hca : (↑(((a : ℚ) : R_alg)) : ℝ) = (a : ℝ) := by push_cast; ring
      have hcb : (↑(((b : ℚ) : R_alg)) : ℝ) = (b : ℝ) := by push_cast; ring
      refine ⟨(((a : ℚ) : R_alg), ((b : ℚ) : R_alg)), ⟨?_, ?_, ?_, ?_⟩, Or.inl ?_⟩
      · rw [← Subtype.coe_lt_coe]; simp only [ZeroMemClass.coe_zero, hca]; linarith
      · rw [hca]; exact ha2
      · rw [hcb]; exact hb1
      · rw [← Subtype.coe_lt_coe]; simp only [OneMemClass.coe_one, hcb]; exact hb2
      · rw [← Subtype.coe_lt_coe, hca]; exact ha1
    · -- `g < ↑(u 0)`: cover `u` by `(s, 1]`.
      obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hg_pos
      obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn hgt
      have hca : (↑(((a : ℚ) : R_alg)) : ℝ) = (a : ℝ) := by push_cast; ring
      have hcb : (↑(((b : ℚ) : R_alg)) : ℝ) = (b : ℝ) := by push_cast; ring
      refine ⟨(((a : ℚ) : R_alg), ((b : ℚ) : R_alg)), ⟨?_, ?_, ?_, ?_⟩, Or.inr ?_⟩
      · rw [← Subtype.coe_lt_coe]; simp only [ZeroMemClass.coe_zero, hca]; exact ha1
      · rw [hca]; exact ha2
      · rw [hcb]; exact hb1
      · rw [← Subtype.coe_lt_coe]; simp only [OneMemClass.coe_one, hcb]; linarith
      · rw [← Subtype.coe_lt_coe, hcb]; exact hb2
  · -- separation: `↑p.1 < g < ↑q.2`
    rintro p ⟨_, hp2, _, _⟩ q ⟨_, _, hq3, _⟩
    rw [← Subtype.coe_lt_coe]; linarith
  · rintro p ⟨hp1, _, _, _⟩; exact hp1
  · rintro p ⟨_, _, _, hp4⟩; exact hp4

end Azurite.BPR
