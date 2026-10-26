/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PiDiv3Bracket
import Azurite.AzFloat.Equiv.PiBracket
import Azurite.AzFloat.Equiv.LogBasePow2Bracket

/-!
# Equivalence: the bracket of `π/3`

`piDiv3Approx_spec` (a strict enclosure of width at most `piDiv3Eps w`, from `piBracket_spec`
and `divBracketByInt_spec`) and the Ziv certificate `piDiv3Approx_isSome_exists`
(`π/3` is irrational).
-/

namespace Azurite.AzFloat

/-- The width bound of `piDiv3Approx`. -/
noncomputable def piDiv3Eps (w : ℕ) : ℝ := piEps w + 4 * (|Real.pi| + piEps w) * (1 / 2 : ℝ) ^ w

theorem tendsto_piDiv3Eps : Filter.Tendsto piDiv3Eps Filter.atTop (nhds 0) := by
  have hp := tendsto_piEps
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hA : Filter.Tendsto (fun _ : ℕ => |Real.pi|) Filter.atTop (nhds |Real.pi|) :=
    tendsto_const_nhds
  have := hp.add (((hA.add hp).const_mul 4).mul hu)
  simp only [mul_zero, add_zero] at this
  exact this

theorem irrational_pi_div_three : Irrational (Real.pi / 3) := by
  have h := irrational_pi.div_natCast (by norm_num : (3 : ℕ) ≠ 0)
  simpa using h

theorem ofInt_three_ne_zero : AzInt.ofInt 3 ≠ 0 := fun h => by
  have := congrArg AzInt.toInt h
  rw [AzInt.toInt_ofInt, AzInt.toInt_zero] at this
  omega

theorem piDiv3Approx_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (piDiv3Approx w).1 lv ∧ Rounds (piDiv3Approx w).2 hv ∧
      lv < Real.pi / 3 ∧ Real.pi / 3 < hv ∧ hv - lv ≤ piDiv3Eps w := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨lo, hi, hlo, hhi, -, h1, h2, h3⟩ := piBracket_spec hw
  have h3' : ((AzInt.ofInt 3).toInt : ℝ) = 3 := by rw [AzInt.toInt_ofInt]; norm_num
  obtain ⟨lv, hv, hl, hh, hlo', hhi', hwid⟩ := divBracketByInt_spec (w := w) hlo hhi h1.le h2 h3
    (AzInt.ofInt 3) ofInt_three_ne_zero (by rw [h3']; exact irrational_pi_div_three)
  rw [h3'] at hlo' hhi'
  exact ⟨lv, hv, hl, hh, hlo', hhi', hwid⟩

/-- The termination certificate for `π/3`. -/
theorem piDiv3Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (piDiv3Approx (w₀ * 2 ^ f)).1 (piDiv3Approx (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode piDiv3Approx irrational_pi_div_three piDiv3Eps
    tendsto_piDiv3Eps 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩ := piDiv3Approx_spec hw
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

end Azurite.AzFloat
