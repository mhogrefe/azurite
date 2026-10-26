/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.OneDivPiBracket
import Azurite.AzFloat.Equiv.PiBracket
import Azurite.AzFloat.Equiv.LogBaseFloatBracket

/-!
# Equivalence: the bracket of `1/π`

`oneDivPiBracket_spec` (through `divBracketByPosBracket_spec` with the lower end `≥ 2`),
`oneDivPiApprox_spec` (a strict enclosure of width at most `oneDivPiEps w`, `π⁻¹` being
irrational) and the Ziv certificate `oneDivPiApprox_isSome_exists`.
-/

namespace Azurite.AzFloat

/-- The width bound of `oneDivPiBracket`. -/
noncomputable def oneDivPiEps (w : ℕ) : ℝ := divEps (1 / 2) 1 0 (piEps w) w

theorem tendsto_oneDivPiEps : Filter.Tendsto oneDivPiEps Filter.atTop (nhds 0) :=
  tendsto_divEps (1 / 2) 1 tendsto_const_nhds tendsto_piEps

theorem oneDivPiBracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (oneDivPiBracket w).1.toVal = some (lo : EReal) ∧
      (oneDivPiBracket w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.pi⁻¹ ∧ Real.pi⁻¹ ≤ hi ∧ hi - lo ≤ oneDivPiEps w := by
  obtain ⟨lv, hv, hlv, hhv, -, hlo, hhi, hwid⟩ := piBracket_spec hw
  have hpi : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  simp only [oneDivPiBracket]
  obtain ⟨lo, hi, hlo', hhi', h1, h2', h3⟩ :=
    divBracketByPosBracket_spec hw (X := (one, one))
      (B := (maxOf (piBracket w).1 two, (piBracket w).2)) (L := 1) (M := Real.pi) (ε := 0)
      (δ := piEps w) toVal_one' toVal_one'
      (toVal_maxOf hlv toVal_two) hhv (by linarith [le_max_right lv 2]) (max_le hlo.le hpi) hhi
      (by linarith [le_max_left lv 2]) le_rfl le_rfl (by norm_num)
  rw [one_div] at h1 h2'
  rw [abs_one] at h3
  refine ⟨lo, hi, hlo', hhi', h1, h2', ?_⟩
  unfold oneDivPiEps
  refine h3.trans (divEps_mono w ?_ (one_div_pos.mpr (by linarith [le_max_right lv 2])).le
    (by norm_num) le_rfl (by linarith))
  rw [div_le_div_iff₀ (by linarith [le_max_right lv 2]) (by norm_num)]
  linarith [le_max_right lv 2]

theorem oneDivPiApprox_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (oneDivPiApprox w).1 lv ∧ Rounds (oneDivPiApprox w).2 hv ∧
      lv < Real.pi⁻¹ ∧ Real.pi⁻¹ < hv ∧ hv - lv ≤ oneDivPiEps w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := oneDivPiBracket_spec hw
  obtain ⟨r1, r2, r3, r4⟩ := rounds_of_bracket hlo hhi h1 h2 irrational_pi.inv
  exact ⟨lo, hi, r1, r2, r3, r4, h3⟩

/-- The termination certificate for `1/π`. -/
theorem oneDivPiApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (oneDivPiApprox (w₀ * 2 ^ f)).1 (oneDivPiApprox (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode oneDivPiApprox irrational_pi.inv oneDivPiEps
    tendsto_oneDivPiEps 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩ := oneDivPiApprox_spec hw
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

end Azurite.AzFloat
