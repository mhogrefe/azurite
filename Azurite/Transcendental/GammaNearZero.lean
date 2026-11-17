/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# The gamma function next to its pole at `0`

For `0 < |x| ≤ 1/2`:

* `gamma_near_zero`: `1/x − 2 < Γ(x) < 1/x`;
* `inv_gamma_near_zero`: `x < 1/Γ(x) < x + x²`.

Both follow from `Γ(x) = Γ(1 + x) / x` and the position of `Γ` relative to `1`:
`Γ < 1` on `(1, 2)` (`Real.Gamma_lt_one`, by convexity through `Γ(3/2) < 1`), `Γ > 1` on
`(0, 1)` and beyond `2` (Mathlib's strict monotonicity).  They are what the tiny-argument paths
of `AzFloat.gammaPrecRound` and `AzFloat.reciprocalGammaPrecRound` use.
-/

namespace Azurite

open Real Set

/-- `Γ(t) < 1` for `1 < t < 2`. -/
theorem Gamma_lt_one_of_mem_Ioo {t : ℝ} (h1 : 1 < t) (h2 : t < 2) : Gamma t < 1 := by
  have h32 := Gamma_three_div_two_lt_one
  rcases le_total t (3 / 2) with h | h
  · -- `t` between `1` and `3/2`
    have hc := convexOn_Gamma.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
      (show (3 / 2 : ℝ) ∈ Ioi 0 by norm_num) (show (0 : ℝ) ≤ 2 * (3 / 2 - t) by linarith)
      (show (0 : ℝ) ≤ 2 * (t - 1) by linarith) (by ring)
    simp only [smul_eq_mul, Gamma_one] at hc
    have ht : 2 * (3 / 2 - t) * 1 + 2 * (t - 1) * (3 / 2) = t := by ring
    rw [ht] at hc
    nlinarith
  · have hc := convexOn_Gamma.2 (show (3 / 2 : ℝ) ∈ Ioi 0 by norm_num)
      (show (2 : ℝ) ∈ Ioi 0 by norm_num) (show (0 : ℝ) ≤ 2 * (2 - t) by linarith)
      (show (0 : ℝ) ≤ 2 * (t - 3 / 2) by linarith) (by ring)
    simp only [smul_eq_mul, Gamma_two] at hc
    have ht : 2 * (2 - t) * (3 / 2) + 2 * (t - 3 / 2) * 2 = t := by ring
    rw [ht] at hc
    nlinarith

/-- `Γ(t) > 1` for `0 < t < 1`. -/
theorem one_lt_Gamma_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : 1 < Gamma t := by
  have := Gamma_strictAntiOn_Ioc ⟨h0, h1.le⟩ ⟨one_pos, le_rfl⟩ h1
  rwa [Gamma_one] at this

/-- `Γ(t) > 1` for `t > 2`. -/
theorem one_lt_Gamma_of_two_lt {t : ℝ} (h2 : 2 < t) : 1 < Gamma t := by
  have := Gamma_strictMonoOn_Ici (mem_Ici.mpr le_rfl) (mem_Ici.mpr h2.le) h2
  rwa [Gamma_two] at this

/-- `Γ(1 + x)` between `1` and `1/(1 + x)`, on the side that the sign of `x` decides. -/
theorem gamma_one_add_bounds {x : ℝ} (hx : |x| ≤ 1 / 2) :
    (0 < x → 1 < (1 + x) * Gamma (1 + x) ∧ Gamma (1 + x) < 1) ∧
      (x < 0 → (1 + x) * Gamma (1 + x) < 1 ∧ 1 < Gamma (1 + x)) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hx
  have hrec : Gamma (1 + x + 1) = (1 + x) * Gamma (1 + x) :=
    Gamma_add_one (by linarith : (1 + x : ℝ) ≠ 0)
  constructor
  · intro hpos
    refine ⟨?_, Gamma_lt_one_of_mem_Ioo (by linarith) (by linarith)⟩
    rw [← hrec]
    exact one_lt_Gamma_of_two_lt (by linarith)
  · intro hneg
    refine ⟨?_, one_lt_Gamma_of_lt_one (by linarith) (by linarith)⟩
    rw [← hrec]
    exact Gamma_lt_one_of_mem_Ioo (by linarith) (by linarith)

/-- **`x < 1/Γ(x) < x + x²`** for `0 < |x| ≤ 1/2`. -/
theorem inv_gamma_near_zero {x : ℝ} (hx0 : x ≠ 0) (hx : |x| ≤ 1 / 2) :
    x < (Gamma x)⁻¹ ∧ (Gamma x)⁻¹ < x + x ^ 2 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hx
  obtain ⟨hP, hN⟩ := gamma_one_add_bounds hx
  have hg : Gamma (1 + x) = x * Gamma x := by rw [add_comm]; exact Gamma_add_one hx0
  have hgpos : 0 < Gamma (1 + x) := Gamma_pos_of_pos (by linarith)
  have hinv : (Gamma x)⁻¹ = x / Gamma (1 + x) := by
    have hG0 : Gamma x ≠ 0 := fun h => by rw [hg, h, mul_zero] at hgpos; exact lt_irrefl _ hgpos
    rw [hg]; field_simp
  rw [hinv]
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · obtain ⟨h1, h2⟩ := hN hneg
    constructor
    · rw [lt_div_iff₀ hgpos]; nlinarith
    · rw [div_lt_iff₀ hgpos]; nlinarith
  · obtain ⟨h1, h2⟩ := hP hpos
    constructor
    · rw [lt_div_iff₀ hgpos]; nlinarith
    · rw [div_lt_iff₀ hgpos]; nlinarith

/-- **`1/x − 2 < Γ(x) < 1/x`** for `0 < |x| ≤ 1/2`. -/
theorem gamma_near_zero {x : ℝ} (hx0 : x ≠ 0) (hx : |x| ≤ 1 / 2) :
    1 / x - 2 < Gamma x ∧ Gamma x < 1 / x := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hx
  obtain ⟨hP, hN⟩ := gamma_one_add_bounds hx
  have hg : Gamma (1 + x) = x * Gamma x := by rw [add_comm]; exact Gamma_add_one hx0
  have hG : Gamma x = Gamma (1 + x) / x := by rw [hg]; field_simp
  rw [hG]
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · obtain ⟨h1, h2⟩ := hN hneg
    constructor
    · rw [lt_div_iff_of_neg hneg, sub_mul, one_div, inv_mul_cancel₀ hx0]; nlinarith
    · have e : 1 / x - Gamma (1 + x) / x = (1 - Gamma (1 + x)) * x⁻¹ := by ring
      have := mul_pos_of_neg_of_neg (by linarith : 1 - Gamma (1 + x) < 0) (inv_lt_zero.mpr hneg)
      linarith
  · obtain ⟨h1, h2⟩ := hP hpos
    constructor
    · rw [lt_div_iff₀ hpos, sub_mul, one_div, inv_mul_cancel₀ hx0]; nlinarith
    · exact div_lt_div_of_pos_right h2 hpos

end Azurite
