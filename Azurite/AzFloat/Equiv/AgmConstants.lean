/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AgmConstants
import Azurite.AzFloat.Equiv.EnclConv
import Azurite.BrentZimmermann.Chapter4.Lemniscate
import Azurite.Chudnovsky.GammaValues

/-!
# The constants computed with the AGM: convergence, irrationality, Ziv certificates

* `gammaOneQuarterEncl_conv`, `gammaOneThirdEncl_conv`, `gaussBracket_conv`,
  `lemniscateBracket_conv`: the enclosures of `Γ(1/4)`, `Γ(1/3)`, Gauss's constant
  `G = 1/AGM(1, √2)` and the lemniscate constant `ϖ = π G` converge (`LConv`,
  `Equiv/EnclConv.lean`).
* `irrational_gauss`, `irrational_lemniscate`: `G = Γ(1/4)²/(2π √(2π))` and `ϖ` are irrational,
  since `Γ(1/4)` is not algebraic over `ℚ(π)` (Chudnovsky's theorem,
  `Chudnovsky.not_algOver_gamma_one_quarter`).
* `gammaOneQuarterApprox_cert`, `gammaOneThirdApprox_cert`, `gaussApprox_cert`,
  `lemniscateApprox_cert`: the Ziv certificates.
-/

namespace Azurite.AzFloat

open Azurite.BZ Azurite.Chudnovsky Real

/-! ### Convergence of the enclosures -/

/-- **The enclosure of `Γ(1/4)` converges.** -/
theorem gammaOneQuarterEncl_conv : LConv gammaOneQuarterEncl (Real.Gamma (1 / 4)) := by
  have h2 := LConv.nat (n := 2) (by norm_num)
  have hM := (LConv.const toVal_one' one_pos).agm 32 (h2.sqrt 32)
  have hT := h2.mul 32 (LConv.pi 32)
  have hE := ((hT.mul 32 (hT.sqrt 32)).div 32 hM).sqrt 32
  have hval : Real.sqrt (((2 : ℕ) : ℝ) * π * Real.sqrt (((2 : ℕ) : ℝ) * π)
      / AGM 1 (Real.sqrt ((2 : ℕ) : ℝ))) = Real.Gamma (1 / 4) := by
    have hg : 0 ≤ Real.Gamma (1 / 4) := (Real.Gamma_pos_of_pos (by norm_num)).le
    rw [← Real.sqrt_sq hg, gamma_one_quarter_sq]
    norm_num
  rw [hval] at hE
  exact hE

/-- **The enclosure of `Γ(1/3)` converges.** -/
theorem gammaOneThirdEncl_conv : LConv gammaOneThirdEncl (Real.Gamma (1 / 3)) := by
  have h3 := LConv.nat (n := 3) (by norm_num)
  have h2 := LConv.nat (n := 2) (by norm_num)
  have hr := h3.sqrt 32
  have hA := ((hr.add 32 h3.half).half).sqrt 32
  have hM := hA.agm 32 (hr.sqrt 32)
  have hP := LConv.pi 32
  have hN := (h2.mul 32 (h2.cbrt 32)).mul 32 (hP.mul 32 hP)
  have hE := (hN.div 32 hM).cbrt 32
  have hval : realCbrt (((2 : ℕ) : ℝ) * realCbrt ((2 : ℕ) : ℝ) * (π * π)
      / AGM (Real.sqrt ((Real.sqrt ((3 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) / 2) / 2))
        (Real.sqrt (Real.sqrt ((3 : ℕ) : ℝ)))) = Real.Gamma (1 / 3) := by
    have hg : 0 ≤ Real.Gamma (1 / 3) := (Real.Gamma_pos_of_pos (by norm_num)).le
    apply realCbrt_eq_of_pow_three hg
    rw [gamma_one_third_cube (realCbrt_pos (by norm_num : (0 : ℝ) < 2)) (realCbrt_pow_three 2)]
    push_cast
    ring
  rw [hval] at hE
  exact hE

/-- **The bracket of Gauss's constant converges.** -/
theorem gaussBracket_conv : LConv gaussBracket (AGM 1 (Real.sqrt 2))⁻¹ := by
  have hb := (LConv.const toVal_two (by norm_num : (0 : ℝ) < 2)).sqrt 0
  have hR := (LConv.const toVal_one' one_pos).agmRaw 0 hb
  have hE := (LConv.const toVal_one' one_pos).div 0 hR
  rw [one_div] at hE
  exact hE

/-- **The bracket of the lemniscate constant converges.** -/
theorem lemniscateBracket_conv : LConv lemniscateBracket BZ.lemniscate := by
  have hE := (LConv.pi 0).mul 0 gaussBracket_conv
  rw [← lemniscate_eq_pi_mul_gauss] at hE
  exact hE

/-! ### Irrationality of Gauss's constant and of the lemniscate constant -/

/-- Gauss's constant is not algebraic over `ℚ(π)`: `Γ(1/4)² = 2π √(2π) G`. -/
theorem not_algOver_gauss :
    ¬ AlgOver (Real.pi : ℂ) (((AGM 1 (Real.sqrt 2))⁻¹ : ℝ) : ℂ) := by
  intro h
  apply not_algOver_gamma_one_quarter
  have hπ : AlgOver (Real.pi : ℂ) (Real.pi : ℂ) := algOver_self _
  have h2π : AlgOver (Real.pi : ℂ) (((2 : ℕ) : ℂ) * Real.pi) := (algOver_natCast _ 2).mul hπ
  have hs : AlgOver (Real.pi : ℂ) ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
    refine AlgOver.of_pow (n := 2) (by norm_num) ?_
    have e : ((Real.sqrt (2 * π) : ℝ) : ℂ) ^ 2 = ((2 : ℕ) : ℂ) * Real.pi := by
      have := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * π)
      exact_mod_cast this
    rw [e]
    exact h2π
  refine AlgOver.of_pow (n := 2) (by norm_num) ?_
  have e : ((Real.Gamma (1 / 4) : ℝ) : ℂ) ^ 2
      = ((2 : ℕ) : ℂ) * Real.pi * ((Real.sqrt (2 * π) : ℝ) : ℂ)
        * (((AGM 1 (Real.sqrt 2))⁻¹ : ℝ) : ℂ) := by
    have := gamma_one_quarter_sq
    rw [div_eq_mul_inv] at this
    exact_mod_cast this
  rw [e]
  exact (h2π.mul hs).mul h

/-- **Gauss's constant `1/AGM(1, √2)` is irrational** (Chudnovsky). -/
theorem irrational_gauss : Irrational (AGM 1 (Real.sqrt 2))⁻¹ :=
  irrational_of_not_algOver not_algOver_gauss

/-- **The lemniscate constant `ϖ = π/AGM(1, √2)` is irrational** (Chudnovsky). -/
theorem irrational_lemniscate : Irrational BZ.lemniscate := by
  refine irrational_of_not_algOver (ϖ := (Real.pi : ℂ)) fun h => not_algOver_gauss ?_
  have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : (((AGM 1 (Real.sqrt 2))⁻¹ : ℝ) : ℂ) = (BZ.lemniscate : ℂ) / (Real.pi : ℂ) := by
    rw [lemniscate_eq_pi_mul_gauss]
    push_cast
    field_simp
  rw [e]
  exact h.div hπ0 (algOver_self _)

/-! ### The certificates -/

/-- **The Ziv certificate of `Γ(1/4)`.** -/
theorem gammaOneQuarterApprox_cert (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (gammaOneQuarterApprox (w₀ * 2 ^ f)).1
      (gammaOneQuarterApprox (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  gammaOneQuarterEncl_conv.lnGammaApproxOf_bracketConv.exists_isSome
    (Real.Gamma_pos_of_pos (by norm_num)).ne' p
    (not_mem_floatSet_of_irrational p (irrational_of_not_algOver not_algOver_gamma_one_quarter))
    mode w₀ hw₀

/-- **The Ziv certificate of `Γ(1/3)`.** -/
theorem gammaOneThirdApprox_cert (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (gammaOneThirdApprox (w₀ * 2 ^ f)).1
      (gammaOneThirdApprox (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  gammaOneThirdEncl_conv.lnGammaApproxOf_bracketConv.exists_isSome
    (Real.Gamma_pos_of_pos (by norm_num)).ne' p
    (not_mem_floatSet_of_irrational p (irrational_of_not_algOver not_algOver_gamma_one_third))
    mode w₀ hw₀

/-- **The Ziv certificate of Gauss's constant.** -/
theorem gaussApprox_cert (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (gaussApprox (w₀ * 2 ^ f)).1 (gaussApprox (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  gaussBracket_conv.bracketConv.exists_isSome irrational_gauss.ne_zero p
    (not_mem_floatSet_of_irrational p irrational_gauss) mode w₀ hw₀

/-- **The Ziv certificate of the lemniscate constant.** -/
theorem lemniscateApprox_cert (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (lemniscateApprox (w₀ * 2 ^ f)).1
      (lemniscateApprox (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  lemniscateBracket_conv.bracketConv.exists_isSome irrational_lemniscate.ne_zero p
    (not_mem_floatSet_of_irrational p irrational_lemniscate) mode w₀ hw₀

end Azurite.AzFloat
