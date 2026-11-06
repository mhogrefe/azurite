/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.ConstantKernel
import Azurite.DLMF.Chapter3.Section12
import Azurite.DLMF.Chapter4.Section2
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# DLMF §4.2(ii): Logarithms to a general base

Formalizations of <https://dlmf.nist.gov/4.2.ii>. `log_a z = ln z / ln a` (`logBase`) with the
principal branch `ln = Complex.log` of §4.2(i).

* 4.2.8–4.2.10: `dlmf_4_2_8`, `dlmf_4_2_9`, `dlmf_4_2_10` (`a, b ≠ 0, 1`); for positive real `a`,
  `x` the logarithm is Mathlib's `Real.logb` (`logBase_ofReal`).
* 4.2.11, 4.2.12: `e` is the unique positive number with `ln e = 1` (`dlmf_4_2_12`), with the
  20 decimals of 4.2.11 (`dlmf_4_2_11`); 4.2.13: `∫₁^e dt/t = 1` (`dlmf_4_2_13`).
* 4.2.14–4.2.16: `log_e z = ln z`, `log₁₀ z = ln z / ln 10 = (log₁₀ e) ln z`,
  `ln z = (ln 10) log₁₀ z` (`dlmf_4_2_14`, `dlmf_4_2_15`, `dlmf_4_2_16`).
* 4.2.17, 4.2.18: the 20 decimals of `log₁₀ e` and `ln 10` (`dlmf_4_2_17`, `dlmf_4_2_18`).

The three constants are certified with AzFloat's correctly rounded constants `ePrecRound`,
`log10EPrecRound` and `ln10PrecRound` at 80 bits, rounded down and up: each is shown to equal
Ziv's loop with fuel (`zivLoop`, which the kernel evaluates; the certified loop behind the constants
uses well-founded recursion, which it does not), whose results are read off by `decide +kernel`
(`e80_data` in §3.12, `log10E80_data`, `ln1080_data`), with the helpers of
`AzFloat/Equiv/ConstantKernel.lean`.

"`log_e x = ln x` is also called the Napierian or hyperbolic logarithm. `log₁₀ x` is the common or
Briggs logarithm" is terminology.
-/

open Complex Real Filter Topology

namespace Azurite.DLMF

/-- **DLMF 4.2.8**: `log_a z = ln z / ln a`. -/
noncomputable def logBase (a z : ℂ) : ℂ := Complex.log z / Complex.log a

theorem log_ne_zero_of {a : ℂ} (ha0 : a ≠ 0) (ha1 : a ≠ 1) : Complex.log a ≠ 0 :=
  fun h => ha1 ((dlmf_4_2_i_zero ha0).mp h)

/-- **DLMF 4.2.8**. -/
theorem dlmf_4_2_8 (a z : ℂ) : logBase a z = Complex.log z / Complex.log a := rfl

/-- **DLMF 4.2.9**: `log_a z = log_b z / log_b a` (`a, b ≠ 0, 1`). -/
theorem dlmf_4_2_9 {a b : ℂ} (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hb0 : b ≠ 0) (hb1 : b ≠ 1) (z : ℂ) :
    logBase a z = logBase b z / logBase b a := by
  have ha := log_ne_zero_of ha0 ha1
  have hb := log_ne_zero_of hb0 hb1
  simp only [logBase]
  field_simp

/-- **DLMF 4.2.10**: `log_a b = 1 / log_b a` (`a, b ≠ 0, 1`). -/
theorem dlmf_4_2_10 {a b : ℂ} (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    logBase a b = 1 / logBase b a := by
  have ha := log_ne_zero_of ha0 ha1
  have hb := log_ne_zero_of hb0 hb1
  simp only [logBase]
  field_simp

/-- For positive real `a` and `x`, `log_a x` is `Real.logb a x`. -/
theorem logBase_ofReal {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    logBase a x = (Real.logb a x : ℂ) := by
  rw [logBase, Real.logb, ofReal_div, ofReal_log hx.le, ofReal_log ha.le]

/-- **DLMF 4.2.12**: `e` is the unique positive number with `ln e = 1` (`e = exp 1`), also as a
complex logarithm. -/
theorem dlmf_4_2_12 :
    (∃! x : ℝ, 0 < x ∧ Real.log x = 1) ∧ Real.log (Real.exp 1) = 1 ∧
      Complex.log (Real.exp 1 : ℂ) = 1 := by
  refine ⟨⟨Real.exp 1, ⟨Real.exp_pos 1, Real.log_exp 1⟩, fun x ⟨hx, h⟩ => ?_⟩,
    Real.log_exp 1, ?_⟩
  · rw [← h, Real.exp_log hx]
  · rw [← ofReal_log (Real.exp_pos 1).le, Real.log_exp, ofReal_one]

/-- **DLMF 4.2.13**: `∫₁^e dt/t = 1`. -/
theorem dlmf_4_2_13 : ∫ t in (1 : ℝ)..Real.exp 1, 1 / t = 1 := by
  rw [integral_one_div_of_pos one_pos (Real.exp_pos 1), div_one, Real.log_exp]

/-- **DLMF 4.2.14**: `log_e z = ln z`. -/
theorem dlmf_4_2_14 (z : ℂ) : logBase (Real.exp 1) z = Complex.log z := by
  rw [logBase, (dlmf_4_2_12).2.2, div_one]

/-- **DLMF 4.2.15**: `log₁₀ z = ln z / ln 10 = (log₁₀ e) ln z`. -/
theorem dlmf_4_2_15 (z : ℂ) :
    logBase 10 z = Complex.log z / Complex.log 10 ∧
      logBase 10 z = logBase 10 (Real.exp 1) * Complex.log z := by
  refine ⟨rfl, ?_⟩
  rw [logBase, logBase, (dlmf_4_2_12).2.2]
  ring

/-- **DLMF 4.2.16**: `ln z = (ln 10) log₁₀ z`. -/
theorem dlmf_4_2_16 (z : ℂ) : Complex.log z = Complex.log 10 * logBase 10 z := by
  have h : Complex.log 10 ≠ 0 := log_ne_zero_of (by norm_num) (by norm_num)
  rw [logBase]
  field_simp

/-! ### The constants `e`, `log₁₀ e`, `ln 10` -/

open Azurite.AzFloat Encl

set_option maxRecDepth 100000 in
/-- `log₁₀ e` at 80 bits, rounded down and up. -/
theorem log10E80_data :
    (valData (zivLoop log10EApprox 80 .Floor 3 144).1,
        valData (zivLoop log10EApprox 80 .Ceiling 3 144).1) =
      (some (true, 1050059624977998906996059, 2417851639229258349412352),
        some (true, 262514906244499726749015, 604462909807314587353088)) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `ln 10` at 80 bits, rounded down and up. -/
theorem ln1080_data :
    (valData (zivLoop ln10Approx 80 .Floor 3 144).1,
        valData (zivLoop ln10Approx 80 .Ceiling 3 144).1) =
      (some (true, 347956821347531727009067, 151115727451828646838272),
        some (true, 695913642695063454018135, 302231454903657293676544)) := by
  decide +kernel

/-- **DLMF 4.2.11**: `e = 2.71828 18284 59045 23536 …` (= 3.12.3, from `ePrecRound 80` rounded
down and up). -/
theorem dlmf_4_2_11 :
    2.71828182845904523536 < Real.exp 1 ∧ Real.exp 1 < 2.71828182845904523537 :=
  dlmf_3_12_3

/-- **DLMF 4.2.17**: `log₁₀ e = 0.43429 44819 03251 82765 …`, from `log10EPrecRound 80`. -/
theorem dlmf_4_2_17 :
    0.43429448190325182765 < Real.logb 10 (Real.exp 1) ∧
      Real.logb 10 (Real.exp 1) < 0.43429448190325182766 := by
  rw [logb_ten_exp_one]
  obtain ⟨d1, d2⟩ := Prod.mk.inj log10E80_data
  have hF := const_eq_zivLoop log10EApprox_ok (log10EPrecRound_eq_liftVal₀ 80 .Floor)
    (by norm_num) d1
  have hC := const_eq_zivLoop log10EApprox_ok (log10EPrecRound_eq_liftVal₀ 80 .Ceiling)
    (by norm_num) d2
  have l := le_of_floor_data (log10EPrecRound_eq_liftVal₀ 80 .Floor) (hF ▸ d1)
  have u := ge_of_ceiling_data (log10EPrecRound_eq_liftVal₀ 80 .Ceiling) (hC ▸ d2)
  push_cast at l u
  exact ⟨lt_of_lt_of_le (by norm_num) l, lt_of_le_of_lt u (by norm_num)⟩

/-- **DLMF 4.2.18**: `ln 10 = 2.30258 50929 94045 68401 …`, from `ln10PrecRound 80`. -/
theorem dlmf_4_2_18 :
    2.30258509299404568401 < Real.log 10 ∧ Real.log 10 < 2.30258509299404568402 := by
  obtain ⟨d1, d2⟩ := Prod.mk.inj ln1080_data
  have hF := const_eq_zivLoop ln10Approx_ok (ln10PrecRound_eq_liftVal₀ 80 .Floor)
    (by norm_num) d1
  have hC := const_eq_zivLoop ln10Approx_ok (ln10PrecRound_eq_liftVal₀ 80 .Ceiling)
    (by norm_num) d2
  have l := le_of_floor_data (ln10PrecRound_eq_liftVal₀ 80 .Floor) (hF ▸ d1)
  have u := ge_of_ceiling_data (ln10PrecRound_eq_liftVal₀ 80 .Ceiling) (hC ▸ d2)
  push_cast at l u
  exact ⟨lt_of_lt_of_le (by norm_num) l, lt_of_le_of_lt u (by norm_num)⟩

end Azurite.DLMF
