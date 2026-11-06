/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section2
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# DLMF §4.2(iii): The exponential function

Formalizations of <https://dlmf.nist.gov/4.2.iii>. `exp` is `Complex.exp`, `ph` is `Complex.arg`,
and the general logarithm `Ln ζ` of §4.2(i) is the set `genLogSet ζ = {ln ζ + 2kπi : k ∈ ℤ}` of
the values of `∫₁^ζ dt/t` along paths avoiding `0` (`genLogSet_eq_pathIntegrals`, from 4.2.1 and
4.2.6).

* 4.2.19: the Maclaurin series (`dlmf_4_2_19`).
* "an entire function of `z`, with no real or complex zeros" (`dlmf_4_2_iii_entire`,
  `dlmf_4_2_iii_ne_zero`); "period `2πi`", 4.2.20 (`dlmf_4_2_20`, `dlmf_4_2_iii_periodic`).
* 4.2.21, 4.2.22 (`dlmf_4_2_21`, `dlmf_4_2_22`).
* 4.2.23: the general value of the phase: the `θ` with `exp z = |exp z| e^{iθ}` are exactly
  `Im z + 2kπ` (`dlmf_4_2_23`); the principal phase is one of them (`dlmf_4_2_23_arg`).
* 4.2.24: `exp z = eˣ cos y + i eˣ sin y` (`dlmf_4_2_24`).
* 4.2.25: `exp z = ζ ⟺ z = Ln ζ` (`ζ ≠ 0`, `dlmf_4_2_25`).

Hobson (1928, pp. 289–296) is a reference.
-/

open Complex Set
open scoped Real

namespace Azurite.DLMF

/-- **DLMF 4.2.19**: `exp z = 1 + z/1! + z²/2! + ⋯`. -/
theorem dlmf_4_2_19 (z : ℂ) : HasSum (fun n : ℕ => z ^ n / n.factorial) (exp z) := by
  rw [exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

/-- **DLMF §4.2(iii)**: "The function `exp` is an entire function of `z`". -/
theorem dlmf_4_2_iii_entire : Differentiable ℂ exp := differentiable_exp

/-- **DLMF §4.2(iii)**: "… with no real or complex zeros". -/
theorem dlmf_4_2_iii_ne_zero (z : ℂ) : exp z ≠ 0 := exp_ne_zero z

/-- **DLMF 4.2.20**: `exp(z + 2πi) = exp z`. -/
theorem dlmf_4_2_20 (z : ℂ) : exp (z + 2 * π * I) = exp z := exp_periodic z

/-- **DLMF §4.2(iii)**: "It has period `2πi`": the periods of `exp` are exactly the `2kπi`, so
`2πi` is a fundamental period. -/
theorem dlmf_4_2_iii_periodic (c : ℂ) :
    (∀ z, exp (z + c) = exp z) ↔ ∃ k : ℤ, c = k * (2 * π * I) := by
  constructor
  · intro h
    exact exp_eq_one_iff.mp (by simpa using h 0)
  · rintro ⟨k, rfl⟩ z
    rw [exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/-- **DLMF 4.2.21**: `exp(−z) = 1/exp(z)`. -/
theorem dlmf_4_2_21 (z : ℂ) : exp (-z) = 1 / exp z := by rw [exp_neg, one_div]

/-- **DLMF 4.2.22**: `|exp z| = exp(Re z)`. -/
theorem dlmf_4_2_22 (z : ℂ) : ‖exp z‖ = Real.exp z.re := norm_exp z

/-- **DLMF 4.2.23**: the general value of the phase of `exp z`: `exp z = |exp z| e^{iθ}` exactly
for `θ = Im z + 2kπ`, `k ∈ ℤ`. -/
theorem dlmf_4_2_23 (z : ℂ) (θ : ℝ) :
    exp z = ‖exp z‖ * exp (θ * I) ↔ ∃ k : ℤ, θ = z.im + 2 * k * π := by
  have hz : exp z = (Real.exp z.re : ℂ) * exp (z.im * I) := by
    rw [ofReal_exp, ← exp_add]; congr 1; exact (re_add_im z).symm
  have hpos : (Real.exp z.re : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  rw [norm_exp, hz, mul_right_inj' hpos, eq_comm, exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have := congrArg im hk
    simp at this
    linarith
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; ring⟩

/-- **DLMF 4.2.23**: the principal phase `ph(exp z)` is one of the values `Im z + 2kπ`. -/
theorem dlmf_4_2_23_arg (z : ℂ) : ∃ k : ℤ, arg (exp z) = z.im + 2 * k * π := by
  refine (dlmf_4_2_23 z (arg (exp z))).mp ?_
  exact (norm_mul_exp_arg_mul_I (exp z)).symm

/-- **DLMF 4.2.24**: with `z = x + iy`, `exp z = eˣ cos y + i eˣ sin y`. -/
theorem dlmf_4_2_24 (x y : ℝ) :
    exp (x + y * I) = Real.exp x * Real.cos y + I * (Real.exp x * Real.sin y) := by
  rw [exp_add, ← ofReal_exp, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  ring

/-- The general logarithm `Ln ζ = ln ζ + 2kπi` (4.2.6) as a set of values. -/
def genLogSet (ζ : ℂ) : Set ℂ := {w | ∃ k : ℤ, w = log ζ + 2 * k * π * I}

/-- The values of `Ln ζ` are exactly the integrals `∫₁^ζ dt/t` along `C¹` paths from `1` to `ζ`
avoiding `0` (4.2.1, 4.2.6). -/
theorem genLogSet_eq_pathIntegrals {ζ : ℂ} (hζ : ζ ≠ 0) :
    genLogSet ζ = {w | ∃ γ : ℝ → ℂ, ContDiff ℝ 1 γ ∧ (∀ s ∈ Icc (0 : ℝ) 1, γ s ≠ 0) ∧
      γ 0 = 1 ∧ γ 1 = ζ ∧ pathLogIntegral γ = w} := by
  ext w
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨γ, hγ, h0, h1, h2, h3⟩ := dlmf_4_2_1 hζ k
    exact ⟨γ, hγ, fun s _ => h0 s, h1, h2, h3⟩
  · rintro ⟨γ, hγ, h0, h1, h2, rfl⟩
    obtain ⟨k, hk⟩ := dlmf_4_2_6 hγ h0 h1
    exact ⟨k, by rw [hk, h2]⟩

/-- **DLMF 4.2.25**: for `ζ ≠ 0`, `exp z = ζ ⟺ z = Ln ζ` (`z` is one of the values of the general
logarithm). -/
theorem dlmf_4_2_25 {ζ : ℂ} (hζ : ζ ≠ 0) (z : ℂ) : exp z = ζ ↔ z ∈ genLogSet ζ := by
  rw [← exp_log hζ, exp_eq_exp_iff_exists_int, exp_log hζ]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [hk]; ring⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [hk]; ring⟩

end Azurite.DLMF
