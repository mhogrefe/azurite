/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section19
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# DLMF §4.19: the secant series 4.19.5 and the Euler numbers

The Euler numbers are defined only in DLMF §24.2(ii), by the generating function 24.2.6,
`2eᵗ/(e^{2t} + 1) = ∑ Eₙ tⁿ/n!` (`|t| < π/2`). They are formalized here from that definition:
`eulerNumber n` is `n!` times the `n`-th Taylor coefficient of `eulerGen t = 2eᵗ/(e^{2t} + 1)`
at `0`, and `hasSum_eulerGen` proves the expansion on `|t| < π/2`.

* 4.19.5 (`|z| < π/2`): `dlmf_4_19_5`. Since `sec z = eulerGen(iz)` and the odd Euler numbers
  vanish (`eulerNumber_odd`), the series has only the even terms.
* The displayed terms `1 + z²/2 + 5z⁴/24 + 61z⁶/720`: `secCoeff_values`. They use
  `E₂ = −1`, `E₄ = 5`, `E₆ = −61` (`eulerNumber_values`), which come from the Leibniz
  recurrence of `eulerGen · cosh = 1` (`eulerNumber_rec`).
-/

open Set Filter Topology Complex
open scoped Real Nat

namespace Azurite.DLMF

/-- The generating function of DLMF 24.2.6: `2eᵗ/(e^{2t} + 1)`. -/
noncomputable def eulerGen (t : ℂ) : ℂ := 2 * exp t / (exp (2 * t) + 1)

/-- **DLMF 24.2.6**: the Euler numbers `Eₙ`, the coefficients of `2eᵗ/(e^{2t} + 1) = ∑ Eₙ tⁿ/n!`. -/
noncomputable def eulerNumber (n : ℕ) : ℂ := iteratedDeriv n eulerGen 0

theorem eulerGen_eq (t : ℂ) : eulerGen t = (cosh t)⁻¹ := by
  rw [eulerGen, Complex.cosh, show 2 * t = t + t by ring, exp_add]
  have he : exp t ≠ 0 := exp_ne_zero t
  have hm : exp (-t) = (exp t)⁻¹ := exp_neg t
  rw [hm]
  rcases eq_or_ne (exp t * exp t + 1) 0 with h | h
  · have : exp t + (exp t)⁻¹ = 0 := by
      field_simp; linear_combination h
    rw [h, this]; simp
  · field_simp

theorem cosh_ne_zero_of_norm_lt {t : ℂ} (ht : ‖t‖ < π / 2) : cosh t ≠ 0 := by
  rw [show t = (-(t * I)) * I by rw [neg_mul, mul_assoc, I_mul_I]; ring, cosh_mul_I, cos_neg]
  exact cos_ne_zero_of_norm_lt_pi_div_two (by rw [norm_mul, norm_I, mul_one]; exact ht)

theorem differentiableOn_eulerGen : DifferentiableOn ℂ eulerGen (Metric.ball 0 (π / 2)) := by
  intro t ht
  have ht' : ‖t‖ < π / 2 := by simpa using ht
  have h : DifferentiableAt ℂ (fun t => (cosh t)⁻¹) t :=
    (Complex.differentiable_cosh t).inv (cosh_ne_zero_of_norm_lt ht')
  rw [show eulerGen = fun t => (cosh t)⁻¹ from funext eulerGen_eq]
  exact h.differentiableWithinAt

/-- **DLMF 24.2.6**: `2eᵗ/(e^{2t} + 1) = ∑ Eₙ tⁿ/n!`, `|t| < π/2`. -/
theorem hasSum_eulerGen {t : ℂ} (ht : ‖t‖ < π / 2) :
    HasSum (fun n : ℕ => eulerNumber n * t ^ n / n !) (eulerGen t) := by
  have h := Complex.hasSum_taylorSeries_on_ball differentiableOn_eulerGen
    (z := t) (by simpa using ht)
  convert h using 1
  funext n
  simp only [eulerNumber, sub_zero, smul_eq_mul]
  field_simp

theorem eulerGen_neg (t : ℂ) : eulerGen (-t) = eulerGen t := by
  rw [eulerGen_eq, eulerGen_eq, cosh_neg]

/-- The odd Euler numbers vanish (`eulerGen` is even). -/
theorem eulerNumber_odd {n : ℕ} (hn : Odd n) : eulerNumber n = 0 := by
  have h := iteratedDeriv_comp_neg n eulerGen 0
  have hf : (fun x => eulerGen (-x)) = eulerGen := funext eulerGen_neg
  rw [hf, neg_zero, hn.neg_one_pow, smul_eq_mul, neg_one_mul] at h
  have : (2 : ℂ) * eulerNumber n = 0 := by
    unfold eulerNumber; linear_combination h
  simpa using this

theorem eulerNumber_zero : eulerNumber 0 = 1 := by
  simp [eulerNumber, eulerGen]
  norm_num

theorem iteratedDeriv_cosh_zero (k : ℕ) :
    iteratedDeriv k cosh 0 = if Even k then 1 else 0 := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [iteratedDeriv_even_cosh, ite_eq_left_iff.mpr (fun h => absurd ⟨j, by ring⟩ h),
      cosh_zero]
  · rw [iteratedDeriv_odd_cosh,
      ite_eq_right_iff.mpr (fun h => absurd h (Nat.not_even_iff_odd.mpr ⟨j, rfl⟩)), sinh_zero]

/-- The Leibniz recurrence from `eulerGen · cosh = 1`: `∑ C(n,i) Eᵢ cosh^{(n−i)}(0) = 0`. -/
theorem eulerNumber_rec {n : ℕ} (hn : n ≠ 0) :
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * eulerNumber i *
      iteratedDeriv (n - i) cosh 0 = 0 := by
  have hcd : ContDiffAt ℂ n eulerGen 0 :=
    (differentiableOn_eulerGen.contDiffOn Metric.isOpen_ball).contDiffAt
      (Metric.ball_mem_nhds 0 (by positivity))
  have hch : ContDiffAt ℂ n cosh 0 := Complex.contDiff_cosh.contDiffAt
  have h := iteratedDeriv_mul hcd hch
  have hev : (eulerGen * cosh) =ᶠ[𝓝 0] fun _ => (1 : ℂ) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by positivity : (0 : ℝ) < π / 2)] with t ht
    have ht' : ‖t‖ < π / 2 := by simpa using ht
    simp only [Pi.mul_apply, eulerGen_eq]
    exact inv_mul_cancel₀ (cosh_ne_zero_of_norm_lt ht')
  rw [hev.iteratedDeriv_eq, iteratedDeriv_const, ite_eq_right_iff.mpr (fun h => absurd h hn)] at h
  exact h.symm

/-- `E₂ = −1`, `E₄ = 5`, `E₆ = −61`. -/
theorem eulerNumber_values : eulerNumber 2 = -1 ∧ eulerNumber 4 = 5 ∧ eulerNumber 6 = -61 := by
  have o1 := eulerNumber_odd (n := 1) ⟨0, rfl⟩
  have o3 := eulerNumber_odd (n := 3) ⟨1, rfl⟩
  have o5 := eulerNumber_odd (n := 5) ⟨2, rfl⟩
  have r2 := eulerNumber_rec (n := 2) (by norm_num)
  have r4 := eulerNumber_rec (n := 4) (by norm_num)
  have r6 := eulerNumber_rec (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_cosh_zero,
    eulerNumber_zero, o1, o3, o5, Nat.choose, Nat.even_iff] at r2 r4 r6
  norm_num at r2 r4 r6
  have e2 : eulerNumber 2 = -1 := by linear_combination r2
  have e4 : eulerNumber 4 = 5 := by linear_combination r4 - 6 * r2
  refine ⟨e2, e4, ?_⟩
  rw [e2, e4] at r6
  linear_combination r6

/-- The coefficient of `z^{2n}` in 4.19.5: `(−1)ⁿ E_{2n}/(2n)!`. -/
noncomputable def secCoeff (n : ℕ) : ℂ := (-1) ^ n * eulerNumber (2 * n) / (2 * n)!

/-- **DLMF 4.19.5**: `sec z = 1 + z²/2 + 5z⁴/24 + 61z⁶/720 + ⋯ + ((−1)ⁿ E_{2n}/(2n)!) z^{2n} + ⋯`,
`|z| < π/2`. -/
theorem dlmf_4_19_5 {z : ℂ} (hz : ‖z‖ < π / 2) :
    HasSum (fun n : ℕ => secCoeff n * z ^ (2 * n)) (secC z) := by
  have ht : ‖z * I‖ < π / 2 := by rw [norm_mul, norm_I, mul_one]; exact hz
  have h := hasSum_eulerGen ht
  have hsec : eulerGen (z * I) = secC z := by rw [eulerGen_eq, cosh_mul_I, secC, one_div]
  rw [hsec] at h
  have hinj : Function.Injective (fun n : ℕ => 2 * n) := fun a b h => by simpa using h
  rw [← hinj.hasSum_iff (fun n hn => by
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    · exact absurd ⟨j, rfl⟩ hn
    · rw [eulerNumber_odd ⟨j, rfl⟩]; simp)] at h
  convert h using 1
  funext n
  simp only [secCoeff, Function.comp, mul_pow, pow_mul, I_sq]
  ring

/-- **DLMF 4.19.5**, the displayed terms `1 + z²/2 + 5z⁴/24 + 61z⁶/720`. -/
theorem secCoeff_values : secCoeff 0 = 1 ∧ secCoeff 1 = 1 / 2 ∧ secCoeff 2 = 5 / 24 ∧
    secCoeff 3 = 61 / 720 := by
  obtain ⟨e2, e4, e6⟩ := eulerNumber_values
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [secCoeff, eulerNumber_zero, e2, e4, e6, Nat.factorial]

end Azurite.DLMF
