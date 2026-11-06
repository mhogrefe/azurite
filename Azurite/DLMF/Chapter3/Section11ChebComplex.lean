/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section11ChebSeries
import Azurite.DLMF.Chapter1.Section10Laurent
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# DLMF §3.11(ii): Chebyshev series in the complex plane

"If `x` is replaced by a complex variable `z` and `f(z)` is analytic, then the expansion (3.11.11)
converges within an ellipse."

* `chebEllipse ρ = {z : |z − 1| + |z + 1| < ρ + ρ⁻¹}` (`ρ > 1`): the open ellipse with foci `±1`,
  image of the annulus `ρ⁻¹ < |w| < ρ` under the Joukowski map `w ↦ ½(w + w⁻¹)`
  (`norm_joukowski_sub_add`, `joukowski_mem`, `exists_joukowski`).
* `chebCoeffC f n` is 3.11.10 for complex-valued `f` (`chebCoeffC_eq`).
* `dlmf_3_11_ii_complex`: if `f` is analytic in `chebEllipse ρ`, then
  `f(z) = ∑'_{n=0}^∞ cₙ Tₙ(z)` for every `z` in the ellipse. Proof: `G(w) = f(½(w + w⁻¹))` is
  analytic on the annulus, its Laurent coefficients on `|w| = 1` are the Fourier coefficients of
  `f(cos θ)` (`laurentCoeff_joukowski`), i.e. `½cₙ` for `±n`, and
  `Tₙ(½(w + w⁻¹)) = ½(wⁿ + w⁻ⁿ)` (`T_joukowski`).

The comparison with Maclaurin expansions and Mason and Handscomb (2003, §5.10) are not
formalized.
-/

open Polynomial Polynomial.Chebyshev Finset MeasureTheory Filter Topology Set Complex
open scoped Real

namespace Azurite.DLMF

/-! ### The Joukowski map and the ellipse -/

/-- The open ellipse with foci `±1` and sum of semi-axes `ρ`. -/
def chebEllipse (ρ : ℝ) : Set ℂ := {z | ‖z - 1‖ + ‖z + 1‖ < ρ + ρ⁻¹}

theorem norm_joukowski_sub_add {w : ℂ} (hw : w ≠ 0) :
    ‖(w + w⁻¹) / 2 - 1‖ + ‖(w + w⁻¹) / 2 + 1‖ = ‖w‖ + ‖w‖⁻¹ := by
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have e1 : (w + w⁻¹) / 2 - 1 = (w - 1) ^ 2 / (2 * w) := by field_simp; ring
  have e2 : (w + w⁻¹) / 2 + 1 = (w + 1) ^ 2 / (2 * w) := by field_simp; ring
  have hp := parallelogram_law_with_norm ℝ w 1
  rw [e1, e2, norm_div, norm_div, norm_pow, norm_pow, norm_mul, Complex.norm_two]
  simp only [norm_one] at hp
  field_simp
  nlinarith [hp]

theorem add_inv_lt_of_mem {ρ r : ℝ} (hρ : 1 < ρ) (h1 : ρ⁻¹ < r) (h2 : r < ρ) :
    r + r⁻¹ < ρ + ρ⁻¹ := by
  have hρ0 : 0 < ρ := by linarith
  have hr : 0 < r := lt_trans (by positivity) h1
  have key : (r - ρ) * (r - ρ⁻¹) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
  have hρi : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ0.ne'
  have hri : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  have : r * (r + r⁻¹) < r * (ρ + ρ⁻¹) := by nlinarith
  exact lt_of_mul_lt_mul_left this hr.le

theorem lt_of_add_inv_lt {ρ r : ℝ} (hρ : 1 < ρ) (hr : 1 ≤ r) (h : r + r⁻¹ < ρ + ρ⁻¹) :
    r < ρ := by
  by_contra hle
  push Not at hle
  have hρ0 : 0 < ρ := by linarith
  have hr0 : 0 < r := by linarith
  have hρi : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ0.ne'
  have hri : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
  have hinv : r⁻¹ ≤ ρ⁻¹ := inv_anti₀ hρ0 hle
  -- `r + 1/r − ρ − 1/ρ = (r − ρ)(1 − 1/(rρ)) ≥ 0`
  have h1 : r⁻¹ * ρ⁻¹ ≤ 1 := by
    calc r⁻¹ * ρ⁻¹ ≤ 1 * 1 :=
          mul_le_mul (inv_le_one_of_one_le₀ hr) (inv_le_one_of_one_le₀ hρ.le) (by positivity)
            zero_le_one
      _ = 1 := one_mul 1
  have h2 : r + r⁻¹ - (ρ + ρ⁻¹) = (r - ρ) * (1 - r⁻¹ * ρ⁻¹) := by
    field_simp
    ring
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) (sub_nonneg.mpr h1)]

theorem joukowski_mem {ρ : ℝ} (hρ : 1 < ρ) {w : ℂ} (hw : w ∈ annulus 0 ρ⁻¹ ρ) :
    (w + w⁻¹) / 2 ∈ chebEllipse ρ := by
  have h1 : ρ⁻¹ < ‖w‖ := by simpa using hw.1
  have h2 : ‖w‖ < ρ := by simpa using hw.2
  have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans (by positivity) h1)
  show ‖(w + w⁻¹) / 2 - 1‖ + ‖(w + w⁻¹) / 2 + 1‖ < ρ + ρ⁻¹
  rw [norm_joukowski_sub_add hw0]
  exact add_inv_lt_of_mem hρ h1 h2

theorem exists_joukowski {ρ : ℝ} (hρ : 1 < ρ) {z : ℂ} (hz : z ∈ chebEllipse ρ) :
    ∃ w ∈ annulus 0 ρ⁻¹ ρ, (w + w⁻¹) / 2 = z := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (z ^ 2 - 1) two_pos
  have hprod : (z + s) * (z - s) = 1 := by linear_combination -hs
  have hw1 : z + s ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hw2 : z - s ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have hinv1 : (z + s)⁻¹ = z - s := inv_eq_of_mul_eq_one_right hprod
  have hinv2 : (z - s)⁻¹ = z + s := inv_eq_of_mul_eq_one_left hprod
  have hJ1 : (z + s + (z + s)⁻¹) / 2 = z := by rw [hinv1]; ring
  have hJ2 : (z - s + (z - s)⁻¹) / 2 = z := by rw [hinv2]; ring
  have hρ0 : 0 < ρ := by linarith
  have hmem : ∀ w : ℂ, w ≠ 0 → 1 ≤ ‖w‖ → (w + w⁻¹) / 2 = z → w ∈ annulus 0 ρ⁻¹ ρ := by
    intro w hw h1 hJ
    have hsum : ‖w‖ + ‖w‖⁻¹ < ρ + ρ⁻¹ := by
      have := norm_joukowski_sub_add hw
      rw [hJ] at this
      rw [← this]
      exact hz
    refine ⟨?_, ?_⟩
    · simp only [sub_zero]
      exact lt_of_lt_of_le (inv_lt_one_of_one_lt₀ hρ) h1
    · simp only [sub_zero]
      exact lt_of_add_inv_lt hρ h1 hsum
  by_cases h : 1 ≤ ‖z + s‖
  · exact ⟨z + s, hmem _ hw1 h hJ1, hJ1⟩
  · push Not at h
    have : 1 ≤ ‖z - s‖ := by
      rw [← hinv1, norm_inv]
      exact (one_le_inv₀ (norm_pos_iff.mpr hw1)).mpr h.le
    exact ⟨z - s, hmem _ hw2 this hJ2, hJ2⟩

/-- `Tₙ(½(w + w⁻¹)) = ½(wⁿ + w⁻ⁿ)`. -/
theorem T_joukowski (n : ℕ) {w : ℂ} (hw : w ≠ 0) :
    (T ℂ n).eval ((w + w⁻¹) / 2) = (w ^ n + (w ^ n)⁻¹) / 2 := by
  set θ : ℂ := -I * log w with hθ
  have hθI : θ * I = log w := by rw [hθ]; ring_nf; rw [I_sq]; ring
  have he1 : exp (θ * I) = w := by rw [hθI, exp_log hw]
  have he2 : exp (-θ * I) = w⁻¹ := by rw [neg_mul, exp_neg, he1]
  have hc : Complex.cos θ = (w + w⁻¹) / 2 := by
    have h1 := cos_add_sin_I θ
    have h2 := cos_sub_sin_I θ
    rw [he1] at h1
    rw [he2] at h2
    linear_combination (h1 + h2) / 2
  have he3 : exp ((n : ℂ) * θ * I) = w ^ n := by
    rw [mul_assoc, exp_nat_mul, he1]
  have he4 : exp (-((n : ℂ) * θ) * I) = (w ^ n)⁻¹ := by
    rw [neg_mul, exp_neg, he3]
  rw [← hc, T_complex_cos]
  have h3 := cos_add_sin_I ((n : ℂ) * θ)
  have h4 := cos_sub_sin_I ((n : ℂ) * θ)
  rw [he3] at h3
  rw [he4] at h4
  push_cast
  linear_combination (h3 + h4) / 2

/-! ### Coefficients -/

/-- **DLMF 3.11.10** for complex-valued `f`: `cₙ = (2/π) ∫₀^π f(cos θ) cos(nθ) dθ`, here defined
as the Fourier cosine coefficient of `θ ↦ f(cos θ)` (`chebCoeffC_eq`). -/
noncomputable def chebCoeffC (f : ℂ → ℂ) (n : ℕ) : ℂ := fourierA (fun θ => f (Real.cos θ)) n

theorem integral_even_symm_complex {φ : ℝ → ℂ} (hφ : ∀ x, φ (-x) = φ x) (hc : Continuous φ)
    (a : ℝ) : ∫ x in (-a)..a, φ x = 2 * ∫ x in (0 : ℝ)..a, φ x := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := a) φ
  simp only [neg_zero, hφ] at h
  rw [← h]
  ring

theorem chebCoeffC_eq {f : ℂ → ℂ} (hf : Continuous fun θ : ℝ => f (Real.cos θ)) (n : ℕ) :
    chebCoeffC f n = (2 / π : ℝ) * ∫ θ in (0 : ℝ)..π, f (Real.cos θ) * Real.cos (n * θ) := by
  have hc : Continuous fun x : ℝ => f (Real.cos x) * (Real.cos (n * x) : ℂ) :=
    hf.mul (by fun_prop)
  rw [chebCoeffC, fourierA, integral_even_symm_complex
    (φ := fun x : ℝ => f (Real.cos x) * (Real.cos (n * x) : ℂ))
    (fun x => by simp [Real.cos_neg]) hc, Complex.real_smul]
  push_cast
  ring

/-- On the unit circle, the Laurent coefficients of `f(½(w + w⁻¹))` are the Fourier coefficients
of `f(cos θ)`. -/
theorem laurentCoeff_joukowski (f : ℂ → ℂ) (k : ℤ) :
    laurentCoeff (fun w => f ((w + w⁻¹) / 2)) 0 1 k = fourierC (fun θ => f (Real.cos θ)) k := by
  set g : ℝ → ℂ := fun θ => f (Real.cos θ)
  have hcm : ∀ θ : ℝ, circleMap 0 1 θ = exp (θ * I) := fun θ => by simp [circleMap]
  have hne : ∀ θ : ℝ, exp (θ * I) ≠ 0 := fun θ => exp_ne_zero _
  have hcos : ∀ θ : ℝ, (exp (θ * I) + (exp (θ * I))⁻¹) / 2 = (Real.cos θ : ℂ) := fun θ => by
    have h1 := cos_add_sin_I (θ : ℂ)
    have h2 := cos_sub_sin_I (θ : ℂ)
    rw [← exp_neg, ← neg_mul, ofReal_cos]
    linear_combination -(h1 + h2) / 2
  have hint : ∀ θ : ℝ, deriv (circleMap 0 1) θ •
      ((fun w => f ((w + w⁻¹) / 2)) (circleMap 0 1 θ) / (circleMap 0 1 θ - 0) ^ (k + 1)) =
      I * (g θ * exp (-(k * θ * I))) := fun θ => by
    rw [deriv_circleMap, hcm, smul_eq_mul]
    simp only [sub_zero, hcos, g]
    rw [zpow_add_one₀ (hne θ), show (k : ℂ) * θ * I = k * (θ * I) by ring, exp_neg,
      exp_int_mul]
    field_simp
  -- the integrand over a period
  set φ : ℝ → ℂ := fun θ => g θ * exp (-(k * θ * I))
  have hper : Function.Periodic φ (2 * π) := fun θ => by
    simp only [φ, g, Real.cos_add_two_pi]
    congr 1
    rw [show -((k : ℂ) * ((θ + 2 * π : ℝ) : ℂ) * I) = -(k * θ * I) + -(k * (2 * π * I)) by
      push_cast; ring, exp_add, exp_neg (k * (2 * π * I)), exp_int_mul_two_pi_mul_I, inv_one,
      mul_one]
  have hshift : ∫ θ in (0 : ℝ)..2 * π, φ θ = ∫ θ in (-π)..π, φ θ := by
    have := hper.intervalIntegral_add_eq 0 (-π)
    rw [zero_add, show -π + 2 * π = π by ring] at this
    exact this
  rw [laurentCoeff, circleIntegral, intervalIntegral.integral_congr fun θ _ => hint θ,
    intervalIntegral.integral_const_mul, hshift, fourierC, Complex.real_smul]
  have hφ : ∫ θ in (-π)..π, φ θ = ∫ x in (-π)..π, g x * exp (-(k * x * I)) := rfl
  rw [← hφ]
  generalize (∫ θ in (-π)..π, φ θ) = J
  have hI : I ≠ 0 := I_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

/-! ### Convergence in the ellipse -/

/-- **DLMF §3.11(ii)**: if `f` is analytic in the ellipse `chebEllipse ρ` (`ρ > 1`, foci `±1`),
then the Chebyshev expansion 3.11.11 converges to `f(z)` at every `z` in the ellipse:
`f(z) = ½c₀ + ∑_{n ≥ 1} cₙ Tₙ(z)`. -/
theorem dlmf_3_11_ii_complex {f : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ)
    (hf : DifferentiableOn ℂ f (chebEllipse ρ)) {z : ℂ} (hz : z ∈ chebEllipse ρ) :
    HasSum (fun n => (if n = 0 then chebCoeffC f 0 / 2 else chebCoeffC f n) * (T ℂ n).eval z)
      (f z) := by
  set G : ℂ → ℂ := fun w => f ((w + w⁻¹) / 2)
  have hρ0 : 0 < ρ := by linarith
  have hρi : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
  -- `G` is analytic on the annulus
  have hG : DifferentiableOn ℂ G (annulus 0 ρ⁻¹ ρ) := by
    refine hf.comp (fun w hw => ?_) fun w hw => joukowski_mem hρ hw
    have hw0 : w ≠ 0 := by
      have : ρ⁻¹ < ‖w - 0‖ := hw.1
      rw [sub_zero] at this
      exact norm_pos_iff.mp (lt_trans (by positivity) this)
    exact ((differentiableAt_id.add (differentiableAt_inv hw0)).div_const 2)
      |>.differentiableWithinAt
  obtain ⟨w, hw, hwz⟩ := exists_joukowski hρ hz
  have hw0 : w ≠ 0 := by
    have : ρ⁻¹ < ‖w - 0‖ := hw.1
    rw [sub_zero] at this
    exact norm_pos_iff.mp (lt_trans (by positivity) this)
  have h1mem : (1 : ℝ) ∈ Ioo ρ⁻¹ ρ := ⟨hρi, hρ⟩
  obtain ⟨S₁, S₂, h1, h2, hS⟩ := hasSum_laurent (inv_nonneg.mpr hρ0.le) hG h1mem hw
  -- the coefficients
  set g : ℝ → ℂ := fun θ => f (Real.cos θ)
  have hgi : IntervalIntegrable g volume (-π) π := by
    -- `f ∘ cos` is continuous: `f` is continuous on the ellipse, which contains `[−1, 1]`
    have hsub : ∀ θ : ℝ, ((Real.cos θ : ℝ) : ℂ) ∈ chebEllipse ρ := fun θ => by
      have := joukowski_mem hρ (w := exp (θ * I)) ⟨by simpa using hρi, by simpa using hρ⟩
      rwa [show (exp (θ * I) + (exp (θ * I))⁻¹) / 2 = (Real.cos θ : ℂ) by
        have h1 := cos_add_sin_I (θ : ℂ)
        have h2 := cos_sub_sin_I (θ : ℂ)
        rw [← exp_neg, ← neg_mul, ofReal_cos]
        linear_combination -(h1 + h2) / 2] at this
    exact (hf.continuousOn.comp_continuous (continuous_ofReal.comp Real.continuous_cos)
      hsub).intervalIntegrable _ _
  have heven : ∀ n : ℕ, fourierB g n = 0 := fun n =>
    dlmf_1_8_i_even (f := g) (fun x => by simp [g]) n
  have hpos : ∀ n : ℕ, laurentCoeff G 0 1 n = chebCoeffC f n / 2 := fun n => by
    rw [laurentCoeff_joukowski, fourierC_natCast hgi, heven, mul_zero, sub_zero]
    rfl
  have hneg : ∀ n : ℕ, laurentCoeff G 0 1 (-n) = chebCoeffC f n / 2 := fun n => by
    rw [laurentCoeff_joukowski, fourierC_neg_natCast hgi, heven, mul_zero, add_zero]
    rfl
  -- combine the two halves
  set b : ℕ → ℂ := fun n => if n = 0 then 0 else chebCoeffC f n / 2 * (w ^ n)⁻¹
  have hb : HasSum b S₂ := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    simp only [Finset.sum_range_one, b, ↓reduceIte, sub_zero, Nat.add_one_ne_zero]
    convert h2 using 2 with m
    rw [hneg, sub_zero, zpow_neg, zpow_natCast]
  have hsum := (h1.add hb)
  have hGw : G w = f z := by simp only [G, hwz]
  rw [hS, hGw] at hsum
  convert hsum using 1
  funext n
  simp only [b, sub_zero]
  rw [hpos n, ← hwz, T_joukowski n hw0]
  split_ifs with hn
  · subst hn; simp
  · ring

end Azurite.DLMF
