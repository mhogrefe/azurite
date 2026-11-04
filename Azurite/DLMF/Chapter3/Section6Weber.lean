/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section6Examples
import Azurite.DLMF.Chapter3.Section6Inhom
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# DLMF §3.6(vi), Example 2: the Weber function

`𝐄ₙ(1)` is defined by the integral **11.10.2** `𝐄_ν(z) = (1/π) ∫₀^π sin(νθ − z sin θ) dθ`
(`weberE`); `|𝐄_ν(z)| ≤ 1` (`abs_weberE_le`).

* **3.6.14** (`dlmf_3_6_14`, `weberE_rec`): `sin((n+1)θ − sin θ) + sin((n−1)θ − sin θ) =
  2n sin(nθ − sin θ) + 2 (cos(nθ − sin θ))′`, integrated over `[0, π]`.
* **3.6.15**, **3.6.16** (`dlmf_3_6_15`, `dlmf_3_6_16`) from the two-term expansion
  `π𝐄ₙ(1) = 1/(n − 1) − (−1)ⁿ/(n + 1) + Rₙ`, `|Rₙ| ≤ 4π/(n − 1)³` (`weberE_expansion`: two
  integrations by parts with `φ = nθ − sin θ`, antiderivative `−cos φ/φ′ − sin φ sin θ/φ′³`).
* `𝐄₀(1) = −(1/π) ∫₀^π sin(sin θ) dθ` (`weberE_zero_one`) and its Maclaurin series
  `∫₀^π sin(sin θ) dθ = ∑ₖ (−1)ᵏ (∫₀^π sin^{2k+1})/(2k+1)!` (`hasSum_weberE0Term`, §11.10(iii)).
* "The asymptotic behavior of the particular solution `𝐄ₙ(1)` is intermediate to those of the
  complementary functions": `Jₙ(1)/𝐄ₙ(1) → 0`, `𝐄ₙ(1)/pₙ → 0` (`dlmf_3_6_vi_weber_intermediate`,
  `weberE_lower`); "the conditions for Olver's algorithm are satisfied", so it converges
  (`dlmf_3_6_vi_weber_olver`).

Table 3.6.1: `Section6WeberTable`.
-/

open Filter Topology Finset Asymptotics Real

namespace Azurite.DLMF

/-- The Weber function `𝐄_ν(z) = (1/π) ∫₀^π sin(νθ − z sin θ) dθ` (**DLMF 11.10.2**). -/
noncomputable def weberE (ν z : ℝ) : ℝ := 1 / π * ∫ θ in (0 : ℝ)..π, sin (ν * θ - z * sin θ)

/-- `|𝐄_ν(z)| ≤ 1`. -/
theorem abs_weberE_le (ν z : ℝ) : |weberE ν z| ≤ 1 := by
  unfold weberE
  have h : ‖∫ θ in (0 : ℝ)..π, sin (ν * θ - z * sin θ)‖ ≤ 1 * |π - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => by
      rw [Real.norm_eq_abs]; exact abs_sin_le_one _
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos pi_pos, one_mul] at h
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
  calc 1 / π * |∫ θ in (0 : ℝ)..π, sin (ν * θ - z * sin θ)| ≤ 1 / π * π := by gcongr
    _ = 1 := by field_simp

theorem intervalIntegrable_sin_phase (ν : ℝ) :
    IntervalIntegrable (fun θ => sin (ν * θ - sin θ)) MeasureTheory.volume 0 π :=
  (by fun_prop : Continuous fun θ => sin (ν * θ - sin θ)).intervalIntegrable _ _

/-! ### The difference equation 3.6.14 -/

/-- `𝐄_{m+2}(1) − 2(m+1) 𝐄_{m+1}(1) + 𝐄_m(1) = −(2/π)(1 − (−1)^{m+1})`. -/
theorem weberE_rec (m : ℕ) :
    weberE ((m + 2 : ℕ) : ℝ) 1 - 2 * ((m : ℝ) + 1) * weberE ((m + 1 : ℕ) : ℝ) 1 +
      weberE (m : ℝ) 1 = -(2 / π) * (1 - (-1) ^ (m + 1)) := by
  set n : ℝ := (m : ℝ) + 1
  -- `F θ = cos(nθ − sin θ)`, `F′ θ = −sin(nθ − sin θ)(n − cos θ)`
  have hF : ∀ θ ∈ Set.uIcc (0 : ℝ) π, HasDerivAt (fun θ => cos (n * θ - sin θ))
      (-sin (n * θ - sin θ) * (n - cos θ)) θ := fun θ _ => by
    have h1 : HasDerivAt (fun θ => n * θ - sin θ) (n * 1 - cos θ) θ :=
      ((hasDerivAt_id' θ).const_mul n).sub (hasDerivAt_sin θ)
    rw [mul_one] at h1
    simpa using h1.cos
  have hFi : IntervalIntegrable (fun θ => -sin (n * θ - sin θ) * (n - cos θ))
      MeasureTheory.volume 0 π := (by fun_prop :
        Continuous fun θ => -sin (n * θ - sin θ) * (n - cos θ)).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hFi
  have hcos : cos (n * π - sin π) = (-1) ^ (m + 1) := by
    rw [sin_pi, sub_zero, show n = ((m + 1 : ℕ) : ℝ) by push_cast; ring, cos_nat_mul_pi]
  rw [hcos, mul_zero, sin_zero, sub_zero, cos_zero] at hFTC
  -- the pointwise identity
  have hpt : ∀ θ : ℝ, sin ((((m + 2 : ℕ) : ℝ)) * θ - sin θ) + sin ((m : ℝ) * θ - sin θ) =
      2 * n * sin (n * θ - sin θ) + 2 * (-sin (n * θ - sin θ) * (n - cos θ)) := fun θ => by
    have e1 : (((m + 2 : ℕ) : ℝ)) * θ - sin θ = (n * θ - sin θ) + θ := by push_cast; ring
    have e2 : (m : ℝ) * θ - sin θ = (n * θ - sin θ) - θ := by ring
    rw [e1, e2]
    generalize n * θ - sin θ = φ
    rw [sin_add, sin_sub]
    ring
  have hsum : (∫ θ in (0 : ℝ)..π, sin ((((m + 2 : ℕ) : ℝ)) * θ - sin θ)) +
      ∫ θ in (0 : ℝ)..π, sin ((m : ℝ) * θ - sin θ) =
      2 * n * (∫ θ in (0 : ℝ)..π, sin (n * θ - sin θ)) +
        2 * ∫ θ in (0 : ℝ)..π, -sin (n * θ - sin θ) * (n - cos θ) := by
    rw [← intervalIntegral.integral_add (intervalIntegrable_sin_phase _)
      (intervalIntegrable_sin_phase _), intervalIntegral.integral_congr fun θ _ => hpt θ,
      intervalIntegral.integral_add ((intervalIntegrable_sin_phase n).const_mul _)
        (hFi.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hFTC] at hsum
  unfold weberE
  have hn : ((m + 1 : ℕ) : ℝ) = n := by push_cast; ring
  rw [hn]
  simp only [one_mul]
  linear_combination (1 / π) * hsum

/-- The coefficients of 3.6.14 in the form 3.6.1: `dₙ = −(2/π)(1 − (−1)ⁿ)`. -/
noncomputable def weberD (n : ℕ) : ℂ := -(2 / π) * (1 - (-1) ^ n)

/-- `wₙ = 𝐄ₙ(1)`. -/
noncomputable def weberW (n : ℕ) : ℂ := (weberE n 1 : ℂ)

/-- **DLMF 3.6.14**: `𝐄ₙ(1)` satisfies `w_{n+1} − 2n wₙ + w_{n−1} = −(2/π)(1 − (−1)ⁿ)`,
`n = 1, 2, …` (from the integral 11.10.2). -/
theorem dlmf_3_6_14 : IsRec3Inh besA besB besC weberD weberW := fun n hn => by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := congrArg (fun t : ℝ => (t : ℂ)) (weberE_rec m)
  simp only [besA, besB, besC, weberD, weberW, one_mul, Nat.add_sub_cancel] at h ⊢
  push_cast at h ⊢
  rw [show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring]
  linear_combination h

/-! ### The asymptotic forms 3.6.15–3.6.16 -/

/-- `π 𝐄ₙ(1) = 1/(n − 1) − (−1)ⁿ/(n + 1) + Rₙ` with `|Rₙ| ≤ 4π/(n − 1)³`, `n ≥ 2` (two
integrations by parts). -/
theorem weberE_expansion {n : ℕ} (hn : 2 ≤ n) :
    |π * weberE n 1 - (1 / ((n : ℝ) - 1) - (-1) ^ n / ((n : ℝ) + 1))| ≤
      4 * π / ((n : ℝ) - 1) ^ 3 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set N : ℝ := (n : ℝ)
  -- `φ′ = N − cos θ ≥ N − 1`
  have hd : ∀ θ : ℝ, N - 1 ≤ N - cos θ := fun θ => by linarith [cos_le_one θ]
  have hdpos : ∀ θ : ℝ, 0 < N - cos θ := fun θ => by linarith [hd θ]
  set ψ : ℝ → ℝ := fun θ => cos θ / (N - cos θ) ^ 3 - 3 * sin θ ^ 2 / (N - cos θ) ^ 4
  set G : ℝ → ℝ := fun θ =>
    -cos (N * θ - sin θ) / (N - cos θ) - sin (N * θ - sin θ) * sin θ / (N - cos θ) ^ 3
  have hG : ∀ θ ∈ Set.uIcc (0 : ℝ) π, HasDerivAt G
      (sin (N * θ - sin θ) - sin (N * θ - sin θ) * ψ θ) θ := fun θ _ => by
    have hφ : HasDerivAt (fun θ => N * θ - sin θ) (N * 1 - cos θ) θ :=
      ((hasDerivAt_id' θ).const_mul N).sub (hasDerivAt_sin θ)
    rw [mul_one] at hφ
    have hφ' : HasDerivAt (fun θ => N - cos θ) (sin θ) θ := by
      simpa using (hasDerivAt_cos θ).const_sub N
    have h1 := (hφ.cos.neg).div hφ' (hdpos θ).ne'
    have h2 := ((hφ.sin.mul (hasDerivAt_sin θ)).div (hφ'.pow 3) (pow_ne_zero 3 (hdpos θ).ne'))
    convert h1.sub h2 using 1
    simp only [ψ, Pi.pow_apply, Pi.mul_apply, Pi.neg_apply]
    have := (hdpos θ).ne'
    field_simp
    ring
  have hGi : IntervalIntegrable (fun θ => sin (N * θ - sin θ) - sin (N * θ - sin θ) * ψ θ)
      MeasureTheory.volume 0 π := by
    refine ContinuousOn.intervalIntegrable fun θ _ => ?_
    refine ContinuousAt.continuousWithinAt ?_
    have := (hdpos θ).ne'
    simp only [ψ]
    fun_prop (disch := exact pow_ne_zero _ this)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hG hGi
  have hψi : IntervalIntegrable (fun θ => sin (N * θ - sin θ) * ψ θ) MeasureTheory.volume 0 π := by
    refine ContinuousOn.intervalIntegrable fun θ _ => ?_
    refine ContinuousAt.continuousWithinAt ?_
    have := (hdpos θ).ne'
    simp only [ψ]
    fun_prop (disch := exact pow_ne_zero _ this)
  rw [intervalIntegral.integral_sub (intervalIntegrable_sin_phase N) hψi] at hFTC
  -- boundary values
  have hGπ : G π = -(-1) ^ n / (N + 1) := by
    simp only [G, sin_pi, mul_zero, sub_zero, cos_pi, zero_div, sub_zero]
    rw [show N * π = (n : ℝ) * π from rfl, cos_nat_mul_pi]
    ring_nf
  have hG0 : G 0 = -1 / (N - 1) := by simp [G]
  rw [hGπ, hG0] at hFTC
  -- the remainder
  have hψ : ∀ θ, |ψ θ| ≤ 4 / (N - 1) ^ 3 := fun θ => by
    have h1 : |cos θ / (N - cos θ) ^ 3| ≤ 1 / (N - 1) ^ 3 := by
      rw [abs_div, abs_of_pos (pow_pos (hdpos θ) 3)]
      exact div_le_div₀ zero_le_one (abs_cos_le_one θ) (by positivity) (pow_le_pow_left₀
        (by linarith) (hd θ) 3)
    have h2 : |3 * sin θ ^ 2 / (N - cos θ) ^ 4| ≤ 3 / (N - 1) ^ 3 := by
      have hs : sin θ ^ 2 ≤ 1 := sin_sq_le_one θ
      have hN3 : 0 < (N - 1) ^ 3 := pow_pos (by linarith) 3
      have hN4 : 0 < (N - 1) ^ 4 := pow_pos (by linarith) 4
      rw [abs_of_nonneg (div_nonneg (by positivity) (pow_pos (hdpos θ) 4).le)]
      calc 3 * sin θ ^ 2 / (N - cos θ) ^ 4 ≤ 3 / (N - 1) ^ 4 :=
            div_le_div₀ (by norm_num) (by nlinarith) hN4
              (pow_le_pow_left₀ (by linarith) (hd θ) 4)
        _ ≤ 3 / (N - 1) ^ 3 :=
            div_le_div_of_nonneg_left (by norm_num) hN3 (pow_le_pow_right₀ hn1 (by norm_num))
    calc |ψ θ| ≤ |cos θ / (N - cos θ) ^ 3| + |3 * sin θ ^ 2 / (N - cos θ) ^ 4| := abs_sub _ _
      _ ≤ 1 / (N - 1) ^ 3 + 3 / (N - 1) ^ 3 := add_le_add h1 h2
      _ = 4 / (N - 1) ^ 3 := by ring
  have hR : |∫ θ in (0 : ℝ)..π, sin (N * θ - sin θ) * ψ θ| ≤ 4 / (N - 1) ^ 3 * |π - 0| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π)
      (f := fun θ => sin (N * θ - sin θ) * ψ θ) (C := 4 / (N - 1) ^ 3) fun θ _ => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |sin (N * θ - sin θ)| * |ψ θ| ≤ 1 * (4 / (N - 1) ^ 3) :=
              mul_le_mul (abs_sin_le_one _) (hψ θ) (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
    simpa [Real.norm_eq_abs] using this
  rw [sub_zero, abs_of_pos pi_pos] at hR
  have hE : π * weberE n 1 = ∫ θ in (0 : ℝ)..π, sin (N * θ - sin θ) := by
    unfold weberE
    simp only [one_mul]
    field_simp
    rfl
  rw [hE]
  have hkey : (∫ θ in (0 : ℝ)..π, sin (N * θ - sin θ)) - (1 / (N - 1) - (-1) ^ n / (N + 1)) =
      ∫ θ in (0 : ℝ)..π, sin (N * θ - sin θ) * ψ θ := by
    linear_combination hFTC
  rw [hkey]
  calc _ ≤ 4 / (N - 1) ^ 3 * π := hR
    _ = 4 * π / (N - 1) ^ 3 := by ring

/-- **DLMF 3.6.15**: `𝐄_{2n}(1) ∼ 2/((4n² − 1)π)` as `n → ∞`. -/
theorem dlmf_3_6_15 : (fun n : ℕ => weberE (2 * (n : ℝ)) 1) ~[atTop]
    fun n => 2 / ((4 * (n : ℝ) ^ 2 - 1) * π) := by
  refine isEquivalent_of_tendsto_one ?_
  have hbound : ∀ n : ℕ, 1 ≤ n →
      |weberE (2 * (n : ℝ)) 1 / (2 / ((4 * (n : ℝ) ^ 2 - 1) * π)) - 1| ≤ 6 * π / n := by
    intro n hn
    have h := weberE_expansion (n := 2 * n) (by omega)
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : 0 < 4 * (n : ℝ) ^ 2 - 1 := by nlinarith
    have hpos2 : 0 < 2 * (n : ℝ) - 1 := by linarith
    push_cast at h
    rw [show ((-1 : ℝ) ^ (2 * n)) = 1 by rw [pow_mul]; norm_num] at h
    have e : weberE (2 * (n : ℝ)) 1 / (2 / ((4 * (n : ℝ) ^ 2 - 1) * π)) - 1 =
        (4 * (n : ℝ) ^ 2 - 1) / 2 *
          (π * weberE (2 * (n : ℝ)) 1 - (1 / (2 * (n : ℝ) - 1) - 1 / (2 * (n : ℝ) + 1))) := by
      have h3 : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
      have h4 : 2 * (n : ℝ) - 1 ≠ 0 := hpos2.ne'
      rw [show 4 * (n : ℝ) ^ 2 - 1 = (2 * n - 1) * (2 * n + 1) by ring]
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos (by positivity)]
    calc (4 * (n : ℝ) ^ 2 - 1) / 2 *
          |π * weberE (2 * (n : ℝ)) 1 - (1 / (2 * (n : ℝ) - 1) - 1 / (2 * (n : ℝ) + 1))|
        ≤ (4 * (n : ℝ) ^ 2 - 1) / 2 * (4 * π / (2 * (n : ℝ) - 1) ^ 3) := by gcongr
      _ = 2 * π * (2 * (n : ℝ) + 1) / (2 * (n : ℝ) - 1) ^ 2 := by
          have h4 : 2 * (n : ℝ) - 1 ≠ 0 := hpos2.ne'
          rw [show 4 * (n : ℝ) ^ 2 - 1 = (2 * n - 1) * (2 * n + 1) by ring]
          field_simp; ring
      _ ≤ 2 * π * (3 * n) / (n : ℝ) ^ 2 := by
          gcongr
          · linarith
          · nlinarith
      _ = 6 * π / n := by field_simp; ring
  have h0 : Tendsto (fun n : ℕ => 6 * π / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [eventually_ge_atTop 1] with n hn
  simpa [Real.norm_eq_abs] using hbound n hn

/-- **DLMF 3.6.16**: `𝐄_{2n+1}(1) ∼ 2/((2n + 1)π)` as `n → ∞`. -/
theorem dlmf_3_6_16 : (fun n : ℕ => weberE (2 * (n : ℝ) + 1) 1) ~[atTop]
    fun n => 2 / ((2 * (n : ℝ) + 1) * π) := by
  refine isEquivalent_of_tendsto_one ?_
  have hbound : ∀ n : ℕ, 1 ≤ n →
      |weberE (2 * (n : ℝ) + 1) 1 / (2 / ((2 * (n : ℝ) + 1) * π)) - 1| ≤ (1 + π) / n := by
    intro n hn
    have h := weberE_expansion (n := 2 * n + 1) (by omega)
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h
    rw [show ((-1 : ℝ) ^ (2 * n + 1)) = -1 by rw [pow_succ, pow_mul]; norm_num] at h
    rw [show 2 * (n : ℝ) + 1 - 1 = 2 * n by ring] at h
    have e : weberE (2 * (n : ℝ) + 1) 1 / (2 / ((2 * (n : ℝ) + 1) * π)) - 1 =
        1 / (4 * n * (n + 1)) + (2 * (n : ℝ) + 1) / 2 *
          (π * weberE (2 * (n : ℝ) + 1) 1 - (1 / (2 * (n : ℝ)) - -1 / (2 * (n : ℝ) + 1 + 1))) := by
      have : (n : ℝ) ≠ 0 := by positivity
      have : (n : ℝ) + 1 ≠ 0 := by positivity
      have : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
      have : 2 * (n : ℝ) + 1 + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [e]
    calc |1 / (4 * (n : ℝ) * (n + 1)) + (2 * (n : ℝ) + 1) / 2 *
          (π * weberE (2 * (n : ℝ) + 1) 1 - (1 / (2 * (n : ℝ)) - -1 / (2 * (n : ℝ) + 1 + 1)))|
        ≤ |1 / (4 * (n : ℝ) * (n + 1))| + |(2 * (n : ℝ) + 1) / 2 *
          (π * weberE (2 * (n : ℝ) + 1) 1 - (1 / (2 * (n : ℝ)) - -1 / (2 * (n : ℝ) + 1 + 1)))| :=
          abs_add_le _ _
      _ ≤ 1 / n + (2 * (n : ℝ) + 1) / 2 * (4 * π / (2 * (n : ℝ)) ^ 3) := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * n + 1) / 2),
            abs_of_pos (by positivity)]
          gcongr
          nlinarith
      _ ≤ 1 / n + π / n := by
          gcongr
          rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [pi_pos, mul_pos pi_pos (by positivity : (0 : ℝ) < n),
            mul_pos (mul_pos pi_pos (by positivity : (0 : ℝ) < n)) (by positivity : (0 : ℝ) < n)]
      _ = (1 + π) / n := by ring
  have h0 : Tendsto (fun n : ℕ => (1 + π) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [eventually_ge_atTop 1] with n hn
  simpa [Real.norm_eq_abs] using hbound n hn

/-! ### The Maclaurin series of `𝐄₀(1)` -/

/-- The terms `(−1)ᵏ (∫₀^π sin^{2k+1}) / (2k+1)!` with `∫₀^π sin^{2k+1} = 2∏_{i<k}(2i+2)/(2i+3)`. -/
noncomputable def weberE0Term (k : ℕ) : ℝ :=
  (-1) ^ k * (2 * ∏ i ∈ range k, (2 * (i : ℝ) + 2) / (2 * i + 3)) / (2 * k + 1).factorial

/-- `∫₀^π sin(sin θ) dθ = ∑ₖ (−1)ᵏ (∫₀^π sin^{2k+1}) / (2k+1)!` (termwise integration of the
sine series, §11.10(iii)). -/
theorem hasSum_weberE0Term :
    HasSum weberE0Term (∫ θ in (0 : ℝ)..π, sin (sin θ)) := by
  have hfac : Summable fun k : ℕ => (1 : ℝ) / k.factorial := by
    simpa using Real.summable_pow_div_factorial 1
  have hsum1 : Summable fun k : ℕ => (1 : ℝ) / (2 * k + 1).factorial :=
    Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => one_div_le_one_div_of_le
      (by positivity) (by exact_mod_cast Nat.factorial_le (by omega))) hfac
  have hmeas : ∀ k : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (-1) ^ k * sin θ ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))
      (MeasureTheory.volume.restrict (Set.uIoc 0 π)) := fun k =>
    (by fun_prop : Continuous fun θ : ℝ =>
      (-1) ^ k * sin θ ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)).aestronglyMeasurable
  have hbd : ∀ k : ℕ, ∀ᵐ θ ∂MeasureTheory.volume, θ ∈ Set.uIoc 0 π →
      ‖(-1) ^ k * sin θ ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)‖ ≤
        (fun (k : ℕ) (_ : ℝ) => (1 : ℝ) / (2 * k + 1).factorial) k θ := fun k =>
    Eventually.of_forall fun θ _ => by
      simp only [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        Nat.abs_cast]
      gcongr
      exact pow_le_one₀ (abs_nonneg _) (abs_sin_le_one θ)
  have hint : IntervalIntegrable (fun θ : ℝ => ∑' k : ℕ,
      (fun (k : ℕ) (_ : ℝ) => (1 : ℝ) / (2 * k + 1).factorial) k θ) MeasureTheory.volume 0 π :=
    intervalIntegrable_const
  have hlim : ∀ᵐ θ ∂MeasureTheory.volume, θ ∈ Set.uIoc 0 π →
      HasSum (fun k : ℕ => (-1) ^ k * sin θ ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))
        (sin (sin θ)) :=
    Eventually.of_forall fun θ _ => Real.hasSum_sin (sin θ)
  have h : HasSum (fun k : ℕ => ∫ θ in (0 : ℝ)..π,
      (-1) ^ k * sin θ ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))
      (∫ θ in (0 : ℝ)..π, sin (sin θ)) :=
    intervalIntegral.hasSum_integral_of_dominated_convergence _ hmeas hbd
      (Eventually.of_forall fun θ _ => hsum1) hint hlim
  refine h.congr_fun fun k => ?_
  simp only [weberE0Term]
  rw [show (fun θ => (-1) ^ k * sin θ ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) =
      fun θ => (-1) ^ k / ((2 * k + 1).factorial : ℝ) * sin θ ^ (2 * k + 1) by
    ext θ; ring, intervalIntegral.integral_const_mul, integral_sin_pow_odd]
  ring

/-- `𝐄₀(1) = −(1/π) ∫₀^π sin(sin θ) dθ`. -/
theorem weberE_zero_one : weberE 0 1 = -(1 / π) * ∫ θ in (0 : ℝ)..π, sin (sin θ) := by
  unfold weberE
  simp only [zero_mul, one_mul, zero_sub, sin_neg, intervalIntegral.integral_neg]
  ring

/-! ### Olver's algorithm applies -/

theorem tendsto_weberW_div_olverP :
    Tendsto (fun n => weberW n / olverP besA besB besC n) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h0 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [norm_div, weberW, Complex.norm_real, Real.norm_eq_abs]
  exact div_le_div₀ zero_le_one (abs_weberE_le _ _) hn' (norm_olverP_bes_ge n)

/-- **DLMF §3.6(vi)**: "the conditions for Olver's algorithm are satisfied" — with the
complementary functions `Jₙ(1)` (`J₀(1) ≠ 0`, recessive) and `pₙ` (dominant, in place of `Yₙ(1)`),
the values of Olver's algorithm started from `𝐄₀(1)` converge to `𝐄ₙ(1)`. -/
theorem dlmf_3_6_vi_weber_olver (n : ℕ) :
    Tendsto (fun N => olverW besA besB besC weberD (weberW 0) N n) atTop (𝓝 (weberW n)) :=
  dlmf_3_6_v_inhom besA_ne dlmf_3_6_11 (olverP_isRec3 besA_ne)
    (by simpa [besJ1] using besselJNat_zero_one_pos.ne')
    ((eventually_ge_atTop 1).mono fun n hn => olverP_bes_ne n hn) tendsto_besJ1_div_olverP
    dlmf_3_6_14 tendsto_weberW_div_olverP (fun k hk => olverP_bes_ne k hk) n

/-- `π 𝐄ₙ(1) ≥ 1/n²` for `n ≥ 101`. -/
theorem weberE_lower {n : ℕ} (hn : 101 ≤ n) : 1 / (n : ℝ) ^ 2 ≤ π * weberE n 1 := by
  have h := weberE_expansion (n := n) (by omega)
  have hn' : (101 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (n : ℝ) / 2 ≤ n - 1 := by linarith
  have hmain : 2 / ((n : ℝ) ^ 2 - 1) ≤ 1 / ((n : ℝ) - 1) - (-1) ^ n / ((n : ℝ) + 1) := by
    rcases neg_one_pow_eq_or ℝ n with h1 | h1 <;> rw [h1]
    · rw [show (n : ℝ) ^ 2 - 1 = (n - 1) * (n + 1) by ring]
      have : (n : ℝ) - 1 ≠ 0 := by linarith
      have : (n : ℝ) + 1 ≠ 0 := by linarith
      field_simp; ring_nf; rfl
    · rw [show (n : ℝ) ^ 2 - 1 = (n - 1) * (n + 1) by ring]
      have h3 : (0 : ℝ) < n - 1 := by linarith
      have h4 : (0 : ℝ) < n + 1 := by linarith
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith
  have h2 : 2 * (1 / (n : ℝ) ^ 2) ≤ 2 / ((n : ℝ) ^ 2 - 1) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by nlinarith) (by linarith)
  have h3 : 4 * π / ((n : ℝ) - 1) ^ 3 ≤ 1 / (n : ℝ) ^ 2 := by
    have hpi := pi_lt_d2
    rw [div_le_div_iff₀ (pow_pos (by linarith) 3) (by positivity)]
    have : ((n : ℝ) / 2) ^ 3 ≤ ((n : ℝ) - 1) ^ 3 := pow_le_pow_left₀ (by positivity) hn1 3
    nlinarith
  have := (abs_le.mp h).1
  linarith

/-- **DLMF §3.6(vi)**: "the asymptotic behavior of the particular solution `𝐄ₙ(1)` is intermediate
to those of the complementary functions `Jₙ(1)` and `Yₙ(1)`": `Jₙ(1)/𝐄ₙ(1) → 0` and
`𝐄ₙ(1)/pₙ → 0` for the dominant solution `pₙ`. -/
theorem dlmf_3_6_vi_weber_intermediate :
    Tendsto (fun n => besJ1 n / weberW n) atTop (𝓝 0) ∧
      Tendsto (fun n => weberW n / olverP besA besB besC n) atTop (𝓝 0) := by
  refine ⟨?_, tendsto_weberW_div_olverP⟩
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h0 : Tendsto (fun n : ℕ => Real.exp (1 / 4) * π * ((n : ℝ) ^ 2 * (1 / 2) ^ n)) atTop
      (𝓝 (Real.exp (1 / 4) * π * 0)) :=
    (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 (by norm_num)).const_mul _
  rw [mul_zero] at h0
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [eventually_ge_atTop 101] with n hn
  have hE := weberE_lower hn
  have hn' : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) (by exact_mod_cast hn : (101 : ℝ) ≤ n)
  have hEpos : 0 < weberE n 1 := by
    have : 0 < π * weberE n 1 := lt_of_lt_of_le (by positivity) hE
    exact pos_of_mul_pos_right this pi_pos.le
  have hJ := BZ.abs_besselJNat_le n 1
  rw [norm_div, besJ1, weberW, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hEpos, div_le_iff₀ hEpos]
  have hf : (1 : ℝ) ≤ n.factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
  simp only [abs_one, one_pow] at hJ
  calc |BZ.besselJNat n 1| ≤ (1 / 2) ^ n / n.factorial * Real.exp (1 / 4) := by
        simpa [div_pow] using hJ
    _ ≤ (1 / 2) ^ n * Real.exp (1 / 4) := by
        gcongr
        exact div_le_self (by positivity) hf
    _ = Real.exp (1 / 4) * π * ((n : ℝ) ^ 2 * (1 / 2) ^ n) * (1 / ((n : ℝ) ^ 2 * π)) := by
        field_simp
    _ ≤ Real.exp (1 / 4) * π * ((n : ℝ) ^ 2 * (1 / 2) ^ n) * weberE n 1 := by
        gcongr
        rw [div_le_iff₀ (by positivity)]
        have h' : 1 ≤ π * weberE n 1 * (n : ℝ) ^ 2 := (div_le_iff₀ (by positivity)).mp hE
        linarith [h', show weberE n 1 * ((n : ℝ) ^ 2 * π) = π * weberE n 1 * (n : ℝ) ^ 2 by ring]

end Azurite.DLMF
