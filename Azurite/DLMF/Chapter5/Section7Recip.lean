/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section7Log
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# DLMF 5.7.1–5.7.2: the Maclaurin series of `1/Γ`

Formalization of <https://dlmf.nist.gov/5.7> (part 4).

* 5.7.1, `1/Γ(z) = ∑_{k≥1} c_k zᵏ` for every `z` (`dlmf_5_7_1`), the `c_k` being the Taylor
  coefficients of the entire `1/Γ` at `0` (`recipGammaCoeff`, `c₀ = 0`); `c₁ = 1`, `c₂ = γ`
  (`recipGammaCoeff_one`, `recipGammaCoeff_two`).
* 5.7.2, `(k − 1) c_k = γ c_{k−1} − ζ(2) c_{k−2} + ζ(3) c_{k−3} − ⋯ + (−1)ᵏ ζ(k − 1) c₁`,
  `k ≥ 3` (`dlmf_5_7_2`, with `k = n + 2`; it holds for `k = 2` too). Proof: `1/Γ(z) = z h(z)`
  with `h(z) = 1/Γ(1 + z)` (`recipGammaCoeff_succ`), `h′ = −h ψ(1 + ·)` near `0`, Leibniz's
  rule (`iteratedDeriv_mul`), and the Taylor coefficients of `−ψ(1 + z)` read off 5.7.4 by
  uniqueness of power series (`hasFPowerSeriesAt_of_hasSum`,
  `iteratedDeriv_div_factorial_of_hasSum`).
-/

open Complex Filter Topology Set Finset Metric
open scoped Real Nat

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-- A power series `∑ aₙ zⁿ` converging to `f` on a disc about `0` is a power series of `f`. -/
theorem hasFPowerSeriesAt_of_hasSum {f : ℂ → ℂ} {a : ℕ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => a n * z ^ n) (f z)) :
    HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
  set r : NNReal := ⟨ρ / 2, by positivity⟩ with hr
  have hr' : (r : ℝ) = ρ / 2 := rfl
  have hrpos : (0 : ℝ) < r := by rw [hr']; positivity
  refine ⟨r, { r_le := ?_, r_pos := ?_, hasSum := ?_ }⟩
  · refine FormalMultilinearSeries.le_radius_of_tendsto _ (l := 0) ?_
    have h1 := (h (r : ℂ) (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, hr']; linarith)).summable
    have h2 := h1.tendsto_atTop_zero.norm
    rw [norm_zero] at h2
    refine h2.congr fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hrpos]
  · exact_mod_cast hrpos
  · intro y hy
    have hy' : ‖y‖ < ρ := by
      have h1 : edist y 0 < r := Metric.mem_eball.mp hy
      rw [edist_zero_right] at h1
      have h2 : ‖y‖₊ < r := by exact_mod_cast h1
      have h3 : ‖y‖ < r := by exact_mod_cast h2
      rw [hr'] at h3
      linarith
    rw [zero_add]
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using h y hy'

/-- The coefficients of a power series converging to `f` on a disc about `0` are its Taylor
coefficients. -/
theorem iteratedDeriv_div_factorial_of_hasSum {f : ℂ → ℂ} {a : ℕ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => a n * z ^ n) (f z)) (n : ℕ) :
    iteratedDeriv n f 0 / n ! = a n := by
  have h1 := hasFPowerSeriesAt_of_hasSum hρ h
  have h2 := h1.analyticAt.hasFPowerSeriesAt
  exact congrFun (FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    (h2.eq_formalMultilinearSeries h1)) n

/-- The coefficients `c_k` of DLMF 5.7.1, `1/Γ(z) = ∑ c_k zᵏ`: the Taylor coefficients of the
entire function `1/Γ` at `0`. -/
noncomputable def recipGammaCoeff (k : ℕ) : ℂ := iteratedDeriv k (fun z => (Gamma z)⁻¹) 0 / k !

/-- The Taylor coefficients of `1/Γ(1 + z)` at `0`. -/
noncomputable def recipGammaOneAddCoeff (n : ℕ) : ℂ :=
  iteratedDeriv n (fun z => (Gamma (1 + z))⁻¹) 0 / n !

/-- The Taylor coefficients of `−ψ(1 + z)` at `0` (5.7.4): `γ`, then `(−1)ʲ ζ(j + 1)`. -/
noncomputable def negDigammaOneAddCoeff : ℕ → ℂ
  | 0 => γ
  | j + 1 => (-1) ^ (j + 1) * riemannZeta (j + 2)

theorem differentiable_recipGamma_one_add : Differentiable ℂ fun z : ℂ => (Gamma (1 + z))⁻¹ :=
  differentiable_one_div_Gamma.comp (differentiable_id.const_add 1)

theorem hasSum_recipGamma (z : ℂ) :
    HasSum (fun k => recipGammaCoeff k * z ^ k) (Gamma z)⁻¹ := by
  have h := Complex.hasSum_taylorSeries_of_entire differentiable_one_div_Gamma 0 z
  simp only [sub_zero, smul_eq_mul] at h
  convert h using 1
  funext k
  simp only [recipGammaCoeff]
  ring

theorem hasSum_recipGamma_one_add (z : ℂ) :
    HasSum (fun n => recipGammaOneAddCoeff n * z ^ n) (Gamma (1 + z))⁻¹ := by
  have h := Complex.hasSum_taylorSeries_of_entire differentiable_recipGamma_one_add 0 z
  simp only [sub_zero, smul_eq_mul] at h
  convert h using 1
  funext k
  simp only [recipGammaOneAddCoeff]
  ring

theorem recipGammaCoeff_zero : recipGammaCoeff 0 = 0 := by
  simp [recipGammaCoeff, Complex.Gamma_zero]

/-- **DLMF 5.7.1**: `1/Γ(z) = ∑_{k=1}^∞ c_k zᵏ`, every `z`. -/
theorem dlmf_5_7_1 (z : ℂ) :
    HasSum (fun k => recipGammaCoeff (k + 1) * z ^ (k + 1)) (Gamma z)⁻¹ := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_recipGamma z)
  simpa [recipGammaCoeff_zero] using h

theorem recipGamma_eq_mul (z : ℂ) : (Gamma z)⁻¹ = z * (Gamma (1 + z))⁻¹ := by
  by_cases hz : z = 0
  · subst hz
    simp [Complex.Gamma_zero]
  · rw [show 1 + z = z + 1 by ring, Complex.Gamma_add_one z hz, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ hz, one_mul]

theorem recipGammaCoeff_succ (n : ℕ) : recipGammaCoeff (n + 1) = recipGammaOneAddCoeff n := by
  have key := iteratedDeriv_div_factorial_of_hasSum one_pos (f := fun z => (Gamma z)⁻¹)
    (a := fun k => if k = 0 then 0 else recipGammaOneAddCoeff (k - 1)) (fun z _ => by
      refine (hasSum_nat_add_iff' 1).mp ?_
      simp only [sum_range_one, ↓reduceIte, zero_mul, sub_zero, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, Nat.add_sub_cancel]
      rw [recipGamma_eq_mul]
      convert (hasSum_recipGamma_one_add z).mul_left z using 1
      funext n
      ring) (n + 1)
  simpa [recipGammaCoeff] using key

theorem one_add_not_mem_gammaPoles {z : ℂ} (hz : ‖z‖ < 1) : 1 + z ∉ gammaPoles :=
  not_mem_gammaPoles_of_re_pos (by
    simp only [add_re, one_re]
    linarith [abs_re_le_norm z, neg_abs_le z.re])

theorem hasSum_negDigammaOneAddCoeff {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => negDigammaOneAddCoeff n * z ^ n) (-digamma (1 + z)) := by
  refine (hasSum_nat_add_iff' 1).mp ?_
  simp only [sum_range_one, negDigammaOneAddCoeff, pow_zero, mul_one]
  convert (dlmf_5_7_4 hz).neg using 1
  · funext j
    ring
  · ring

theorem hasDerivAt_recipGamma_one_add {z : ℂ} (hp : 1 + z ∉ gammaPoles) :
    HasDerivAt (fun w => (Gamma (1 + w))⁻¹) ((Gamma (1 + z))⁻¹ * -digamma (1 + z)) z := by
  have hG : HasDerivAt (fun w => Gamma (1 + w)) (Gamma (1 + z) * digamma (1 + z)) z := by
    have h := (differentiableAt_Gamma _ (not_mem_gammaPoles.mp hp)).hasDerivAt.comp z
      ((hasDerivAt_id z).const_add 1)
    rw [deriv_Gamma_eq_mul_digamma hp, mul_one] at h
    exact h
  have hne : Gamma (1 + z) ≠ 0 := Complex.Gamma_ne_zero (not_mem_gammaPoles.mp hp)
  convert hG.inv hne using 1
  field_simp

/-- `(n + 1) h_{n+1} = ∑_{i ≤ n} hᵢ q_{n−i}` for the Taylor coefficients `h` of `1/Γ(1 + z)`
and `q` of `−ψ(1 + z)`. -/
theorem recipGammaOneAddCoeff_succ (n : ℕ) :
    ((n : ℂ) + 1) * recipGammaOneAddCoeff (n + 1) =
      ∑ i ∈ range (n + 1), recipGammaOneAddCoeff i * negDigammaOneAddCoeff (n - i) := by
  have hQc := iteratedDeriv_div_factorial_of_hasSum one_pos
    (fun z hz => hasSum_negDigammaOneAddCoeff hz)
  have hQa := (hasFPowerSeriesAt_of_hasSum one_pos
    (fun z hz => hasSum_negDigammaOneAddCoeff hz)).analyticAt
  simp only [recipGammaOneAddCoeff]
  simp_rw [← hQc]
  set h : ℂ → ℂ := fun w => (Gamma (1 + w))⁻¹ with hh
  set Q : ℂ → ℂ := fun w => -digamma (1 + w) with hQ
  have hha : AnalyticAt ℂ h 0 := differentiable_recipGamma_one_add.analyticAt 0
  have hev : deriv h =ᶠ[𝓝 0] h * Q := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (one_pos : (0 : ℝ) < 1))] with w hw
    rw [mem_ball_zero_iff] at hw
    exact (hasDerivAt_recipGamma_one_add (one_add_not_mem_gammaPoles hw)).deriv
  have hL := iteratedDeriv_mul (n := n) (x := (0 : ℂ)) hha.contDiffAt hQa.contDiffAt
  rw [← hev.iteratedDeriv_eq n, ← iteratedDeriv_succ'] at hL
  rw [hL, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hS : ∀ S : ℂ, ((n : ℂ) + 1) * (S / (((n : ℂ) + 1) * (n ! : ℂ))) = S / (n ! : ℂ) := by
    intro S; field_simp
  rw [hS, sum_div]
  refine sum_congr rfl fun i hi => ?_
  have hle : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hc : ((n.choose i : ℕ) : ℂ) * (i ! : ℂ) * ((n - i) ! : ℂ) = n ! := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hle
  have hi1 : (i ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hi2 : ((n - i) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - i))
  rw [div_mul_div_comm, div_eq_div_iff hn (mul_ne_zero hi1 hi2), ← hc]
  ring

/-- **DLMF 5.7.2**: `(k − 1) c_k = γ c_{k−1} − ζ(2) c_{k−2} + ζ(3) c_{k−3} − ⋯
+ (−1)ᵏ ζ(k − 1) c₁`, written with `k = n + 2` (DLMF states `k ≥ 3`; `k = 2` holds too). -/
theorem dlmf_5_7_2 (n : ℕ) :
    ((n : ℂ) + 1) * recipGammaCoeff (n + 2) =
      γ * recipGammaCoeff (n + 1) +
        ∑ i ∈ range n, (-1) ^ (i + 1) * riemannZeta (i + 2) * recipGammaCoeff (n - i) := by
  rw [show n + 2 = (n + 1) + 1 by ring, recipGammaCoeff_succ, recipGammaCoeff_succ,
    recipGammaOneAddCoeff_succ, sum_range_succ, Nat.sub_self]
  simp only [negDigammaOneAddCoeff]
  rw [add_comm, mul_comm (recipGammaOneAddCoeff n)]
  congr 1
  rw [← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j < n := mem_range.mp hj
  rw [show n - (n - 1 - j) = j + 1 by omega, show n - j = (n - 1 - j) + 1 by omega,
    recipGammaCoeff_succ]
  ring

/-- `c₁ = 1`. -/
theorem recipGammaCoeff_one : recipGammaCoeff 1 = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, recipGammaCoeff_succ]
  simp [recipGammaOneAddCoeff, Complex.Gamma_one]

/-- `c₂ = γ`. -/
theorem recipGammaCoeff_two : recipGammaCoeff 2 = γ := by
  have h := dlmf_5_7_2 0
  simpa [recipGammaCoeff_one] using h

end Azurite.DLMF
