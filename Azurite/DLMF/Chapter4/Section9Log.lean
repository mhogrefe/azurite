/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section12VanVleck
import Azurite.DLMF.Chapter3.Section5GaussLegendre
import Azurite.DLMF.Chapter4.Section9Exp
import Azurite.DLMF.Chapter4.Section9Markov
import Mathlib.Analysis.Complex.Convex

/-!
# DLMF §4.9(i): Continued fractions for logarithms

Formalizations of <https://dlmf.nist.gov/4.9> 4.9.1 and 4.9.2 on DLMF's full regions. The
convergents are `Cₙ = Aₙ/Bₙ` (`cfA`, `cfB` of §1.12).

* The integrals `ψ(α, β, γ) = ∫ₐᵇ (t − a)^α (b − t)^β (1 + z t)^{−γ} dt` (`logPsi`) and three
  contiguous relations: `logPsi_split`, `logPsi_mul`, `logPsi_parts` (integration by parts).
* The errors `L Bᵣ − Aᵣ` of the convergents are explicit multiples of `z^{N} ψ(…)`
  (`lg1_err`, `lg2_err`), hence `O(z^{N})` at `0`.
* With `pade_unique`, the convergents are the Gauss quadrature approximations of
  `∫ dt/(1 + z t)` (`lg1_even_eq`, `lg1_odd_eq`, `lg2_eq`), and they converge by Markov's theorem
  `gauss_tendsto`.
* 4.9.1: `dlmf_4_9_1` (for `|ph(1 + z)| < π`); 4.9.2: `dlmf_4_9_2`
  (for `z ∈ ℂ ∖ ((−∞, −1] ∪ [1, ∞))`).
-/

open Polynomial Finset Set MeasureTheory Filter Topology Complex
open scoped Real Nat

namespace Azurite.DLMF

/-! ### The integrals `ψ(α, β, γ)` -/

/-- `ψ(α, β, γ) = ∫ₐᵇ (t − a)^α (b − t)^β / (1 + z t)^γ dt`. -/
noncomputable def logPsi (a b : ℝ) (α β γ : ℕ) (z : ℂ) : ℂ :=
  ∫ t in a..b, ((t : ℂ) - a) ^ α * ((b : ℂ) - t) ^ β / (1 + z * t) ^ γ

variable {a b : ℝ} {z : ℂ}

theorem logPsi_continuousOn (hz : ∀ t ∈ Icc a b, 1 + z * t ≠ 0) (α β γ : ℕ) :
    ContinuousOn (fun t : ℝ => ((t : ℂ) - a) ^ α * ((b : ℂ) - t) ^ β / (1 + z * t) ^ γ)
      (Icc a b) :=
  (((continuous_ofReal.sub continuous_const).pow α).mul
    ((continuous_const.sub continuous_ofReal).pow β)).continuousOn.div
    ((continuous_const.add (continuous_const.mul continuous_ofReal)).pow γ).continuousOn
    fun t ht => pow_ne_zero _ (hz t ht)

theorem logPsi_integrable (hab : a ≤ b) (hz : ∀ t ∈ Icc a b, 1 + z * t ≠ 0) (α β γ : ℕ) :
    IntervalIntegrable (fun t : ℝ => ((t : ℂ) - a) ^ α * ((b : ℂ) - t) ^ β / (1 + z * t) ^ γ)
      volume a b :=
  ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hab]; exact logPsi_continuousOn hz α β γ)

theorem logPsi_zero_zero_zero (a b : ℝ) (z : ℂ) : logPsi a b 0 0 0 z = b - a := by
  simp [logPsi]

/-- `(b − a) ψ(α, β, γ) = ψ(α + 1, β, γ) + ψ(α, β + 1, γ)`. -/
theorem logPsi_split (hab : a ≤ b) (hz : ∀ t ∈ Icc a b, 1 + z * t ≠ 0) (α β γ : ℕ) :
    ((b : ℂ) - a) * logPsi a b α β γ z = logPsi a b (α + 1) β γ z + logPsi a b α (β + 1) γ z := by
  simp only [logPsi]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
    (logPsi_integrable hab hz _ _ _) (logPsi_integrable hab hz _ _ _)]
  congr 1; funext t; ring

/-- `ψ(α, β, γ) = (1 + z a) ψ(α, β, γ + 1) + z ψ(α + 1, β, γ + 1)`. -/
theorem logPsi_mul (hab : a ≤ b) (hz : ∀ t ∈ Icc a b, 1 + z * t ≠ 0) (α β γ : ℕ) :
    logPsi a b α β γ z =
      (1 + z * a) * logPsi a b α β (γ + 1) z + z * logPsi a b (α + 1) β (γ + 1) z := by
  simp only [logPsi]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((logPsi_integrable hab hz _ _ _).const_mul _)
      ((logPsi_integrable hab hz _ _ _).const_mul _)]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hab] at ht
  have hD := hz t ht
  have hD' : 1 + (t : ℂ) * z ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

/-- Integration by parts:
`(α + 1) ψ(α, β + 1, γ + 1) − (β + 1) ψ(α + 1, β, γ + 1) = (γ + 1) z ψ(α + 1, β + 1, γ + 2)`. -/
theorem logPsi_parts (hab : a ≤ b) (hz : ∀ t ∈ Icc a b, 1 + z * t ≠ 0) (α β γ : ℕ) :
    (α + 1) * logPsi a b α (β + 1) (γ + 1) z - (β + 1) * logPsi a b (α + 1) β (γ + 1) z =
      (γ + 1) * z * logPsi a b (α + 1) (β + 1) (γ + 2) z := by
  set G : ℂ → ℂ := fun u => (u - a) ^ (α + 1) * ((b : ℂ) - u) ^ (β + 1) / (1 + z * u) ^ (γ + 1)
  set G' : ℝ → ℂ := fun t =>
    (α + 1) * (((t : ℂ) - a) ^ α * ((b : ℂ) - t) ^ (β + 1) / (1 + z * t) ^ (γ + 1)) -
      (β + 1) * (((t : ℂ) - a) ^ (α + 1) * ((b : ℂ) - t) ^ β / (1 + z * t) ^ (γ + 1)) -
      (γ + 1) * z * (((t : ℂ) - a) ^ (α + 1) * ((b : ℂ) - t) ^ (β + 1) / (1 + z * t) ^ (γ + 2))
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (fun s : ℝ => G s) (G' t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have hD := hz t ht
    have h := ((((hasDerivAt_id (t : ℂ)).sub_const (a : ℂ)).fun_pow (α + 1)).mul
      (((hasDerivAt_id (t : ℂ)).const_sub (b : ℂ)).fun_pow (β + 1))).div
      ((((hasDerivAt_id (t : ℂ)).const_mul z).const_add 1).fun_pow (γ + 1))
      (by simp only [id]; exact pow_ne_zero _ hD)
    convert h.comp_ofReal using 1
    case e'_8 => rfl
    simp only [G', id, Nat.add_sub_cancel, Pi.mul_apply, Nat.cast_add, Nat.cast_one]
    generalize (t : ℂ) - a = X
    generalize (b : ℂ) - t = Y
    generalize hDdef : 1 + z * (t : ℂ) = D at hD ⊢
    field_simp
    ring
  have hint : IntervalIntegrable G' volume a b := by
    simp only [G']
    exact (((logPsi_integrable hab hz _ _ _).const_mul _).sub
      ((logPsi_integrable hab hz _ _ _).const_mul _)).sub
      ((logPsi_integrable hab hz _ _ _).const_mul _)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hGa : G a = 0 := by simp [G]
  have hGb : G b = 0 := by simp [G]
  rw [hGa, hGb, sub_zero] at hFTC
  simp only [G'] at hFTC
  rw [intervalIntegral.integral_sub (((logPsi_integrable hab hz _ _ _).const_mul _).sub
      ((logPsi_integrable hab hz _ _ _).const_mul _))
      ((logPsi_integrable hab hz _ _ _).const_mul _),
    intervalIntegral.integral_sub ((logPsi_integrable hab hz _ _ _).const_mul _)
      ((logPsi_integrable hab hz _ _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hFTC
  simp only [logPsi]
  linear_combination hFTC

/-- `ψ` is bounded near `z = 0` when `[a, b] ⊆ [−1, 1]`. -/
theorem logPsi_bound (hab : a ≤ b) (ha : -1 ≤ a) (hb : b ≤ 1) (α β γ : ℕ) :
    ∃ C, ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → ‖logPsi a b α β γ z‖ ≤ C := by
  refine ⟨2 ^ α * 2 ^ β * 2 ^ γ * |b - a|, fun z hz =>
    intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_⟩
  rw [uIoc_of_le hab] at ht
  have hta : |t - a| ≤ 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htb : |b - t| ≤ 2 := abs_le.mpr ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
  have hD := norm_one_add_mul_ge hz (x := t) (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_pow,
    show (t : ℂ) - a = ((t - a : ℝ) : ℂ) by push_cast; ring,
    show (b : ℂ) - t = ((b - t : ℝ) : ℂ) by push_cast; ring, norm_real, norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, div_le_iff₀ (by positivity)]
  have h1 : |t - a| ^ α ≤ 2 ^ α := pow_le_pow_left₀ (abs_nonneg _) hta α
  have h2 : |b - t| ^ β ≤ 2 ^ β := pow_le_pow_left₀ (abs_nonneg _) htb β
  have h3 : (1 : ℝ) ≤ 2 ^ γ * ‖1 + z * t‖ ^ γ := by
    rw [← mul_pow]; exact one_le_pow₀ (by linarith)
  calc |t - a| ^ α * |b - t| ^ β ≤ 2 ^ α * 2 ^ β := by gcongr
    _ = 2 ^ α * 2 ^ β * 1 := by ring
    _ ≤ 2 ^ α * 2 ^ β * (2 ^ γ * ‖1 + z * t‖ ^ γ) := by gcongr
    _ = 2 ^ α * 2 ^ β * 2 ^ γ * ‖1 + z * t‖ ^ γ := by ring

/-! ### 4.9.1: the continued fraction for `ln(1 + z)` -/

theorem logPsi01_split (hz : ∀ t ∈ Icc (0 : ℝ) 1, 1 + z * t ≠ 0) (α β γ : ℕ) :
    logPsi 0 1 α β γ z = logPsi 0 1 (α + 1) β γ z + logPsi 0 1 α (β + 1) γ z := by
  have := logPsi_split zero_le_one hz α β γ
  simpa using this

theorem logPsi01_mul (hz : ∀ t ∈ Icc (0 : ℝ) 1, 1 + z * t ≠ 0) (α β γ : ℕ) :
    logPsi 0 1 α β γ z = logPsi 0 1 α β (γ + 1) z + z * logPsi 0 1 (α + 1) β (γ + 1) z := by
  have := logPsi_mul zero_le_one hz α β γ
  simpa using this

/-- `a₁ = z`, `a_{2j} = a_{2j+1} = j² z` in
`z/(1 + z/(2 + z/(3 + 4z/(4 + 4z/(5 + 9z/(6 + 9z/(7 + ⋯)))))))`. -/
noncomputable def lg1a (z : ℂ) (r : ℕ) : ℂ := if r = 1 then z else (((r / 2) ^ 2 : ℕ) : ℂ) * z

/-- `b₀ = 0`, `bᵣ = r`. -/
noncomputable def lg1b (_z : ℂ) (r : ℕ) : ℂ := r

/-- `z ∫₀¹ dt/(1 + z t)` (`= ln(1 + z)`, `lgL1_eq_log`). -/
noncomputable def lgL1 (z : ℂ) : ℂ := z * logPsi 0 1 0 0 1 z

theorem lg1_err (hz : ∀ t ∈ Icc (0 : ℝ) 1, 1 + z * t ≠ 0) (n : ℕ) :
    lgL1 z * cfB (lg1a z) (lg1b z) (2 * n) - cfA (lg1a z) (lg1b z) (2 * n) =
      (n ! : ℂ) ^ 2 * z ^ (2 * n + 1) * logPsi 0 1 n n (n + 1) z ∧
    lgL1 z * cfB (lg1a z) (lg1b z) (2 * n + 1) - cfA (lg1a z) (lg1b z) (2 * n + 1) =
      -((n ! : ℂ) * ((n + 1)! : ℂ)) * z ^ (2 * n + 2) * logPsi 0 1 (n + 1) n (n + 1) z := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [cfA, cfB, cfP, cfQ, lg1b, lgL1]
    · simp only [cfA, cfB, cfP, cfQ, lg1a, lg1b, lgL1]
      have h := logPsi01_mul hz 0 0 0
      have h0 := logPsi_zero_zero_zero (0 : ℝ) 1 z
      simp at h h0 ⊢
      linear_combination -z * h + z * h0
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    have hfac : ((n + 1)! : ℂ) = (n + 1) * n ! := by push_cast [Nat.factorial_succ]; ring
    have hfac2 : ((n + 1 + 1)! : ℂ) = (n + 2) * ((n + 1) * n !) := by
      push_cast [Nat.factorial_succ]; ring
    have hE2 : lgL1 z * cfB (lg1a z) (lg1b z) (2 * (n + 1)) -
        cfA (lg1a z) (lg1b z) (2 * (n + 1)) =
        ((n + 1)! : ℂ) ^ 2 * z ^ (2 * (n + 1) + 1) * logPsi 0 1 (n + 1) (n + 1) (n + 2) z := by
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, cfErr_add_two, h0, h1]
      have hb : lg1b z (2 * n + 2) = 2 * n + 2 := by simp [lg1b]
      have ha : lg1a z (2 * n + 2) = (n + 1) ^ 2 * z := by
        simp only [lg1a]
        rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)),
          show (2 * n + 2) / 2 = n + 1 by omega]; push_cast; ring
      rw [hb, ha, hfac]
      have h3 := logPsi_parts zero_le_one hz n n n
      have hs := logPsi01_split hz n n (n + 1)
      linear_combination ((n ! : ℂ) ^ 2 * (n + 1) * z ^ (2 * n + 2)) * h3 +
        ((n ! : ℂ) ^ 2 * (n + 1) ^ 2 * z ^ (2 * n + 2)) * hs
    refine ⟨hE2, ?_⟩
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, cfErr_add_two,
      show 2 * n + 1 + 1 = 2 * (n + 1) by ring, hE2, h1]
    have hb : lg1b z (2 * n + 1 + 2) = 2 * n + 3 := by simp [lg1b]; ring
    have ha : lg1a z (2 * n + 1 + 2) = (n + 1) ^ 2 * z := by
      simp only [lg1a]
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)),
        show (2 * n + 1 + 2) / 2 = n + 1 by omega]; push_cast; ring
    rw [hb, ha, hfac2, hfac]
    have h3 := logPsi_parts zero_le_one hz (n + 1) n n
    have h2 := logPsi01_mul hz (n + 1) (n + 1) (n + 1)
    have hs := logPsi01_split hz (n + 1) n (n + 1)
    push_cast at h3
    linear_combination ((n ! : ℂ) ^ 2 * (n + 1) ^ 2 * z ^ (2 * n + 3)) *
      (h3 - (2 * n + 3) * h2 - (n + 1) * hs)

/-! ### 4.9.2: the continued fraction for `ln((1 + z)/(1 − z))` -/

theorem logPsi11_split (hz : ∀ t ∈ Icc (-1 : ℝ) 1, 1 + z * t ≠ 0) (α β γ : ℕ) :
    2 * logPsi (-1) 1 α β γ z = logPsi (-1) 1 (α + 1) β γ z + logPsi (-1) 1 α (β + 1) γ z := by
  have := logPsi_split (by norm_num) hz α β γ
  push_cast at this; norm_num at this; exact this

theorem logPsi11_mul (hz : ∀ t ∈ Icc (-1 : ℝ) 1, 1 + z * t ≠ 0) (α β γ : ℕ) :
    logPsi (-1) 1 α β γ z =
      (1 - z) * logPsi (-1) 1 α β (γ + 1) z + z * logPsi (-1) 1 (α + 1) β (γ + 1) z := by
  have := logPsi_mul (by norm_num) hz α β γ
  push_cast at this; rw [this]; ring

theorem lg2_i (hz : ∀ t ∈ Icc (-1 : ℝ) 1, 1 + z * t ≠ 0) (m : ℕ) :
    z * logPsi (-1) 1 (m + 1) (m + 1) (m + 2) z =
      2 * logPsi (-1) 1 m m (m + 1) z - 2 * logPsi (-1) 1 (m + 1) m (m + 1) z := by
  have pB := logPsi_parts (by norm_num) hz m m m
  have s2 := logPsi11_split hz m m (m + 1)
  have hm : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  refine mul_left_cancel₀ hm ?_
  linear_combination -pB - (m + 1) * s2

theorem lg2_ii (hz : ∀ t ∈ Icc (-1 : ℝ) 1, 1 + z * t ≠ 0) (m : ℕ) :
    (m + 2) * z * logPsi (-1) 1 (m + 2) (m + 1) (m + 2) z =
      ((m + 2) * z - (2 * m + 3)) * logPsi (-1) 1 (m + 1) (m + 1) (m + 2) z +
        2 * (m + 1) * logPsi (-1) 1 m m (m + 1) z := by
  have pA := logPsi_parts (by norm_num) hz (m + 1) m m
  have mM := logPsi11_mul hz (m + 1) (m + 1) (m + 1)
  have s1 := logPsi11_split hz (m + 1) m (m + 1)
  have s2 := logPsi11_split hz m m (m + 1)
  have pB := logPsi_parts (by norm_num) hz m m m
  push_cast at pA pB
  linear_combination pA - (2 * m + 3) * mM - (m + 1) * s1 - (m + 1) * s2 - pB

/-- `a₁ = 2z`, `a_{n+1} = −n² z²` in `2z/(1 − z²/(3 − 4z²/(5 − 9z²/(7 − 16z²/(9 − ⋯)))))`. -/
noncomputable def lg2a (z : ℂ) (r : ℕ) : ℂ :=
  if r = 1 then 2 * z else -((((r - 1) ^ 2 : ℕ) : ℂ) * z ^ 2)

/-- `b₀ = 0`, `bᵣ = 2r − 1`. -/
noncomputable def lg2b (_z : ℂ) (r : ℕ) : ℂ := if r = 0 then 0 else 2 * (r : ℂ) - 1

/-- `z ∫₋₁¹ dt/(1 + z t)` (`= ln((1 + z)/(1 − z))`, `lgL2_eq_log`). -/
noncomputable def lgL2 (z : ℂ) : ℂ := z * logPsi (-1) 1 0 0 1 z

theorem lg2_err (hz : ∀ t ∈ Icc (-1 : ℝ) 1, 1 + z * t ≠ 0) (m : ℕ) :
    lgL2 z * cfB (lg2a z) (lg2b z) m - cfA (lg2a z) (lg2b z) m =
      (m ! : ℂ) / 2 ^ m * z ^ (2 * m + 1) * logPsi (-1) 1 m m (m + 1) z ∧
    lgL2 z * cfB (lg2a z) (lg2b z) (m + 1) - cfA (lg2a z) (lg2b z) (m + 1) =
      ((m + 1)! : ℂ) / 2 ^ (m + 1) * z ^ (2 * m + 3) *
        logPsi (-1) 1 (m + 1) (m + 1) (m + 2) z := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [cfA, cfB, cfP, cfQ, lg2b, lgL2]
    · simp only [cfA, cfB, cfP, cfQ, lg2a, lg2b, lgL2]
      have hp := logPsi_parts (by norm_num) hz 0 0 0
      have hs := logPsi11_split hz 0 0 1
      have hm := logPsi11_mul hz 0 0 0
      have h0 := logPsi_zero_zero_zero (-1 : ℝ) 1 z
      push_cast at hp h0
      norm_num at hp h0 ⊢
      linear_combination (z ^ 2 / 2) * hp + (z ^ 2 / 2) * hs - z * hm + z * h0
  | succ m ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    rw [show m + 1 + 1 = m + 2 by ring, cfErr_add_two, h1, h0]
    have hb : lg2b z (m + 2) = 2 * m + 3 := by simp [lg2b]; ring
    have ha : lg2a z (m + 2) = -((m + 1) ^ 2 * z ^ 2) := by
      simp only [lg2a]
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)),
        show m + 2 - 1 = m + 1 by omega]; push_cast; ring
    have hfac : ((m + 1)! : ℂ) = (m + 1) * m ! := by push_cast [Nat.factorial_succ]; ring
    have hfac2 : ((m + 1 + 1)! : ℂ) = (m + 2) * ((m + 1) * m !) := by
      push_cast [Nat.factorial_succ]; ring
    rw [hb, ha, hfac2, hfac]
    have hi := lg2_i hz (m + 1)
    have hii := lg2_ii hz m
    rw [show m + 1 + 1 = m + 2 by ring, show m + 1 + 2 = m + 3 by ring] at hi ⊢
    linear_combination ((m ! : ℂ) / 2 ^ m * (m + 1) / 4 * z ^ (2 * m + 3)) *
      (-(m + 2) * z * hi + 2 * hii)

/-! ### Degrees of the convergents -/

theorem isPolyFunDeg_lg1a (i : ℕ) : IsPolyFunDeg (fun z => lg1a z i) 1 := by
  by_cases h : i = 1
  · exact IsPolyFunDeg.id.congr fun z => by simp [lg1a, h]
  · exact (IsPolyFunDeg.const_mul_id ((((i / 2) ^ 2 : ℕ) : ℂ))).congr fun z => by
      simp only [lg1a, h, ↓reduceIte]

theorem lg1_deg (i : ℕ) : IsPolyFunDeg (fun z => cfP (lg1a z) (lg1b z) i) (i / 2) ∧
    IsPolyFunDeg (fun z => cfQ (lg1a z) (lg1b z) i) ((i - 1) / 2) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 => exact ⟨(IsPolyFunDeg.const 1).congr fun z => rfl,
        (IsPolyFunDeg.const 0).congr fun z => rfl⟩
    | 1 => exact ⟨(IsPolyFunDeg.const 0).congr fun z => by simp [cfP, lg1b],
        (IsPolyFunDeg.const 1).congr fun z => rfl⟩
    | 2 => exact ⟨IsPolyFunDeg.id.congr fun z => by simp [cfP, lg1a, lg1b],
        (IsPolyFunDeg.const 1).congr fun z => by simp [cfQ, lg1b]⟩
    | k + 3 =>
      obtain ⟨p2, q2⟩ := ih (k + 2) (by omega)
      obtain ⟨p1, q1⟩ := ih (k + 1) (by omega)
      have hb : IsPolyFunDeg (fun z => lg1b z (k + 2)) 0 :=
        (IsPolyFunDeg.const ((k + 2 : ℕ) : ℂ)).congr fun z => rfl
      have ha := isPolyFunDeg_lg1a (k + 2)
      exact ⟨(((hb.mul p2).mono (by omega)).add ((ha.mul p1).mono (by omega))).congr
          fun z => rfl,
        (((hb.mul q2).mono (by omega)).add ((ha.mul q1).mono (by omega))).congr fun z => rfl⟩

theorem isPolyFunDeg_lg2a (i : ℕ) : IsPolyFunDeg (fun z => lg2a z i) 2 := by
  by_cases h : i = 1
  · exact ((IsPolyFunDeg.const_mul_id 2).mono (by omega)).congr fun z => by simp [lg2a, h]
  · exact ((IsPolyFunDeg.const (-((((i - 1) ^ 2 : ℕ) : ℂ)))).mul
      (IsPolyFunDeg.id.mul IsPolyFunDeg.id)).congr fun z => by
      simp only [lg2a, h, ↓reduceIte]; ring

theorem lg2_deg (i : ℕ) : IsPolyFunDeg (fun z => cfP (lg2a z) (lg2b z) i) (i - 1) ∧
    IsPolyFunDeg (fun z => cfQ (lg2a z) (lg2b z) i) (i - 1) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 => exact ⟨(IsPolyFunDeg.const 1).congr fun z => rfl,
        (IsPolyFunDeg.const 0).congr fun z => rfl⟩
    | 1 => exact ⟨(IsPolyFunDeg.const 0).congr fun z => by simp [cfP, lg2b],
        (IsPolyFunDeg.const 1).congr fun z => rfl⟩
    | 2 => exact ⟨(IsPolyFunDeg.const_mul_id 2).congr fun z => by simp [cfP, lg2a, lg2b],
        ((IsPolyFunDeg.const 1).mono (by omega)).congr fun z => by simp [cfQ, lg2b]; norm_num⟩
    | k + 3 =>
      obtain ⟨p2, q2⟩ := ih (k + 2) (by omega)
      obtain ⟨p1, q1⟩ := ih (k + 1) (by omega)
      have hb : IsPolyFunDeg (fun z => lg2b z (k + 2)) 0 :=
        (IsPolyFunDeg.const (2 * ((k + 2 : ℕ) : ℂ) - 1)).congr fun z => by simp [lg2b]
      have ha := isPolyFunDeg_lg2a (k + 2)
      exact ⟨(((hb.mul p2).mono (by omega)).add ((ha.mul p1).mono (by omega))).congr
          fun z => rfl,
        (((hb.mul q2).mono (by omega)).add ((ha.mul q1).mono (by omega))).congr fun z => rfl⟩

/-! ### Identification with Gauss quadrature -/

theorem bigO_of_formula {E ψ : ℂ → ℂ} {κ : ℂ} {N : ℕ}
    (hψ : ∃ C, ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → ‖ψ z‖ ≤ C)
    (hE : ∀ z : ℂ, ‖z‖ < 1 / 2 → E z = κ * z ^ N * ψ z) :
    ∃ δ > 0, ∃ C, ∀ z, ‖z‖ < δ → ‖E z‖ ≤ C * ‖z‖ ^ N := by
  obtain ⟨C, hC⟩ := hψ
  refine ⟨1 / 2, by norm_num, ‖κ‖ * C, fun z hz => ?_⟩
  rw [hE z hz, norm_mul, norm_mul, norm_pow]
  have := hC z hz.le
  have h0 : 0 ≤ ‖z‖ ^ N := by positivity
  calc ‖κ‖ * ‖z‖ ^ N * ‖ψ z‖ ≤ ‖κ‖ * ‖z‖ ^ N * C := by gcongr
    _ = ‖κ‖ * C * ‖z‖ ^ N := by ring

theorem noPole_small (ha : -1 ≤ a) (hb : b ≤ 1) (hz : ‖z‖ ≤ 1 / 2) :
    ∀ t ∈ Icc a b, 1 + z * t ≠ 0 := fun t ht =>
  one_add_mul_ne_zero hz (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)

theorem logPsi_001 (a b : ℝ) (z : ℂ) :
    logPsi a b 0 0 1 z = ∫ x in a..b, (1 : ℂ) / (1 + z * x) := by
  simp [logPsi]

theorem logPsi01_101 (z : ℂ) : logPsi 0 1 1 0 1 z = ∫ x in (0 : ℝ)..1, (x : ℂ) / (1 + z * x) := by
  simp [logPsi]

theorem isGaussWeight_one01 : IsGaussWeight (Ioo (0 : ℝ) 1) (fun _ => 1) where
  isOpen := isOpen_Ioo
  ordConnected := ordConnected_Ioo
  nonempty := ⟨1 / 2, by norm_num, by norm_num⟩
  pos := fun _ _ => one_pos
  integrableOn := fun k =>
    ((continuous_pow k).mul continuous_const).integrableOn_Icc.mono_set Ioo_subset_Icc_self

theorem isGaussWeight_id01 : IsGaussWeight (Ioo (0 : ℝ) 1) (fun x => x) where
  isOpen := isOpen_Ioo
  ordConnected := ordConnected_Ioo
  nonempty := ⟨1 / 2, by norm_num, by norm_num⟩
  pos := fun _ hx => hx.1
  integrableOn := fun k =>
    ((continuous_pow k).mul continuous_id).integrableOn_Icc.mono_set Ioo_subset_Icc_self

/-- The monic Legendre polynomials on `(0, 1)`. -/
noncomputable def gP1 (n : ℕ) : ℝ[X] := (exists_isOrthMonic isGaussWeight_one01 n).choose

theorem gP1_spec (n : ℕ) : IsOrthMonic (Ioo 0 1) (fun _ => 1) n (gP1 n) :=
  (exists_isOrthMonic isGaussWeight_one01 n).choose_spec

/-- The monic orthogonal polynomials for the weight `t` on `(0, 1)`. -/
noncomputable def gPt (n : ℕ) : ℝ[X] := (exists_isOrthMonic isGaussWeight_id01 n).choose

theorem gPt_spec (n : ℕ) : IsOrthMonic (Ioo 0 1) (fun x => x) n (gPt n) :=
  (exists_isOrthMonic isGaussWeight_id01 n).choose_spec

/-- The monic Legendre polynomials on `(−1, 1)`. -/
noncomputable def gP2 (n : ℕ) : ℝ[X] := (exists_isOrthMonic isGaussWeight_legendre n).choose

theorem gP2_spec (n : ℕ) : IsOrthMonic (Ioo (-1) 1) (fun _ => 1) n (gP2 n) :=
  (exists_isOrthMonic isGaussWeight_legendre n).choose_spec

/-- The even convergents of 4.9.1 are `z ×` the `n`-point Gauss–Legendre rule on `(0, 1)`. -/
theorem lg1_even_eq {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    cfA (lg1a z) (lg1b z) (2 * n) * gaussB (gP1 n) z =
      (z * gaussA 0 1 (fun _ => 1) (gP1 n) z) * cfB (lg1a z) (lg1b z) (2 * n) := by
  have hcard := gauss_card isGaussWeight_one01 (gP1_spec n)
  refine pade_unique (A := fun z => cfA (lg1a z) (lg1b z) (2 * n))
    (B := fun z => cfB (lg1a z) (lg1b z) (2 * n)) (A' := fun z => z * gaussA 0 1 _ (gP1 n) z)
    (B' := gaussB (gP1 n)) (L := lgL1) (d := 2 * n) (N := 2 * n + 1) ?_ (by omega)
    (lg1_deg (2 * n + 1)).2.continuous (isPolyFunDeg_gaussB _).continuous ?_ ?_ z
  · have hA := (lg1_deg (2 * n + 1)).1
    have hB := (lg1_deg (2 * n + 1)).2
    have hB' := isPolyFunDeg_gaussB (gP1 n)
    have hA' := IsPolyFunDeg.id.mul (isPolyFunDeg_gaussA 0 1 (fun _ => 1) (gP1 n))
    rw [hcard] at hB' hA'
    exact ((hA.mul hB').mono (by omega)).sub ((hA'.mul hB).mono (by omega))
  · obtain ⟨C, hC⟩ := logPsi_bound zero_le_one (by norm_num) le_rfl n n (n + 1)
    refine bigO_of_formula (ψ := logPsi 0 1 n n (n + 1)) (κ := (n ! : ℂ) ^ 2) ⟨C, hC⟩
      fun z hz => ?_
    rw [← (lg1_err (noPole_small (by norm_num) le_rfl hz.le) n).1]; ring
  · obtain ⟨C, hC⟩ := gauss_err_bound isGaussWeight_one01 continuous_const zero_le_one
      (by norm_num) le_rfl (fun _ _ => zero_le_one) (gP1_spec n)
    refine ⟨1 / 2, by norm_num, C, fun z hz => ?_⟩
    have h := hC z hz.le
    simp only [ofReal_one] at h
    rw [← logPsi_001] at h
    calc ‖gaussB (gP1 n) z * lgL1 z - z * gaussA 0 1 (fun _ => 1) (gP1 n) z‖
        = ‖z‖ * ‖gaussB (gP1 n) z * logPsi 0 1 0 0 1 z - gaussA 0 1 (fun _ => 1) (gP1 n) z‖ := by
          rw [lgL1, ← norm_mul]; congr 1; ring
      _ ≤ ‖z‖ * (C * ‖z‖ ^ (2 * n)) := by gcongr
      _ = C * ‖z‖ ^ (2 * n + 1) := by ring

/-- The odd convergents of 4.9.1 are `z − z² ×` the `n`-point Gauss rule for the weight `t` on
`(0, 1)`. -/
theorem lg1_odd_eq {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    cfA (lg1a z) (lg1b z) (2 * n + 1) * gaussB (gPt n) z =
      (z * gaussB (gPt n) z - z ^ 2 * gaussA 0 1 (fun x => x) (gPt n) z) *
        cfB (lg1a z) (lg1b z) (2 * n + 1) := by
  have hcard := gauss_card isGaussWeight_id01 (gPt_spec n)
  refine pade_unique (A := fun z => cfA (lg1a z) (lg1b z) (2 * n + 1))
    (B := fun z => cfB (lg1a z) (lg1b z) (2 * n + 1))
    (A' := fun z => z * gaussB (gPt n) z - z ^ 2 * gaussA 0 1 _ (gPt n) z)
    (B' := gaussB (gPt n)) (L := lgL1) (d := 2 * n + 1) (N := 2 * n + 2) ?_ (by omega)
    (lg1_deg (2 * n + 2)).2.continuous (isPolyFunDeg_gaussB _).continuous ?_ ?_ z
  · have hA := (lg1_deg (2 * n + 2)).1
    have hB := (lg1_deg (2 * n + 2)).2
    have hB' := isPolyFunDeg_gaussB (gPt n)
    have hA1 := IsPolyFunDeg.id.mul (isPolyFunDeg_gaussB (gPt n))
    have hA2 := (IsPolyFunDeg.id.mul IsPolyFunDeg.id).mul
      (isPolyFunDeg_gaussA 0 1 (fun x => x) (gPt n))
    rw [hcard] at hB' hA1 hA2
    have hA' : IsPolyFunDeg (fun z => z * gaussB (gPt n) z -
        z ^ 2 * gaussA 0 1 (fun x => x) (gPt n) z) (n + 1) :=
      ((hA1.mono (by omega : 1 + n ≤ n + 1)).sub
      (hA2.mono (by omega : 1 + 1 + (n - 1) ≤ n + 1))).congr fun z => by ring
    exact ((hA.mul hB').mono (by omega)).sub ((hA'.mul hB).mono (by omega))
  · obtain ⟨C, hC⟩ := logPsi_bound zero_le_one (by norm_num) le_rfl (n + 1) n (n + 1)
    refine bigO_of_formula (ψ := logPsi 0 1 (n + 1) n (n + 1))
      (κ := -((n ! : ℂ) * ((n + 1)! : ℂ))) ⟨C, hC⟩ fun z hz => ?_
    rw [← (lg1_err (noPole_small (by norm_num) le_rfl hz.le) n).2]; ring
  · obtain ⟨C, hC⟩ := gauss_err_bound isGaussWeight_id01 continuous_id zero_le_one
      (by norm_num) le_rfl (fun _ hx => hx.1) (gPt_spec n)
    refine ⟨1 / 2, by norm_num, C, fun z hz => ?_⟩
    have h := hC z hz.le
    rw [← logPsi01_101] at h
    have hm := logPsi01_mul (noPole_small (by norm_num) le_rfl hz.le) 0 0 0
    have h0 := logPsi_zero_zero_zero (0 : ℝ) 1 z
    simp at hm h0
    have hL : gaussB (gPt n) z * lgL1 z -
        (z * gaussB (gPt n) z - z ^ 2 * gaussA 0 1 (fun x => x) (gPt n) z) =
        -(z ^ 2) * (gaussB (gPt n) z * logPsi 0 1 1 0 1 z - gaussA 0 1 (fun x => x) (gPt n) z) := by
      rw [lgL1]; linear_combination -(gaussB (gPt n) z * z) * hm + (gaussB (gPt n) z * z) * h0
    rw [hL, norm_mul, norm_neg, norm_pow]
    calc ‖z‖ ^ 2 * ‖gaussB (gPt n) z * logPsi 0 1 1 0 1 z - gaussA 0 1 (fun x => x) (gPt n) z‖
        ≤ ‖z‖ ^ 2 * (C * ‖z‖ ^ (2 * n)) := by gcongr
      _ = C * ‖z‖ ^ (2 * n + 2) := by ring

/-- The convergents of 4.9.2 are `z ×` the `r`-point Gauss–Legendre rule on `(−1, 1)`. -/
theorem lg2_eq {r : ℕ} (hr : 1 ≤ r) (z : ℂ) :
    cfA (lg2a z) (lg2b z) r * gaussB (gP2 r) z =
      (z * gaussA (-1) 1 (fun _ => 1) (gP2 r) z) * cfB (lg2a z) (lg2b z) r := by
  have hcard := gauss_card isGaussWeight_legendre (gP2_spec r)
  refine pade_unique (A := fun z => cfA (lg2a z) (lg2b z) r)
    (B := fun z => cfB (lg2a z) (lg2b z) r) (A' := fun z => z * gaussA (-1) 1 _ (gP2 r) z)
    (B' := gaussB (gP2 r)) (L := lgL2) (d := 2 * r) (N := 2 * r + 1) ?_ (by omega)
    (lg2_deg (r + 1)).2.continuous (isPolyFunDeg_gaussB _).continuous ?_ ?_ z
  · have hA := (lg2_deg (r + 1)).1
    have hB := (lg2_deg (r + 1)).2
    have hB' := isPolyFunDeg_gaussB (gP2 r)
    have hA' := IsPolyFunDeg.id.mul (isPolyFunDeg_gaussA (-1) 1 (fun _ => 1) (gP2 r))
    rw [hcard] at hB' hA'
    exact ((hA.mul hB').mono (by omega)).sub ((hA'.mul hB).mono (by omega))
  · obtain ⟨C, hC⟩ := logPsi_bound (by norm_num : (-1 : ℝ) ≤ 1) le_rfl le_rfl r r (r + 1)
    refine bigO_of_formula (ψ := logPsi (-1) 1 r r (r + 1)) (κ := (r ! : ℂ) / 2 ^ r) ⟨C, hC⟩
      fun z hz => ?_
    rw [← (lg2_err (noPole_small le_rfl le_rfl hz.le) r).1]; ring
  · obtain ⟨C, hC⟩ := gauss_err_bound isGaussWeight_legendre continuous_const
      (by norm_num : (-1 : ℝ) ≤ 1) le_rfl le_rfl (fun _ _ => zero_le_one) (gP2_spec r)
    refine ⟨1 / 2, by norm_num, C, fun z hz => ?_⟩
    have h := hC z hz.le
    simp only [ofReal_one] at h
    rw [← logPsi_001] at h
    calc ‖gaussB (gP2 r) z * lgL2 z - z * gaussA (-1) 1 (fun _ => 1) (gP2 r) z‖
        = ‖z‖ * ‖gaussB (gP2 r) z * logPsi (-1) 1 0 0 1 z -
            gaussA (-1) 1 (fun _ => 1) (gP2 r) z‖ := by
          rw [lgL2, ← norm_mul]; congr 1; ring
      _ ≤ ‖z‖ * (C * ‖z‖ ^ (2 * r)) := by gcongr
      _ = C * ‖z‖ ^ (2 * r + 1) := by ring

/-! ### Nonvanishing denominators and the limits -/

theorem cfQ_of_a_zero {a' b' : ℕ → ℂ} (ha : ∀ k ≥ 1, a' k = 0) (r : ℕ) :
    cfQ a' b' (r + 1) = ∏ k ∈ Finset.Icc 1 r, b' k := by
  induction r with
  | zero => simp [cfQ]
  | succ r ih =>
    show b' (r + 1) * cfQ a' b' (r + 1) + a' (r + 1) * cfQ a' b' r = _
    rw [ih, ha (r + 1) (by omega), prod_Icc_succ_top (by omega)]; ring

/-- If `Aᵣ = Bᵣ = 0` then some `a_k` (`1 ≤ k ≤ r`) vanishes (determinant formula 1.12.7). -/
theorem exists_a_zero_of_cf_zero {a' b' : ℕ → ℂ} {r : ℕ} (hA : cfA a' b' r = 0)
    (hB : cfB a' b' r = 0) : ∃ k ∈ Finset.Icc 1 r, a' k = 0 := by
  have h := dlmf_1_12_7 a' b' r
  rw [hA, hB] at h
  simp only [zero_mul, sub_zero] at h
  have : ∏ k ∈ Finset.Icc 1 r, a' k = 0 := by
    rcases mul_eq_zero.mp h.symm with h1 | h1
    · exact absurd h1 (pow_ne_zero _ (by norm_num))
    · exact h1
  exact prod_eq_zero_iff.mp this

/-- Turning `A B' = A' B` into equality of quotients. -/
theorem div_eq_of_cross {A B A' B' : ℂ} (h : A * B' = A' * B) (hB' : B' ≠ 0)
    (hdet : A = 0 → B = 0 → False) : B ≠ 0 ∧ A / B = A' / B' := by
  have hB : B ≠ 0 := fun hB0 => hdet (by
    rw [hB0, mul_zero] at h; exact (mul_eq_zero.mp h).resolve_right hB') hB0
  exact ⟨hB, by rw [div_eq_div_iff hB hB', h]⟩

theorem lg1_det (z : ℂ) (r : ℕ) :
    cfA (lg1a z) (lg1b z) r = 0 → cfB (lg1a z) (lg1b z) r = 0 → False := by
  intro hA hB
  by_cases hz0 : z = 0
  · subst hz0
    rw [cfB, cfQ_of_a_zero (fun k _ => by simp [lg1a])] at hB
    obtain ⟨k, hk, hk0⟩ := prod_eq_zero_iff.mp hB
    simp only [lg1b, Nat.cast_eq_zero] at hk0
    exact absurd hk0 (by have := (Finset.mem_Icc.mp hk).1; omega)
  · obtain ⟨k, hk, hk0⟩ := exists_a_zero_of_cf_zero hA hB
    have hk1 := (Finset.mem_Icc.mp hk).1
    by_cases h1 : k = 1
    · simp [lg1a, h1, hz0] at hk0
    · simp only [lg1a, h1, ↓reduceIte, mul_eq_zero, hz0, or_false, Nat.cast_eq_zero,
        pow_eq_zero_iff (two_ne_zero)] at hk0
      omega

theorem lg2_det (z : ℂ) (r : ℕ) :
    cfA (lg2a z) (lg2b z) r = 0 → cfB (lg2a z) (lg2b z) r = 0 → False := by
  intro hA hB
  by_cases hz0 : z = 0
  · subst hz0
    rw [cfB, cfQ_of_a_zero (fun k _ => by simp [lg2a])] at hB
    obtain ⟨k, hk, hk0⟩ := prod_eq_zero_iff.mp hB
    have hk1 := (Finset.mem_Icc.mp hk).1
    simp only [lg2b, show k ≠ 0 by omega, ↓reduceIte] at hk0
    have : ((2 * k - 1 : ℕ) : ℂ) = 0 := by push_cast [show 1 ≤ 2 * k by omega]; exact hk0
    exact absurd (Nat.cast_eq_zero.mp this) (by omega)
  · obtain ⟨k, hk, hk0⟩ := exists_a_zero_of_cf_zero hA hB
    have hk1 := (Finset.mem_Icc.mp hk).1
    by_cases h1 : k = 1
    · simp [lg2a, h1, hz0] at hk0
    · simp only [lg2a, h1, ↓reduceIte, neg_eq_zero, mul_eq_zero, Nat.cast_eq_zero,
        pow_eq_zero_iff two_ne_zero, hz0, or_false] at hk0
      omega

theorem gauss_ne_zero_of_noPole {a b : ℝ} {w : ℝ → ℝ} (hw : IsGaussWeight (Ioo a b) w)
    {n : ℕ} {p : ℝ[X]} (hp : IsOrthMonic (Ioo a b) w n p)
    (hz : ∀ t ∈ Icc a b, 1 + z * t ≠ 0) : ∀ k ∈ p.roots.toFinset, 1 + z * k ≠ 0 :=
  fun k hk => hz k (Ioo_subset_Icc_self (gauss_nodes_mem hw hp hk))

theorem continuousOn_inv_one_add (hz : ∀ t ∈ Icc a b, 1 + z * t ≠ 0) :
    ContinuousOn (fun t : ℝ => 1 / (1 + z * t)) (Icc a b) :=
  continuousOn_const.div
    (continuous_const.add (continuous_const.mul continuous_ofReal)).continuousOn hz

/-- The convergents of 4.9.1 tend to `z ∫₀¹ dt/(1 + z t)` when `1 + z t ≠ 0` on `[0, 1]`. -/
theorem lg1_tendsto (hz : ∀ t ∈ Icc (0 : ℝ) 1, 1 + z * t ≠ 0) :
    (∀ᶠ r in atTop, cfB (lg1a z) (lg1b z) r ≠ 0) ∧
      Tendsto (fun r => cfA (lg1a z) (lg1b z) r / cfB (lg1a z) (lg1b z) r) atTop
        (𝓝 (lgL1 z)) := by
  have hev : ∀ n, 1 ≤ n → cfB (lg1a z) (lg1b z) (2 * n) ≠ 0 ∧
      cfA (lg1a z) (lg1b z) (2 * n) / cfB (lg1a z) (lg1b z) (2 * n) =
        z * gaussQuad 0 1 (fun _ => 1) (gP1 n) (fun t => 1 / (1 + z * t)) := fun n hn => by
    have hne := gauss_ne_zero_of_noPole isGaussWeight_one01 (gP1_spec n) hz
    obtain ⟨hB, hq⟩ := div_eq_of_cross (lg1_even_eq hn z) (gaussB_ne_zero hne) (lg1_det z _)
    refine ⟨hB, ?_⟩
    rw [hq, gaussA_eq hne]; field_simp [gaussB_ne_zero hne]
  have hod : ∀ n, 1 ≤ n → cfB (lg1a z) (lg1b z) (2 * n + 1) ≠ 0 ∧
      cfA (lg1a z) (lg1b z) (2 * n + 1) / cfB (lg1a z) (lg1b z) (2 * n + 1) =
        z - z ^ 2 * gaussQuad 0 1 (fun x => x) (gPt n) (fun t => 1 / (1 + z * t)) :=
      fun n hn => by
    have hne := gauss_ne_zero_of_noPole isGaussWeight_id01 (gPt_spec n) hz
    obtain ⟨hB, hq⟩ := div_eq_of_cross (lg1_odd_eq hn z) (gaussB_ne_zero hne) (lg1_det z _)
    refine ⟨hB, ?_⟩
    rw [hq, gaussA_eq hne]; field_simp [gaussB_ne_zero hne]
  have hg := continuousOn_inv_one_add hz
  have hT1 := gauss_tendsto isGaussWeight_one01 continuous_const zero_le_one
    (fun _ _ => zero_le_one) gP1_spec hg
  have hT2 := gauss_tendsto isGaussWeight_id01 continuous_id zero_le_one
    (fun _ hx => hx.1) gPt_spec hg
  have hI1 : (∫ x in (0 : ℝ)..1, (((fun _ => (1 : ℝ)) x : ℝ) : ℂ) * (1 / (1 + z * x))) =
      logPsi 0 1 0 0 1 z := by simp [logPsi]
  have hI2 : (∫ x in (0 : ℝ)..1, (((fun x => x) x : ℝ) : ℂ) * (1 / (1 + z * x))) =
      logPsi 0 1 1 0 1 z := by simp [logPsi, div_eq_mul_inv]
  rw [hI1] at hT1
  rw [hI2] at hT2
  have hm := logPsi01_mul hz 0 0 0
  have h0 := logPsi_zero_zero_zero (0 : ℝ) 1 z
  simp at hm h0
  have hL : z - z ^ 2 * logPsi 0 1 1 0 1 z = lgL1 z := by
    rw [lgL1]; linear_combination z * hm - z * h0
  refine ⟨eventually_atTop.2 ⟨2, fun r hr => ?_⟩, tendsto_of_even_odd ?_ ?_⟩
  · rcases Nat.even_or_odd' r with ⟨n, rfl | rfl⟩
    · exact (hev n (by omega)).1
    · exact (hod n (by omega)).1
  · refine Tendsto.congr' (eventually_atTop.2 ⟨1, fun n hn => (hev n hn).2.symm⟩) ?_
    rw [lgL1]; exact hT1.const_mul z
  · refine Tendsto.congr' (eventually_atTop.2 ⟨1, fun n hn => (hod n hn).2.symm⟩) ?_
    rw [← hL]; exact tendsto_const_nhds.sub (hT2.const_mul _)

/-- The convergents of 4.9.2 tend to `z ∫₋₁¹ dt/(1 + z t)` when `1 + z t ≠ 0` on `[−1, 1]`. -/
theorem lg2_tendsto (hz : ∀ t ∈ Icc (-1 : ℝ) 1, 1 + z * t ≠ 0) :
    (∀ᶠ r in atTop, cfB (lg2a z) (lg2b z) r ≠ 0) ∧
      Tendsto (fun r => cfA (lg2a z) (lg2b z) r / cfB (lg2a z) (lg2b z) r) atTop
        (𝓝 (lgL2 z)) := by
  have hev : ∀ r, 1 ≤ r → cfB (lg2a z) (lg2b z) r ≠ 0 ∧
      cfA (lg2a z) (lg2b z) r / cfB (lg2a z) (lg2b z) r =
        z * gaussQuad (-1) 1 (fun _ => 1) (gP2 r) (fun t => 1 / (1 + z * t)) := fun r hr => by
    have hne := gauss_ne_zero_of_noPole isGaussWeight_legendre (gP2_spec r) hz
    obtain ⟨hB, hq⟩ := div_eq_of_cross (lg2_eq hr z) (gaussB_ne_zero hne) (lg2_det z _)
    refine ⟨hB, ?_⟩
    rw [hq, gaussA_eq hne]; field_simp [gaussB_ne_zero hne]
  have hT := gauss_tendsto isGaussWeight_legendre continuous_const (by norm_num)
    (fun _ _ => zero_le_one) gP2_spec (continuousOn_inv_one_add hz)
  have hI : (∫ x in (-1 : ℝ)..1, (((fun _ => (1 : ℝ)) x : ℝ) : ℂ) * (1 / (1 + z * x))) =
      logPsi (-1) 1 0 0 1 z := by simp [logPsi]
  rw [hI] at hT
  refine ⟨eventually_atTop.2 ⟨1, fun r hr => (hev r hr).1⟩, ?_⟩
  refine Tendsto.congr' (eventually_atTop.2 ⟨1, fun r hr => (hev r hr).2.symm⟩) ?_
  rw [lgL2]; exact hT.const_mul z

/-! ### The values: `ln(1 + z)` and `ln((1 + z)/(1 − z))` -/

/-- `∫ₐᵇ z/(1 + z t) dt = log F(b) − log F(a)` for `F(t) = c (1 + z t)` in the slit plane. -/
theorem integral_div_one_add_mul {a b : ℝ} (hab : a ≤ b) {c : ℂ} (hc : c ≠ 0)
    (hs : ∀ t ∈ Icc a b, c * (1 + z * t) ∈ slitPlane) :
    (∫ t in a..b, z / (1 + z * t)) = log (c * (1 + z * b)) - log (c * (1 + z * a)) := by
  have hne : ∀ t ∈ Icc a b, 1 + z * t ≠ 0 := fun t ht =>
    right_ne_zero_of_mul (slitPlane_ne_zero (hs t ht))
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => log (c * (1 + z * (t : ℂ)))) (fun t ht => ?_) ?_
  · rw [uIcc_of_le hab] at ht
    have h1 : HasDerivAt (fun t : ℝ => c * (1 + z * (t : ℂ))) (c * z) t := by
      simpa using (((hasDerivAt_id (t : ℂ)).const_mul z).const_add 1 |>.const_mul c).comp_ofReal
    convert h1.clog_real (hs t ht) using 1
    field_simp [hne t ht]
  · exact ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le hab]
      exact continuousOn_const.div (continuous_const.add
        (continuous_const.mul continuous_ofReal)).continuousOn hne)

/-- `z ∫₀¹ dt/(1 + z t) = ln(1 + z)` for `1 + z` in the cut plane. -/
theorem lgL1_eq_log (hz : 1 + z ∈ slitPlane) : lgL1 z = log (1 + z) := by
  have hs : ∀ t ∈ Icc (0 : ℝ) 1, 1 * (1 + z * t) ∈ slitPlane := fun t ht => by
    have := StarConvex.add_smul_mem starConvex_one_slitPlane (y := z) hz ht.1 ht.2
    rw [one_mul]; rw [real_smul, mul_comm] at this; exact this
  rw [lgL1, logPsi_001, ← intervalIntegral.integral_const_mul]
  simp_rw [mul_one_div]
  rw [integral_div_one_add_mul zero_le_one one_ne_zero hs]
  simp

/-- `(1 + z)/(1 − z)` lies in the cut plane for `z ∉ (−∞, −1] ∪ [1, ∞)`. -/
theorem one_add_div_one_sub_mem_slitPlane (hz : ∀ x : ℝ, x ≤ -1 ∨ 1 ≤ x → z ≠ x) :
    (1 + z) / (1 - z) ∈ slitPlane := by
  have h1 : 1 - z ≠ 0 := fun h => hz 1 (Or.inr le_rfl) (by push_cast; linear_combination -h)
  rw [mem_slitPlane_iff_not_le_zero, nonpos_iff]
  rintro ⟨hre, him⟩
  set r := ((1 + z) / (1 - z)).re
  have hw : (1 + z) / (1 - z) = r := Complex.ext (by simp [r]) (by simp [him])
  rw [div_eq_iff h1] at hw
  have hr1 : r ≠ -1 := fun h => by
    rw [h] at hw; push_cast at hw
    have := congrArg re hw; simp at this; linarith
  have hr1' : (r : ℂ) + 1 ≠ 0 := fun h => hr1 (by
    have := congrArg re h; simp at this; linarith)
  have hzr : z = ((r - 1) / (r + 1) : ℝ) := by
    push_cast
    rw [eq_div_iff hr1']
    linear_combination hw
  refine hz _ ?_ hzr
  rcases lt_or_gt_of_ne hr1 with h | h
  · right; rw [le_div_iff_of_neg (by linarith)]; linarith
  · left; rw [div_le_iff₀ (by linarith)]; linarith

/-- `z ∫₋₁¹ dt/(1 + z t) = ln((1 + z)/(1 − z))` for `z ∉ (−∞, −1] ∪ [1, ∞)`. -/
theorem lgL2_eq_log (hz : ∀ x : ℝ, x ≤ -1 ∨ 1 ≤ x → z ≠ x) :
    lgL2 z = log ((1 + z) / (1 - z)) := by
  have h1 : 1 - z ≠ 0 := fun h => hz 1 (Or.inr le_rfl) (by push_cast; linear_combination -h)
  have hw := one_add_div_one_sub_mem_slitPlane hz
  have hs : ∀ t ∈ Icc (-1 : ℝ) 1, (1 - z)⁻¹ * (1 + z * t) ∈ slitPlane := fun t ht => by
    have := StarConvex.add_smul_mem starConvex_one_slitPlane (y := 2 * z / (1 - z))
      (by rwa [show (1 : ℂ) + 2 * z / (1 - z) = (1 + z) / (1 - z) by field_simp; ring])
      (t := (1 + t) / 2) (by linarith [ht.1]) (by linarith [ht.2])
    convert this using 1
    rw [real_smul]; push_cast; field_simp; ring
  rw [lgL2, logPsi_001, ← intervalIntegral.integral_const_mul]
  simp_rw [mul_one_div]
  rw [integral_div_one_add_mul (by norm_num) (inv_ne_zero h1) hs]
  have : (1 - z)⁻¹ * (1 + z * ((-1 : ℝ) : ℂ)) = 1 := by push_cast; field_simp; ring
  rw [this, log_one, sub_zero]
  congr 1; push_cast; field_simp

/-- **DLMF 4.9.1**: `ln(1 + z) = z/(1 + z/(2 + z/(3 + 4z/(4 + 4z/(5 + 9z/(6 + 9z/(7 + ⋯)))))))`
for `|ph(1 + z)| < π`: the denominators are eventually nonzero and the convergents tend to
`ln(1 + z)`. The even convergents are Gauss–Legendre quadratures of `z ∫₀¹ dt/(1 + z t)`
(`lg1_even_eq`). -/
theorem dlmf_4_9_1 (z : ℂ) (hz0 : 1 + z ≠ 0) (hph : |arg (1 + z)| < π) :
    (∀ᶠ r in atTop, cfB (lg1a z) (lg1b z) r ≠ 0) ∧
      Tendsto (fun r => cfA (lg1a z) (lg1b z) r / cfB (lg1a z) (lg1b z) r) atTop
        (𝓝 (log (1 + z))) := by
  have hs : 1 + z ∈ slitPlane := mem_slitPlane_iff_arg.mpr ⟨fun h => by
    rw [h, abs_of_pos Real.pi_pos] at hph; exact lt_irrefl _ hph, hz0⟩
  have hz : ∀ t ∈ Icc (0 : ℝ) 1, 1 + z * t ≠ 0 := fun t ht => by
    have := StarConvex.add_smul_mem starConvex_one_slitPlane (y := z) hs ht.1 ht.2
    rw [real_smul, mul_comm] at this; exact slitPlane_ne_zero this
  rw [← lgL1_eq_log hs]
  exact lg1_tendsto hz

/-- **DLMF 4.9.2**: `ln((1 + z)/(1 − z)) = 2z/(1 − z²/(3 − 4z²/(5 − 9z²/(7 − 16z²/(9 − ⋯)))))`
for `z ∈ ℂ ∖ ((−∞, −1] ∪ [1, ∞))`. The convergents are the Gauss–Legendre quadratures of
`z ∫₋₁¹ dt/(1 + z t)` (`lg2_eq`). -/
theorem dlmf_4_9_2 (z : ℂ) (hz : ∀ x : ℝ, x ≤ -1 ∨ 1 ≤ x → z ≠ x) :
    (∀ᶠ r in atTop, cfB (lg2a z) (lg2b z) r ≠ 0) ∧
      Tendsto (fun r => cfA (lg2a z) (lg2b z) r / cfB (lg2a z) (lg2b z) r) atTop
        (𝓝 (log ((1 + z) / (1 - z)))) := by
  have h1 : 1 - z ≠ 0 := fun h => hz 1 (Or.inr le_rfl) (by push_cast; linear_combination -h)
  have hw := one_add_div_one_sub_mem_slitPlane hz
  have hnp : ∀ t ∈ Icc (-1 : ℝ) 1, 1 + z * t ≠ 0 := fun t ht h => by
    have := StarConvex.add_smul_mem starConvex_one_slitPlane (y := 2 * z / (1 - z))
      (by rwa [show (1 : ℂ) + 2 * z / (1 - z) = (1 + z) / (1 - z) by field_simp; ring])
      (t := (1 + t) / 2) (by linarith [ht.1]) (by linarith [ht.2])
    refine slitPlane_ne_zero this ?_
    rw [real_smul]; push_cast
    rw [show (1 : ℂ) + (1 + t) / 2 * (2 * z / (1 - z)) = (1 + z * t) / (1 - z) by
      field_simp; ring, h, zero_div]
  rw [← lgL2_eq_log hz]
  exact lg2_tendsto hnp

end Azurite.DLMF
