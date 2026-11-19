/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.GammaThird
import Azurite.Chudnovsky.PeriodI
import Mathlib.Analysis.Real.Pi.Irrational

/-!
# Irrationality of the Gamma function at rationals with denominator 2, 3, 4, 6

* `cmI`: the CM data of `ℤ[i]`; `not_algOver_gamma_one_quarter`: `Γ(1/4)` is not algebraic over
  `ℤ[π]` (Chudnovsky's theorem for `ℤ[i]` and `8π ℘(1/2) = Γ(1/4)⁴`).
* By the reflection and duplication formulas: `Γ(3/4)` is not algebraic over `ℤ[π]`, and
  `Γ(2/3)`, `Γ(1/6)`, `Γ(5/6)` are not algebraic over `ℤ[2π/√3]`.
* **`irrational_gamma_of_den`**: `Γ(q)` is irrational for every rational `q` with denominator
  `2`, `3`, `4` or `6` (`Γ(x + 1) = x Γ(x)`).
-/

namespace Azurite.Chudnovsky

open Polynomial UpperHalfPlane

/-! ### The lattice `ℤ[i]` -/

/-- The CM data of the lattice `ℤ[i]`. -/
noncomputable def cmI : CMData where
  τ := UpperHalfPlane.I
  p := 0
  q := 1
  u := 0
  v := -1
  c := 2
  hn := by simp
  hr := by simp
  hsq := by simp
  hp := by norm_num
  hq := by norm_num
  hη := by
    have h := quasiPeriod_latI_I
    rw [coe_I, h, quasiPeriod_latI_one]
    push_cast
    ring
  hu := by norm_num
  hv := by norm_num
  hg := by
    have := g₂_latI
    rw [this]
    push_cast
    ring
  hc := by norm_num
  hα := by
    rw [coe_I]
    intro h
    have : (2 : ℂ) * Complex.I = 0 := by linear_combination -h
    simp at this

/-- **`Γ(1/4)` is not algebraic over `ℤ[π]`.** -/
theorem not_algOver_gamma_one_quarter :
    ¬ AlgOver (Real.pi : ℂ) ((Real.Gamma (1 / 4) : ℝ) : ℂ) := by
  intro hG
  have hϖ : cmI.ϖ = (Real.pi : ℂ) := quasiPeriod_latI_one
  have he : cmI.e = (iE : ℂ) := halfValue_latI
  have hnot : ¬ AlgOver (Real.pi : ℂ) (iE : ℂ) := by
    have := cmI.not_algOver (c₀ := 2 ^ 49) (by rw [hϖ]; exact hasMeasure_pi)
    rwa [hϖ, he] at this
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h4 := hG.pow 4
  have hC : ((8 : ℕ) : ℂ) * (Real.pi : ℂ) * (iE : ℂ) = ((Real.Gamma (1 / 4) : ℝ) : ℂ) ^ 4 := by
    exact_mod_cast iE_eq
  rw [← hC] at h4
  exact hnot (AlgOver.of_mul (mul_ne_zero (by norm_num) hπ)
    ((algOver_natCast _ 8).mul (algOver_self _)) h4)

/-! ### Algebraic real numbers -/

theorem algOver_ofReal_of_pow {ϖ : ℂ} {t : ℝ} {n : ℕ} (hn : 0 < n) {r : ℚ} (h : t ^ n = r) :
    AlgOver ϖ (t : ℂ) := by
  refine AlgOver.of_pow hn ?_
  have : (t : ℂ) ^ n = (r : ℂ) := by exact_mod_cast h
  rw [this]
  exact algOver_ratCast ϖ r

theorem algOver_sqrt_two (ϖ : ℂ) : AlgOver ϖ ((√2 : ℝ) : ℂ) :=
  algOver_ofReal_of_pow (n := 2) (r := 2) (by norm_num) (by
    rw [Real.sq_sqrt (by norm_num)]
    norm_num)

theorem algOver_sqrt_three (ϖ : ℂ) : AlgOver ϖ ((√3 : ℝ) : ℂ) :=
  algOver_ofReal_of_pow (n := 2) (r := 3) (by norm_num) (by
    rw [Real.sq_sqrt (by norm_num)]
    norm_num)

/-! ### The other values -/

/-- `Γ(3/4)` is not algebraic over `ℤ[π]`. -/
theorem not_algOver_gamma_three_quarters :
    ¬ AlgOver (Real.pi : ℂ) ((Real.Gamma (3 / 4) : ℝ) : ℂ) := by
  intro h
  apply not_algOver_gamma_one_quarter
  have hR := Real.Gamma_mul_Gamma_one_sub (1 / 4)
  rw [show Real.pi * (1 / 4 : ℝ) = Real.pi / 4 by ring, Real.sin_pi_div_four,
    show (1 - 1 / 4 : ℝ) = 3 / 4 by norm_num] at hR
  have hy : 0 < Real.Gamma (3 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hs2 : (0 : ℝ) < √2 := by positivity
  have hx : Real.Gamma (1 / 4) = Real.pi * 2 / √2 / Real.Gamma (3 / 4) := by
    field_simp
    field_simp at hR
    linarith
  rw [hx]
  push_cast
  refine AlgOver.div (by exact_mod_cast hy.ne') (AlgOver.div (by exact_mod_cast hs2.ne')
    ((algOver_self _).mul ?_) (algOver_sqrt_two _)) h
  exact_mod_cast algOver_natCast (Real.pi : ℂ) 2

/-- `Γ(2/3)` is not algebraic over `ℤ[2π/√3]`. -/
theorem not_algOver_gamma_two_thirds :
    ¬ AlgOver varpiRho ((Real.Gamma (2 / 3) : ℝ) : ℂ) := by
  intro h
  apply not_algOver_gamma_one_third
  have hR := Real.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show Real.pi * (1 / 3 : ℝ) = Real.pi / 3 by ring, Real.sin_pi_div_three,
    show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num] at hR
  have hy : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hs3 : (0 : ℝ) < √3 := by positivity
  have hx : Real.Gamma (1 / 3) = 2 * Real.pi / √3 / Real.Gamma (2 / 3) := by
    field_simp
    field_simp at hR
    linarith
  rw [hx]
  push_cast
  exact AlgOver.div (by exact_mod_cast hy.ne') (algOver_self _) h

/-- `√π` is algebraic over `ℤ[2π/√3]`. -/
theorem algOver_sqrt_pi : AlgOver varpiRho ((√Real.pi : ℝ) : ℂ) := by
  refine AlgOver.of_pow (n := 2) (by norm_num) ?_
  have : ((√Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  rw [this]
  exact algOver_pi

/-- `Γ(1/6)` is not algebraic over `ℤ[2π/√3]`. -/
theorem not_algOver_gamma_one_sixth :
    ¬ AlgOver varpiRho ((Real.Gamma (1 / 6) : ℝ) : ℂ) := by
  intro h
  apply not_algOver_gamma_one_third
  have hD := Real.Gamma_mul_Gamma_add_half (1 / 6)
  rw [show (1 / 6 + 1 / 2 : ℝ) = 2 / 3 by norm_num,
    show (2 * (1 / 6) : ℝ) = 1 / 3 by norm_num,
    show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num] at hD
  -- `w = 2^(2/3)`
  set w : ℝ := (2 : ℝ) ^ (2 / 3 : ℝ) with hw
  have hw0 : 0 < w := by positivity
  have hw3 : w ^ 3 = ((4 : ℚ) : ℝ) := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hwA : AlgOver varpiRho (w : ℂ) := algOver_ofReal_of_pow (by norm_num) hw3
  have hx : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hy : 0 < Real.Gamma (1 / 6) := Real.Gamma_pos_of_pos (by norm_num)
  have hz : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hsπ : 0 < √Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  -- `Γ(2/3) = Γ(1/6)⁻¹ Γ(1/3) w √π` is algebraic iff `Γ(1/3)` is
  have hz' : AlgOver varpiRho ((Real.Gamma (2 / 3) : ℝ) : ℂ) → False :=
    not_algOver_gamma_two_thirds
  -- instead: `Γ(1/3) = Γ(1/6) Γ(2/3)/(w √π)` and `Γ(2/3) = ϖ/Γ(1/3)`
  have hR := Real.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show Real.pi * (1 / 3 : ℝ) = Real.pi / 3 by ring, Real.sin_pi_div_three,
    show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num] at hR
  have hs3 : (0 : ℝ) < √3 := by positivity
  have hsq : Real.Gamma (1 / 3) ^ 2
      = Real.Gamma (1 / 6) * (2 * Real.pi / √3) / (w * √Real.pi) := by
    field_simp
    field_simp at hR
    linear_combination (-(Real.Gamma (1 / 3) * √3)) * hD + Real.Gamma (1 / 6) * hR
  refine AlgOver.of_pow (n := 2) (by norm_num) ?_
  have hC : ((Real.Gamma (1 / 3) : ℝ) : ℂ) ^ 2
      = ((Real.Gamma (1 / 6) : ℝ) : ℂ) * varpiRho / ((w : ℂ) * ((√Real.pi : ℝ) : ℂ)) := by
    rw [varpiRho]
    exact_mod_cast hsq
  rw [hC]
  exact AlgOver.div (mul_ne_zero (by exact_mod_cast hw0.ne') (by exact_mod_cast hsπ.ne'))
    (h.mul (algOver_self _)) (hwA.mul algOver_sqrt_pi)

/-- `Γ(5/6)` is not algebraic over `ℤ[2π/√3]`. -/
theorem not_algOver_gamma_five_sixths :
    ¬ AlgOver varpiRho ((Real.Gamma (5 / 6) : ℝ) : ℂ) := by
  intro h
  apply not_algOver_gamma_one_sixth
  have hR := Real.Gamma_mul_Gamma_one_sub (1 / 6)
  rw [show Real.pi * (1 / 6 : ℝ) = Real.pi / 6 by ring, Real.sin_pi_div_six,
    show (1 - 1 / 6 : ℝ) = 5 / 6 by norm_num] at hR
  have hy : 0 < Real.Gamma (5 / 6) := Real.Gamma_pos_of_pos (by norm_num)
  have hx : Real.Gamma (1 / 6) = 2 * Real.pi / Real.Gamma (5 / 6) := by
    field_simp
    field_simp at hR
    linarith
  rw [hx]
  push_cast
  refine AlgOver.div (by exact_mod_cast hy.ne') (AlgOver.mul ?_ algOver_pi) h
  exact_mod_cast algOver_natCast varpiRho 2

/-! ### All rationals with denominator 2, 3, 4, 6 -/

theorem irrational_gamma_one_half : Irrational (Real.Gamma (1 / 2)) := by
  rw [Real.Gamma_one_half_eq]
  refine Irrational.of_pow 2 ?_
  rw [Real.sq_sqrt Real.pi_pos.le]
  exact irrational_pi

/-- `Γ(a/d)` is irrational for `d ∈ {2, 3, 4, 6}`, `0 < a < d` coprime to `d`. -/
theorem irrational_gamma_frac {a d : ℕ} (hd : d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 6) (ha0 : 0 < a)
    (had : a < d) (hc : Nat.Coprime a d) : Irrational (Real.Gamma ((a : ℝ) / d)) := by
  rcases hd with rfl | rfl | rfl | rfl
  · interval_cases a
    have := irrational_gamma_one_half
    simpa using this
  · interval_cases a
    · have := irrational_of_not_algOver not_algOver_gamma_one_third
      simpa using this
    · have := irrational_of_not_algOver not_algOver_gamma_two_thirds
      simpa using this
  · interval_cases a
    · have := irrational_of_not_algOver not_algOver_gamma_one_quarter
      simpa using this
    · exact absurd hc (by decide)
    · have := irrational_of_not_algOver not_algOver_gamma_three_quarters
      simpa using this
  · interval_cases a
    · have := irrational_of_not_algOver not_algOver_gamma_one_sixth
      simpa using this
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
    · have := irrational_of_not_algOver not_algOver_gamma_five_sixths
      simpa using this

/-- Shifting the argument by an integer preserves the irrationality of `Γ`. -/
theorem irrational_gamma_add_int {x : ℚ} (hx : ∀ m : ℤ, x ≠ m)
    (h : Irrational (Real.Gamma (x : ℝ))) (n : ℤ) :
    Irrational (Real.Gamma ((x + n : ℚ) : ℝ)) := by
  have hne : ∀ k : ℤ, ((x + k : ℚ) : ℝ) ≠ 0 := by
    intro k h0
    have h1 : (x + k : ℚ) = 0 := by exact_mod_cast h0
    apply hx (-k)
    push_cast
    linarith
  induction n using Int.induction_on with
  | zero => simpa using h
  | succ k ih =>
    have e : ((x + ((k : ℤ) + 1 : ℤ) : ℚ) : ℝ) = ((x + (k : ℤ) : ℚ) : ℝ) + 1 := by
      push_cast
      ring
    rw [e, Real.Gamma_add_one (hne k)]
    exact ih.ratCast_mul (by exact_mod_cast hne k)
  | pred k ih =>
    have e : ((x + (-(k : ℤ)) : ℚ) : ℝ) = ((x + (-(k : ℤ) - 1 : ℤ) : ℚ) : ℝ) + 1 := by
      push_cast
      ring
    have ih' : Irrational (Real.Gamma ((x + (-(k : ℤ)) : ℚ) : ℝ)) := by
      simpa using ih
    rw [e, Real.Gamma_add_one (hne _)] at ih'
    exact ih'.of_ratCast_mul

/-- **`Γ(q)` is irrational for every rational `q` with denominator `2`, `3`, `4` or `6`.** -/
theorem irrational_gamma_of_den (q : ℚ)
    (hden : q.den = 2 ∨ q.den = 3 ∨ q.den = 4 ∨ q.den = 6) : Irrational (Real.Gamma (q : ℝ)) := by
  set d := q.den with hd
  have hd0 : 0 < d := q.den_pos
  have hd2 : 2 ≤ d := by rcases hden with h | h | h | h <;> omega
  set a := q.num % (d : ℤ) with ha
  set n := q.num / (d : ℤ) with hn
  have ha0 : 0 ≤ a := Int.emod_nonneg _ (by exact_mod_cast hd0.ne')
  have had : a < d := Int.emod_lt_of_pos _ (by exact_mod_cast hd0)
  have hnum : q.num = (d : ℤ) * n + a := (Int.mul_ediv_add_emod q.num d).symm
  -- `a` is coprime to `d`
  have hcop : Nat.Coprime a.toNat d := by
    have h1 : Int.gcd a d = 1 := by
      have h2 : Int.gcd q.num d = 1 := by
        rw [Int.gcd, Int.natAbs_natCast]
        exact q.reduced
      have hco : IsCoprime q.num (d : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr h2
      have hco' : IsCoprime a (d : ℤ) := by
        have h3 := hco.add_mul_right_left (-n)
        have e : q.num + -n * (d : ℤ) = a := by rw [hnum]; ring
        rwa [e] at h3
      exact Int.isCoprime_iff_gcd_eq_one.mp hco'
    have h3 : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha0
    rw [Nat.Coprime, ← Int.gcd_natCast_natCast, h3]
    exact h1
  have hapos : 0 < a.toNat := by
    rcases Nat.eq_zero_or_pos a.toNat with h0 | h0
    · rw [h0, Nat.coprime_zero_left] at hcop
      omega
    · exact h0
  have hat : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha0
  have hbase := irrational_gamma_frac hden hapos (by omega) hcop
  -- `q = a/d + n`
  have hq : q = ((a.toNat : ℚ) / d) + n := by
    have h1 : q = (q.num : ℚ) / d := (Rat.num_div_den q).symm
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0.ne'
    have h2 : (a.toNat : ℚ) = a := by exact_mod_cast hat
    rw [h1, hnum, h2]
    push_cast
    field_simp
    ring
  have hnotint : ∀ m : ℤ, ((a.toNat : ℚ) / d) ≠ m := by
    intro m hm
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0.ne'
    have h1 : (a.toNat : ℚ) = m * d := by
      field_simp at hm
      linarith
    have h2 : (a.toNat : ℤ) = m * d := by exact_mod_cast h1
    have hm1 : 0 < m := by
      by_contra hcon
      have : m * (d : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hcon) (by positivity)
      omega
    have : (d : ℤ) ≤ m * d := le_mul_of_one_le_left (by positivity) hm1
    omega
  have hb' : Irrational (Real.Gamma (((a.toNat : ℚ) / d : ℚ) : ℝ)) := by
    have : (((a.toNat : ℚ) / d : ℚ) : ℝ) = (a.toNat : ℝ) / d := by push_cast; ring
    rw [this]
    exact hbase
  have := irrational_gamma_add_int hnotint hb' n
  rwa [← hq] at this

end Azurite.Chudnovsky
