/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.GammaValues
import Azurite.Feldman.Theorem4
import Mathlib.NumberTheory.Niven

/-!
# Irrational values of the Beta function

`B(a, b) = Γ(a) Γ(b) / Γ(a + b)` at rational arguments that are not integers is irrational in
two families.

* **`a + b` a positive integer** (`irrational_beta_of_add_eq_nat`): by the reflection formula
  `B(a, b)` is a nonzero rational multiple of `π / sin (π a)`, the sine of a rational multiple
  of `π` is algebraic (Niven), and `π` is transcendental.
* **Denominators dividing `4`, or dividing `6`, with `a + b` not an integer**
  (`irrational_beta_div_four`, `irrational_beta_div_six`).  Every such `Γ` value is a power
  `g^d` of `g = Γ(1/4)` (resp. `Γ(1/3)`) times a nonzero number algebraic over `ℤ[π]`
  (`GDeg`: `d = 1, 0, −1` at `1/4, 1/2, 3/4`; `d = 2, 1, 0, −1, −2` at `1/6, …, 5/6`), the
  degree is multiplicative, and the degree of `B(a, b)` is `±2` (resp. `±3`) whenever `a + b`
  is not an integer.  A number of nonzero degree is irrational, since `g` is not algebraic
  over `ℤ[π]` (Chudnovsky's theorem).

`irrational_beta_of_den` puts the two together.
-/

namespace Azurite.Chudnovsky

open Real

/-! ### Shifting the argument of `Γ` by an integer -/

/-- `Γ(x + n)` is a nonzero rational multiple of `Γ(x)` for a rational `x` that is not an
integer. -/
theorem gamma_add_int_eq {x : ℚ} (hx : ∀ m : ℤ, x ≠ m) (n : ℤ) :
    ∃ ρ : ℚ, ρ ≠ 0 ∧ Real.Gamma ((x + n : ℚ) : ℝ) = ρ * Real.Gamma (x : ℝ) := by
  have hne : ∀ k : ℤ, (x + k : ℚ) ≠ 0 := by
    intro k h0
    apply hx (-k)
    push_cast
    linarith
  induction n using Int.induction_on with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | succ k ih =>
    obtain ⟨ρ, hρ, h⟩ := ih
    refine ⟨(x + (k : ℤ)) * ρ, mul_ne_zero (hne k) hρ, ?_⟩
    have e : ((x + ((k : ℤ) + 1 : ℤ) : ℚ) : ℝ) = ((x + (k : ℤ) : ℚ) : ℝ) + 1 := by
      push_cast
      ring
    rw [e, Real.Gamma_add_one (by exact_mod_cast hne k), h]
    push_cast
    ring
  | pred k ih =>
    obtain ⟨ρ, hρ, h⟩ := ih
    have hk := hne (-(k : ℤ) - 1)
    refine ⟨ρ / (x + (-(k : ℤ) - 1 : ℤ)), div_ne_zero hρ hk, ?_⟩
    have e : ((x + (-(k : ℤ)) : ℚ) : ℝ) = ((x + (-(k : ℤ) - 1 : ℤ) : ℚ) : ℝ) + 1 := by
      push_cast
      ring
    have h' : Real.Gamma ((x + (-(k : ℤ)) : ℚ) : ℝ) = ρ * Real.Gamma (x : ℝ) := by
      simpa using h
    rw [e, Real.Gamma_add_one (by exact_mod_cast hk)] at h'
    have hk' : ((x + (-(k : ℤ) - 1 : ℤ) : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hk
    rw [Rat.cast_div, div_mul_eq_mul_div, ← h']
    field_simp

/-! ### `a + b` a positive integer -/

theorem isAlgebraic_ratCast_real (r : ℚ) : IsAlgebraic ℤ (r : ℝ) :=
  (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) r)

/-- `Γ(a) Γ(b)` is irrational for a rational `a` that is not an integer and `a + b` an
integer: a nonzero rational multiple of `π / sin (π a)`. -/
theorem irrational_gamma_mul_gamma_of_add_int {a b : ℚ} (ha : ∀ k : ℤ, a ≠ k) {m : ℤ}
    (hab : a + b = m) : Irrational (Real.Gamma (a : ℝ) * Real.Gamma (b : ℝ)) := by
  have h1a : ∀ k : ℤ, (1 - a : ℚ) ≠ k := fun k hk => ha (1 - k) (by push_cast; linarith)
  obtain ⟨ρ, hρ, hΓ⟩ := gamma_add_int_eq h1a (m - 1)
  have hb : ((1 - a + (m - 1 : ℤ) : ℚ)) = b := by push_cast; linarith
  rw [hb] at hΓ
  have hR := Real.Gamma_mul_Gamma_one_sub (a : ℝ)
  have hsin : Real.sin (π * a) ≠ 0 := by
    intro h0
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h0
    have : (a : ℝ) = n := by
      have hπ := Real.pi_pos
      have : (n : ℝ) * π = a * π := by linarith
      exact (mul_right_cancel₀ hπ.ne' this).symm
    exact ha n (by exact_mod_cast this)
  rintro ⟨r, hr⟩
  have hprod : Real.Gamma (a : ℝ) * Real.Gamma (b : ℝ) = ρ * (π / Real.sin (π * a)) := by
    rw [hΓ, ← hR]
    push_cast
    ring
  have hπ : π = (r : ℝ) / ρ * Real.sin ((a : ℝ) * π) := by
    have hρ' : (ρ : ℝ) ≠ 0 := by exact_mod_cast hρ
    rw [mul_comm (a : ℝ) π, hr, hprod]
    field_simp
  apply Azurite.Feldman.transcendental_pi_real
  rw [hπ]
  have halg : IsAlgebraic ℤ (((r / ρ : ℚ) : ℝ)) := isAlgebraic_ratCast_real _
  have hs := Real.isAlgebraic_sin_rat_mul_pi a
  have := halg.mul hs
  convert this using 2
  push_cast
  rfl

/-- **`B(a, b)` is irrational when `a` is not an integer and `a + b` is a positive
integer.** -/
theorem irrational_beta_of_add_eq_nat {a b : ℚ} (ha : ∀ k : ℤ, a ≠ k) {m : ℕ} (hm : 1 ≤ m)
    (hab : a + b = m) :
    Irrational (Real.Gamma (a : ℝ) * Real.Gamma (b : ℝ) / Real.Gamma ((a : ℝ) + b)) := by
  have h := irrational_gamma_mul_gamma_of_add_int ha (m := (m : ℤ)) (by exact_mod_cast hab)
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hs : (a : ℝ) + b = (k : ℝ) + 1 := by exact_mod_cast hab
  rw [hs, Real.Gamma_nat_eq_factorial]
  have hf : ((k.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have := h.div_ratCast hf
  simpa using this

/-! ### Degrees in `Γ(1/4)` and `Γ(1/3)` -/

/-- `x` is `g^d` times a nonzero number that is algebraic over `ℤ[ϖ]`. -/
def GDeg (ϖ : ℂ) (g x : ℝ) (d : ℤ) : Prop :=
  x ≠ 0 ∧ AlgOver ϖ ((x * g ^ (-d) : ℝ) : ℂ)

variable {ϖ : ℂ} {g x y : ℝ} {d d₁ d₂ : ℤ}

theorem GDeg.mul (hg : g ≠ 0) (hx : GDeg ϖ g x d₁) (hy : GDeg ϖ g y d₂) :
    GDeg ϖ g (x * y) (d₁ + d₂) := by
  refine ⟨mul_ne_zero hx.1 hy.1, ?_⟩
  have e : x * y * g ^ (-(d₁ + d₂)) = (x * g ^ (-d₁)) * (y * g ^ (-d₂)) := by
    rw [neg_add, zpow_add₀ hg]
    ring
  rw [e]
  push_cast
  have h1 := hx.2
  have h2 := hy.2
  push_cast at h1 h2
  exact h1.mul h2

theorem GDeg.div (hg : g ≠ 0) (hx : GDeg ϖ g x d₁) (hy : GDeg ϖ g y d₂) :
    GDeg ϖ g (x / y) (d₁ - d₂) := by
  refine ⟨div_ne_zero hx.1 hy.1, ?_⟩
  have hgz : g ^ (-d₂) ≠ 0 := zpow_ne_zero _ hg
  have e : x / y * g ^ (-(d₁ - d₂)) = (x * g ^ (-d₁)) / (y * g ^ (-d₂)) := by
    rw [show -(d₁ - d₂) = -d₁ + d₂ by ring, zpow_add₀ hg, zpow_neg g d₂]
    field_simp
  rw [e]
  push_cast
  have h1 := hx.2
  have h2 := hy.2
  push_cast at h1 h2
  refine AlgOver.div ?_ h1 h2
  have : y * g ^ (-d₂) ≠ 0 := mul_ne_zero hy.1 hgz
  exact_mod_cast this

theorem GDeg.rat_mul (hx : GDeg ϖ g x d) {ρ : ℚ} (hρ : ρ ≠ 0) : GDeg ϖ g (ρ * x) d := by
  refine ⟨mul_ne_zero (by exact_mod_cast hρ) hx.1, ?_⟩
  have e : (ρ : ℝ) * x * g ^ (-d) = ρ * (x * g ^ (-d)) := by ring
  rw [e]
  push_cast
  have h1 := hx.2
  push_cast at h1
  exact (algOver_ratCast ϖ ρ).mul h1

/-- A number algebraic over `ℤ[ϖ]` and not `0` has degree `0`. -/
theorem GDeg.of_algOver (hx0 : x ≠ 0) (hx : AlgOver ϖ (x : ℂ)) : GDeg ϖ g x 0 :=
  ⟨hx0, by simpa using hx⟩

/-- **A number of nonzero degree is irrational** when `g` is not algebraic over `ℤ[ϖ]`. -/
theorem GDeg.irrational (hg : g ≠ 0) (hgn : ¬ AlgOver ϖ (g : ℂ)) (hx : GDeg ϖ g x d)
    (hd : d ≠ 0) : Irrational x := by
  rintro ⟨r, hr⟩
  obtain ⟨hx0, hA⟩ := hx
  have hr0 : (r : ℂ) ≠ 0 := by
    have : (r : ℝ) ≠ 0 := hr ▸ hx0
    exact_mod_cast this
  have hpow : AlgOver ϖ ((g ^ (-d) : ℝ) : ℂ) := by
    have h := AlgOver.div hr0 hA (algOver_ratCast ϖ r)
    have e : ((x * g ^ (-d) : ℝ) : ℂ) / (r : ℂ) = ((g ^ (-d) : ℝ) : ℂ) := by
      rw [← hr]
      push_cast
      field_simp
    rwa [e] at h
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg (-d)
  · have hn0 : 0 < n := by omega
    rw [hn, zpow_natCast] at hpow
    push_cast at hpow
    exact hgn (AlgOver.of_pow hn0 hpow)
  · have hn0 : 0 < n := by omega
    rw [hn, zpow_neg, zpow_natCast] at hpow
    push_cast at hpow
    have hgc : ((g : ℂ) ^ n)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hg))
    have := AlgOver.inv hgc hpow
    rw [inv_inv] at this
    exact hgn (AlgOver.of_pow hn0 this)

/-! ### The degrees of the `Γ` values -/

theorem gdeg_self (ϖ : ℂ) {g : ℝ} (hg : g ≠ 0) : GDeg ϖ g g 1 := by
  refine ⟨hg, ?_⟩
  rw [zpow_neg, zpow_one, mul_inv_cancel₀ hg]
  simpa using algOver_one ϖ

theorem gamma_quarter_pos : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)

theorem gamma_third_pos : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)

/-- `Γ(1/2) = √π` has degree `0` over `ℤ[π]`. -/
theorem gdeg_gamma_half_pi (g : ℝ) : GDeg (Real.pi : ℂ) g (Real.Gamma (1 / 2)) 0 := by
  refine GDeg.of_algOver (Real.Gamma_pos_of_pos (by norm_num)).ne' ?_
  rw [Real.Gamma_one_half_eq]
  refine AlgOver.of_pow (n := 2) (by norm_num) ?_
  have : ((√Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  rw [this]
  exact algOver_self _

/-- `Γ(3/4) = π √2 / Γ(1/4)` has degree `−1`. -/
theorem gdeg_gamma_three_quarters :
    GDeg (Real.pi : ℂ) (Real.Gamma (1 / 4)) (Real.Gamma (3 / 4)) (-1) := by
  have hR := Real.Gamma_mul_Gamma_one_sub (1 / 4)
  rw [show Real.pi * (1 / 4 : ℝ) = Real.pi / 4 by ring, Real.sin_pi_div_four,
    show (1 - 1 / 4 : ℝ) = 3 / 4 by norm_num] at hR
  have hy : 0 < Real.Gamma (3 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hs2 : (0 : ℝ) < √2 := by positivity
  refine ⟨hy.ne', ?_⟩
  have e : Real.Gamma (3 / 4) * Real.Gamma (1 / 4) ^ (-(-1 : ℤ)) = Real.pi * 2 / √2 := by
    rw [neg_neg, zpow_one, mul_comm, hR]
    field_simp
  rw [e]
  push_cast
  refine AlgOver.div (by exact_mod_cast hs2.ne') ((algOver_self _).mul ?_) (algOver_sqrt_two _)
  exact_mod_cast algOver_natCast (Real.pi : ℂ) 2

/-- `Γ(1/2) = √π` has degree `0` over `ℤ[2π/√3]`. -/
theorem gdeg_gamma_half_rho (g : ℝ) : GDeg varpiRho g (Real.Gamma (1 / 2)) 0 := by
  refine GDeg.of_algOver (Real.Gamma_pos_of_pos (by norm_num)).ne' ?_
  rw [Real.Gamma_one_half_eq]
  exact algOver_sqrt_pi

theorem gamma_third_mul_two_thirds :
    Real.Gamma (1 / 3) * Real.Gamma (2 / 3) = 2 * Real.pi / √3 := by
  have hR := Real.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show Real.pi * (1 / 3 : ℝ) = Real.pi / 3 by ring, Real.sin_pi_div_three,
    show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num] at hR
  have hs3 : (0 : ℝ) < √3 := by positivity
  rw [hR]
  field_simp

/-- `Γ(2/3) = (2π/√3) / Γ(1/3)` has degree `−1`. -/
theorem gdeg_gamma_two_thirds :
    GDeg varpiRho (Real.Gamma (1 / 3)) (Real.Gamma (2 / 3)) (-1) := by
  refine ⟨(Real.Gamma_pos_of_pos (by norm_num)).ne', ?_⟩
  have e : Real.Gamma (2 / 3) * Real.Gamma (1 / 3) ^ (-(-1 : ℤ)) = 2 * Real.pi / √3 := by
    rw [neg_neg, zpow_one, mul_comm, gamma_third_mul_two_thirds]
  rw [e]
  have : (((2 * Real.pi / √3 : ℝ)) : ℂ) = varpiRho := by
    rw [varpiRho]
    push_cast
    rfl
  rw [this]
  exact algOver_self _

/-- `w = 2^(2/3)` and `Γ(1/3)² = Γ(1/6) (2π/√3) / (w √π)` (the duplication formula). -/
theorem gamma_third_sq :
    ∃ w : ℝ, 0 < w ∧ AlgOver varpiRho (w : ℂ) ∧
      Real.Gamma (1 / 3) ^ 2 = Real.Gamma (1 / 6) * (2 * Real.pi / √3) / (w * √Real.pi) := by
  have hD := Real.Gamma_mul_Gamma_add_half (1 / 6)
  rw [show (1 / 6 + 1 / 2 : ℝ) = 2 / 3 by norm_num,
    show (2 * (1 / 6) : ℝ) = 1 / 3 by norm_num,
    show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num] at hD
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
  have hR := Real.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show Real.pi * (1 / 3 : ℝ) = Real.pi / 3 by ring, Real.sin_pi_div_three,
    show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num] at hR
  have hs3 : (0 : ℝ) < √3 := by positivity
  refine ⟨w, hw0, hwA, ?_⟩
  field_simp
  field_simp at hR
  linear_combination (-(Real.Gamma (1 / 3) * √3)) * hD + Real.Gamma (1 / 6) * hR

theorem varpiRho_eq : (((2 * Real.pi / √3 : ℝ)) : ℂ) = varpiRho := by
  rw [varpiRho]
  push_cast
  rfl

/-- `Γ(1/6) = Γ(1/3)² w √π / (2π/√3)` has degree `2`. -/
theorem gdeg_gamma_one_sixth :
    GDeg varpiRho (Real.Gamma (1 / 3)) (Real.Gamma (1 / 6)) 2 := by
  obtain ⟨w, hw0, hwA, hsq⟩ := gamma_third_sq
  have hx : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hy : 0 < Real.Gamma (1 / 6) := Real.Gamma_pos_of_pos (by norm_num)
  have hsπ : 0 < √Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hs3 : (0 : ℝ) < √3 := by positivity
  refine ⟨hy.ne', ?_⟩
  have e : Real.Gamma (1 / 6) * Real.Gamma (1 / 3) ^ (-(2 : ℤ))
      = w * √Real.pi / (2 * Real.pi / √3) := by
    rw [zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hsq]
    field_simp
  rw [e]
  push_cast
  have h := AlgOver.div varpiRho_ne_zero (hwA.mul algOver_sqrt_pi) (algOver_self varpiRho)
  rw [← varpiRho_eq] at h
  push_cast at h
  exact h

/-- `Γ(5/6) = 2π / Γ(1/6)` has degree `−2`. -/
theorem gdeg_gamma_five_sixths :
    GDeg varpiRho (Real.Gamma (1 / 3)) (Real.Gamma (5 / 6)) (-2) := by
  have hR := Real.Gamma_mul_Gamma_one_sub (1 / 6)
  rw [show Real.pi * (1 / 6 : ℝ) = Real.pi / 6 by ring, Real.sin_pi_div_six,
    show (1 - 1 / 6 : ℝ) = 5 / 6 by norm_num] at hR
  have hy : 0 < Real.Gamma (5 / 6) := Real.Gamma_pos_of_pos (by norm_num)
  have h6 : 0 < Real.Gamma (1 / 6) := Real.Gamma_pos_of_pos (by norm_num)
  have hx : Real.Gamma (5 / 6) = 2 * Real.pi / Real.Gamma (1 / 6) := by
    field_simp
    field_simp at hR
    linarith
  have h2π : GDeg varpiRho (Real.Gamma (1 / 3)) (2 * Real.pi) 0 := by
    refine GDeg.of_algOver (by positivity) ?_
    push_cast
    refine AlgOver.mul ?_ algOver_pi
    exact_mod_cast algOver_natCast varpiRho 2
  have := h2π.div gamma_third_pos.ne' gdeg_gamma_one_sixth
  rw [← hx] at this
  simpa using this

/-! ### Arguments `N/4` and `N/6` -/

/-- The degree in `Γ(1/4)` of `Γ(N/4)`. -/
def deg4 (N : ℤ) : ℤ := if N % 4 = 1 then 1 else if N % 4 = 3 then -1 else 0

/-- The degree in `Γ(1/3)` of `Γ(N/6)`. -/
def deg6 (N : ℤ) : ℤ :=
  if N % 6 = 1 then 2 else if N % 6 = 2 then 1 else if N % 6 = 4 then -1
  else if N % 6 = 5 then -2 else 0

/-- `Γ((r + D n)/D)` is a nonzero rational multiple of `Γ(r/D)` for `0 < r < D`. -/
theorem gamma_div_eq {D : ℕ} {r : ℕ} (hr0 : 0 < r) (hrD : r < D) (n : ℤ) :
    ∃ ρ : ℚ, ρ ≠ 0 ∧ Real.Gamma ((((r : ℤ) + D * n : ℤ) : ℝ) / D)
      = ρ * Real.Gamma ((r : ℝ) / D) := by
  have hD0 : (D : ℚ) ≠ 0 := by
    have : 0 < D := by omega
    exact_mod_cast this.ne'
  have hx : ∀ m : ℤ, ((r : ℚ) / D) ≠ m := by
    intro m hm
    have h1 : (r : ℚ) = m * D := by
      field_simp at hm
      linarith
    have h2 : (r : ℤ) = m * D := by exact_mod_cast h1
    have hm1 : 0 < m := by
      by_contra hcon
      have : m * (D : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hcon) (by positivity)
      omega
    have : (D : ℤ) ≤ m * D := le_mul_of_one_le_left (by positivity) hm1
    omega
  obtain ⟨ρ, hρ, h⟩ := gamma_add_int_eq hx n
  refine ⟨ρ, hρ, ?_⟩
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD0
  have e1 : (((r : ℤ) + D * n : ℤ) : ℝ) / D = (((r : ℚ) / D + n : ℚ) : ℝ) := by
    push_cast
    field_simp
  have e2 : (r : ℝ) / D = (((r : ℚ) / D : ℚ) : ℝ) := by push_cast; rfl
  rw [e1, e2]
  exact h

/-- **The degree of `Γ(N/4)`**, `N` not a multiple of `4`. -/
theorem gdeg_gamma_div_four {N : ℤ} (h : N % 4 ≠ 0) :
    GDeg (Real.pi : ℂ) (Real.Gamma (1 / 4)) (Real.Gamma ((N : ℝ) / 4)) (deg4 N) := by
  have hN := Int.emod_add_mul_ediv N 4
  have h0 := Int.emod_nonneg N (by norm_num : (4 : ℤ) ≠ 0)
  have h4 := Int.emod_lt_of_pos N (by norm_num : (0 : ℤ) < 4)
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = N % 4 := ⟨(N % 4).toNat, Int.toNat_of_nonneg h0⟩
  obtain ⟨ρ, hρ, hΓ⟩ := gamma_div_eq (D := 4) (r := r) (by omega) (by omega) (N / 4)
  have hNr : ((r : ℤ) + ((4 : ℕ) : ℤ) * (N / 4)) = N := by
    rw [hr]
    push_cast
    linarith
  rw [hNr] at hΓ
  push_cast at hΓ
  rw [hΓ]
  have hr3 : r = 1 ∨ r = 2 ∨ r = 3 := by omega
  unfold deg4
  rcases hr3 with rfl | rfl | rfl
  · have h1 : N % 4 = 1 := by omega
    rw [ite_eq_left h1]
    have := (gdeg_self (Real.pi : ℂ) gamma_quarter_pos.ne').rat_mul hρ
    convert this using 2
    all_goals norm_num
  · have h1 : ¬ N % 4 = 1 := by omega
    have h3 : ¬ N % 4 = 3 := by omega
    rw [ite_eq_right h1, ite_eq_right h3]
    have := (gdeg_gamma_half_pi (Real.Gamma (1 / 4))).rat_mul hρ
    convert this using 2
    all_goals norm_num
  · have h1 : ¬ N % 4 = 1 := by omega
    have h3 : N % 4 = 3 := by omega
    rw [ite_eq_right h1, ite_eq_left h3]
    have := gdeg_gamma_three_quarters.rat_mul hρ
    convert this using 2

/-- **The degree of `Γ(N/6)`**, `N` not a multiple of `6`. -/
theorem gdeg_gamma_div_six {N : ℤ} (h : N % 6 ≠ 0) :
    GDeg varpiRho (Real.Gamma (1 / 3)) (Real.Gamma ((N : ℝ) / 6)) (deg6 N) := by
  have hN := Int.emod_add_mul_ediv N 6
  have h0 := Int.emod_nonneg N (by norm_num : (6 : ℤ) ≠ 0)
  have h6 := Int.emod_lt_of_pos N (by norm_num : (0 : ℤ) < 6)
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = N % 6 := ⟨(N % 6).toNat, Int.toNat_of_nonneg h0⟩
  obtain ⟨ρ, hρ, hΓ⟩ := gamma_div_eq (D := 6) (r := r) (by omega) (by omega) (N / 6)
  have hNr : ((r : ℤ) + ((6 : ℕ) : ℤ) * (N / 6)) = N := by
    rw [hr]
    push_cast
    linarith
  rw [hNr] at hΓ
  push_cast at hΓ
  rw [hΓ]
  have hr5 : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
  unfold deg6
  rcases hr5 with rfl | rfl | rfl | rfl | rfl
  · rw [ite_eq_left (by omega)]
    have := gdeg_gamma_one_sixth.rat_mul hρ
    convert this using 2
    all_goals norm_num
  · rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    have := (gdeg_self varpiRho gamma_third_pos.ne').rat_mul hρ
    convert this using 2
    all_goals norm_num
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
    have := (gdeg_gamma_half_rho (Real.Gamma (1 / 3))).rat_mul hρ
    convert this using 2
    all_goals norm_num
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    have := gdeg_gamma_two_thirds.rat_mul hρ
    convert this using 2
    all_goals norm_num
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left (by omega)]
    have := gdeg_gamma_five_sixths.rat_mul hρ
    convert this using 2

/-- **`B(N₁/4, N₂/4)` is irrational** when none of `N₁`, `N₂`, `N₁ + N₂` is a multiple of
`4`. -/
theorem irrational_beta_div_four {N₁ N₂ : ℤ} (h₁ : N₁ % 4 ≠ 0) (h₂ : N₂ % 4 ≠ 0)
    (hs : (N₁ + N₂) % 4 ≠ 0) :
    Irrational (Real.Gamma ((N₁ : ℝ) / 4) * Real.Gamma ((N₂ : ℝ) / 4)
      / Real.Gamma ((N₁ : ℝ) / 4 + (N₂ : ℝ) / 4)) := by
  have hg := gamma_quarter_pos.ne'
  have hD := ((gdeg_gamma_div_four h₁).mul hg (gdeg_gamma_div_four h₂)).div hg
    (gdeg_gamma_div_four hs)
  have e : (((N₁ + N₂ : ℤ)) : ℝ) / 4 = (N₁ : ℝ) / 4 + (N₂ : ℝ) / 4 := by push_cast; ring
  rw [e] at hD
  refine hD.irrational hg not_algOver_gamma_one_quarter ?_
  unfold deg4
  split_ifs <;> omega

/-- **`B(N₁/6, N₂/6)` is irrational** when none of `N₁`, `N₂`, `N₁ + N₂` is a multiple of
`6`. -/
theorem irrational_beta_div_six {N₁ N₂ : ℤ} (h₁ : N₁ % 6 ≠ 0) (h₂ : N₂ % 6 ≠ 0)
    (hs : (N₁ + N₂) % 6 ≠ 0) :
    Irrational (Real.Gamma ((N₁ : ℝ) / 6) * Real.Gamma ((N₂ : ℝ) / 6)
      / Real.Gamma ((N₁ : ℝ) / 6 + (N₂ : ℝ) / 6)) := by
  have hg := gamma_third_pos.ne'
  have hD := ((gdeg_gamma_div_six h₁).mul hg (gdeg_gamma_div_six h₂)).div hg
    (gdeg_gamma_div_six hs)
  have e : (((N₁ + N₂ : ℤ)) : ℝ) / 6 = (N₁ : ℝ) / 6 + (N₂ : ℝ) / 6 := by push_cast; ring
  rw [e] at hD
  refine hD.irrational hg not_algOver_gamma_one_third ?_
  unfold deg6
  split_ifs <;> omega

/-! ### Rational arguments -/

/-- A rational whose denominator divides `D` is `N/D`; `N` is a multiple of `D` only when the
rational is an integer. -/
theorem exists_int_div {a : ℚ} {D : ℕ} (hD : 0 < D) (h : a.den ∣ D) :
    ∃ N : ℤ, (a : ℝ) = (N : ℝ) / D ∧ (a.den ≠ 1 → N % (D : ℤ) ≠ 0) := by
  obtain ⟨c, hc⟩ := h
  have hden : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  have hc0 : (c : ℚ) ≠ 0 := by
    rintro h0
    have : c = 0 := by exact_mod_cast h0
    rw [this, mul_zero] at hc
    omega
  have hq : a = ((a.num * c : ℤ) : ℚ) / D := by
    have h1 : a = (a.num : ℚ) / a.den := (Rat.num_div_den a).symm
    rw [hc]
    push_cast
    rw [mul_div_mul_right _ _ hc0]
    exact h1
  refine ⟨a.num * c, by exact_mod_cast congrArg (fun t : ℚ => (t : ℝ)) hq, fun hne hmod => hne ?_⟩
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hmod
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have : a = (k : ℚ) := by
    rw [hq, hk]
    push_cast
    field_simp
  rw [this]
  exact Rat.den_intCast k

/-- **Irrational values of the Beta function at rational arguments**: `a`, `b` not integers,
and either `a + b` a positive integer, or `a + b` not an integer and the denominators of `a`
and `b` both divide `4` or both divide `6`. -/
theorem irrational_beta_of_den {a b : ℚ} (ha : a.den ≠ 1) (hb : b.den ≠ 1)
    (h : ((a + b).den = 1 ∧ 0 < a + b) ∨
      ((a + b).den ≠ 1 ∧ ((a.den ∣ 4 ∧ b.den ∣ 4) ∨ (a.den ∣ 6 ∧ b.den ∣ 6)))) :
    Irrational (Real.Gamma (a : ℝ) * Real.Gamma (b : ℝ) / Real.Gamma ((a : ℝ) + b)) := by
  rcases h with ⟨hs, hpos⟩ | ⟨hs, hcls⟩
  · have hint : ∀ k : ℤ, a ≠ k := fun k hk => ha (by rw [hk]; exact Rat.den_intCast k)
    have hsum : a + b = ((a + b).num : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den (a + b), hs]
      simp
    have hnum : 0 < (a + b).num := Rat.num_pos.mpr hpos
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (a + b).num = m := ⟨(a + b).num.toNat, by omega⟩
    exact irrational_beta_of_add_eq_nat hint (m := m) (by omega) (by rw [hsum, hm]; simp)
  · have key : ∀ D : ℕ, 0 < D → a.den ∣ D → b.den ∣ D →
        ∃ N₁ N₂ : ℤ, (a : ℝ) = (N₁ : ℝ) / D ∧ (b : ℝ) = (N₂ : ℝ) / D ∧ N₁ % (D : ℤ) ≠ 0 ∧
          N₂ % (D : ℤ) ≠ 0 ∧ (N₁ + N₂) % (D : ℤ) ≠ 0 := by
      intro D hD h1 h2
      obtain ⟨N₁, e₁, n₁⟩ := exists_int_div hD h1
      obtain ⟨N₂, e₂, n₂⟩ := exists_int_div hD h2
      refine ⟨N₁, N₂, e₁, e₂, n₁ ha, n₂ hb, fun hmod => hs ?_⟩
      obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hmod
      have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
      have : ((a + b : ℚ) : ℝ) = ((k : ℚ) : ℝ) := by
        push_cast
        rw [e₁, e₂, ← add_div]
        have : ((N₁ : ℝ) + N₂) = (D : ℝ) * k := by exact_mod_cast hk
        rw [this]
        field_simp
      have hq : a + b = (k : ℚ) := by exact_mod_cast this
      rw [hq]
      exact Rat.den_intCast k
    rcases hcls with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨N₁, N₂, e₁, e₂, n₁, n₂, ns⟩ := key 4 (by norm_num) h1 h2
      rw [e₁, e₂]
      exact_mod_cast irrational_beta_div_four n₁ n₂ ns
    · obtain ⟨N₁, N₂, e₁, e₂, n₁, n₂, ns⟩ := key 6 (by norm_num) h1 h2
      rw [e₁, e₂]
      exact_mod_cast irrational_beta_div_six n₁ n₂ ns

end Azurite.Chudnovsky
