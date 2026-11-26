/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Montgomery reduction: the arithmetic

The number-theoretic content of Montgomery reduction (P. L. Montgomery, *Modular multiplication
without trial division*, Math. Comp. 44 (1985)), on natural numbers and in `ZMod`, independent
of any limb representation.  The implementation on `AzNat` limbs is in `AzNat/Montgomery.lean`.

For an odd modulus `N`, a base `β` and `R = β ^ n`, a number `T < N R` is reduced by adding a
multiple `Q N` (`Q < R`) that makes the sum divisible by `R`; the quotient `x = (T + Q N) / R`
is below `2 N` and satisfies `x R ≡ T (mod N)`.  `Q` is found digit by digit — here two digits
at a time — from `n' = −N⁻¹ mod β`.

* `dvd_two_digit_step`: the two quotient digits chosen from the two lowest digits of the
  running value make it divisible by `β ^ 2`.
* `quotient_lt_two_mul`, `quotient_modEq`, `quotient_sub_modEq`: the size and the residue of
  the quotient, before and after the final subtraction.
* `natCast_eq_mul_inv`: in `ZMod N`, a number `r` with `r R ≡ T` is `T R⁻¹`.
-/

namespace Azurite.Montgomery

/-- **One two-digit step.**  Let the running value be `t₀ + t₁ β + β² V'`, the modulus
`n₀ + n₁ β + β² N'`, and `n₀ n' ≡ −1 (mod β)`.  With `q₀ = t₀ n' mod β`, the low digit `l₀` of
`n₀ q₀ + t₀` vanishes; with `u₁` the low digit of `n₁ q₀ + t₁ + h₀` (`h₀` the high digit before)
and `q₁ = u₁ n' mod β`, adding `(q₀ + q₁ β)` times the modulus gives a multiple of `β²`. -/
theorem dvd_two_digit_step {β t₀ t₁ n₀ n₁ n' h₀ l₀ h₁ u₁ q₀ q₁ V' N' : ℕ}
    (hinv : β ∣ n₀ * n' + 1) (hq₀ : q₀ = t₀ * n' % β)
    (hm₀ : h₀ * β + l₀ = n₀ * q₀ + t₀) (hl₀ : l₀ < β)
    (hm₁ : h₁ * β + u₁ = n₁ * q₀ + t₁ + h₀) (hq₁ : q₁ = u₁ * n' % β) :
    β ^ 2 ∣ (t₀ + t₁ * β + β ^ 2 * V') + (q₀ + q₁ * β) * (n₀ + n₁ * β + β ^ 2 * N') := by
  obtain ⟨k, hk⟩ := hinv
  have e₂ := Nat.div_add_mod (t₀ * n') β
  have e₅ := Nat.div_add_mod (u₁ * n') β
  rw [← hq₀] at e₂
  rw [← hq₁] at e₅
  generalize t₀ * n' / β = a at e₂
  generalize u₁ * n' / β = b at e₅
  zify at hk e₂ e₅ hm₀ hm₁
  have hl : l₀ = 0 := by
    have hd : (β : ℤ) ∣ (l₀ : ℤ) := ⟨t₀ * k - n₀ * a - h₀, by
      linear_combination hm₀ + (n₀ : ℤ) * e₂ + (t₀ : ℤ) * hk⟩
    exact Nat.eq_zero_of_dvd_of_lt (Int.natCast_dvd_natCast.mp hd) hl₀
  subst hl
  rw [← Int.natCast_dvd_natCast]
  push_cast
  refine ⟨h₁ + u₁ * k - b * n₀ + q₁ * n₁ + (q₀ + q₁ * β) * N' + V', ?_⟩
  linear_combination -(β : ℤ) * hm₁ - hm₀ + (β : ℤ) * (n₀ : ℤ) * e₅ + (β : ℤ) * (u₁ : ℤ) * hk

/-- The quotient `x = (T + Q N) / R` is below `2 N`. -/
theorem quotient_lt_two_mul {N R T Q x : ℕ} (hT : T < N * R) (hQ : Q ≤ R)
    (hx : x * R = T + Q * N) : x < 2 * N := by
  have hR : 0 < R := Nat.pos_of_ne_zero (by rintro rfl; simp at hT)
  have h : x * R < 2 * N * R := by
    have h1 := Nat.mul_le_mul_right N hQ
    have h2 : R * N = N * R := Nat.mul_comm _ _
    rw [hx, Nat.mul_assoc]
    omega
  exact Nat.lt_of_mul_lt_mul_right h

/-- The quotient represents `T R⁻¹`: `x R ≡ T (mod N)`. -/
theorem quotient_modEq {N R T Q x : ℕ} (hx : x * R = T + Q * N) : x * R ≡ T [MOD N] := by
  rw [hx]
  exact (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).mpr ⟨Q, by rw [Nat.add_sub_cancel_left,
    Nat.mul_comm]⟩ |>.symm

/-- So does the quotient after the final subtraction. -/
theorem quotient_sub_modEq {N R T Q x : ℕ} (hx : x * R = T + Q * N) (h : N ≤ x) :
    (x - N) * R ≡ T [MOD N] := by
  refine Nat.ModEq.trans ?_ (quotient_modEq hx)
  have : x * R = (x - N) * R + R * N := by
    rw [Nat.sub_mul, Nat.mul_comm R N]
    exact (Nat.sub_add_cancel (Nat.mul_le_mul_right R h)).symm
  rw [this]
  exact (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).mpr ⟨R, by rw [Nat.add_sub_cancel_left,
    Nat.mul_comm]⟩

/-- In `ZMod N`, a number `r` with `r R ≡ T (mod N)` is `T R⁻¹` (`R` prime to `N`). -/
theorem natCast_eq_mul_inv {N R T r : ℕ} (hc : Nat.Coprime R N) (h : r * R ≡ T [MOD N]) :
    (r : ZMod N) = (T : ZMod N) * (R : ZMod N)⁻¹ := by
  have h1 : ((r * R : ℕ) : ZMod N) = (T : ZMod N) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  have h2 : (R : ZMod N) * (R : ZMod N)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one R hc
  rw [← h1, Nat.cast_mul, mul_assoc, h2, mul_one]

end Azurite.Montgomery
