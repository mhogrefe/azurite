/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Azurite.UInt64.Equiv.AddWithCarry
import Azurite.UInt64.WideAdd3

namespace UInt64

/-- Correctness of `wideAdd3`: the returned triple represents the sum of the two
192-bit inputs modulo `2^192`. -/
theorem toNat_wideAdd3 (x y : UInt64 × UInt64 × UInt64) :
    (wideAdd3 x y).1.toNat * 2 ^ 128 + (wideAdd3 x y).2.1.toNat * 2 ^ 64
        + (wideAdd3 x y).2.2.toNat
      = (x.1.toNat * 2 ^ 128 + x.2.1.toNat * 2 ^ 64 + x.2.2.toNat
          + (y.1.toNat * 2 ^ 128 + y.2.1.toNat * 2 ^ 64 + y.2.2.toNat)) % 2 ^ 192 := by
  unfold wideAdd3
  set X2 : ℕ := x.1.toNat
  set X1 : ℕ := x.2.1.toNat
  set X0 : ℕ := x.2.2.toNat
  set Y2 : ℕ := y.1.toNat
  set Y1 : ℕ := y.2.1.toNat
  set Y0 : ℕ := y.2.2.toNat
  have hX2 : X2 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hX1 : X1 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hX0 : X0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hY2 : Y2 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hY1 : Y1 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hY0 : Y0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  set r0 := addWithCarry x.2.2 y.2.2 false
  set r1 := addWithCarry x.2.1 y.2.1 r0.2
  set r2 := addWithCarry x.1 y.1 r1.2
  have he0 : X0 + Y0 + 0 = (if r0.2 then 1 else 0) * 2 ^ 64 + r0.1.toNat :=
    addWithCarry_eq x.2.2 y.2.2 false
  have he1 : X1 + Y1 + (if r0.2 then 1 else 0)
      = (if r1.2 then 1 else 0) * 2 ^ 64 + r1.1.toNat :=
    addWithCarry_eq x.2.1 y.2.1 r0.2
  have he2 : X2 + Y2 + (if r1.2 then 1 else 0)
      = (if r2.2 then 1 else 0) * 2 ^ 64 + r2.1.toNat :=
    addWithCarry_eq x.1 y.1 r1.2
  have hr0_lt : r0.1.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hr1_lt : r1.1.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hr2_lt : r2.1.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have h128 : (2 : ℕ) ^ 128 = 2 ^ 64 * 2 ^ 64 := by
    show (2 : ℕ) ^ (64 + 64) = 2 ^ 64 * 2 ^ 64; exact pow_add 2 64 64
  have h192 : (2 : ℕ) ^ 192 = 2 ^ 128 * 2 ^ 64 := by
    show (2 : ℕ) ^ (128 + 64) = 2 ^ 128 * 2 ^ 64; exact pow_add 2 128 64
  -- Combine the three equations into a single identity with a top carry c2.
  have hc0_range : (if r0.2 then 1 else 0 : ℕ) ≤ 1 := by split <;> simp
  have hc1_range : (if r1.2 then 1 else 0 : ℕ) ≤ 1 := by split <;> simp
  have hc2_range : (if r2.2 then 1 else 0 : ℕ) ≤ 1 := by split <;> simp
  -- The full identity: X + Y = c2 * 2^192 + (r2.1*2^128 + r1.1*2^64 + r0.1)
  have hfull : X2 * 2 ^ 128 + X1 * 2 ^ 64 + X0 + (Y2 * 2 ^ 128 + Y1 * 2 ^ 64 + Y0)
      = (if r2.2 then 1 else 0) * 2 ^ 192
          + (r2.1.toNat * 2 ^ 128 + r1.1.toNat * 2 ^ 64 + r0.1.toNat) := by
    have e0 : X0 + Y0 = (if r0.2 then 1 else 0) * 2 ^ 64 + r0.1.toNat := by linarith
    have e1 : X1 + Y1 + (if r0.2 then 1 else 0)
        = (if r1.2 then 1 else 0) * 2 ^ 64 + r1.1.toNat := he1
    have e2 : X2 + Y2 + (if r1.2 then 1 else 0)
        = (if r2.2 then 1 else 0) * 2 ^ 64 + r2.1.toNat := he2
    -- Multiply e1 by 2^64 and e2 by 2^128.
    have step1 : X1 * 2 ^ 64 + Y1 * 2 ^ 64 + (if r0.2 then 1 else 0) * 2 ^ 64
        = (if r1.2 then 1 else 0) * 2 ^ 128 + r1.1.toNat * 2 ^ 64 := by
      have : (X1 + Y1 + (if r0.2 then 1 else 0)) * 2 ^ 64
          = ((if r1.2 then 1 else 0) * 2 ^ 64 + r1.1.toNat) * 2 ^ 64 := by
        rw [e1]
      rw [h128]; linarith [this]
    have step2 : X2 * 2 ^ 128 + Y2 * 2 ^ 128 + (if r1.2 then 1 else 0) * 2 ^ 128
        = (if r2.2 then 1 else 0) * 2 ^ 192 + r2.1.toNat * 2 ^ 128 := by
      have : (X2 + Y2 + (if r1.2 then 1 else 0)) * 2 ^ 128
          = ((if r2.2 then 1 else 0) * 2 ^ 64 + r2.1.toNat) * 2 ^ 128 := by
        rw [e2]
      rw [h192]; linarith [this]
    linarith [e0, step1, step2]
  -- Final: goal reduces to r2.1.toNat * 2^128 + r1.1.toNat * 2^64 + r0.1.toNat mod 2^192
  -- which equals the full sum mod 2^192 by hfull.
  have hresult_lt :
      r2.1.toNat * 2 ^ 128 + r1.1.toNat * 2 ^ 64 + r0.1.toNat < 2 ^ 192 := by
    have hr1_bnd : r1.1.toNat * 2 ^ 64 + r0.1.toNat < 2 ^ 128 := by
      rw [h128]
      have : r1.1.toNat + 1 ≤ 2 ^ 64 := hr1_lt
      have h1 : (r1.1.toNat + 1) * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 := Nat.mul_le_mul_right _ this
      have h2 : (r1.1.toNat + 1) * 2 ^ 64 = r1.1.toNat * 2 ^ 64 + 2 ^ 64 := by ring
      linarith
    rw [h192]
    have : r2.1.toNat + 1 ≤ 2 ^ 64 := hr2_lt
    have h1 : (r2.1.toNat + 1) * 2 ^ 128 ≤ 2 ^ 64 * 2 ^ 128 := Nat.mul_le_mul_right _ this
    have h2 : (r2.1.toNat + 1) * 2 ^ 128 = r2.1.toNat * 2 ^ 128 + 2 ^ 128 := by ring
    have hswap : 2 ^ 128 * 2 ^ 64 = 2 ^ 64 * 2 ^ 128 := by ring
    rw [hswap]
    linarith
  -- Show goal.
  change r2.1.toNat * 2 ^ 128 + r1.1.toNat * 2 ^ 64 + r0.1.toNat
      = (X2 * 2 ^ 128 + X1 * 2 ^ 64 + X0 + (Y2 * 2 ^ 128 + Y1 * 2 ^ 64 + Y0)) % 2 ^ 192
  rw [hfull]
  by_cases hc2 : r2.2
  · rw [ite_eq_left hc2]
    have : (1 * 2 ^ 192 + (r2.1.toNat * 2 ^ 128 + r1.1.toNat * 2 ^ 64 + r0.1.toNat))
        % 2 ^ 192 = r2.1.toNat * 2 ^ 128 + r1.1.toNat * 2 ^ 64 + r0.1.toNat := by
      rw [Nat.one_mul, Nat.add_mod_left, Nat.mod_eq_of_lt hresult_lt]
    linarith [this]
  · rw [ite_eq_right hc2]
    have : (0 * 2 ^ 192 + (r2.1.toNat * 2 ^ 128 + r1.1.toNat * 2 ^ 64 + r0.1.toNat))
        % 2 ^ 192 = r2.1.toNat * 2 ^ 128 + r1.1.toNat * 2 ^ 64 + r0.1.toNat := by
      rw [Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hresult_lt]
    linarith [this]

end UInt64
