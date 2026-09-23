/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZModPow2.Inv
import Azurite.AzZModPow2.Equiv.Pow
import Azurite.AzZModPow2.ToString
import Azurite.AzNat.Equiv.Parity

/-!
## Correctness of the modular inverse `AzZModPow2.invOdd`

`invOdd` is a two-sided inverse of any odd residue (and hence such a residue is a
unit).  The proof follows the Newton-lifting analysis described in `Inv.lean`: the
residual `1 − a · xₙ` squares each step, so `1 − a · xₙ = (1 − a)^(2ⁿ)`, and after
`⌈log₂ k⌉` steps that power vanishes modulo `2^k` because `a` odd makes `1 − a`
even.  The vanishing is checked through the ring isomorphism `toZMod`.
-/

namespace Azurite.AzZModPow2

variable {k : Nat}

theorem isOdd_iff (a : AzZModPow2 k) : a.isOdd = true ↔ Odd a.val.toNat :=
  AzNat.isOdd_iff a.val

@[simp] theorem val_toNat_ofNat (k m : Nat) : (ofNat k m).val.toNat = m % 2 ^ k := by
  show ((AzNat.ofNat m).modPow2 k).toNat = m % 2 ^ k
  rw [AzNat.toNat_modPow2, AzNat.toNat_ofNat]

/-- **Newton-lifting invariant.**  In any commutative ring the residual squares,
so after `n` iterations `1 − a · xₙ = (1 − a)^(2ⁿ)`. -/
theorem one_sub_mul_invOddAux (a : AzZModPow2 k) (n : Nat) :
    1 - a * invOddAux a n = (1 - a) ^ (2 ^ n) := by
  induction n with
  | zero => simp only [invOddAux, mul_one, pow_zero, pow_one]
  | succ n ih =>
    have hstep : invOddAux a (n + 1) = invOddAux a n * (2 - a * invOddAux a n) := rfl
    rw [hstep,
        show 1 - a * (invOddAux a n * (2 - a * invOddAux a n))
            = (1 - a * invOddAux a n) ^ 2 from by ring,
        ih, ← pow_mul, ← pow_succ]

/-- After `⌈log₂ k⌉` iterations the residual `(1 − a)^(2ⁿ)` vanishes in `ℤ / 2^k`:
`a` odd makes `1 − a` even, so the power is divisible by `2^(2ⁿ)`, hence by `2^k`. -/
theorem one_sub_pow_clog_eq_zero (a : AzZModPow2 k) (h : a.isOdd = true) :
    ((1 : AzZModPow2 k) - a) ^ (2 ^ Nat.clog 2 k) = 0 := by
  apply toZMod_injective
  rw [toZMod_zero,
      show ((1 : AzZModPow2 k) - a) ^ (2 ^ Nat.clog 2 k)
          = ((1 : AzZModPow2 k) - a).pow (2 ^ Nat.clog 2 k) from rfl,
      toZMod_pow, toZMod_sub, toZMod_one]
  -- `1 − toZMod a` is the image of the integer `1 − a.val.toNat`.
  have key : (1 : ZMod (2 ^ k)) - toZMod a = (((1 - a.val.toNat : ℤ)) : ZMod (2 ^ k)) := by
    simp only [toZMod]; push_cast; ring
  rw [key, ← Int.cast_pow, ZMod.intCast_zmod_eq_zero_iff_dvd]
  -- Reduce to a divisibility of integers.
  obtain ⟨s, hs⟩ := (isOdd_iff a).mp h
  have hdvd2 : (2 : ℤ) ∣ ((1 : ℤ) - a.val.toNat) := ⟨-(s : ℤ), by rw [hs]; push_cast; ring⟩
  have hm : k ≤ 2 ^ Nat.clog 2 k := Nat.le_pow_clog (by norm_num) k
  calc ((2 ^ k : ℕ) : ℤ) = (2 : ℤ) ^ k := by push_cast; ring
    _ ∣ (2 : ℤ) ^ (2 ^ Nat.clog 2 k) := pow_dvd_pow 2 hm
    _ ∣ ((1 : ℤ) - a.val.toNat) ^ (2 ^ Nat.clog 2 k) := pow_dvd_pow_of_dvd hdvd2 _

/-- **Correctness:** `invOdd` is a right inverse. -/
@[simp] theorem mul_invOdd (a : AzZModPow2 k) (h : a.isOdd = true) : a * a.invOdd h = 1 := by
  show a * invOddAux a (Nat.clog 2 k) = 1
  have key := one_sub_mul_invOddAux a (Nat.clog 2 k)
  rw [one_sub_pow_clog_eq_zero a h] at key
  exact (sub_eq_zero.mp key).symm

/-- **Correctness:** `invOdd` is a left inverse. -/
@[simp] theorem invOdd_mul (a : AzZModPow2 k) (h : a.isOdd = true) : a.invOdd h * a = 1 := by
  rw [mul_comm]; exact mul_invOdd a h

/-- An odd residue is a unit of `ℤ / 2^k`. -/
theorem isUnit_of_isOdd (a : AzZModPow2 k) (h : a.isOdd = true) : IsUnit a :=
  ⟨⟨a, a.invOdd h, mul_invOdd a h, invOdd_mul a h⟩, rfl⟩

end Azurite.AzZModPow2

/-! ### Tests -/

section Tests

open Azurite Azurite.AzZModPow2

-- Oddness of a literal residue: reduce to `Odd (m % 2^k)` by `m % 2 = 1`.
private theorem oddLit {k m : Nat} (hm : m % 2 ^ k % 2 = 1) : (AzZModPow2.ofNat k m).isOdd = true := by
  rw [isOdd_iff, val_toNat_ofNat, Nat.odd_iff]; exact hm

-- `3⁻¹ = 11` in `ℤ/16` (`3·11 = 33 ≡ 1`); `7⁻¹ = 183` in `ℤ/256` (`7·183 = 1281 ≡ 1`).
#guard Azurite.AzZModPow2.toString
  ((AzZModPow2.ofNat 4 3).invOdd (oddLit (by decide))) == "11"
#guard Azurite.AzZModPow2.toString
  ((AzZModPow2.ofNat 8 7).invOdd (oddLit (by decide))) == "183"
-- The inverse really inverts.
#guard Azurite.AzZModPow2.toString
  (AzZModPow2.ofNat 8 7 * (AzZModPow2.ofNat 8 7).invOdd (oddLit (by decide))) == "1"
#guard Azurite.AzZModPow2.toString (AzZModPow2.ofNat 32 123456789 *
  (AzZModPow2.ofNat 32 123456789).invOdd (oddLit (by decide))) == "1"
-- Multi-limb modulus `ℤ/2^128`.
#guard Azurite.AzZModPow2.toString (AzZModPow2.ofNat 128 (2 ^ 127 - 1) *
  (AzZModPow2.ofNat 128 (2 ^ 127 - 1)).invOdd (oddLit (by decide))) == "1"

end Tests
