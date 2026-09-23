/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Basic
import Azurite.UInt64.Pow2

namespace Azurite

/-- Construct the AzNat equal to `2 ^ k` by placing a single set bit in the correct limb. -/
def AzNat.pow2 (k : Nat) : AzNat where
  limbs := (Array.replicate (k / 64) (0 : UInt64)).push (1 <<< (UInt64.ofNat (k % 64)))
  last_ne_zero := by
    rw [Array.back?_push]
    intro h
    have h := Option.some.inj h
    have h1 : ((1 : UInt64) <<< (UInt64.ofNat (k % 64))).toNat = 0 := congrArg UInt64.toNat h
    simp only [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat,
               show 1 % 2 ^ 64 = 1 from by omega, Nat.one_shiftLeft] at h1
    have h2 : (UInt64.ofNat (k % 64)).toNat % 64 < 64 := Nat.mod_lt _ (by omega)
    rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) h2)] at h1
    exact absurd h1 (by have := Nat.two_pow_pos ((UInt64.ofNat (k % 64)).toNat % 64); omega)

/-- Check if limbs in `[0, k)` are all zero. -/
def AzNat.allZeroLoop (a : Array UInt64) (k : Nat) (h : k ≤ a.size) : Bool :=
  match k with
  | 0 => true
  | k + 1 =>
    have : k < a.size := by omega
    a[k] == 0 && AzNat.allZeroLoop a k (by omega)

/-- Test whether an AzNat is a positive power of 2 (i.e. `2 ^ k` for some `k`). Returns `false` for `0`. -/
def AzNat.isPowerOfTwo (a : AzNat) : Bool :=
  match h : a.limbs.size with
  | 0 => false
  | n + 1 =>
    have hi : n < a.limbs.size := by omega
    let last := a.limbs[n]
    last.isPowerOfTwo && AzNat.allZeroLoop a.limbs n (by omega)

end Azurite
