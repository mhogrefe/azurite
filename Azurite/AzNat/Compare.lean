/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Basic

namespace Azurite.AzNat

def compareLimbs (a b : Array UInt64) (aLo bLo k : Nat)
    (ha : aLo + k ≤ a.size) (hb : bLo + k ≤ b.size) : Ordering :=
  match k with
  | 0 => Ordering.eq
  | k + 1 =>
    have hai : aLo + k < a.size := by omega
    have hbi : bLo + k < b.size := by omega
    match Ord.compare a[aLo + k] b[bLo + k] with
    | Ordering.eq => compareLimbs a b aLo bLo k (by omega) (by omega)
    | ord => ord

@[simp] theorem compareLimbs_zero (a b : Array UInt64) (aLo bLo : Nat)
    (ha : aLo ≤ a.size) (hb : bLo ≤ b.size) :
    compareLimbs a b aLo bLo 0 (by omega) (by omega) = Ordering.eq := rfl

def compare (a b : AzNat) : Ordering :=
  match h : Ord.compare a.limbs.size b.limbs.size with
  | Ordering.eq =>
    have hs : a.limbs.size = b.limbs.size := Nat.compare_eq_eq.mp h
    compareLimbs a.limbs b.limbs 0 0 a.limbs.size (by omega) (by omega)
  | ord => ord

instance instOrdAzNat : Ord AzNat where
  compare := compare

instance : LE AzNat where le a b := compare a b ≠ Ordering.gt
instance : LT AzNat where lt a b := compare a b = Ordering.lt

instance : DecidableRel (α := AzNat) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (compare a b ≠ Ordering.gt))

instance : DecidableRel (α := AzNat) (· < ·) :=
  fun a b => inferInstanceAs (Decidable (compare a b = Ordering.lt))

instance : Max AzNat where max a b := if a ≤ b then b else a
instance : Min AzNat where min a b := if a ≤ b then a else b

end Azurite.AzNat
