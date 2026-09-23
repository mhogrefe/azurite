/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZMod.Equiv.Basic
import Azurite.AzZMod.Equiv.Conversion
import Azurite.AzZMod.Equiv.Pow
import Azurite.Algorithm.Equiv.SlidingWindowPowAzNat

/-!
## `CommRing (AzZMod m)`

The ring structure pinned by the projection `toZMod : AzZMod m → ZMod m.toNat`:
every axiom is the corresponding `ZMod` axiom pulled back through the injective,
operation-preserving `toZMod` (mirroring `AzZModPow2`'s `CommRing`).  The
arithmetic that runs is the computable residue arithmetic: `+`/`-`/`*` are the
add-then-subtract / borrow / reduce-the-product operations, and `nsmul`/`zsmul`
are one cast plus one multiplication (not the default `n`-fold sums).  A nonzero
modulus (`NeZero m.toNat`) is required throughout, as for the underlying residue
operations and the `ZMod` bridge.

`npow` is left as the default `npowRec` for now (an `O(log n)` sliding-window
`pow` would mirror `AzZModPow2.pow`, but is deferred along with the rest of the
multiplicative tower).
-/

namespace Azurite.AzZMod

variable {m : AzNat}

/-- Computable `NatCast`: reduce the literal modulo `m` (the default
    `Nat.unaryCast` would be `n` additions of `1`). -/
instance [NeZero m.toNat] : NatCast (AzZMod m) := ⟨fun n => ofNat m n⟩

@[simp] theorem toZMod_natCast [NeZero m.toNat] (n : ℕ) :
    toZMod (n : AzZMod m) = (n : ZMod m.toNat) := by
  show toZMod (ofAzNat m (AzNat.ofNat n)) = (n : ZMod m.toNat)
  rw [toZMod_ofAzNat, AzNat.toNat_ofNat]

/-- Computable `IntCast`: convert through `AzInt.ofInt` and reduce modulo `m`. -/
instance [NeZero m.toNat] : IntCast (AzZMod m) := ⟨fun i => ofAzInt m (AzInt.ofInt i)⟩

@[simp] theorem toZMod_intCast [NeZero m.toNat] (i : ℤ) :
    toZMod (i : AzZMod m) = (i : ZMod m.toNat) := by
  show toZMod (ofAzInt m (AzInt.ofInt i)) = (i : ZMod m.toNat)
  rw [toZMod_ofAzInt, AzInt.toInt_ofInt]

instance instCommRing [NeZero m.toNat] : CommRing (AzZMod m) where
  add_assoc a b c := toZMod_injective (by simp only [toZMod_add]; ring)
  zero_add a := toZMod_injective (by simp)
  add_zero a := toZMod_injective (by simp)
  add_comm a b := toZMod_injective (by simp only [toZMod_add]; ring)
  mul_assoc a b c := toZMod_injective (by simp only [toZMod_mul]; ring)
  one_mul a := toZMod_injective (by simp)
  mul_one a := toZMod_injective (by simp)
  left_distrib a b c := toZMod_injective (by simp only [toZMod_add, toZMod_mul]; ring)
  right_distrib a b c := toZMod_injective (by simp only [toZMod_add, toZMod_mul]; ring)
  zero_mul a := toZMod_injective (by simp)
  mul_zero a := toZMod_injective (by simp)
  mul_comm a b := toZMod_injective (by simp only [toZMod_mul]; ring)
  neg_add_cancel a := toZMod_injective (by simp)
  sub_eq_add_neg a b := toZMod_injective (by simp only [toZMod_sub, toZMod_add, toZMod_neg]; ring)
  natCast_zero := toZMod_injective (by simp)
  natCast_succ n := toZMod_injective (by simp [toZMod_add])
  intCast_ofNat n := toZMod_injective (by simp)
  intCast_negSucc n := toZMod_injective (by simp [toZMod_neg, Int.negSucc_eq])
  -- `n • a` / `i • a` are one cast plus one multiplication.
  nsmul n a := (n : AzZMod m) * a
  nsmul_zero a := toZMod_injective (by
    show (((0 : ℕ) : AzZMod m) * a).toZMod = _
    simp)
  nsmul_succ n a := toZMod_injective (by
    show ((((n + 1 : ℕ)) : AzZMod m) * a).toZMod = ((((n : ℕ)) : AzZMod m) * a + a).toZMod
    simp [toZMod_add, toZMod_mul]
    ring)
  zsmul i a := (i : AzZMod m) * a
  zsmul_zero' a := toZMod_injective (by
    show (((0 : ℤ) : AzZMod m) * a).toZMod = _
    simp)
  zsmul_succ' n a := toZMod_injective (by
    show ((((n + 1 : ℕ) : ℤ) : AzZMod m) * a).toZMod
      = ((((n : ℕ) : ℤ) : AzZMod m) * a + a).toZMod
    simp [toZMod_add, toZMod_mul]
    ring)
  zsmul_neg' n a := toZMod_injective (by
    show (((Int.negSucc n) : AzZMod m) * a).toZMod
      = (-((((n + 1 : ℕ) : ℤ) : AzZMod m) * a)).toZMod
    simp [toZMod_mul, toZMod_neg, Int.negSucc_eq]
    ring)
  -- Exponentiation runs the sliding-window `pow` (`O(log n)` multiplications).
  npow n a := a.pow n
  npow_zero a := toZMod_injective (by
    show (a.pow 0).toZMod = _
    rw [toZMod_pow, pow_zero, toZMod_one])
  npow_succ n a := toZMod_injective (by
    show (a.pow (n + 1)).toZMod = (a.pow n * a).toZMod
    rw [toZMod_mul, toZMod_pow, toZMod_pow, pow_succ])

-- Sanity: the `CommRing` is fully usable — `ring` discharges polynomial identities,
-- and `pow` is the monoid power.
example [NeZero m.toNat] (a b c : AzZMod m) : (a + b) * c = a * c + b * c := by ring
example [NeZero m.toNat] (a : AzZMod m) (n : ℕ) : a ^ n = a.pow n := rfl

end Azurite.AzZMod

/-! ### The `AzNat`-exponent power, post-`Monoid` -/

namespace Azurite.AzZMod

variable {m : AzNat}

/-- **`powAzNat` computes the monoid power** at the `toNat` exponent. -/
theorem powAzNat_eq_pow [NeZero m.toNat] (a : AzZMod m) (n : AzNat) :
    a.powAzNat n = a ^ n.toNat :=
  Azurite.slidingWindowPowAzNat_eq_pow a n

/-- **The `AzNat`-exponent power agrees with `ZMod`.** -/
@[simp] theorem toZMod_powAzNat [NeZero m.toNat] (a : AzZMod m) (n : AzNat) :
    toZMod (a.powAzNat n) = (toZMod a) ^ n.toNat := by
  rw [powAzNat_eq_pow]
  induction n.toNat with
  | zero => simp [toZMod_one]
  | succ k ih => rw [pow_succ, pow_succ, toZMod_mul, ih]

end Azurite.AzZMod
