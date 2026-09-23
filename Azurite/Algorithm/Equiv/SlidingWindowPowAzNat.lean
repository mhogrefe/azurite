/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Algorithm.SlidingWindowPowAzNat
import Azurite.AzNat.Equiv.TestBit
import Azurite.AzNat.Equiv.Size
import Mathlib.Data.Nat.Size

/-!
# Correctness of `slidingWindowPowAzNat`

`slidingWindowPowAzNat a n = a ^ n.toNat` in any monoid.

The proof mirrors the ℕ-exponent `slidingWindowPow_eq_pow`: the loop keeps the accumulator equal to
a power of `a` (so everything commutes), and the invariant

`slidingWindowPowAzNatAux a n i (a ^ h) = a ^ (h · 2^i + n.toNat % 2^i)`

is closed by the binary-expansion step `m % 2^(i+1) = 2^i · (m.testBit i).toNat + m % 2^i`, with the
limb-level `AzNat.testBit` identified with `Nat.testBit n.toNat` via
`AzNat.testBit_eq_toNat_testBit`, and the final `m % 2^(n.size) = m` from `AzNat.size_toNat`.
-/

namespace Azurite

variable {M : Type _}

/-- Binary-expansion step: peeling one bit off `m % 2^(i+1)`. -/
private lemma nat_mod_two_pow_succ (m i : ℕ) :
    m % 2 ^ (i + 1) = 2 ^ i * (m.testBit i).toNat + m % 2 ^ i := by
  have hbit : (m.testBit i).toNat = m / 2 ^ i % 2 := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ i) with h | h <;> simp [h]
  rw [pow_succ, Nat.mod_mul, hbit]; ring

/-- **Loop invariant.**  Starting from the accumulator `a ^ h`, the loop over bits `i-1 … 0`
produces `a ^ (h · 2^i + (low `i` bits of `n.toNat`))`. -/
theorem slidingWindowPowAzNatAux_eq [Monoid M] [Square M] (a : M) (n : AzNat) :
    ∀ (i h : ℕ), slidingWindowPowAzNatAux a n i (a ^ h)
      = a ^ (h * 2 ^ i + n.toNat % 2 ^ i) := by
  intro i
  induction i with
  | zero => intro h; simp [slidingWindowPowAzNatAux, Nat.mod_one]
  | succ k ih =>
    intro h
    have hnext : (if n.testBit k then Square.square (a ^ h) * a else Square.square (a ^ h))
        = a ^ (h * 2 + (n.testBit k).toNat) := by
      cases n.testBit k
      · simp only [Bool.false_eq_true, ite_false, Square.square_eq, ← pow_add,
          Bool.toNat_false, Nat.add_zero]
        congr 1; ring
      · simp only [ite_true, Square.square_eq, ← pow_add, Bool.toNat_true]
        rw [← pow_succ]; congr 1; ring
    have hstep : slidingWindowPowAzNatAux a n (k + 1) (a ^ h)
        = slidingWindowPowAzNatAux a n k (a ^ (h * 2 + (n.testBit k).toNat)) := by
      show slidingWindowPowAzNatAux a n k
        (if n.testBit k then Square.square (a ^ h) * a else Square.square (a ^ h)) = _
      rw [hnext]
    rw [hstep, ih]
    congr 1
    rw [nat_mod_two_pow_succ n.toNat k, ← AzNat.testBit_eq_toNat_testBit, pow_succ]
    ring

/-- **Correctness of `AzNat`-exponent exponentiation:** `slidingWindowPowAzNat a n = a ^ n.toNat`. -/
theorem slidingWindowPowAzNat_eq_pow [Monoid M] [Square M] (a : M) (n : AzNat) :
    slidingWindowPowAzNat a n = a ^ n.toNat := by
  rw [slidingWindowPowAzNat, show (1 : M) = a ^ 0 from (pow_zero a).symm,
    slidingWindowPowAzNatAux_eq a n n.size 0, zero_mul, zero_add, ← AzNat.size_toNat n]
  exact congrArg (a ^ ·) (Nat.mod_eq_of_lt (Nat.lt_size_self n.toNat))

/-- The loop commutes with a multiplicative map. -/
theorem map_slidingWindowPowAzNatAux [Mul M] [Square M] {N : Type _} [Mul N] [Square N]
    (f : M → N) (hmul : ∀ a b : M, f (a * b) = f a * f b) (a : M) (n : AzNat) :
    ∀ (i : ℕ) (acc : M), f (slidingWindowPowAzNatAux a n i acc)
      = slidingWindowPowAzNatAux (f a) n i (f acc)
  | 0, _ => rfl
  | i + 1, acc => by
    have hsq : f (Square.square acc) = Square.square (f acc) := by
      rw [Square.square_eq, Square.square_eq, hmul]
    show f (slidingWindowPowAzNatAux a n i
        (if n.testBit i then Square.square acc * a else Square.square acc))
      = slidingWindowPowAzNatAux (f a) n i
        (if n.testBit i then Square.square (f acc) * f a else Square.square (f acc))
    rw [map_slidingWindowPowAzNatAux f hmul a n i]
    congr 1
    split_ifs <;> simp only [hmul, hsq]

/-- **Transport of `AzNat`-exponent exponentiation** along a multiplicative, unital map
into a monoid: `f (slidingWindowPowAzNat a n) = f a ^ n.toNat`.  The source needs only
`Mul`/`One`/`Square` (e.g.\ a subtype with a shortcut squaring). -/
theorem map_slidingWindowPowAzNat [Mul M] [One M] [Square M] {N : Type _} [Monoid N] [Square N]
    (f : M → N) (hone : f 1 = 1) (hmul : ∀ a b : M, f (a * b) = f a * f b) (a : M) (n : AzNat) :
    f (slidingWindowPowAzNat a n) = f a ^ n.toNat := by
  rw [slidingWindowPowAzNat, map_slidingWindowPowAzNatAux f hmul, hone]
  exact slidingWindowPowAzNat_eq_pow (f a) n

end Azurite
