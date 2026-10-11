/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Fibonacci
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.AzNat.Equiv.Square.Dispatch
import Azurite.AzNat.Equiv.ShiftLeft
import Mathlib.Data.Nat.Fib.Basic

/-!
## Correctness of `AzNat.fibonacci` and `AzNat.fibonacciPair`

`toNat_fibonacci : (fibonacci n).toNat = Nat.fib n`, and the pair invariant
`toNat_fibonacciPair : (fibonacciPair n).1.toNat = Nat.fib n ∧
(fibonacciPair n).2.toNat + Nat.fib n = Nat.fib (n + 1)` (so the second component is
`Nat.fib (n − 1)` for `n ≥ 1`, `toNat_fibonacciPair_snd`).  The doubling step rests on Mathlib's
`Nat.fib_two_mul` and `Nat.fib_two_mul_add_one`.
-/

namespace Azurite.AzNat

/-- The pair invariant: `a = F_n` and `b + F_n = F_{n+1}`. -/
def FibPair (n : ℕ) (p : AzNat × AzNat) : Prop :=
  p.1.toNat = Nat.fib n ∧ p.2.toNat + Nat.fib n = Nat.fib (n + 1)

theorem fibPair_double {m : ℕ} {a b : AzNat} (h : FibPair m (a, b)) (odd : Bool) :
    FibPair (2 * m + if odd then 1 else 0) (fibonacciDouble a b odd) := by
  obtain ⟨ha, hb⟩ := h
  simp only at ha hb
  have h2m : Nat.fib (2 * m) = a.toNat * (a.toNat + 2 * b.toNat) := by
    rw [Nat.fib_two_mul, ← hb, ← ha]
    congr 1
    omega
  have h2m1 : Nat.fib (2 * m + 1) = (b.toNat + a.toNat) ^ 2 + a.toNat ^ 2 := by
    rw [Nat.fib_two_mul_add_one, ← hb, ← ha]
  have h2m2 : Nat.fib (2 * m + 2) = Nat.fib (2 * m) + Nat.fib (2 * m + 1) := Nat.fib_add_two
  have hc : (a * (a + (b <<< 1))).toNat = a.toNat * (a.toNat + 2 * b.toNat) := by
    rw [toNat_mul, toNat_add, toNat_hShiftLeft, Nat.shiftLeft_eq, pow_one, mul_comm b.toNat]
  have hd : (square a + square b).toNat = a.toNat ^ 2 + b.toNat ^ 2 := by
    rw [toNat_add, toNat_square, toNat_square]
  unfold fibonacciDouble FibPair
  cases odd
  · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    refine ⟨by rw [hc, h2m], ?_⟩
    rw [hd, h2m, h2m1]
    ring
  · simp only [↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [toNat_add, hc, hd, h2m1]
      ring
    · rw [hc, show 2 * m + 1 + 1 = 2 * m + 2 by ring, h2m2, h2m]

theorem fibPair_go : ∀ (fuel n : ℕ), n ≤ fuel → FibPair n (fibonacciPair.go fuel n)
  | 0, n, h => by
    have : n = 0 := by omega
    subst this
    exact ⟨rfl, rfl⟩
  | fuel + 1, n, h => by
    unfold fibonacciPair.go
    split_ifs with h0
    · subst h0; exact ⟨rfl, rfl⟩
    · have ih := fibPair_go fuel (n / 2) (by omega)
      have := fibPair_double ih (decide (n % 2 = 1))
      have hn : 2 * (n / 2) + (if decide (n % 2 = 1) = true then 1 else 0) = n := by
        by_cases hodd : n % 2 = 1
        · simp only [decide_eq_true hodd, ↓reduceIte]; omega
        · simp only [decide_eq_false hodd, Bool.false_eq_true, ↓reduceIte]; omega
      rw [hn] at this
      exact this

/-- **Correctness of `fibonacciPair`**: `F_n`, and the companion with `b + F_n = F_{n+1}`. -/
theorem toNat_fibonacciPair (n : ℕ) :
    (fibonacciPair n).1.toNat = Nat.fib n ∧
      (fibonacciPair n).2.toNat + Nat.fib n = Nat.fib (n + 1) :=
  fibPair_go n n le_rfl

/-- The second component is `F_{n−1}` for `n ≥ 1`. -/
theorem toNat_fibonacciPair_snd (n : ℕ) (h : 0 < n) :
    (fibonacciPair n).2.toNat = Nat.fib (n - 1) := by
  have := (toNat_fibonacciPair n).2
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.fib_add_two] at this
  simp only [Nat.add_sub_cancel]
  omega

theorem fibonacciPair_zero : fibonacciPair 0 = (0, 1) := rfl

/-- **Correctness of `fibonacci`.** -/
theorem toNat_fibonacci (n : ℕ) : (fibonacci n).toNat = Nat.fib n :=
  (toNat_fibonacciPair n).1

end Azurite.AzNat
