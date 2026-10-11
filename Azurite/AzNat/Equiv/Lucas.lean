/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Lucas
import Azurite.AzNat.Equiv.Fibonacci
import Azurite.AzNat.Equiv.Sub

/-!
## Correctness of `AzNat.lucasNumber` and `AzNat.lucasNumberPair`

`toNat_lucasNumber : (lucasNumber n).toNat = Nat.lucas n` and
`toNat_lucasNumberPair_snd : (lucasNumberPair n).2.toNat = Nat.lucas (n − 1)` for `n ≥ 1`,
through the identity `L_n + F_n = 2 F_{n+1}` (`Nat.lucas_add_fib`) and the Fibonacci pair
invariant.
-/

namespace Nat

/-- `L_n + F_n = 2 F_{n+1}`, the link between the Lucas and the Fibonacci numbers. -/
theorem lucas_add_fib : ∀ n : ℕ, lucas n + fib n = 2 * fib (n + 1)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    rw [lucas_add_two, fib_add_two, show n + 2 + 1 = (n + 1) + 2 by ring, fib_add_two]
    have h1 := lucas_add_fib n
    have h2 := lucas_add_fib (n + 1)
    omega

end Nat

namespace Azurite.AzNat

/-- **Correctness of `lucasNumber`.** -/
theorem toNat_lucasNumber (n : ℕ) : (lucasNumber n).toNat = Nat.lucas n := by
  obtain ⟨ha, hb⟩ := toNat_fibonacciPair n
  have hL := Nat.lucas_add_fib n
  unfold lucasNumber lucasNumberPair
  dsimp only
  rw [toNat_add, toNat_hShiftLeft, Nat.shiftLeft_eq, pow_one]
  omega

/-- The second component of the pair is `L_{n−1}` for `n ≥ 1`. -/
theorem toNat_lucasNumberPair_snd (n : ℕ) (h : 0 < n) :
    (lucasNumberPair n).2.toNat = Nat.lucas (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨ha, hb⟩ := toNat_fibonacciPair (k + 1)
  rw [show k + 1 + 1 = k + 2 by ring] at hb
  have hL := Nat.lucas_add_fib k
  have hF : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
  have hb' : (fibonacciPair (k + 1)).2.toNat = Nat.fib (k + 2) - Nat.fib (k + 1) := by omega
  unfold lucasNumberPair
  dsimp only
  rw [toNat_sub, toNat_hShiftLeft, Nat.shiftLeft_eq, pow_one, Nat.add_sub_cancel, ha, hb']
  omega

theorem toNat_lucasNumberPair_fst (n : ℕ) : (lucasNumberPair n).1.toNat = Nat.lucas n :=
  toNat_lucasNumber n

/-- `lucasNumberPair 0 = (2, 0)`: the second component is the truncated `L_{−1} = −1`. -/
theorem toNat_lucasNumberPair_zero :
    (lucasNumberPair 0).1.toNat = 2 ∧ (lucasNumberPair 0).2.toNat = 0 := by
  refine ⟨toNat_lucasNumber 0, ?_⟩
  obtain ⟨ha, hb⟩ := toNat_fibonacciPair 0
  unfold lucasNumberPair
  dsimp only
  rw [toNat_sub, toNat_hShiftLeft, Nat.shiftLeft_eq, pow_one]
  simp only [Nat.fib_zero] at ha hb
  omega

end Azurite.AzNat
