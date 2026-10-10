/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.DoubleFactorial
import Azurite.AzNat.Pow
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
## Multifactorial

`multiFactorial n m = n!⁽ᵐ⁾ = n (n − m)(n − 2m) ⋯`, the product of the positive terms of the
progression; `1` for `n = 0`, and by convention `1` for `m = 0`.  Mathlib has `Nat.factorial`
and `Nat.doubleFactorial` but no multifactorial, so the reference `Nat.multiFactorial` is
defined here first, as the closed-form product `∏_{i < ⌈n/m⌉} (n − i m)`.

The `AzNat` version: `m = 1` and `m = 2` are the factorial and the double factorial.  Otherwise
write `n = q m + r` with `r < m`.  If `r = 0` the product is `∏_{i=1}^{q} i m = m^q · q!`, a power
times a factorial (the prime-factorization factorial).  If `r ≠ 0` the terms `r, r + m, …, n`
have no factorial structure, and their product is formed by a balanced pairing tree
(`product`), i.e. binary splitting over the arithmetic progression.
-/

namespace Nat

/-- **Multifactorial** `n!⁽ᵐ⁾ = n (n − m)(n − 2m) ⋯`: the product of the positive terms, that is
of `n − i m` for `i < ⌈n / m⌉`; `1` for `n = 0` or `m = 0`. -/
def multiFactorial (n m : ℕ) : ℕ := ∏ i ∈ Finset.range ((n + m - 1) / m), (n - i * m)

end Nat

namespace Azurite.AzNat

/-- **Multifactorial** `n!⁽ᵐ⁾`: the factorial for `m = 1`, the double factorial for `m = 2`,
`m^q · q!` when `m ∣ n` with `q = n / m`, and a balanced product of the arithmetic progression
otherwise. -/
def multiFactorial (n m : Nat) : AzNat :=
  if m = 0 then 1
  else if m = 1 then factorial n
  else if m = 2 then doubleFactorial n
  else if n % m = 0 then (ofNat m).pow (n / m) * factorial (n / m)
  else product ((List.range (n / m + 1)).map fun i => ofNat (i * m + n % m))

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def M (n m : Nat) : String := AzNat.toString (multiFactorial n m)

#guard M 5 0 == "1"
#guard M 0 1 == "1"
#guard M 10 1 == "3628800"
#guard M 9 2 == "945"
#guard M 10 2 == "3840"
#guard M 0 3 == "1"
#guard M 1 3 == "1"
#guard M 2 3 == "2"
#guard M 3 3 == "3"
#guard M 9 3 == "162"                  -- 9 · 6 · 3
#guard M 10 3 == "280"                 -- 10 · 7 · 4 · 1
#guard M 10 4 == "120"                 -- 10 · 6 · 2
#guard M 12 4 == "384"                 -- 12 · 8 · 4
#guard M 3 5 == "3"
#guard M 23 5 == "129168"              -- 23 · 18 · 13 · 8 · 3
#guard M 7 7 == "7"
#guard M 30 3 == "214277011200"
#guard M 100 3 == "174548867015437739741494347897360069928419328000000000"
#guard (M 1000 7).length == 369
#guard (M 1000 7).take 20 == "12112076869546170857"
#guard (M 999 3).length == 856
#guard (M 999 3).take 20 == "78644044211937704954"
-- agreement with the plain product (`naive m` steps by `m + 1`)
private def naive (m : Nat) : Nat → AzNat
  | 0 => 1
  | n + 1 => ofNat (n + 1) * naive m (n - m)
#guard (List.range 7).all fun m => (List.range 200).all fun n =>
  multiFactorial n (m + 1) == naive m n
#guard multiFactorial 3001 3 == naive 2 3001
#guard multiFactorial 3000 5 == naive 4 3000

end Tests
