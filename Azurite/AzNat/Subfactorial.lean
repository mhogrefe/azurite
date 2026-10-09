/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul
import Azurite.AzNat.ToStringBase
import Azurite.AzInt.Add
import Azurite.AzInt.Mul
import Azurite.AzInt.Conversion

/-!
## Subfactorial

`subfactorial n = !n`, the number of derangements of `n` objects (Mathlib's `numDerangements`,
defined by the recurrence `!(n+2) = (n+1) (!n + !(n+1))` and proved equal to the number of
fixed-point-free permutations of `Fin n`).

The computation uses the closed form `!n = Σ_{k=0}^{n} (−1)^k n!/k! = Σ_{k=0}^{n} (−1)^k
(k+1)(k+2)⋯n` by **binary splitting**: for an interval `(a, b]` let `P(a, b) = (a+1)⋯b` and
`T(a, b) = Σ_{k=a+1}^{b} (−1)^k (k+1)⋯b`; then for `a < m < b`

`P(a, b) = P(a, m) P(m, b)`, `T(a, b) = T(a, m) P(m, b) + T(m, b)`,

and `!n = P(0, n) + T(0, n)`.  Splitting at the midpoint keeps every multiplication balanced,
for a total cost of `O(M(n log n) log n)`; the sum `T` is carried as an `AzInt`.
-/

namespace Azurite.AzNat

/-- Binary splitting on `(a, b]`: `(P(a, b), T(a, b))` with `P(a, b) = (a+1)⋯b` and
`T(a, b) = Σ_{k=a+1}^{b} (−1)^k (k+1)⋯b`.  `fuel ≥ b − a` suffices (each half is shorter by at
least one). -/
def subfactorialSplit : Nat → Nat → Nat → AzNat × AzInt
  | 0, _, _ => (1, 0)
  | fuel + 1, a, b =>
    if b ≤ a then (1, 0)
    else if b = a + 1 then (ofNat b, if b % 2 = 0 then 1 else -1)
    else
      let m := (a + b) / 2
      let l := subfactorialSplit fuel a m
      let r := subfactorialSplit fuel m b
      (l.1 * r.1, l.2 * r.1.toAzInt + r.2)

/-- **Subfactorial** `!n`, the number of derangements of `n` objects. -/
def subfactorial (n : Nat) : AzNat :=
  let r := subfactorialSplit n 0 n
  (r.1.toAzInt + r.2).natAbs

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def S (n : Nat) : String := AzNat.toString (subfactorial n)

#guard S 0 == "1"
#guard S 1 == "0"
#guard S 2 == "1"
#guard S 3 == "2"
#guard S 4 == "9"
#guard S 5 == "44"
#guard S 6 == "265"
#guard S 7 == "1854"
#guard S 8 == "14833"
#guard S 9 == "133496"
#guard S 10 == "1334961"
#guard S 20 == "895014631192902121"
#guard S 30 == "97581073836835777732377428235481"
#guard (S 100).length == 158
#guard (S 100).take 20 == "34332795984163804765"
#guard (S 100).drop (158 - 20) == "53756854137069878601"
#guard (S 1000).length == 2568
#guard (S 1000).take 20 == "14803000037166908036"
#guard (S 1000).drop (2568 - 20) == "44750044815550686001"
-- agreement with the recurrence `!(n+2) = (n+1) (!n + !(n+1))`, iterated on pairs
private def naivePair : Nat → AzNat × AzNat
  | 0 => (1, 0)
  | n + 1 => let p := naivePair n; (p.2, ofNat (n + 1) * (p.1 + p.2))
private def naive (n : Nat) : AzNat := (naivePair n).1
#guard (List.range 300).all fun n => subfactorial n == naive n
#guard subfactorial 2000 == naive 2000

end Tests
