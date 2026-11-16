/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinRatBracket
import Azurite.AzFloat.AsinWithPeriodBracket

/-!
## The bracket of `arcsin (q) u / (2π)` for a rational `q`

* `asinRatAbsEncl q w` is an enclosure of `arcsin |q|` with a nonnegative lower end and width at
  most `2^(−w)`: `asinRatBracket q w`, except for a **tiny** argument (`|q| < 2^e` with
  `e = ratExpBound q`, `2e ≤ −(w + 8)`), where it is `[⌊|q|⌋, ⌈|q|⌉ + ⌈|q|⌉ 2^(2e)]` at
  `w + 64` bits, at a cost independent of the exponent.
* `asinRatPeriodApprox q u w` is the pair of `Roundable`s of its `atanPeriodScale` for the Ziv
  loop of `AzFloat/AsinRatWithPeriod.lean`, negated and swapped for `q < 0`.

The proofs are in `Equiv/AsinRatWithPeriodBracket.lean`.
-/

namespace Azurite.AzFloat

/-- An enclosure of `arcsin |q|` with a nonnegative lower end, for a rational `0 < |q| < 1` at
level `w`. -/
def asinRatAbsEncl (q : AzRat) (w : Nat) : Encl :=
  let e := ratExpBound q
  if e.sign = false ∧ w + 8 ≤ 2 * e.abs.toNat then
    let V := w + 64
    let l := (ofAzRatRound q.abs V .Floor).1
    let h := (ofAzRatRound q.abs V .Ceiling).1
    (l, (addPrecRound h ((h <<< e) <<< e) V .Ceiling).1)
  else asinRatBracket q w

/-- The bracket of `arcsin (q) u / (2π)` as a pair of `Roundable`s. -/
def asinRatPeriodApprox (q : AzRat) (u : AzNat) (w : Nat) : Roundable × Roundable :=
  enclApprox (!q.sign) (atanPeriodScale (asinRatAbsEncl q w) u (w + 64))

end Azurite.AzFloat
