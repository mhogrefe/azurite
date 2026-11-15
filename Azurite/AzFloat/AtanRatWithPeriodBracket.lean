/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanRatBracket
import Azurite.AzFloat.AtanWithPeriodBracket

/-!
## The bracket of `arctan (q) u / (2π)` for a rational `q`

* `atanRatAbsEncl q w` is an enclosure of `arctan |q|` with a nonnegative lower end and width at
  most `2^(−w)`: `atanRatBracket q w` with the lower end clamped at `0`, except for a **tiny**
  argument (`|q| < 2^e` with `e = ratExpBound q`, `2e ≤ −(w + 8)`), where it is
  `[⌊|q|⌋ − ⌊|q|⌋ 2^(2e), ⌈|q|⌉]` at `w + 64` bits, at a cost independent of the exponent.
* `atanPeriodApproxOf neg A u V` is the pair of `Roundable`s of `atanPeriodScale A u V`, negated
  and swapped when `neg`; `atanRatPeriodApprox q u w` is the instance for the Ziv loop of
  `AzFloat/AtanRatWithPeriod.lean`.

The proofs are in `Equiv/AtanRatWithPeriodBracket.lean`.
-/

namespace Azurite.AzFloat

/-- An enclosure of `arctan |q|` with a nonnegative lower end, for a rational `q` at level
`w`. -/
def atanRatAbsEncl (q : AzRat) (w : Nat) : Encl :=
  let e := ratExpBound q
  if e.sign = false ∧ w + 8 ≤ 2 * e.abs.toNat then
    let V := w + 64
    let l := (ofAzRatRound q.abs V .Floor).1
    let h := (ofAzRatRound q.abs V .Ceiling).1
    (clampNonneg (subPrecRound l ((l <<< e) <<< e) V .Floor).1, h)
  else
    let a := atanRatBracket q w
    (clampNonneg a.1, a.2)

/-- The pair of `Roundable`s of `± A u / (2π)` (`neg`: negated and swapped). -/
def atanPeriodApproxOf (neg : Bool) (A : Encl) (u : AzNat) (V : Nat) : Roundable × Roundable :=
  let b := atanPeriodScale A u V
  if neg then (fun p mode => setPrecRound (-b.2) p mode, fun p mode => setPrecRound (-b.1) p mode)
  else (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bracket of `arctan (q) u / (2π)` as a pair of `Roundable`s. -/
def atanRatPeriodApprox (q : AzRat) (u : AzNat) (w : Nat) : Roundable × Roundable :=
  atanPeriodApproxOf (!q.sign) (atanRatAbsEncl q w) u (w + 64)

end Azurite.AzFloat
