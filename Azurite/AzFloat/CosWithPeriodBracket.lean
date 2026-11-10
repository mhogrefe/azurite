/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosBracket
import Azurite.AzFloat.Conversion
import Azurite.AzRat.Construct

/-!
## The bracket of `cos (2πr)` for a rational `r ∈ [0, 1)`

For `cos (2π x / u)` (`AzFloat/CosWithPeriod.lean`) the argument `x/u = m 2^E / u` is reduced
exactly: `periodFrac m E u` is the fractional part of `m 2^E / u` as a reduced `AzRat`
(`(m 2^E mod u) / u` for `E ≥ 0`, `(m mod u 2^(−E)) / (u 2^(−E))` for `E < 0`), so that
`cos (2π x / u) = cos (2π r)` with `r ∈ [0, 1)`, and the reduced denominator of `r` decides
whether the value is rational (Niven: exactly for the denominators `1, 2, 3, 4, 6`).

`cosPeriodBracket r w` encloses `cos (2πr)` at Ziv level `w`: with `W = cosWork 3 w`, the float
`t = ⌊2 ⌊r⌋_W · lo⌋_W` (`lo` the lower end of `piBracket W`) satisfies `0 ≤ 2πr − t ≤ 48·2^(−W)`,
so `cosBracket t 3 w` widened by `2^(6−W)` encloses `cos (2πr)` (Lipschitz).
-/

namespace Azurite.AzFloat

/-- The fractional part of `m 2^E / u` as a reduced rational (`u ≠ 0`). -/
def periodFrac (m : AzNat) (E : AzInt) (u : AzNat) : AzRat :=
  if E.sign then AzRat.ofAzNats ((m <<< E.abs.toNat) % u) u
  else
    let D := u <<< E.abs.toNat
    AzRat.ofAzNats (m % D) D

/-- The fractional part of `|q| / u` for a rational `q = ±n/d` as a reduced rational
(`u ≠ 0`): `(n mod d u) / (d u)`. -/
def periodFracRat (q : AzRat) (u : AzNat) : AzRat :=
  let D := q.den * u
  AzRat.ofAzNats (q.num % D) D

/-- The bracket of `cos (2πr)` at Ziv level `w` for a rational `r ∈ [0, 1)`. -/
def cosPeriodBracket (r : AzRat) (w : Nat) : AzFloat × AzFloat :=
  let W := cosWork (AzInt.ofInt 3) w
  let P := piBracket W
  let a := (ofAzRatRound r W .Floor).1
  let t := (mulPrecRound (a <<< AzInt.ofInt 1) P.1 W .Floor).1
  let E := one <<< AzInt.ofInt (6 - W)
  Encl.widen W (cosBracket t (AzInt.ofInt 3) w) (Encl.exact E)

/-- `cosPeriodBracket` as a pair of `Roundable`s for the Ziv loop. -/
def cosPeriodApprox (r : AzRat) (w : Nat) : Roundable × Roundable :=
  let b := cosPeriodBracket r w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

end Azurite.AzFloat
