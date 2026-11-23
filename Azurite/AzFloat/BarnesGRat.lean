/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BarnesG
import Azurite.AzFloat.LnGammaBracket
import Azurite.AzRat.Div

/-!
## The Barnes `G`-function of a rational

`barnesGRatPrecRound q p mode` is `G(q)` for an `AzRat` `q`, rounded to precision `p` in `mode`
with the comparison against the exact value; `barnesGRat q p` rounds to nearest.  The bracket is
that of the float function (`barnesGCoreOf`, `AzFloat/BarnesGBracket.lean`) with the argument
entering as a `BarnesIn`:

* the enclosure of `q` by its roundings down and up at `V + eb + 32` bits (`eb` the bits of
  `|q|`), so that its width is below `2^(−V)`;
* the shift from the integer part `⌊|q|⌋` (`barnesRatShift`);
* the factors `|q + k| = |N + k D| / D` for `q = N/D`: the integer `|N + k D|` is exact and
  short, and it is multiplied by one lower bound of `1/D` (`barnesRatFrac`) — a short
  multiplication a step, as for a float.

**Special values**: `G` is `0` exactly at `0, −1, −2, …`; a positive integer up to
`barnesGExactBound p` is evaluated exactly (`barnesGNat`).  **Fuel** as for a float
(`barnesGRatFuel`: `64` more doublings for a negative argument); the specification is
`barnesGRatPrecRoundFuel_zivSpec` (`Equiv/BarnesGRat.lean`).
-/

namespace Azurite.AzFloat

/-- The shift `N` of a rational at `n`: `q + N > n + 1`. -/
def barnesRatShift (q : AzRat) (n : Nat) : Nat :=
  if q.sign then azIntPos ((AzNat.ofNat (n + 2)).toAzInt - (q.num / q.den).toAzInt)
  else n + 3 + (q.num / q.den).toNat

/-- The sign of `q + k` (`true`: negative) and a lower bound of `|q + k|` within `e^(9u)`,
`u = 2^(−V)`: the exact integer `|N + k D|` times a lower bound of `1/D`.  `none` when
`q + k = 0`. -/
def barnesRatFrac (q : AzRat) (V : Nat) : Nat → Option (Bool × AzFloat) :=
  let inv := (Encl.div V (Encl.exact one) (Encl.exact (ofAzNat q.den))).1
  let t0 := AzInt.mkNorm q.sign q.num
  let d := q.den.toAzInt
  fun k =>
    let t := t0 + (AzNat.ofNat k).toAzInt * d
    if t.abs = 0 then none
    else some (!t.sign, (mulPrecRound (ofAzNat t.abs) inv V .Floor).1)

/-- The bits of `|q|`: `|q| < 2^(barnesRatExp q)`. -/
def barnesRatExp (q : AzRat) : Nat := azIntPos (expOf (ofAzNat (q.num / q.den + 1)))

/-- A rational as the argument of the bracket. -/
def barnesRatIn (q : AzRat) : BarnesIn where
  X := fun V => lnGammaRatEncl q (V + barnesRatExp q)
  shift := barnesRatShift q
  frac := barnesRatFrac q
  eb := barnesRatExp q

/-- **`G(q)` rounded to precision `p` with `mode`, with the fuel of the Ziv loop explicit**,
and the comparison with the exact value.  The specification is
`barnesGRatPrecRoundFuel_zivSpec` (`Equiv/BarnesGRat.lean`). -/
def barnesGRatPrecRoundFuel (fuel : Nat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if q.den = 1 then
    if q.num = 0 ∨ q.sign = false then (zero, .eq)
    else if p = 0 then (nan, .eq)
    else if le (ofAzNat q.num) (ofAzNat (AzNat.ofNat (barnesGExactBound p))) then
      setPrecRound (ofAzNat (barnesGNat q.num.toNat)) p mode
    else zivLoop (barnesGApproxOf (barnesRatIn q)) p mode fuel (max 64 (p + 32))
  else if p = 0 then (nan, .eq)
  else zivLoop (barnesGApproxOf (barnesRatIn q)) p mode fuel (max 64 (p + 32))

/-- The fuel of `G` at a rational: that of `Γ`, and `64` more doublings for a negative
argument (practically unbounded: no `NaN` for want of fuel there). -/
def barnesGRatFuel (q : AzRat) (p : Nat) : Nat :=
  if q.sign then gammaFuel p else gammaFuel p + 64

/-- `G(q)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0`, or if the fuel runs out). -/
def barnesGRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  barnesGRatPrecRoundFuel (barnesGRatFuel q p) q p mode

/-- `G(q)` rounded to nearest at precision `p`. -/
def barnesGRat (q : AzRat) (p : Nat) : AzFloat := (barnesGRatPrecRound q p .Nearest).1

end Azurite.AzFloat
