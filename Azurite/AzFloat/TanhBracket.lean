/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Bracket
import Azurite.AzFloat.ExpApprox
import Azurite.AzFloat.SinBracket
import Azurite.AzFloat.SinRatBracket
import Azurite.AzRat.Add

/-!
## The brackets of `tanh x` and `tanh q`

With `v = exp (2a) − 1` for `a = |x| > 0`,

  `tanh a = (e^(2a) − 1) / (e^(2a) + 1) = v / (2 + v)`,

increasing in `v`, without cancellation.  `tanhOfExpM1 v W` evaluates it on an enclosure of `v`
with outward rounding at `W` bits (one division for each end); `tanhBracket a e w` applies it to
`expM1Bracket (2a) (e + 1) w` (relative accuracy for a small `a`), and `tanhRatBracket q w` to
`expM1RatBracket (2|q|) w`.  `tanhApprox`, `tanhRatApprox` are the pairs of `Roundable`s,
negated and swapped for a negative argument.

**Tiny arguments**: `|x| − |x|³ ≤ tanh |x| < |x|`, the bounds of the sine, so the tiny-argument
tests are `sinTiny?` and `sinTinyRat?`.

**Large arguments** (`tanhNearOne?`): `tanh a = exp v` with `v = ln tanh a < 0` and
`|v| ≤ 2/(e^(2a) − 1) < 2^(2 − N)` for a natural `1 ≤ N ≤ 2a`.  So the value is exponentially
close to the float `1`, from below, and the tiny-exponent test of the exponential,
`expNearOne? false`, rounds it at the exponent `2 − N` without computing anything; the Ziv
loop would need about `2.9 a` bits.  `N` is capped at `2^62`.

The proofs are in `Equiv/TanhBracket.lean`.
-/

namespace Azurite.AzFloat

/-- `v/(2 + v)` on an enclosure of `v ≥ 0`, rounded outwards at precision `W`. -/
def tanhOfExpM1 (v : Encl) (W : Nat) : Encl :=
  let two := one <<< AzInt.ofInt 1
  let vl := clampNonneg v.1
  ((divPrecRound vl (addPrecRound two vl W .Ceiling).1 W .Floor).1,
    (divPrecRound v.2 (addPrecRound two v.2 W .Floor).1 W .Ceiling).1)

/-- The bracket of `tanh a` at Ziv level `w` for a positive finite float `a < 2^e`. -/
def tanhBracket (a : AzFloat) (e : AzInt) (w : Nat) : Encl :=
  tanhOfExpM1 (expM1Bracket (a <<< AzInt.ofInt 1) (e + AzInt.ofInt 1) w) (w + 16)

/-- The bracket of `tanh x` as a pair of `Roundable`s: that of `tanh |x|`, negated and swapped
when `neg` (`x < 0`). -/
def tanhApprox (neg : Bool) (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  enclApprox neg (tanhBracket x.abs e w)

/-- The bracket of `tanh |q|` at Ziv level `w` for a rational `q ≠ 0`. -/
def tanhRatBracket (q : AzRat) (w : Nat) : Encl :=
  tanhOfExpM1 (expM1RatBracket (q.abs + q.abs) w) (w + 16)

/-- The bracket of `tanh q` as a pair of `Roundable`s. -/
def tanhRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  enclApprox (!q.sign) (tanhRatBracket q w)

/-- **The large-argument path of `tanh`**: the rounding of `± tanh a` (`pos`: the sign) for
`a > 0` with `N ≤ 2a`, by the tiny-exponent test of the exponential at the exponent
`2 − min N 2^62`.  `none` when `N` is not large enough or the test fails. -/
def tanhNearOne? (pos : Bool) (N : Nat) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  let E := AzInt.ofInt (2 - ((min N 4611686018427387904 : Nat) : Int))
  if pos then expNearOne? false E p mode
  else (expNearOne? false E p (-mode)).map fun r => (-r.1, r.2.swap)

/-- A natural `N ≤ 2|x|` for a finite float `x` of exponent `e` (`|x| ≥ 2^(e−1)`): `⌊2|x|⌋`
for `0 ≤ e ≤ 62`, `2^62` above, and `0` for `e < 0`. -/
def tanhFloatN (x : AzFloat) (e : AzInt) : Nat :=
  if e.sign then
    if e.abs.toNat ≤ 62 then (truncToAzInt (x <<< AzInt.ofInt 1)).abs.toNat else 2 ^ 62
  else 0

/-- A natural `N ≤ 2|q|` for a rational `q`: `⌊2 num / den⌋`. -/
def tanhRatN (q : AzRat) : Nat := ((q.num + q.num) / q.den).toNat

end Azurite.AzFloat
