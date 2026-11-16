/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.TanhBracket
import Azurite.AzFloat.CscBracket

/-!
## The brackets of `coth x` and `coth q`

`coth x = 1 / tanh x`, odd.  With `v = exp (2a) − 1` for `a = |x| > 0`,

  `coth a = (e^(2a) + 1) / (e^(2a) − 1) = 1 + 2/v`,

a sum of positive terms, decreasing in `v`.  `cothOfExpM1 v lb W` evaluates it on an enclosure
of `v` with outward rounding at `W` bits, where the float `lb` is a positive lower bound of `v`
(the lower end of the enclosure is first raised to it): `lb = 2a` for a float `a`, since
`e^(2a) − 1 ≥ 2a`, and `lb = ⌊2|q|⌋` for a rational.  `cothBracket a e w` applies it to
`expM1Bracket (2a) (e + 1) w` (relative accuracy for a small `a`), `cothRatBracket q w` to
`expM1RatBracket (2|q|) w`.  `cothApprox`, `cothRatApprox` are the pairs of `Roundable`s,
negated and swapped for a negative argument.

**Tiny arguments**: `1/a < coth a ≤ 1/a + a` for `0 < a ≤ 1`, the bounds of the cosecant, so
the tiny-argument tests are `cscTiny?` and `cscTinyRat?` (exact end `1/a` at the open side).

**Large arguments** (`cothNearOne?`): `coth a = exp v'` with `v' = −ln tanh a > 0` and
`v' < 2^(2 − N)` for a natural `1 ≤ N ≤ 2a`: the value is exponentially close to the float `1`,
from above, and `expNearOne? true` rounds it at the exponent `2 − N` without computing anything
(the mirror image of `tanhNearOne?`).

The proofs are in `Equiv/CothBracket.lean`.
-/

namespace Azurite.AzFloat

/-- `1 + 2/v` on an enclosure of `v ≥ lb > 0`, rounded outwards at precision `W`. -/
def cothOfExpM1 (v : Encl) (lb : AzFloat) (W : Nat) : Encl :=
  let two := one <<< AzInt.ofInt 1
  ((addPrecRound one (divPrecRound two v.2 W .Floor).1 W .Floor).1,
    (addPrecRound one (divPrecRound two (maxOf v.1 lb) W .Ceiling).1 W .Ceiling).1)

/-- The bracket of `coth a` at Ziv level `w` for a positive finite float `a < 2^e`. -/
def cothBracket (a : AzFloat) (e : AzInt) (w : Nat) : Encl :=
  cothOfExpM1 (expM1Bracket (a <<< AzInt.ofInt 1) (e + AzInt.ofInt 1) w) (a <<< AzInt.ofInt 1)
    (w + 16)

/-- The bracket of `coth x` as a pair of `Roundable`s: that of `coth |x|`, negated and swapped
when `neg` (`x < 0`). -/
def cothApprox (neg : Bool) (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  enclApprox neg (cothBracket x.abs e w)

/-- The bracket of `coth |q|` at Ziv level `w` for a rational `q ≠ 0`. -/
def cothRatBracket (q : AzRat) (w : Nat) : Encl :=
  cothOfExpM1 (expM1RatBracket (q.abs + q.abs) w)
    (ofAzRatRound (q.abs + q.abs) (w + 16) .Floor).1 (w + 16)

/-- The bracket of `coth q` as a pair of `Roundable`s. -/
def cothRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  enclApprox (!q.sign) (cothRatBracket q w)

/-- **The large-argument path of `coth`**: the rounding of `± coth a` (`pos`: the sign) for
`a > 0` with `N ≤ 2a`, by the tiny-exponent test of the exponential at the exponent
`2 − min N 2^62`.  `none` when `N` is not large enough or the test fails. -/
def cothNearOne? (pos : Bool) (N : Nat) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  let E := AzInt.ofInt (2 - ((min N 4611686018427387904 : Nat) : Int))
  if pos then expNearOne? true E p mode
  else (expNearOne? true E p (-mode)).map fun r => (-r.1, r.2.swap)

end Azurite.AzFloat
