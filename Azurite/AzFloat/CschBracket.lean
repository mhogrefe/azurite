/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinhRatBracket

/-!
## The brackets of `csch x` and `csch q`

`csch x = 1 / sinh x`, odd.  `cschOfSinh s lb W` is the reciprocal of an enclosure `s` of
`S = sinh a > 0` with outward rounding at `W` bits, where the float `lb` is a positive lower
bound of `S` (the lower end of `s` is first raised to it): `lb = a` for a float `a = |x|`, since
`sinh a > a`, and `lb = ⌊|q|⌋` for a rational.  `cschBracket a e w` applies it to
`sinhBracket a e w` and `cschRatBracket q w` to `sinhRatBracket q w`, whose relative accuracy
is kept: for a large argument the value is `≈ 2 e^(−|x|)`.  `cschApprox`, `cschRatApprox` are
the pairs of `Roundable`s, negated and swapped for a negative argument.

**Tiny arguments** (`cschTinyCore?`): `1/a − a ≤ csch a < 1/a` for `0 < a ≤ 1`.  For a power of
two `a` the value is exponentially close to the float `1/a`, from below, so the test runs on
`−csch a ∈ (−1/a, −1/a + a]`, with the exact end at the open side (in the negated mode, the
result negated, for a positive argument).  It applies when `|x| < 2^e` with
`2|e| ≥ p + 72`.

The proofs are in `Equiv/CschBracket.lean`.
-/

namespace Azurite.AzFloat

/-- `1/S` on an enclosure of `S ≥ lb > 0`, rounded outwards at precision `W`. -/
def cschOfSinh (s : Encl) (lb : AzFloat) (W : Nat) : Encl :=
  ((divPrecRound one s.2 W .Floor).1, (divPrecRound one (maxOf s.1 lb) W .Ceiling).1)

/-- The bracket of `csch a` at Ziv level `w` for a positive finite float `a < 2^e`. -/
def cschBracket (a : AzFloat) (e : AzInt) (w : Nat) : Encl :=
  cschOfSinh (sinhBracket a e w) a (w + 16)

/-- The bracket of `csch x` as a pair of `Roundable`s: that of `csch |x|`, negated and swapped
when `neg` (`x < 0`). -/
def cschApprox (neg : Bool) (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  enclApprox neg (cschBracket x.abs e w)

/-- The bracket of `csch |q|` at Ziv level `w` for a rational `q ≠ 0`. -/
def cschRatBracket (q : AzRat) (w : Nat) : Encl :=
  cschOfSinh (sinhRatBracket q w) (ofAzRatRound q.abs (w + 16) .Floor).1 (w + 16)

/-- The bracket of `csch q` as a pair of `Roundable`s. -/
def cschRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  enclApprox (!q.sign) (cschRatBracket q w)

/-- The tiny-argument test for `± csch a` (`pos`: the sign), `0 < a < 2^e`, with floats
`alo ≤ a ≤ ahi`: `−csch a ∈ (−1/a, −1/a + a]`. -/
def cschTinyCore? (pos : Bool) (alo ahi : AzFloat) (e : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if e.sign = false ∧ p + zivGuardBits + 8 ≤ 2 * e.abs.toNat then
    let W := p + zivGuardBits + 8
    let lo := -(divPrecRound one alo W .Ceiling).1
    let hi := (addPrecRound (-(divPrecRound one ahi W .Floor).1) ahi W .Ceiling).1
    let r := roundingPossible (fun P M => setPrecRound lo P M) (fun P M => setPrecRound hi P M) p
      (if pos then -mode else mode)
    if pos then r.map fun r => (-r.1, r.2.swap) else r
  else none

/-- The tiny-argument path of `csch x` for a finite `x` of sign `s` and exponent `e`. -/
def cschTiny? (s : Bool) (x : AzFloat) (e : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  cschTinyCore? s x.abs x.abs e p mode

/-- The tiny-argument path of `csch q` for a rational `q`. -/
def cschTinyRat? (q : AzRat) (p : Nat) (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  let W := p + zivGuardBits + 8
  cschTinyCore? q.sign (ofAzRatRound q.abs W .Floor).1 (ofAzRatRound q.abs W .Ceiling).1
    (ratExpBound q) p mode

end Azurite.AzFloat
