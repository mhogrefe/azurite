/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinCosBracket
import Azurite.AzFloat.PowRatBracket

/-!
## The bracket of `sin q` for a rational `q`

`sinRatBracket q w` encloses `sin |q|` for an `AzRat` `q` at Ziv level `w`: with
`eq = ratExpBound q` and `W = cosWork eq w`, the floats `⌊q⌋_W ≤ q ≤ ⌈q⌉_W`; `sinBracket c eq w`
at the one `c` nearer zero (`⌊q⌋_W` for `q > 0`, `⌈q⌉_W` for `q < 0`) encloses `sin |c|`, and the
Lipschitz bound `|sin |q| − sin |c|| ≤ ⌈q⌉_W − ⌊q⌋_W ≤ E` widens it.  `sinRatApprox` negates and
swaps the ends for `q < 0`.

**Tiny arguments** (`sinTinyCore?`, `sinTinyRat?`): `−sin |q| ∈ (−|q|, −|q| + |q|³]`, with
`−|q|` given by its rounding procedure at the open side of the test of `roundingPossible`.
-/

namespace Azurite.AzFloat

/-- The bracket of `sin |q|` at Ziv level `w` for a rational `q`. -/
def sinRatBracket (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  let eq := ratExpBound q
  let W := cosWork eq w
  let xlo := (ofAzRatRound q W .Floor).1
  let xhi := (ofAzRatRound q W .Ceiling).1
  let E := (subPrecRound xhi xlo 64 .Ceiling).1
  Encl.widen W (sinBracket (if q.sign then xlo else xhi) eq w) (Encl.exact E)

/-- The bracket of `sin q` as a pair of `Roundable`s (negated and swapped for `q < 0`). -/
def sinRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  let b := sinRatBracket q w
  if q.sign then (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)
  else (fun p mode => setPrecRound (-b.2) p mode, fun p mode => setPrecRound (-b.1) p mode)

/-- The tiny-argument test for `± sin a`, `0 < a < 2^e`, with `−a` given by its rounding
procedure `nx` and a float `nxHi ≥ −a`: `−sin a ∈ (−a, −a + a³]`.  `neg`: the value is `−sin a`
(tested directly); otherwise `sin a` (the negated mode, the result negated). -/
def sinTinyCore? (neg : Bool) (nx : Roundable) (nxHi : AzFloat) (e : AzInt) (w p : Nat)
    (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  if e.sign = false ∧ w + 8 ≤ e.abs.toNat then
    let hi := (addPrecRound nxHi (((one <<< e) <<< e) <<< e) (w + 8) .Ceiling).1
    let r := roundingPossible nx (fun P M => setPrecRound hi P M) p (if neg then mode else -mode)
    if neg then r else r.map fun r => (-r.1, r.2.swap)
  else none

/-- `−|q|` as a rational. -/
def negAbsRat (q : AzRat) : AzRat := if q.sign then -q else q

/-- The tiny-argument path of `sin q`. -/
def sinTinyRat? (q : AzRat) (p : Nat) (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  let w := p + zivGuardBits
  sinTinyCore? (!q.sign) (fun P M => ofAzRatRound (negAbsRat q) P M)
    (ofAzRatRound (negAbsRat q) (w + 8) .Ceiling).1 (ratExpBound q) w p mode

end Azurite.AzFloat
