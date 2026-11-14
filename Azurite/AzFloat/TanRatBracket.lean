/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinCosRatBracket
import Azurite.AzFloat.TanBracket

/-!
## The bracket of `tan q` for a rational `q`

`tanRatBracket q w` encloses `tan |q|` for an `AzRat` `q` at Ziv level `w`: the quotient step
`tanOfSinCos` (`AzFloat/TanBracket.lean`) applied to the joint bracket `sinCosRatBracket q w` of
`sin |q|` and `cos q` — or the dummy bracket `[−1, 1]` while the bracket of `cos q` contains `0`.
`tanRatApprox` negates and swaps the ends for `q < 0`.

**Tiny arguments** (`tanTinyCore?`, `tanTinyRat?`): `tan |q| ∈ (|q|, |q| + |q|³]`, with `|q|`
given by its rounding procedure at the open side of the test of `roundingPossible`.
-/

namespace Azurite.AzFloat

/-- The bracket of `tan |q|` at Ziv level `w` for a rational `q`, or the dummy bracket `[−1, 1]`
when the bracket of `cos q` contains `0`. -/
def tanRatBracket (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  tanOfSinCos (sinCosRatBracket q w) (w + 12)

/-- The bracket of `tan q` as a pair of `Roundable`s (negated and swapped for `q < 0`). -/
def tanRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  negSwapApprox (!q.sign) (tanRatBracket q w)

/-- The tiny-argument test for `± tan a`, `0 < a < 2^e`, with `a` given by its rounding
procedure `ax` and a float `axHi ≥ a`: `tan a ∈ (a, a + a³]`.  `pos`: the value is `tan a`
(tested directly); otherwise `−tan a` (the negated mode, the result negated). -/
def tanTinyCore? (pos : Bool) (ax : Roundable) (axHi : AzFloat) (e : AzInt) (w p : Nat)
    (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  if e.sign = false ∧ w + 8 ≤ e.abs.toNat then
    let hi := (addPrecRound axHi (((one <<< e) <<< e) <<< e) (w + 8) .Ceiling).1
    let r := roundingPossible ax (fun P M => setPrecRound hi P M) p (if pos then mode else -mode)
    if pos then r else r.map fun r => (-r.1, r.2.swap)
  else none

/-- The tiny-argument path of `tan q`. -/
def tanTinyRat? (q : AzRat) (p : Nat) (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  let w := p + zivGuardBits
  tanTinyCore? q.sign (fun P M => ofAzRatRound q.abs P M)
    (ofAzRatRound q.abs (w + 8) .Ceiling).1 (ratExpBound q) w p mode

end Azurite.AzFloat
