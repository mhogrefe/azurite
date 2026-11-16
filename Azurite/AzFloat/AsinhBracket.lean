/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Bracket
import Azurite.AzFloat.LnBracket
import Azurite.AzFloat.Sqrt
import Azurite.AzFloat.SinBracket
import Azurite.AzFloat.SinRatBracket

/-!
## The brackets of `asinh x` and `asinh q`

`asinh a = ln (a + √(a² + 1))` for `a = |x| > 0`: the argument of the logarithm is a sum of
positive terms, above `1`.  `asinhArg alo W` is a float `y` just below `V = a + √(a² + 1)`
(a product, a sum, a square root and a sum, all rounded down at `W` bits, starting from a float
`alo` just below `a`), with `y ≤ V ≤ y (1 + 8·2^(−W))`; `asinhBracket a w` is
`lnFloorBracket y w` (`AzFloat/LnBracket.lean`: `ln y`, the upper end widened for `V/y`), at
`W = w + 8`.  `asinhRatBracket q w` is the same from `alo = ⌊|q|⌋`.  `asinhApprox`,
`asinhRatApprox` are the pairs of `Roundable`s, negated and swapped for a negative argument.

The logarithm has absolute accuracy, and `asinh a ≈ a` for a small `a`, so the Ziv loops of
`AzFloat/Asinh.lean` start with `leadingZeroBits` more bits, as `lnP1` does.

**Tiny arguments**: `|x| − |x|³ ≤ asinh |x| < |x|`, the bounds of the sine, so the
tiny-argument tests are `sinTiny?` and `sinTinyRat?`.

The proofs are in `Equiv/AsinhBracket.lean`.
-/

namespace Azurite.AzFloat

/-- A float just below `a + √(a² + 1)` from a float `alo` just below `a ≥ 0`, every operation
rounded down at precision `W`. -/
def asinhArg (alo : AzFloat) (W : Nat) : AzFloat :=
  let m := (mulPrecRound alo alo W .Floor).1
  let s := (addPrecRound m one W .Floor).1
  let r := (sqrtPrecRound s W .Floor).1
  (addPrecRound alo r W .Floor).1

/-- The bracket of `asinh a` at Ziv level `w` for a positive finite float `a`. -/
def asinhBracket (a : AzFloat) (w : Nat) : Encl := lnFloorBracket (asinhArg a (w + 8)) w

/-- The bracket of `asinh x` as a pair of `Roundable`s: that of `asinh |x|`, negated and
swapped when `neg` (`x < 0`). -/
def asinhApprox (neg : Bool) (x : AzFloat) (w : Nat) : Roundable × Roundable :=
  enclApprox neg (asinhBracket x.abs w)

/-- The bracket of `asinh |q|` at Ziv level `w` for a rational `q ≠ 0`. -/
def asinhRatBracket (q : AzRat) (w : Nat) : Encl :=
  lnFloorBracket (asinhArg (ofAzRatRound q.abs (w + 8) .Floor).1 (w + 8)) w

/-- The bracket of `asinh q` as a pair of `Roundable`s. -/
def asinhRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  enclApprox (!q.sign) (asinhRatBracket q w)

end Azurite.AzFloat
