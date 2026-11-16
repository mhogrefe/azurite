/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Bracket
import Azurite.AzFloat.LnBracket
import Azurite.AzFloat.TanBracket
import Azurite.AzFloat.TanRatBracket
import Azurite.AzRat.Add
import Azurite.AzRat.Sub

/-!
## The brackets of `atanh x` and `atanh q`

`atanh a = (1/2) ln ((1 + a)/(1 − a))` for `0 < a = |x| < 1`.  `atanhArg su df W` is the float
`⌊su / df⌋` just below `V = (1 + a)/(1 − a)` from a float `su` just below `1 + a` and a float
`df` just above `1 − a` (`y ≤ V ≤ y (1 + 8·2^(−W))`): for a float argument the rounded sum and
difference, for a rational the roundings of the exact rationals `1 ± |q|`, so that `1 − a`
keeps its relative accuracy next to `1`.  The brackets are half of `lnFloorBracket y w`
(`AzFloat/LnBracket.lean`), at `W = w + 8`.  `atanhApprox`, `atanhRatApprox` are the pairs of
`Roundable`s, negated and swapped for a negative argument.

The logarithm has absolute accuracy, and `atanh a ≈ a` for a small `a`, so the Ziv loops of
`AzFloat/Atanh.lean` start with `leadingZeroBits` more bits, as `lnP1` does.

**Tiny arguments**: `|x| < atanh |x| ≤ |x| + |x|³` for `|x| ≤ 1/4`, the bounds of the tangent,
so the tiny-argument tests are `tanTiny?` and `tanTinyRat?`.

The proofs are in `Equiv/AtanhBracket.lean`.
-/

namespace Azurite.AzFloat

/-- A float just below `(1 + a)/(1 − a)` from floats `su` just below `1 + a` and `df` just
above `1 − a`. -/
def atanhArg (su df : AzFloat) (W : Nat) : AzFloat := (divPrecRound su df W .Floor).1

/-- Half of the logarithm bracket of a float `y` just below `(1 + a)/(1 − a)`. -/
def atanhOfArg (y : AzFloat) (w : Nat) : Encl :=
  let b := lnFloorBracket y w
  (b.1 <<< AzInt.ofInt (-1), b.2 <<< AzInt.ofInt (-1))

/-- The bracket of `atanh a` at Ziv level `w` for a finite float `0 < a < 1`. -/
def atanhBracket (a : AzFloat) (w : Nat) : Encl :=
  let W := w + 8
  atanhOfArg
    (atanhArg (addPrecRound one a W .Floor).1 (subPrecRound one a W .Ceiling).1 W) w

/-- The bracket of `atanh x` as a pair of `Roundable`s: that of `atanh |x|`, negated and
swapped when `neg` (`x < 0`). -/
def atanhApprox (neg : Bool) (x : AzFloat) (w : Nat) : Roundable × Roundable :=
  enclApprox neg (atanhBracket x.abs w)

/-- The bracket of `atanh |q|` at Ziv level `w` for a rational `0 < |q| < 1`. -/
def atanhRatBracket (q : AzRat) (w : Nat) : Encl :=
  let W := w + 8
  atanhOfArg
    (atanhArg (ofAzRatRound (1 + q.abs) W .Floor).1 (ofAzRatRound (1 - q.abs) W .Ceiling).1 W) w

/-- The bracket of `atanh q` as a pair of `Roundable`s. -/
def atanhRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  enclApprox (!q.sign) (atanhRatBracket q w)

end Azurite.AzFloat
