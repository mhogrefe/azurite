/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AtanhBracket
import Azurite.AzFloat.LnP1

/-!
## The inverse hyperbolic tangent of a rational

`atanhRatPrecRound q p mode` is `atanh q = (1/2) ln ((1 + q)/(1 − q))` for an `AzRat` `q` with
`|q| ≤ 1`, correctly rounded to precision `p` in `mode`, with the comparison against the exact
value; `atanhRat q p` rounds to nearest.  `atanh 0 = 0` exactly; `atanh (±1) = ±∞`; `NaN` for
`|q| > 1`; tiny arguments by `tanTinyRat?` (`|q| < atanh |q| ≤ |q| + |q|³`); otherwise a
certified Ziv loop (`zivLoopCertified`, no fuel) on `atanhRatApprox`
(`AzFloat/AtanhBracket.lean`, with the exact rationals `1 ± |q|`), total because `atanh q` is
irrational for every rational `0 < |q| < 1`.  The function is odd in `q`.  The specification
`atanhRatPrecRound_eq` is in `Equiv/Atanh.lean`.
-/

namespace Azurite.AzFloat

/-- `atanh q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `|q| > 1`, and for `p = 0` and `0 < |q| < 1`). -/
def atanhRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (zero, .eq)
  else if q.num = q.den then (infinity q.sign, .eq)
  else if h1 : q.den ≤ q.num then (nan, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    match tanTinyRat? q p mode with
    | some r => r
    | none =>
      zivLoopCertified (atanhRatApprox q) p mode
        (p + zivGuardBits + leadingZeroBits (ratExpBound q))
        (atanhRatApprox_isSome_exists p mode q h0 (abs_toRat_lt_one_of q h1) _
          (by unfold zivGuardBits; omega))

/-- `atanh q` rounded to nearest at precision `p`. -/
def atanhRat (q : AzRat) (p : Nat) : AzFloat := (atanhRatPrecRound q p .Nearest).1

end Azurite.AzFloat
