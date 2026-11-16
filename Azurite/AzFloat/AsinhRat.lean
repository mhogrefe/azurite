/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AsinhBracket
import Azurite.AzFloat.LnP1

/-!
## The inverse hyperbolic sine of a rational

`asinhRatPrecRound q p mode` is `asinh q = ln (q + √(q² + 1))` for an `AzRat` `q`, correctly
rounded to precision `p` in `mode`, with the comparison against the exact value;
`asinhRat q p` rounds to nearest.  `asinh 0 = 0` exactly; tiny arguments by `sinTinyRat?`
(`|q| − |q|³ ≤ asinh |q| < |q|`); otherwise a certified Ziv loop (`zivLoopCertified`, no fuel)
on `asinhRatApprox` (`AzFloat/AsinhBracket.lean`), started with the leading zero bits of a
small `q`, total because `asinh q` is irrational for every rational `q ≠ 0`.  The function is
odd in `q`.  The specification `asinhRatPrecRound_eq` is in `Equiv/Asinh.lean`.
-/

namespace Azurite.AzFloat

/-- `asinh q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless `q = 0`). -/
def asinhRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (zero, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    match sinTinyRat? q p mode with
    | some r => r
    | none =>
      zivLoopCertified (asinhRatApprox q) p mode
        (p + zivGuardBits + leadingZeroBits (ratExpBound q))
        (asinhRatApprox_isSome_exists p mode q h0 _ (by unfold zivGuardBits; omega))

/-- `asinh q` rounded to nearest at precision `p`. -/
def asinhRat (q : AzRat) (p : Nat) : AzFloat := (asinhRatPrecRound q p .Nearest).1

end Azurite.AzFloat
