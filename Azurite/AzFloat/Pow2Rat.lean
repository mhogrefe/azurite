/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Pow2Bracket

/-!
## `2^q` for a rational `q`

`pow2RatPrecRound q p mode` is `2^q` correctly rounded to precision `p` in `mode`, for a rational
`q`, with the comparison against the exact value; `pow2Rat q p` rounds to nearest.  An integer
`q` (denominator `1`) gives the exact power of two; otherwise the certified Ziv loop (no fuel)
runs over `pow2RatApprox`, total because `2^q` is irrational for every non-integer rational `q`.
The specification `pow2RatPrecRound_eq` is in `Equiv/Pow2Rat.lean`.
-/

namespace Azurite.AzFloat

/-- `2^q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def pow2RatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else if hd : q.den.toNat = 1 then setPrecRound (powerOf2 (AzInt.mkNorm q.sign q.num)) p mode
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified (pow2RatApprox q) p mode (p + zivGuardBits)
      (pow2RatApprox_isSome_exists p mode q hd (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `2^q` rounded to nearest at precision `p`. -/
def pow2Rat (q : AzRat) (p : Nat) : AzFloat := (pow2RatPrecRound q p .Nearest).1

end Azurite.AzFloat
