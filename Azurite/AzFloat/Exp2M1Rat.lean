/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Exp2Bracket

/-!
## `2^q − 1` for a rational `q`

`exp2M1RatPrecRound q p mode` is `2^q − 1` correctly rounded to precision `p` in `mode`, for a
rational `q`, with the comparison against the exact value; `exp2M1Rat q p` rounds to nearest.
`q = 0` gives `0` exactly, an integer `q` (denominator `1`) the exact `2^n − 1` (one correctly
rounded subtraction); otherwise the certified Ziv loop (no fuel) runs over `exp2M1RatApprox`,
total because `2^q − 1` is irrational for every non-integer rational `q`.  The specification
`exp2M1RatPrecRound_eq` is in `Equiv/Exp2M1Rat.lean`.
-/

namespace Azurite.AzFloat

/-- `2^q − 1` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def exp2M1RatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else if h0 : q.num = 0 then (zero, .eq)
  else if hd : q.den.toNat = 1 then
    subPrecRound (powerOf2 (AzInt.mkNorm q.sign q.num)) one p mode
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified (exp2M1RatApprox q) p mode (p + zivGuardBits)
      (exp2M1RatApprox_isSome_exists p mode q h0 hd (p + zivGuardBits)
        (by unfold zivGuardBits; omega))

/-- `2^q − 1` rounded to nearest at precision `p`. -/
def exp2M1Rat (q : AzRat) (p : Nat) : AzFloat := (exp2M1RatPrecRound q p .Nearest).1

end Azurite.AzFloat
