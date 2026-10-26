/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.ExpApprox

/-!
## `exp q − 1` for a rational `q`

`expM1RatPrecRound q p mode` is `exp q − 1` correctly rounded to precision `p` in `mode`, for a
rational `q`, with the comparison against the exact value; `expM1Rat q p` rounds to nearest.
The bracket (`expM1RatApprox`) is `expM1Bracket` at the float `y = ⌊q⌋_W` below `q`
(`W = w + 16 + size (num q)`), with the exponent `⌊log₂ |q|⌋ + 2` of `q` itself for the
cancellation compensation, the upper end widened by `⌈exp y⌉ · 2^(e + 2 − W) ≥ 2 (q − y) exp y`
— a correction proportional to `|q|`, so small arguments lose nothing.  The certified Ziv loop
needs no fuel since `exp q − 1` is irrational for every rational `q ≠ 0`; `exp 0 − 1 = 0`
exactly.  The specification `expM1RatPrecRound_eq` is in `Equiv/ExpM1Rat.lean`.
-/

namespace Azurite.AzFloat

/-- `exp q − 1` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def expM1RatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else if h0 : q.num = 0 then (zero, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified (expM1RatApprox q) p mode (p + zivGuardBits)
      (expM1RatApprox_isSome_exists p mode q h0 (p + zivGuardBits)
        (by unfold zivGuardBits; omega))

/-- `exp q − 1` rounded to nearest at precision `p`. -/
def expM1Rat (q : AzRat) (p : Nat) : AzFloat := (expM1RatPrecRound q p .Nearest).1

end Azurite.AzFloat
