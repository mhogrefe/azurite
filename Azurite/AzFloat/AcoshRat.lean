/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AcoshBracket

/-!
## The inverse hyperbolic cosine of a rational

`acoshRatPrecRound q p mode` is `acosh q = ln (q + √(q² − 1))` for an `AzRat` `q ≥ 1`,
correctly rounded to precision `p` in `mode`, with the comparison against the exact value;
`acoshRat q p` rounds to nearest.  `NaN` for `q < 1`; `acosh 1 = 0` exactly; otherwise a
certified Ziv loop (`zivLoopCertified`, no fuel) on `acoshRatApprox`
(`AzFloat/AcoshBracket.lean`, with the exact rationals `q − 1` and `q + 1`), started with half
the leading zero bits of `q − 1`, total because `acosh q` is irrational for every rational
`q > 1`.  The specification `acoshRatPrecRound_eq` is in `Equiv/Acosh.lean`.
-/

namespace Azurite.AzFloat

/-- `acosh q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `q < 1`, and for `p = 0` unless `q = 1`). -/
def acoshRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hc : q.sign = true ∧ q.den ≤ q.num then
    if h1 : q.num = q.den then (zero, .eq)
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      zivLoopCertified (acoshRatApprox q) p mode
        (p + zivGuardBits + acoshExtra (ofAzRatRound (q - 1) 2 .Floor).1)
        (acoshRatApprox_isSome_exists p mode q (one_lt_toRat_of_acosh_cond q hc h1) _
          (by unfold zivGuardBits; omega))
  else (nan, .eq)

/-- `acosh q` rounded to nearest at precision `p`. -/
def acoshRat (q : AzRat) (p : Nat) : AzFloat := (acoshRatPrecRound q p .Nearest).1

end Azurite.AzFloat
