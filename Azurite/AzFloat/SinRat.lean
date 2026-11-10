/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.SinRatBracket

/-!
## The sine of a rational

`sinRatPrecRound q p mode` is `sin q` for an `AzRat` `q`, correctly rounded to precision `p` in
`mode`, with the comparison against the exact value; `sinRat q p` rounds to nearest.  `sin 0 = 0`
exactly; tiny arguments (`|q| < 2^e`, `e ≤ −(p + 72)`) by `sinTinyRat?`; otherwise a certified
Ziv loop (`zivLoopCertified`, no fuel) on `sinRatApprox` (`AzFloat/SinRatBracket.lean`), total
because `sin q` is irrational for every rational `q ≠ 0` (`irrational_sin_rat`).  The
specification `sinRatPrecRound_eq` is in `Equiv/SinRat.lean`.
-/

namespace Azurite.AzFloat

/-- `sin q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless `q = 0`). -/
def sinRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (zero, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    match sinTinyRat? q p mode with
    | some r => r
    | none =>
      zivLoopCertified (sinRatApprox q) p mode (p + zivGuardBits)
        (sinRatApprox_isSome_exists p mode q h0 (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `sin q` rounded to nearest at precision `p`. -/
def sinRat (q : AzRat) (p : Nat) : AzFloat := (sinRatPrecRound q p .Nearest).1

end Azurite.AzFloat
