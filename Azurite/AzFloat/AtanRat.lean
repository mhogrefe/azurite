/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AtanRatBracket

/-!
## The arctangent of a rational

`atanRatPrecRound q p mode` is `arctan q` for an `AzRat` `q`, correctly rounded to precision `p`
in `mode`, with the comparison against the exact value; `atanRat q p` rounds to nearest.
`arctan 0 = 0` exactly; tiny arguments (`|q| < 2^e`, `e ≤ −(p + 72)`) by `atanTinyRat?`;
otherwise a certified Ziv loop (`zivLoopCertified`, no fuel) on `atanRatApprox`
(`AzFloat/AtanRatBracket.lean`), total because `arctan q` is irrational for every rational
`q ≠ 0` (`irrational_arctan_rat`).  The argument is never rounded to the target precision: the
bracket follows the rational itself (for `|q| > 1` through the rational `1/|q|`), so e.g.
`arctan (1/3)` is the arctangent of one third and not of the float nearest to it.  The
specification `atanRatPrecRound_eq` is in `Equiv/AtanRat.lean`.
-/

namespace Azurite.AzFloat

/-- `arctan q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless `q = 0`). -/
def atanRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (zero, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    match atanTinyRat? q p mode with
    | some r => r
    | none =>
      zivLoopCertified (atanRatApprox q) p mode (p + zivGuardBits)
        (atanRatApprox_isSome_exists p mode q h0 (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `arctan q` rounded to nearest at precision `p`. -/
def atanRat (q : AzRat) (p : Nat) : AzFloat := (atanRatPrecRound q p .Nearest).1

end Azurite.AzFloat
