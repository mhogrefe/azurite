/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AcosRatBracket
import Azurite.AzFloat.PiConstants

/-!
## The arccosine of a rational

`acosRatPrecRound q p mode` is `arccos q` for an `AzRat` `q`, correctly rounded to precision `p`
in `mode`, with the comparison against the exact value; `acosRat q p` rounds to nearest.

Special values, as for the float `acosPrecRound`: `arccos 1 = 0` exactly; `arccos 0 = π/2` and
`arccos (−1) = π`, correctly rounded; `NaN` for `|q| > 1`.  Otherwise a certified Ziv loop
(`zivLoopCertified`, no fuel) on `acosRatApprox` (`AzFloat/AcosRatBracket.lean`), total because
`arccos q` is irrational for every rational `q` in `[−1, 1)`.  The argument is never rounded to
the target precision: `(1 − |q|)/(1 + |q|)` is formed exactly as a rational, so a rational next
to `1` keeps its distance to `1` and the small result its relative accuracy.

The specification `acosRatPrecRound_eq` is in `Equiv/AcosRat.lean`.
-/

namespace Azurite.AzFloat

/-- `arccos q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `|q| > 1`, and for `p = 0` unless `q = 1`). -/
def acosRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then piDiv2PrecRound p mode
  else if h1 : q.num = q.den then (if q.sign then (zero, .eq) else piPrecRound p mode)
  else if hle : q.num ≤ q.den then
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      zivLoopCertified (acosRatApprox q) p mode (p + zivGuardBits)
        (acosRatApprox_isSome_exists p mode q h0
          (lt_of_le_of_ne ((abs_toRat_le_one_iff q).mp hle)
            (fun h => h1 ((abs_toRat_eq_one_iff q).mp h)))
          (p + zivGuardBits) (by unfold zivGuardBits; omega))
  else (nan, .eq)

/-- `arccos q` rounded to nearest at precision `p`. -/
def acosRat (q : AzRat) (p : Nat) : AzFloat := (acosRatPrecRound q p .Nearest).1

end Azurite.AzFloat
