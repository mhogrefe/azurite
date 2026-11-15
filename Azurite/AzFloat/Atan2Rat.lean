/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2
import Azurite.AzFloat.Equiv.Atan2RatBracket

/-!
## `atan2 (y, x)` for rationals

`atan2RatPrecRound y x p mode` is the angle of the point `(x, y)` with `AzRat` coordinates,
measured from the positive `x`-axis, in `(−π, π]`, correctly rounded to precision `p` in `mode`,
with the comparison against the exact value; `atan2Rat y x p` rounds to nearest.

Special values, as for the float `atan2PrecRound`: `y = 0` gives `0` for `x ≥ 0` and `π` for
`x < 0`; `x = 0`, `y ≠ 0` gives `±π/2` with the sign of `y`.  Otherwise the value is irrational
and the certified Ziv loop (`zivLoopCertified`, no fuel) runs on `atan2RatApprox`
(`AzFloat/Atan2RatBracket.lean`): the quotient `|y|/|x|` is formed as a rational, so the
arguments are never rounded to the target precision, and extreme ratios cost nothing extra.
The loop runs on the negative angle (in the negated mode for `y > 0`, the result negated), as
in `AzFloat/Atan2.lean`.

The specification `atan2RatPrecRound_eq` is in `Equiv/Atan2Rat.lean`.
-/

namespace Azurite.AzFloat

/-- `atan2 (y, x)` for rationals, rounded to precision `p` with `mode`, and the comparison with
the exact value (`(nan, .eq)` for `p = 0` unless the value is `0`). -/
def atan2RatPrecRound (y x : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hy : y.num = 0 then (if x.sign then (zero, .eq) else piPrecRound p mode)
  else if hx : x.num = 0 then signedRound y.sign piDiv2PrecRound p mode
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    let r := zivLoopCertified (atan2RatApprox y x) p (if y.sign then -mode else mode)
      (p + zivGuardBits)
      (atan2RatApprox_isSome_exists p _ y x hy hx (p + zivGuardBits)
        (by unfold zivGuardBits; omega))
    if y.sign then (-r.1, r.2.swap) else r

/-- `atan2 (y, x)` for rationals, rounded to nearest at precision `p`. -/
def atan2Rat (y x : AzRat) (p : Nat) : AzFloat := (atan2RatPrecRound y x p .Nearest).1

end Azurite.AzFloat
