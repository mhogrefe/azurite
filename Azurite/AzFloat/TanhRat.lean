/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.TanhBracket

/-!
## The hyperbolic tangent of a rational

`tanhRatPrecRound q p mode` is `tanh q` for an `AzRat` `q`, correctly rounded to precision `p`
in `mode`, with the comparison against the exact value; `tanhRat q p` rounds to nearest.
`tanh 0 = 0` exactly; tiny arguments by `sinTinyRat?` (`|q| − |q|³ ≤ tanh |q| < |q|`); large
arguments by `tanhNearOne?` at `N = ⌊2|q|⌋` (the value is within `4 e^(−2|q|)` of `±1`);
otherwise a certified Ziv loop (`zivLoopCertified`, no fuel) on `tanhRatApprox`
(`AzFloat/TanhBracket.lean`), total because `tanh q` is irrational for every rational `q ≠ 0`
(`irrational_tanh_rat`).  The function is odd in `q`.  The specification `tanhRatPrecRound_eq`
is in `Equiv/Tanh.lean`.
-/

namespace Azurite.AzFloat

/-- `tanh q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless `q = 0`). -/
def tanhRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (zero, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    match sinTinyRat? q p mode with
    | some r => r
    | none =>
    match tanhNearOne? q.sign (tanhRatN q) p mode with
    | some r => r
    | none =>
      zivLoopCertified (tanhRatApprox q) p mode (p + zivGuardBits)
        (tanhRatApprox_isSome_exists p mode q h0 (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `tanh q` rounded to nearest at precision `p`. -/
def tanhRat (q : AzRat) (p : Nat) : AzFloat := (tanhRatPrecRound q p .Nearest).1

end Azurite.AzFloat
