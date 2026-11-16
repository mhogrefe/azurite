/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.CothBracket

/-!
## The hyperbolic cotangent of a rational

`cothRatPrecRound q p mode` is `coth q = 1 / tanh q` for an `AzRat` `q`, correctly rounded to
precision `p` in `mode`, with the comparison against the exact value; `cothRat q p` rounds to
nearest.  `coth 0 = +∞`; tiny arguments by `cscTinyRat?` (`1/|q| < coth |q| ≤ 1/|q| + |q|`);
large arguments by `cothNearOne?` at `N = ⌊2|q|⌋` (the value is within `4 e^(−2|q|)` of `±1`);
otherwise a certified Ziv loop (`zivLoopCertified`, no fuel) on `cothRatApprox`
(`AzFloat/CothBracket.lean`), total because `tanh q`, hence `coth q`, is irrational for every
rational `q ≠ 0`.  The function is odd in `q`.  The specification `cothRatPrecRound_eq` is in
`Equiv/Coth.lean`.
-/

namespace Azurite.AzFloat

/-- `coth q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless `q = 0`). -/
def cothRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (infinity true, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    match cscTinyRat? q p mode with
    | some r => r
    | none =>
    match cothNearOne? q.sign (tanhRatN q) p mode with
    | some r => r
    | none =>
      zivLoopCertified (cothRatApprox q) p mode (p + zivGuardBits)
        (cothRatApprox_isSome_exists p mode q h0 (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `coth q` rounded to nearest at precision `p`. -/
def cothRat (q : AzRat) (p : Nat) : AzFloat := (cothRatPrecRound q p .Nearest).1

end Azurite.AzFloat
