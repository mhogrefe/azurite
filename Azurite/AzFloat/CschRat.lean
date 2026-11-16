/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.CschBracket

/-!
## The hyperbolic cosecant of a rational

`cschRatPrecRound q p mode` is `csch q = 1 / sinh q` for an `AzRat` `q`, correctly rounded to
precision `p` in `mode`, with the comparison against the exact value; `cschRat q p` rounds to
nearest.  `csch 0 = +∞`; tiny arguments by `cschTinyRat?` (`1/|q| − |q| ≤ csch |q| < 1/|q|`);
otherwise a certified Ziv loop (`zivLoopCertified`, no fuel) on `cschRatApprox`
(`AzFloat/CschBracket.lean`), total because `sinh q`, hence `csch q`, is irrational for every
rational `q ≠ 0`.  The function is odd in `q`.  The specification `cschRatPrecRound_eq` is in
`Equiv/Csch.lean`.
-/

namespace Azurite.AzFloat

/-- `csch q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless `q = 0`). -/
def cschRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (infinity true, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    match cschTinyRat? q p mode with
    | some r => r
    | none =>
      zivLoopCertified (cschRatApprox q) p mode (p + zivGuardBits)
        (cschRatApprox_isSome_exists p mode q h0 (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `csch q` rounded to nearest at precision `p`. -/
def cschRat (q : AzRat) (p : Nat) : AzFloat := (cschRatPrecRound q p .Nearest).1

end Azurite.AzFloat
