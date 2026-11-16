/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.SechBracket

/-!
## The hyperbolic secant of a rational

`sechRatPrecRound q p mode` is `sech q = 1 / cosh q` for an `AzRat` `q`, correctly rounded to
precision `p` in `mode`, with the comparison against the exact value; `sechRat q p` rounds to
nearest.  `sech 0 = 1` exactly; tiny arguments by `expNearOne? false` at the exponent
`coshRatTinyExp q` (`exp (−q²/2) ≤ sech q < 1`); otherwise a certified Ziv loop
(`zivLoopCertified`, no fuel) on `sechRatApprox` (`AzFloat/SechBracket.lean`), total because
`cosh q`, hence `sech q`, is irrational for every rational `q ≠ 0`.  The function is even in
`q`.  The specification `sechRatPrecRound_eq` is in `Equiv/Sech.lean`.
-/

namespace Azurite.AzFloat

/-- `sech q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def sechRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else if h0 : q.num = 0 then setPrecRound one p mode
  else
    haveI : NeZero p := ⟨hp⟩
    match expNearOne? false (coshRatTinyExp q) p mode with
    | some r => r
    | none =>
      zivLoopCertified (sechRatApprox q) p mode (p + zivGuardBits)
        (sechRatApprox_isSome_exists p mode q h0 (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `sech q` rounded to nearest at precision `p`. -/
def sechRat (q : AzRat) (p : Nat) : AzFloat := (sechRatPrecRound q p .Nearest).1

end Azurite.AzFloat
