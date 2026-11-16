/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.CoshBracket

/-!
## The hyperbolic cosine of a rational

`coshRatPrecRound q p mode` is `cosh q` for an `AzRat` `q`, correctly rounded to precision `p`
in `mode`, with the comparison against the exact value; `coshRat q p` rounds to nearest.
`cosh 0 = 1` exactly; tiny arguments by `expNearOne?` at the exponent `coshRatTinyExp q`
(`1 < cosh q ≤ exp (q²/2)`); otherwise a certified Ziv loop (`zivLoopCertified`, no fuel) on
`coshRatApprox` (`AzFloat/CoshBracket.lean`), total because `cosh q` is irrational for every
rational `q ≠ 0` (`irrational_cosh_rat`).  The function is even in `q`.  The specification
`coshRatPrecRound_eq` is in `Equiv/CoshRat.lean`.
-/

namespace Azurite.AzFloat

/-- `cosh q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def coshRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else if h0 : q.num = 0 then setPrecRound one p mode
  else
    haveI : NeZero p := ⟨hp⟩
    match expNearOne? true (coshRatTinyExp q) p mode with
    | some r => r
    | none =>
      zivLoopCertified (coshRatApprox q) p mode (p + zivGuardBits)
        (coshRatApprox_isSome_exists p mode q h0 (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `cosh q` rounded to nearest at precision `p`. -/
def coshRat (q : AzRat) (p : Nat) : AzFloat := (coshRatPrecRound q p .Nearest).1

end Azurite.AzFloat
