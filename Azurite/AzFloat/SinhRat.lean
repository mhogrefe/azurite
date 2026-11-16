/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.SinhRatBracket

/-!
## The hyperbolic sine of a rational

`sinhRatPrecRound q p mode` is `sinh q` for an `AzRat` `q`, correctly rounded to precision `p`
in `mode`, with the comparison against the exact value; `sinhRat q p` rounds to nearest.
`sinh 0 = 0` exactly; tiny arguments (`|q| < 2^e`, `e ≤ −(p + 72)`) by `tanTinyRat?`
(`|q| < sinh |q| ≤ |q| + |q|³`); otherwise a certified Ziv loop (`zivLoopCertified`, no fuel) on
`sinhRatApprox` (`AzFloat/SinhRatBracket.lean`), total because `sinh q` is irrational for every
rational `q ≠ 0` (`irrational_sinh_rat`).  The function is odd in `q`.  The specification
`sinhRatPrecRound_eq` is in `Equiv/SinhRat.lean`.
-/

namespace Azurite.AzFloat

/-- `sinh q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless `q = 0`). -/
def sinhRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (zero, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    match tanTinyRat? q p mode with
    | some r => r
    | none =>
      zivLoopCertified (sinhRatApprox q) p mode (p + zivGuardBits)
        (sinhRatApprox_isSome_exists p mode q h0 (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `sinh q` rounded to nearest at precision `p`. -/
def sinhRat (q : AzRat) (p : Nat) : AzFloat := (sinhRatPrecRound q p .Nearest).1

end Azurite.AzFloat
