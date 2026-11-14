/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.TanRatBracket

/-!
## The tangent of a rational

`tanRatPrecRound q p mode` is `tan q` for an `AzRat` `q`, correctly rounded to precision `p` in
`mode`, with the comparison against the exact value; `tanRat q p` rounds to nearest.  `tan 0 = 0`
exactly; tiny arguments (`|q| < 2^e`, `e ≤ −(p + 72)`) by `tanTinyRat?`; otherwise a certified
Ziv loop (`zivLoopCertified`, no fuel) on `tanRatApprox` (`AzFloat/TanRatBracket.lean`: the
quotient of the joint bracket of `sin |q|` and `cos q`, a rejected placeholder while the bracket
of `cos q` contains `0`), total because `tan q` is irrational for every rational `q ≠ 0`
(`irrational_tan_rat`).  The specification `tanRatPrecRound_eq` is in `Equiv/TanRat.lean`.
-/

namespace Azurite.AzFloat

/-- `tan q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless `q = 0`). -/
def tanRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (zero, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    match tanTinyRat? q p mode with
    | some r => r
    | none =>
      zivLoopCertified (tanRatApprox q) p mode (p + zivGuardBits)
        (tanRatApprox_isSome_exists p mode q h0 (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `tan q` rounded to nearest at precision `p`. -/
def tanRat (q : AzRat) (p : Nat) : AzFloat := (tanRatPrecRound q p .Nearest).1

end Azurite.AzFloat
