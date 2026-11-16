/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.GdBracket

/-!
## The Gudermannian of a rational

`gdRatPrecRound q p mode` is `gd q` for an `AzRat`, correctly rounded to precision `p` in
`mode`, with the comparison against the exact value; `gdRat q p` rounds to nearest.

A certified Ziv loop (no fuel) on `gdRatApprox` (`AzFloat/GdBracket.lean`): the paths of the
float bracket — nothing but `π` for a huge `|q|`, the alternating series of `e^(−|q|)` or of
`tanh (|q|/2)` when few terms suffice, and the general arctangent otherwise — on the rational
brackets of the exponential.  `gd q` is irrational for every rational `q ≠ 0`
(`irrational_gd_rat`).  A tiny `q` is rounded by one test (`sinTinyRat?`).  `gd 0 = 0`
exactly.
-/

namespace Azurite.AzFloat

/-- `gd q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless `q = 0`). -/
def gdRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (zero, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    match sinTinyRat? q p mode with
    | some r => r
    | none =>
      zivLoopCertified (gdRatApprox q) p mode (p + zivGuardBits)
        (gdRatApprox_isSome_exists p mode q h0 (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `gd q` rounded to nearest at precision `p`. -/
def gdRat (q : AzRat) (p : Nat) : AzFloat := (gdRatPrecRound q p .Nearest).1

end Azurite.AzFloat
