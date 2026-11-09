/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.CosRatBracket

/-!
## The cosine of a rational

`cosRatPrecRound q p mode` is `cos q` for an `AzRat` `q`, correctly rounded to precision `p` in
`mode`, with the comparison against the exact value; `cosRat q p` rounds to nearest.  `cos 0 = 1`
exactly; otherwise a certified Ziv loop (`zivLoopCertified`, no fuel) on `cosRatApprox`
(`AzFloat/CosRatBracket.lean`: the float bracket at `⌊q⌋_W`, widened by the Lipschitz bound),
total because `cos q` is irrational for every rational `q ≠ 0` (`irrational_cos_rat`).  The
specification `cosRatPrecRound_eq` is in `Equiv/CosRat.lean`.
-/

namespace Azurite.AzFloat

/-- `cos q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def cosRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else if h0 : q.num = 0 then setPrecRound one p mode
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified (cosRatApprox q) p mode (p + zivGuardBits)
      (cosRatApprox_isSome_exists p mode q h0 (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `cos q` rounded to nearest at precision `p`. -/
def cosRat (q : AzRat) (p : Nat) : AzFloat := (cosRatPrecRound q p .Nearest).1

end Azurite.AzFloat
