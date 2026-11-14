/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosRat
import Azurite.AzFloat.SinRat
import Azurite.AzFloat.Equiv.SinCosRatBracket

/-!
## The sine and the cosine of a rational together

`sinCosRatPrecRound q p mode` is the pair of `sin q` and `cos q` for an `AzRat` `q`, each
correctly rounded to precision `p` in `mode` with the comparison against the exact value:
`sinCosRatPrecRound q p mode = (sinRatPrecRound q p mode, cosRatPrecRound q p mode)`
(`sinCosRatPrecRound_eq`, `Equiv/SinCosRat.lean`), from **one** computation.
`sinCosRat q p` rounds both to nearest.

A certified joint Ziv loop (`zivLoopCertified₂`, no fuel) on `sinCosRatApprox`
(`AzFloat/SinCosRatBracket.lean`: `sinCosBracket` at the float next to `q` on the side of zero,
both components widened by the Lipschitz bound), total because `sin q` and `cos q` are both
irrational for every rational `q ≠ 0`.  `q = 0`, `p = 0` and tiny arguments (where
`sinTinyRat?` or `cosTiny?` answers) are delegated to `sinRatPrecRound` and `cosRatPrecRound`.
-/

namespace Azurite.AzFloat

/-- `(sin q, cos q)` for a rational `q`, each rounded to precision `p` with `mode` and paired
with the comparison with the exact value (as `sinRatPrecRound` and `cosRatPrecRound`), from one
computation. -/
def sinCosRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × (AzFloat × Ordering) :=
  if h0 : q.num = 0 then (sinRatPrecRound q p mode, cosRatPrecRound q p mode)
  else if hp : p = 0 then (sinRatPrecRound q p mode, cosRatPrecRound q p mode)
  else
    haveI : NeZero p := ⟨hp⟩
    match sinTinyRat? q p mode, cosTiny? (ratExpBound q) p mode with
    | none, none =>
      zivLoopCertified₂ (sinCosRatApprox q) p mode (p + zivGuardBits)
        (sinCosRatApprox_isSome_exists p mode q h0 (p + zivGuardBits)
          (by unfold zivGuardBits; omega))
    | _, _ => (sinRatPrecRound q p mode, cosRatPrecRound q p mode)

/-- `(sin q, cos q)`, both rounded to nearest at precision `p`. -/
def sinCosRat (q : AzRat) (p : Nat) : AzFloat × AzFloat :=
  let r := sinCosRatPrecRound q p .Nearest
  (r.1.1, r.2.1)

end Azurite.AzFloat
