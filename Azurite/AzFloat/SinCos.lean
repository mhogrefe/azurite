/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Cos
import Azurite.AzFloat.Sin
import Azurite.AzFloat.Equiv.SinCosBracket

/-!
## The sine and the cosine together

`sinCosPrecRound x p mode` is the pair of `sin x` and `cos x`, each correctly rounded to
precision `p` in `mode` with the comparison against the exact value:
`sinCosPrecRound x p mode = (sinPrecRound x p mode, cosPrecRound x p mode)`
(`sinCosPrecRound_eq`, `Equiv/SinCos.lean`), from **one** computation.  `sinCos x` rounds both to
nearest at the precision of `x`.

A certified joint Ziv loop (`zivLoopCertified₂`, no fuel) on `sinCosApprox`
(`AzFloat/SinCosBracket.lean`): one exact argument reduction, then Algorithm 4.4 (SinCos) of
Brent and Zimmermann, *Modern Computer Arithmetic*, §4.9.1 — the sine and the cosine of the bit
blocks of the reduced argument by binary splitting, combined by the addition formulae — and
three double-angle steps.  The loop terminates because `sin x` and `cos x` are both irrational
for every nonzero float `x`.

Tiny arguments (where `sinTiny?` or `cosTiny?` answers), zero, `NaN` and the infinities are
delegated to `sinPrecRound` and `cosPrecRound`.
-/

namespace Azurite.AzFloat

/-- `(sin x, cos x)`, each rounded to precision `p` with `mode` and paired with the comparison
with the exact value (as `sinPrecRound` and `cosPrecRound`), from one computation. -/
def sinCosPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × (AzFloat × Ordering) :=
  match x with
  | finite s e q m hv =>
    if hp : p = 0 then ((nan, .eq), (nan, .eq))
    else
      haveI : NeZero p := ⟨hp⟩
      match sinTiny? s (finite s e q m hv) e q p mode, cosTiny? e p mode with
      | none, none =>
        zivLoopCertified₂ (sinCosApprox (!s) (finite s e q m hv) e) p mode (p + zivGuardBits)
          (sinCosApprox_isSome_exists p mode (!s) (toVal_finite s e q m hv)
            (finiteVal_ne_zero s e hv) (finiteVal_neg_iff s e hv)
            (abs_finiteVal_bounds s e hv).2 (p + zivGuardBits) (by unfold zivGuardBits; omega))
      | _, _ => (sinPrecRound (finite s e q m hv) p mode, cosPrecRound (finite s e q m hv) p mode)
  | _ => (sinPrecRound x p mode, cosPrecRound x p mode)

/-- `(sin x, cos x)`, both rounded to nearest at the precision of `x`. -/
def sinCos (x : AzFloat) : AzFloat × AzFloat :=
  let r := sinCosPrecRound x (x.precision?.getD 1) .Nearest
  (r.1.1, r.2.1)

end Azurite.AzFloat
