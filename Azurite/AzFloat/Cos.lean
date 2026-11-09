/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.CosBracket

/-!
## The cosine

`cosPrecRound x p mode` is `cos x` correctly rounded to precision `p` in `mode`, with the
comparison against the exact value; `cos x` rounds to nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `cosApprox` (`AzFloat/CosBracket.lean`):
exact argument reduction by `remExact` against the lower end of a bracket of `2π` (the error
`2k(π − lo)` is bounded and widened out), the alternating Taylor series of `cos (r/8)` in interval
arithmetic, and three double-angle steps.  The loop terminates because `cos x` is irrational for
every nonzero float `x` (`irrational_cos_rat`, from Hermite–Lindemann), so the exact value is never
a rounding boundary.

Special values: `cos NaN = NaN`, `cos (±∞) = NaN`, `cos 0 = 1` exactly.
-/

namespace Azurite.AzFloat

/-- `cos x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def cosPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (nan, .eq)
  | zero => if p = 0 then (nan, .eq) else setPrecRound one p mode
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      zivLoopCertified (cosApprox (finite s e q m hv) e) p mode (p + zivGuardBits)
        (cosApprox_isSome_exists p mode (toVal_finite s e q m hv) (finiteVal_ne_zero s e hv)
          (abs_finiteVal_bounds s e hv).2 (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `cos x` rounded to nearest at the precision of `x`. -/
def cos (x : AzFloat) : AzFloat := (cosPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
