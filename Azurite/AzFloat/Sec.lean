/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.SecBracket

/-!
## The secant

`secPrecRound x p mode` is `sec x = 1 / cos x` correctly rounded to precision `p` in `mode`, with
the comparison against the exact value; `sec x` rounds to nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `secApprox` (`AzFloat/SecBracket.lean`):
the reciprocal of the bracket of `cos x` (`cosBracket`: exact argument reduction, Algorithm 4.4
of *Modern Computer Arithmetic*, three double-angle steps of the cosine), by two directed
divisions.  A float is never a pole of the secant (`cos x` is irrational for `x ≠ 0`); at a
working precision that does not yet separate `x` from the nearest pole the bracket is a
placeholder that the rounding test rejects, and the loop raises the precision.  It terminates
because `sec x` is irrational for every nonzero float `x`.

Tiny arguments (`|x| < 2^e`, `e ≤ −(p + 72)`) never reach the loop: `secTiny?` rounds `1⁺`
directly, at a cost independent of `e`.

Special values: `sec NaN = sec (±∞) = NaN`, `sec 0 = 1` exactly.
-/

namespace Azurite.AzFloat

/-- `sec x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def secPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (nan, .eq)
  | zero => if p = 0 then (nan, .eq) else setPrecRound one p mode
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match secTiny? e p mode with
      | some r => r
      | none =>
        zivLoopCertified (secApprox (finite s e q m hv) e) p mode (p + zivGuardBits)
          (secApprox_isSome_exists p mode (toVal_finite s e q m hv) (finiteVal_ne_zero s e hv)
            (abs_finiteVal_bounds s e hv).2 (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `sec x` rounded to nearest at the precision of `x`. -/
def sec (x : AzFloat) : AzFloat := (secPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
