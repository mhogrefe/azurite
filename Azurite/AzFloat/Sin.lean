/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.SinBracket

/-!
## The sine

`sinPrecRound x p mode` is `sin x` correctly rounded to precision `p` in `mode`, with the
comparison against the exact value; `sin x` rounds to nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `sinApprox` (`AzFloat/SinBracket.lean`:
the reduction of `cos`, then `sin |x| = cos (r − π/2)` through the tail of the cosine bracket at
a shifted centre; the ends negated and swapped for `x < 0`).  The loop terminates because
`sin x` is irrational for every nonzero float `x` (`irrational_sin_rat`).

**Extreme arguments.**  Tiny `x` (`|x| < 2^e`, `e ≤ −(max p q + 72)`) never reach the loop:
`sinTiny?` rounds from `|x| − |x|³ ≤ sin |x| < |x|` by one test, at a cost independent of `e`
(the loop would need about `2|e|` bits, since the float `x` itself is next to the value).  For a
huge `x` the reduction needs `π` to about `e` bits beyond the target precision — inherent in
`sin x` for `|x| ≈ 2^e` — and near a multiple of `π` the loop raises the precision until the
small result is resolved (bounded by the precision of `x` plus its exponent).

Special values: `sin NaN = sin (±∞) = NaN`, `sin 0 = 0` exactly.
-/

namespace Azurite.AzFloat

/-- `sin x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0`). -/
def sinPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (nan, .eq)
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match sinTiny? s (finite s e q m hv) e q p mode with
      | some r => r
      | none =>
        zivLoopCertified (sinApprox (!s) (finite s e q m hv) e) p mode (p + zivGuardBits)
          (sinApprox_isSome_exists p mode (!s) (toVal_finite s e q m hv)
            (finiteVal_ne_zero s e hv) (finiteVal_neg_iff s e hv)
            (abs_finiteVal_bounds s e hv).2 (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `sin x` rounded to nearest at the precision of `x`. -/
def sin (x : AzFloat) : AzFloat := (sinPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
