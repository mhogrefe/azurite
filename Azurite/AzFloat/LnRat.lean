/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LnBracket

/-!
## The natural logarithm of a rational

`lnRatPrecRound q p mode` is `ln q` correctly rounded to precision `p` in `mode`, for a rational
`q`, with the comparison against the exact value; `lnRat q p` rounds to nearest.  The bracket
(`lnRatApprox`) is `ln` of the float `⌊q⌋_w` at the working precision `w` — one AGM run of
`lnBracket` — with the upper end widened by `2^(2−w) ≥ ln (q/⌊q⌋_w)`; the certified Ziv loop
needs no fuel since `ln q` is irrational for every rational `q ≠ 1` (`irrational_log_rat`).
Special values: `ln 0 = −∞`, `ln q = NaN` for `q < 0`, `ln 1 = 0` exactly.  The specification
`lnRatPrecRound_eq` is in `Equiv/LnRat.lean`.
-/

namespace Azurite.AzFloat

/-- `ln q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def lnRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (infinity false, .eq)
  else if hs : q.sign = true then
    if h1 : q.num = q.den then (zero, .eq)
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      zivLoopCertified (lnRatApprox q) p mode (p + zivGuardBits)
        (lnRatApprox_isSome_exists p mode q (toRat_pos_of_sign q hs h0)
          (toRat_ne_one_of_num_ne_den q hs h1) (p + zivGuardBits) (by unfold zivGuardBits; omega))
  else (nan, .eq)

/-- `ln q` rounded to nearest at precision `p`. -/
def lnRat (q : AzRat) (p : Nat) : AzFloat := (lnRatPrecRound q p .Nearest).1

end Azurite.AzFloat
