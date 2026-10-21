/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Log2Bracket

/-!
## The base-2 logarithm of a rational

`log2RatPrecRound q p mode` is `log₂ q` correctly rounded to precision `p` in `mode`, for a
rational `q`, with the comparison against the exact value; `log2Rat q p` rounds to nearest.  A
rational power of two (`AzRat.isPowerOfTwo`: positive, numerator and denominator powers of two)
has the integer logarithm `powerOfTwoExponent q`, returned exactly; every other positive rational
has an irrational `log₂ q` (`irrational_logb_two_toRat`), computed as `ln q / ln 2` from the
bracket of `ln q` (`lnFloorBracket` of `⌊q⌋_w`, one AGM run) and the bracket of `ln 2`
(`log2RatApprox`) by the certified Ziv loop, without fuel.  `log₂ 0 = −∞`, `log₂ q = NaN` for
`q < 0`.  The specification `log2RatPrecRound_eq` is in `Equiv/Log2Rat.lean`.
-/

namespace Azurite.AzFloat

/-- `log₂ q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def log2RatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (infinity false, .eq)
  else if hs : q.sign = true then
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match h2 : q.checkedLogBase2 with
      | some k => setPrecRound (ofAzInt k) p mode
      | none =>
        zivLoopCertified (log2RatApprox q) p mode (p + zivGuardBits)
          (log2RatApprox_isSome_exists p mode q (toRat_pos_of_sign q hs h0)
            (AzRat.isPowerOfTwo_eq_false_of_checkedLogBase2_eq_none q h2) (p + zivGuardBits)
            (by unfold zivGuardBits; omega))
  else (nan, .eq)

/-- `log₂ q` rounded to nearest at precision `p`. -/
def log2Rat (q : AzRat) (p : Nat) : AzFloat := (log2RatPrecRound q p .Nearest).1

end Azurite.AzFloat
