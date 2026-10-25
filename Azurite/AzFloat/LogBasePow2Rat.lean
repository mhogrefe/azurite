/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LogBasePow2Bracket
import Azurite.AzRat.Construct
import Azurite.AzRat.LogBase2

/-!
## The logarithm of a rational in a power-of-two base

`logBasePow2RatPrecRound q k p mode` is `log_{2^k} q = log₂ q / k` for a rational `q` and an
integer `k ≠ 0` (possibly negative), correctly rounded to precision `p` in `mode`, with the
comparison against the exact value.  A rational power of two `q = 2^j` (`AzRat.checkedLogBase2`)
has the rational logarithm `j / k`, rounded once (`ofAzRatRound`); every other positive rational
has an irrational `log₂ q / k`, computed by the certified Ziv loop from `logBasePow2RatApprox`.
Special values: `NaN` for `k = 0` and for `q < 0`; `log_{2^k} 0 = ∓∞` by the sign of `k`.
The specification `logBasePow2RatPrecRound_eq` is in `Equiv/LogBasePow2Rat.lean`.
-/

namespace Azurite.AzFloat

/-- `log_{2^k} q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` or `k = 0`). -/
def logBasePow2RatPrecRound (q : AzRat) (k : AzInt) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hk : k = 0 then (nan, .eq)
  else if h0 : q.num = 0 then (infinity (!k.sign), .eq)
  else if hs : q.sign = true then
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match h2 : q.checkedLogBase2 with
      | some j => ofAzRatRound (AzRat.ofAzInts j k) p mode
      | none =>
        zivLoopCertified (logBasePow2RatApprox q k) p mode (p + zivGuardBits)
          (logBasePow2RatApprox_isSome_exists p mode q (toRat_pos_of_sign q hs h0)
            (AzRat.isPowerOfTwo_eq_false_of_checkedLogBase2_eq_none q h2) k hk
            (p + zivGuardBits) (by unfold zivGuardBits; omega))
  else (nan, .eq)

/-- `log_{2^k} q` rounded to nearest at precision `p`. -/
def logBasePow2Rat (q : AzRat) (k : AzInt) (p : Nat) : AzFloat :=
  (logBasePow2RatPrecRound q k p .Nearest).1

end Azurite.AzFloat
