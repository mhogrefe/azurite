/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LogBasePow2Bracket
import Azurite.AzRat.Construct

/-!
## The logarithm in a power-of-two base

`logBasePow2PrecRound x k p mode` is `log_{2^k} x = log₂ x / k` for an integer `k ≠ 0`
(possibly negative), correctly rounded to precision `p` in `mode`, with the comparison against
the exact value.  A float whose significand is a power of two is `2^(e−1)`, and its logarithm
is the rational `(e − 1) / k`, rounded exactly once (`ofAzRatRound`).  Every other positive
float has an irrational `log₂ x / k`, computed by the certified Ziv loop from the bracket
`logBasePow2Approx`.  Special values: `NaN` for `NaN`, `−∞`, negatives and the base `1`
(`k = 0`); `log_{2^k} (+∞) = ±∞` and `log_{2^k} 0 = ∓∞` with the sign of `k`.  The
specification `logBasePow2PrecRound_eq_liftVal` is in `Equiv/LogBasePow2.lean`.
-/

namespace Azurite.AzFloat

/-- `log_{2^k} x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` or `k = 0`). -/
def logBasePow2PrecRound (x : AzFloat) (k : AzInt) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hk : k = 0 then (nan, .eq)
  else
    match x with
    | nan => (nan, .eq)
    | infinity s => if s then (infinity k.sign, .eq) else (nan, .eq)
    | zero => (infinity (!k.sign), .eq)
    | finite false _ _ _ _ => (nan, .eq)
    | finite true e q m hv =>
      if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        if h2 : m.isPowerOfTwo = true then ofAzRatRound (AzRat.ofAzInts (e - 1) k) p mode
        else
          zivLoopCertified (logBasePow2Approx (finite true e q m hv) e k) p mode
            (p + zivGuardBits)
            (logBasePow2Approx_isSome_exists p mode e hv (Bool.eq_false_iff.mpr h2) k hk
              (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `log_{2^k} x` rounded to nearest at the precision of `x`. -/
def logBasePow2 (x : AzFloat) (k : AzInt) : AzFloat :=
  (logBasePow2PrecRound x k (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
