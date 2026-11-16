/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.GdBracket
import Azurite.AzFloat.Atan2
import Azurite.AzFloat.PiConstants

/-!
## The Gudermannian `gd x`

`gdPrecRound x p mode` is `gd x = ∫₀ˣ sech t dt = 2 arctan (tanh (x/2))` (DLMF 4.23.39–40) of
a float `x`, correctly rounded to precision `p` in `mode`, with the comparison against the
exact value; `gd x` rounds to nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `gdApprox` (`AzFloat/GdBracket.lean`).
The loop terminates because `gd x` is irrational for every nonzero float `x`
(`irrational_gd_rat`: a Hermite–Lindemann argument at the four numbers `±x ± i gd x`,
`Transcendental/Gudermannian.lean`).

**Cost.**  One exponential and one arctangent in general.  For `|x|` below about `1/2` or
above about `3/2` (at 53 bits; the window widens with the precision) the arctangent is the
alternating series of a small argument, a fraction of the general one; for `|x| ≥ p + 72` or
so nothing but `π` is computed, at a cost independent of `x`.  A tiny `x` (`|x| < 2^e`,
`e ≤ −(max p q + 72)`) is rounded by one test (`sinTiny?`: `|x| − |x|³ ≤ gd |x| < |x|`).

Special values: `gd NaN = NaN`, `gd (±∞) = ±π/2` (correctly rounded), `gd 0 = 0` exactly.  The
function is odd.
-/

namespace Azurite.AzFloat

/-- `gd x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless `x = 0`). -/
def gdPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if p = 0 then (nan, .eq) else signedRound s piDiv2PrecRound p mode
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match sinTiny? s (finite s e q m hv) e q p mode with
      | some r => r
      | none =>
      zivLoopCertified (gdApprox (!s) (finite s e q m hv) e) p mode (p + zivGuardBits)
        (gdApprox_isSome_exists p mode (!s) (toVal_finite s e q m hv) (finiteVal_ne_zero s e hv)
          e (abs_finiteVal_bounds s e hv).1 (abs_finiteVal_bounds s e hv).2
          (finiteVal_neg_iff s e hv) (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `gd x` rounded to nearest at the precision of `x`. -/
def gd (x : AzFloat) : AzFloat := (gdPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
