/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AsecBracket
import Azurite.AzFloat.PiConstants

/-!
## The arcsecant

`asecPrecRound x p mode` is `arcsec x = arccos (1/x)` — the inverse of the secant on `[0, π]`,
defined for `|x| ≥ 1` — correctly rounded to precision `p` in `mode`, with the comparison against
the exact value; `asec x` rounds to nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `asecApprox` (`AzFloat/AsecBracket.lean`):
`arcsec |x| = 2 arctan √((|x| − 1)/(|x| + 1))`, with no reciprocal, and
`arcsec (−|x|) = π − arcsec |x|`.  The loop terminates because `arccos q` is irrational for
every rational `q` in `[−1, 1)`.

**Extreme arguments.**  Next to `1` the result is small, `≈ √(2 (x − 1))`; `x − 1` is correctly
rounded and the arctangent runs with relative accuracy.  A huge `x` gives a value next to the
irrational `π/2` and costs no more than any other.

Special values: `asec NaN = NaN`; `asec x = NaN` for `|x| < 1`, including `0`;
`asec (±∞) = π/2`, correctly rounded (the value the function tends to); `asec 1 = 0` exactly
(the only exact case); `asec (−1) = π`, correctly rounded.
-/

namespace Azurite.AzFloat

/-- `arcsec x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `|x| < 1`, and for `p = 0` unless `x = 1`). -/
def asecPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => piDiv2PrecRound p mode
  | zero => (nan, .eq)
  | finite s e q m hv =>
    if h1 : eqIEEE (finite s e q m hv).abs one = true then
      (if s then (zero, .eq) else piPrecRound p mode)
    else if he : e.sign = true ∧ e.abs.toNat ≠ 0 then
      if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        zivLoopCertified (asecApprox (!s) (finite s e q m hv)) p mode (p + zivGuardBits)
          (asecApprox_isSome_exists p mode (toVal_finite s e q m hv)
            (one_lt_abs_of_exponent (abs_finiteVal_bounds s e hv).1 he (fun h => by
              have habs : (finite s e q m hv).abs.toVal
                  = some ((|finiteVal s e m| : ℝ) : EReal) := by
                rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
                congr 1
              exact h1 ((eqIEEE_iff _ _).mpr ⟨_, habs, by rw [h]; exact toVal_one'⟩)))
            (finiteVal_neg_iff s e hv) (p + zivGuardBits)
            (by unfold zivGuardBits; omega))
    else (nan, .eq)

/-- `arcsec x` rounded to nearest at the precision of `x`. -/
def asec (x : AzFloat) : AzFloat := (asecPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
