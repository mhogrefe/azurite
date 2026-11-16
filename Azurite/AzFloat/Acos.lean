/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AcosBracket
import Azurite.AzFloat.Equiv.AsinBracket
import Azurite.AzFloat.PiConstants

/-!
## The arccosine

`acosPrecRound x p mode` is `arccos x` correctly rounded to precision `p` in `mode`, with the
comparison against the exact value; `acos x` rounds to nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `acosApprox` (`AzFloat/AcosBracket.lean`):
`arccos |x| = 2 arctan √((1 − |x|)/(1 + |x|))`, the arctangent by the levels of
`AzFloat/AtanBracket.lean`, and `arccos (−|x|) = π − arccos |x|`.  The loop terminates because
`arccos x` is irrational for every float `x` in `[−1, 1)` (`irrational_arccos_rat`, from
`irrational_cos_rat`).

**Extreme arguments.**  Next to `1` the result is small, `≈ √(2 (1 − x))`; `1 − x` is correctly
rounded and the arctangent runs with relative accuracy.  A tiny `x` gives a value next to the
irrational `π/2` and costs no more than any other.

Special values: `arccos NaN = NaN`; `arccos x = NaN` for `|x| > 1`, in particular for `±∞`;
`arccos 1 = 0` exactly (the only exact case); `arccos 0 = π/2` and `arccos (−1) = π`, correctly
rounded.
-/

namespace Azurite.AzFloat

/-- `arccos x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `|x| > 1`, and for `p = 0` unless `x = 1`). -/
def acosPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (nan, .eq)
  | zero => piDiv2PrecRound p mode
  | finite s e q m hv =>
    if eqIEEE (finite s e q m hv).abs one = true then
      (if s then (zero, .eq) else piPrecRound p mode)
    else if he : e.sign = true ∧ e.abs.toNat ≠ 0 then (nan, .eq)
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      zivLoopCertified (acosApprox (!s) (finite s e q m hv)) p mode (p + zivGuardBits)
        (acosApprox_isSome_exists p mode (toVal_finite s e q m hv)
          (finiteVal_ne_zero s e hv)
          (abs_lt_one_of_exponent (abs_finiteVal_bounds s e hv).2 he)
          (finiteVal_neg_iff s e hv) (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `arccos x` rounded to nearest at the precision of `x` (at precision `1` for `x = 0`). -/
def acos (x : AzFloat) : AzFloat := (acosPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
