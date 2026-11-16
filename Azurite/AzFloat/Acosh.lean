/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AcoshBracket

/-!
## The inverse hyperbolic cosine

`acoshPrecRound x p mode` is `acosh x = ln (x + √(x² − 1))`, defined for `x ≥ 1`, correctly
rounded to precision `p` in `mode`, with the comparison against the exact value; `acosh x`
rounds to nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `acoshApprox`
(`AzFloat/AcoshBracket.lean`): the logarithm of a float just below `x + √((x − 1)(x + 1))`.
The loop terminates because `acosh q` is irrational for every rational `q > 1`
(`irrational_arcosh_rat`: its hyperbolic cosine is rational).

**Extreme arguments.**  Next to `1` the result is `≈ √(2 (x − 1))`; `x − 1` is rounded with
relative accuracy, and the loop starts with half the leading zero bits of `x − 1` more
(`acoshExtra`), the logarithm being accurate absolutely.  A huge `x` gives `≈ ln (2x)` and
costs one logarithm.

Special values: `acosh NaN = NaN`; `acosh x = NaN` for `x < 1`, including `0` and `−∞`;
`acosh (+∞) = +∞`; `acosh 1 = 0` exactly (the only exact case).
-/

namespace Azurite.AzFloat

/-- `acosh x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `x < 1`, and for `p = 0` unless `x = 1` or `x = +∞`). -/
def acoshPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (nan, .eq)
  | zero => (nan, .eq)
  | finite s e q m hv =>
    if hs : s = true then
      if h1 : eqIEEE (finite s e q m hv) one = true then (zero, .eq)
      else if he : e.sign = true ∧ e.abs.toNat ≠ 0 then
        if hp : p = 0 then (nan, .eq)
        else
          haveI : NeZero p := ⟨hp⟩
          zivLoopCertified (acoshApprox (finite s e q m hv)) p mode
            (p + zivGuardBits + acoshExtra (subPrecRound (finite s e q m hv) one q .Floor).1)
            (acoshApprox_isSome_exists p mode (toVal_finite s e q m hv)
              (one_lt_of_acosh_cond hv hs h1 he) _ (by unfold zivGuardBits; omega))
      else (nan, .eq)
    else (nan, .eq)

/-- `acosh x` rounded to nearest at the precision of `x`. -/
def acosh (x : AzFloat) : AzFloat := (acoshPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
