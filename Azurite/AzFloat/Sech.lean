/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.SechBracket

/-!
## The hyperbolic secant

`sechPrecRound x p mode` is `sech x = 1 / cosh x = 2 / (e^x + e^(−x))` correctly rounded to
precision `p` in `mode`, with the comparison against the exact value; `sech x` rounds to
nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `sechApprox`
(`AzFloat/SechBracket.lean`), the reciprocal of the bracket of `cosh x`.  The loop terminates
because `cosh q`, hence `sech q`, is irrational for every rational `q ≠ 0`
(`irrational_cosh_rat`).

**Extreme arguments.**  A tiny `x` (`|x| < 2^e`, `2e − 1 ≤ −(p + 72)`) gives a value in
`[1 − 2^(2e−1), 1)`, rounded by one test (`expNearOne?`) at no cost; the Ziv loop would need
about `2|e|` bits to separate the value from `1`.  A huge `x` gives `≈ 2 e^(−|x|)`, with
relative accuracy, at the cost of `exp x`; nothing underflows.

Special values: `sech NaN = NaN`, `sech (±∞) = 0`, `sech 0 = 1` exactly.  The function is even.
-/

namespace Azurite.AzFloat

/-- `sech x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` and a finite `x`). -/
def sechPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (zero, .eq)
  | zero => if p = 0 then (nan, .eq) else setPrecRound one p mode
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match expNearOne? false (coshTinyExp e) p mode with
      | some r => r
      | none =>
      zivLoopCertified (sechApprox (finite s e q m hv) e) p mode (p + zivGuardBits)
        (sechApprox_isSome_exists p mode (toVal_finite s e q m hv) (finiteVal_ne_zero s e hv)
          (abs_finiteVal_bounds s e hv).2 (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `sech x` rounded to nearest at the precision of `x`. -/
def sech (x : AzFloat) : AzFloat := (sechPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
