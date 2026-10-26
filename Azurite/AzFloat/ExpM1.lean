/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.ExpApprox

/-!
## `exp x − 1`

`expM1PrecRound x p mode` is `exp x − 1` (MPFR's `expm1`) correctly rounded to precision `p` in
`mode`, with the comparison against the exact value; `expM1 x` rounds to nearest at the
precision of `x`.  Subtracting `1` from a bracket of `exp x` cancels about `−e` bits for an
argument of exponent `e ≤ 0`, so the bracket (`expM1Approx`) runs `expBracket` at the working
precision `w + max(−e, 0)` and subtracts `1` outward; a tiny argument (`|x| < 2^(−w)`) is
enclosed by `[x, x + |x| 2^e]` from `x ≤ exp x − 1 ≤ x + x²` without any series or `ln 2`.  The
certified Ziv loop needs no fuel since `exp x − 1` is irrational for every finite float `x`.
Special values: `expM1 NaN = NaN`, `expM1 (+∞) = +∞`, `expM1 (−∞) = −1`, `expM1 0 = 0` exactly.
The specification `expM1PrecRound_eq_liftVal` is in `Equiv/ExpM1.lean`.
-/

namespace Azurite.AzFloat

/-- `exp x − 1` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def expM1PrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s =>
    if s then (infinity true, .eq) else if p = 0 then (nan, .eq) else setPrecRound (-one) p mode
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      zivLoopCertified (expM1Approx (finite s e q m hv) e) p mode (p + zivGuardBits)
        (expM1Approx_isSome_exists p mode s e hv (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `exp x − 1` rounded to nearest at the precision of `x`. -/
def expM1 (x : AzFloat) : AzFloat := (expM1PrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
