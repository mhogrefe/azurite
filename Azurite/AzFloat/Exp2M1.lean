/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Exp2Bracket

/-!
## `2^x − 1`

`exp2M1PrecRound x p mode` is `2^x − 1` correctly rounded to precision `p` in `mode`, with the
comparison against the exact value; `exp2M1 x` rounds to nearest at the precision of `x`.  An
integer `x` gives the exact `2^n − 1` (one correctly rounded subtraction); otherwise the certified
Ziv loop (no fuel) runs over `exp2M1Approx`, the bracket of `x ln 2` at the compensated precision
`w + max(−e, 0)` fed to `expM1OfBracket`, total because `2^x − 1` is irrational for every
non-integer float `x`.  Special values: `exp2M1 NaN = NaN`, `exp2M1 (+∞) = +∞`,
`exp2M1 (−∞) = −1`, `exp2M1 0 = 0` exactly.  The specification `exp2M1PrecRound_eq_liftVal` is
in `Equiv/Exp2M1.lean`.
-/

namespace Azurite.AzFloat

/-- `2^x − 1` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def exp2M1PrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s =>
    if s then (infinity true, .eq) else if p = 0 then (nan, .eq) else setPrecRound (-one) p mode
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else if hi : isInteger (finite s e q m hv) = true then
      subPrecRound (powerOf2 (truncToAzInt (finite s e q m hv))) one p mode
    else
      haveI : NeZero p := ⟨hp⟩
      zivLoopCertified (exp2M1Approx (finite s e q m hv) e) p mode (p + zivGuardBits)
        (exp2M1Approx_isSome_exists p mode s e hv hi (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `2^x − 1` rounded to nearest at the precision of `x`. -/
def exp2M1 (x : AzFloat) : AzFloat := (exp2M1PrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
