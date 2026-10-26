/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Exp2Bracket

/-!
## `2^x`

`exp2PrecRound x p mode` is `2^x` correctly rounded to precision `p` in `mode`, with the
comparison against the exact value; `exp2 x` rounds to nearest at the precision of `x`.  An
integer `x` gives the exact power of two (`powerOf2`, one `setPrecRound`); otherwise the
certified Ziv loop (no fuel) runs over `exp2Approx` (`2^x = exp (x ln 2)`, the bracket of
`x ln 2` from the bracket of `ln 2` and `expOfBracket`), total because `2^x` is irrational for
every non-integer dyadic `x`.  Special values: `2^NaN = NaN`, `2^(+∞) = +∞`, `2^(−∞) = 0`,
`2^0 = 1`.  The specification `exp2PrecRound_eq_liftVal` is in `Equiv/Exp2.lean`.
-/

namespace Azurite.AzFloat

/-- `2^x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def exp2PrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (zero, .eq)
  | zero => if p = 0 then (nan, .eq) else setPrecRound one p mode
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else if hi : isInteger (finite s e q m hv) = true then
      setPrecRound (powerOf2 (truncToAzInt (finite s e q m hv))) p mode
    else
      haveI : NeZero p := ⟨hp⟩
      zivLoopCertified (exp2Approx (finite s e q m hv) e) p mode (p + zivGuardBits)
        (exp2Approx_isSome_exists p mode s e hv hi (p + zivGuardBits)
          (by unfold zivGuardBits; omega))

/-- `2^x` rounded to nearest at the precision of `x`. -/
def exp2 (x : AzFloat) : AzFloat := (exp2PrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
