/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GelfondBracket
import Azurite.AzFloat.Equiv.GelfondBracket

/-!
## The Gelfond–Schneider constant `2^√2`

`sqrt2Ln2Bracket w` encloses `√2 ln 2` (the floats below and above `√2` times the ends of
`ln2Bracket w`, directed products) and `gelfondSchneiderBracket w = expOfBracket` of it
(`AzFloat/GelfondBracket.lean`).  `2^√2` is irrational — the Gelfond–Schneider theorem (1934),
here `Azurite.irrational_two_rpow_sqrt_two` (`Transcendental/GelfondSchneider.lean`) — and the
brackets converge, so the Ziv loop has a termination certificate
(`gelfondSchneiderApprox_cert`, `Equiv/GelfondBracket.lean`): no fuel is involved in the
result, and the specification `gelfondSchneiderPrecRound_eq_liftVal₀`
(`Equiv/GelfondSchneider.lean`) is "correctly rounded".
-/

namespace Azurite.AzFloat

/-- `2^√2` rounded to precision `p` with `mode`, and the comparison with the exact value
(`NaN` at precision `0`).  The value is irrational (the Gelfond–Schneider theorem,
`Azurite.irrational_two_rpow_sqrt_two`), so the Ziv loop has a termination certificate
(`gelfondSchneiderApprox_cert`) and the result is always the correctly rounded value
(`gelfondSchneiderPrecRound_eq_liftVal₀`). -/
def gelfondSchneiderPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopBacked gelfondSchneiderApprox p mode (zivDefaultFuel p) (p + zivGuardBits)
      (gelfondSchneiderApprox_cert p mode _ (by unfold zivGuardBits; omega))

/-- `2^√2` rounded to nearest at precision `p`. -/
def gelfondSchneider (p : Nat) : AzFloat := (gelfondSchneiderPrecRound p .Nearest).1

end Azurite.AzFloat
