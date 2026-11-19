/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GelfondBracket
import Azurite.AzFloat.Equiv.GelfondBracket

/-!
## Gelfond's constant `e^π`

`gelfondBracket w = expOfBracket (piBracket w) w` (`AzFloat/GelfondBracket.lean`;
`AzFloat/ExpApprox`: the exponential of a bracket).  `e^π = (−1)^(−i)` is irrational —
Gelfond's theorem (1929), here `Azurite.irrational_exp_pi`
(`Transcendental/GelfondSchneider.lean`) — and the brackets converge, so the Ziv loop has a
termination certificate (`gelfondApprox_cert`, `Equiv/GelfondBracket.lean`): no fuel is
involved in the result, and the specification `gelfondPrecRound_eq_liftVal₀`
(`Equiv/Gelfond.lean`) is "correctly rounded".
-/

namespace Azurite.AzFloat

/-- `e^π` rounded to precision `p` with `mode`, and the comparison with the exact value
(`NaN` at precision `0`).  The value is irrational (Gelfond's theorem,
`Azurite.irrational_exp_pi`), so the Ziv loop has a termination certificate
(`gelfondApprox_cert`) and the result is always the correctly rounded value
(`gelfondPrecRound_eq_liftVal₀`); the loop with fuel in front of the certified one keeps the
function evaluable by the kernel (`zivLoopBacked`). -/
def gelfondPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopBacked gelfondApprox p mode (zivDefaultFuel p) (p + zivGuardBits)
      (gelfondApprox_cert p mode _ (by unfold zivGuardBits; omega))

/-- `e^π` rounded to nearest at precision `p`. -/
def gelfond (p : Nat) : AzFloat := (gelfondPrecRound p .Nearest).1

end Azurite.AzFloat
