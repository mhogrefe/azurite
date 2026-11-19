/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AgmConstants
import Azurite.AzFloat.Equiv.AgmConstants

/-!
## Gauss's constant

`G = 1/AGM(1, √2) = 0.8346268416740731862814297327990468089939930134903470024498…`
(`= Γ(1/4)²/(2π)^(3/2) = √2 K(1/√2)/π`, the reciprocal of the lemniscate-to-circle ratio).

Computed by the interval AGM of `Agm.lean`: `√2` is enclosed by its floor and ceiling at the
working precision `w` (`sqrt2PrecRound`), the enclosure is iterated, and `G` lies between
`⌊1/aHi⌋_w` and `⌈1/bLo⌉_w` (`gaussApprox`); Ziv's loop rounds.

`G` is irrational — `G = Γ(1/4)²/(2π)^(3/2)`, and `π` and `Γ(1/4)` are algebraically
independent (Chudnovsky 1976, formalized in `Azurite/Chudnovsky`; `irrational_gauss`) — and the
brackets converge, so the Ziv loop has a termination certificate (`gaussApprox_cert`,
`Equiv/AgmConstants.lean`): no fuel is involved in the result, and the specification
`gaussConstantPrecRound_eq_liftVal₀` (`Equiv/GaussConstant.lean`) is "correctly rounded".  The
bracket is in `AzFloat/AgmConstants.lean`.
-/

namespace Azurite.AzFloat

/-- **Gauss's constant** `G = 1/AGM(1, √2)` rounded to precision `p` with `mode`, and the
comparison with the exact value (`NaN` at precision `0`).  Always the correctly rounded value
(`gaussConstantPrecRound_eq_liftVal₀`): the loop with fuel is backed by a certified one
(`zivLoopBacked`). -/
def gaussConstantPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopBacked gaussApprox p mode (agmFuel p) (p + zivGuardBits)
      (gaussApprox_cert p mode _ (by unfold zivGuardBits; omega))

/-- Gauss's constant rounded to nearest at precision `p`. -/
def gaussConstant (p : Nat) : AzFloat := (gaussConstantPrecRound p .Nearest).1

end Azurite.AzFloat
