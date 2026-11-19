/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AgmConstants
import Azurite.AzFloat.Equiv.AgmConstants

/-!
## The lemniscate constant

`ϖ = 2 ∫₀¹ dt/√(1 − t⁴) = π · G = π/AGM(1, √2) = 2.62205755429211981046483958989111941368…`
(`Chapter4/Lemniscate.lean`).  The bracket is the product of the brackets of `π`
(`piBracket`) and of Gauss's constant `G` (`gaussBracket`) at the working precision, rounded
outwards (`lemniscateBracket`), and Ziv's loop rounds it.

`ϖ = Γ(1/4)²/(2√(2π))` is irrational — `π` and `Γ(1/4)` are algebraically independent
(Chudnovsky 1976, formalized in `Azurite/Chudnovsky`; `irrational_lemniscate`) — and the
brackets converge, so the Ziv loop has a termination certificate (`lemniscateApprox_cert`,
`Equiv/AgmConstants.lean`): no fuel is involved in the result, and the specification
`lemniscateConstantPrecRound_eq_liftVal₀` (`Equiv/Lemniscate.lean`) is "correctly rounded".
-/

namespace Azurite.AzFloat

/-- **The lemniscate constant** `ϖ` rounded to precision `p` with `mode`, and the comparison
with the exact value (`NaN` at precision `0`).  Always the correctly rounded value
(`lemniscateConstantPrecRound_eq_liftVal₀`). -/
def lemniscateConstantPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopBacked lemniscateApprox p mode (agmFuel p) (p + zivGuardBits)
      (lemniscateApprox_cert p mode _ (by unfold zivGuardBits; omega))

/-- The lemniscate constant rounded to nearest at precision `p`. -/
def lemniscateConstant (p : Nat) : AzFloat := (lemniscateConstantPrecRound p .Nearest).1

end Azurite.AzFloat
