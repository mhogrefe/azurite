/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GelfondBracket
import Azurite.AzFloat.Equiv.GelfondBracket

/-!
## Ramanujan's constant `e^(π √163)`

`piSqrt163Bracket w` multiplies the bracket of `π` by the bracket of `√163` (`sqrtBracket` at the
exact float `163`) with directed rounding; `ramanujanBracket w = expOfBracket` of it
(`AzFloat/GelfondBracket.lean`).  `e^(π √163) = (−1)^(−i √163)` is irrational — the
Gelfond–Schneider theorem, here `Azurite.irrational_exp_pi_sqrt`
(`Transcendental/GelfondSchneider.lean`) — and the brackets converge, so the Ziv loop has a
termination certificate (`ramanujanApprox_cert`, `Equiv/GelfondBracket.lean`): no fuel is
involved in the result, and the specification `ramanujanPrecRound_eq_liftVal₀`
(`Equiv/Ramanujan.lean`) is "correctly rounded".  `e^(π √163) =
262537412640768743.99999999999925…` is within `7.5 · 10^(−13)` of the integer `640320³ + 744`,
so the first Ziv level succeeds only from precision about `100` on; the loop doubles the
working precision until it does.
-/

namespace Azurite.AzFloat

/-- `e^(π √163)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`NaN` at precision `0`).  The value is irrational (the Gelfond–Schneider theorem,
`Azurite.irrational_exp_pi_sqrt`), so the Ziv loop has a termination certificate
(`ramanujanApprox_cert`) and the result is always the correctly rounded value
(`ramanujanPrecRound_eq_liftVal₀`); the loop with fuel in front of the certified one keeps the
function evaluable by the kernel (`zivLoopBacked`, used in `Transcendental/Ramanujan.lean`). -/
def ramanujanPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopBacked ramanujanApprox p mode (zivDefaultFuel p) (p + zivGuardBits)
      (ramanujanApprox_cert p mode _ (by unfold zivGuardBits; omega))

/-- `e^(π √163)` rounded to nearest at precision `p`. -/
def ramanujan (p : Nat) : AzFloat := (ramanujanPrecRound p .Nearest).1

end Azurite.AzFloat
