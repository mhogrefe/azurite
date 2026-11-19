/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AgmConstants
import Azurite.AzFloat.LnGamma
import Azurite.AzFloat.Equiv.AgmConstants

/-!
## The constants `Γ(1/4)` and `Γ(1/3)`

`Γ(1/4) = 3.62560990822190831193068515586767200299…` and
`Γ(1/3) = 2.67893853470774763365569294097467764412…`, by the arithmetic–geometric mean
(`Transcendental/GammaAGM.lean`):

  `Γ(1/4)² = 2π √(2π) / AGM(1, √2)`,
  `Γ(1/3)³ = 2 ∛2 π² / AGM(√((√3 + 3/2)/2), √√3)`.

Each is one interval AGM (`Encl.agm`, the iteration of `Agm.lean` from two enclosures), the
bracket of `π`, and a few roots at the working precision; the AGM starts from two numbers
that agree to a few percent, so it is in its quadratic regime from the first step.

Both constants are irrational (Chudnovsky 1976: `π` and `Γ(1/4)`, and `π` and `Γ(1/3)`, are
algebraically independent; formalized in `Azurite/Chudnovsky`) and the enclosures converge
(`Equiv/EnclConv.lean`), so the Ziv loops have termination certificates
(`gammaOneQuarterApprox_cert`, `gammaOneThirdApprox_cert`, `Equiv/AgmConstants.lean`): no fuel
is involved in the results, and the specifications (`Equiv/GammaConstants.lean`) are
"correctly rounded".  The enclosures themselves are in `AzFloat/AgmConstants.lean`.
-/

namespace Azurite.AzFloat

/-- **`Γ(1/4)`** rounded to precision `p` with `mode`, and the comparison with the exact value
(`NaN` at precision `0`).  Always the correctly rounded value
(`gammaOneQuarterPrecRound_eq`): the loop with fuel is backed by a certified one
(`zivLoopBacked`). -/
def gammaOneQuarterPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopBacked gammaOneQuarterApprox p mode (agmFuel p) (max 64 (p + 32))
      (gammaOneQuarterApprox_cert p mode _ (by omega))

/-- `Γ(1/4)` rounded to nearest at precision `p`. -/
def gammaOneQuarter (p : Nat) : AzFloat := (gammaOneQuarterPrecRound p .Nearest).1

/-- **`Γ(1/3)`** rounded to precision `p` with `mode`, and the comparison with the exact value
(`NaN` at precision `0`).  Always the correctly rounded value
(`gammaOneThirdPrecRound_eq`). -/
def gammaOneThirdPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopBacked gammaOneThirdApprox p mode (agmFuel p) (max 64 (p + 32))
      (gammaOneThirdApprox_cert p mode _ (by omega))

/-- `Γ(1/3)` rounded to nearest at precision `p`. -/
def gammaOneThird (p : Nat) : AzFloat := (gammaOneThirdPrecRound p .Nearest).1

end Azurite.AzFloat
