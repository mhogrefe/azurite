/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.WrightOmega

/-!
## The omega constant

`Ω = W₀(1) = 0.5671432904097838729999686622103555497538157871865125081351…`, the real root of
`Ω e^Ω = 1` (equivalently `Ω = e^(−Ω)`, `Ω + ln Ω = 0`).

`Ω = ω(0)` for the Wright function `ω(x) = W₀(eˣ)`, and that is how it is computed
(`wrightOmegaPrecRound` at `0`): a Newton candidate for `y + ln y = 0` with half the bits
wanted, verified and refined by one enclosure of its residual — one logarithm at full
precision and the Newton steps below it, against about three and a half exponentials for
`lambertW0PrecRound` at `1` (a Halley candidate and its verification by the mean value
theorem).  No series of the hypergeometric kind is known for `Ω`, so one elementary function
at full precision is the floor for any method.

`Ω` is irrational (`ln Ω = −Ω`; `irrational_lambertW0_one`), so Ziv's loop has a termination
certificate and no fuel: the specification `omegaConstantPrecRound_eq`
(`Equiv/OmegaConstant.lean`) is "correctly rounded".
-/

namespace Azurite.AzFloat

/-- **The omega constant** `Ω = W₀(1)` rounded to precision `p` with `mode`, and the comparison
with the exact value (`NaN` at precision `0`). -/
def omegaConstantPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  wrightOmegaPrecRound zero p mode

/-- The omega constant rounded to nearest at precision `p`. -/
def omegaConstant (p : Nat) : AzFloat := (omegaConstantPrecRound p .Nearest).1

end Azurite.AzFloat
