/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanBracket

/-!
## The bracket of `arctan (x) u / (2π)`

The arctangent measured in `u`ths of a turn: the common scaling step.

`atanPeriodScale A u V` multiplies an enclosure `A` of an angle `0 ≤ θ ≤ 2` by `u/(2π)`: one
interval division by `piBracket V`, then the exact float `u/2` with directed roundings.  It is
used by the brackets of `atan2 (y, x) u / (2π)` (`AzFloat/Atan2WithPeriodBracket.lean`, which
also serves the float `atanWithPeriodPrecRound`) and of the rational arctangent with a period
(`AzFloat/AtanRatWithPeriodBracket.lean`).

The proofs are in `Equiv/AtanWithPeriodBracket.lean`.
-/

namespace Azurite.AzFloat

/-- `A u / (2π)` for a nonnegative enclosure `A` and a natural `u`, at precision `V`. -/
def atanPeriodScale (A : Encl) (u : AzNat) (V : Nat) : Encl :=
  let d := Encl.div V A (piBracket V)
  let uf := ofAzNat u <<< AzInt.ofInt (-1)
  ((mulPrecRound d.1 uf V .Floor).1, (mulPrecRound d.2 uf V .Ceiling).1)

end Azurite.AzFloat
