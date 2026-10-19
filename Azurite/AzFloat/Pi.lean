/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.PiBracket

/-!
## The constant `π`

`π` by the Brent–Salamin (Gauss–Legendre) AGM iteration (MCA §4.8.2), run on enclosures with
directed rounding (`PiBracket.lean`), and rounded by the certified Ziv loop: `π` is irrational
(`irrational_pi`) and the bracket width tends to zero (`piApprox_spec`), so `zivLoopCertified`
needs no fuel and `piPrecRound` is total and proven correctly rounded (`Equiv/Pi.lean`).

The cost at precision `p` is dominated by the first Ziv level, `w = p + 64`: `⌊lg w⌋ + 1` AGM
steps, each a multiplication, a square root, a square and three additions at precision `w`,
then one division.
-/

namespace Azurite.AzFloat

/-- `π` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def piPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (zero, .lt)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified piApprox p mode (p + zivGuardBits)
      (piApprox_isSome_exists p mode (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `π` rounded to nearest at precision `p`. -/
def pi (p : Nat) : AzFloat := (piPrecRound p .Nearest).1

end Azurite.AzFloat
