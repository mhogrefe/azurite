/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Constants

/-!
# The golden ratio

`φ = (1 + √5)/2` is the one quadratic-irrational constant that is not a single correctly rounded
primitive: `phiPrecRound p mode` is the certified Ziv loop (`zivLoopCertified`, no fuel) over
`phiApprox` (`Constants.lean`: `l/2 + 1/2 ≤ φ ≤ h/2 + 1/2` for a truncation `l ≤ √5 ≤ h` at the
working precision and the next float up), certified by the irrationality of `φ`
(`phiApprox_isSome_exists`).  `(nan, .eq)` at precision `0`.  The specification
`phiPrecRound_eq_liftVal₀` is in `Equiv/Phi.lean`.
-/

namespace Azurite.AzFloat

/-- The golden ratio `φ = (1 + √5)/2` rounded to precision `p` with `mode`, and the comparison
with the exact value. -/
def phiPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified phiApprox p mode (p + zivGuardBits)
      (phiApprox_isSome_exists p mode (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- The golden ratio rounded to nearest at precision `p`. -/
def phi (p : Nat) : AzFloat := (phiPrecRound p .Nearest).1

end Azurite.AzFloat
