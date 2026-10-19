/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Agm
import Azurite.AzFloat.Constants
import Azurite.AzFloat.Div

/-!
## Gauss's constant

`G = 1/AGM(1, √2) = 0.8346268416740731862814297327990468089939930134903470024498…`
(`= Γ(1/4)²/(2π)^(3/2) = √2 K(1/√2)/π`, the reciprocal of the lemniscate-to-circle ratio).

Computed by the interval AGM of `Agm.lean`: `√2` is enclosed by its floor and ceiling at the
working precision `w` (`sqrt2PrecRound`), the enclosure is iterated, and `G` lies between
`⌊1/aHi⌋_w` and `⌈1/bLo⌉_w` (`gaussApprox`); Ziv's loop (`zivLoop`, fuel `agmFuel p`) rounds.

Termination: `G` is transcendental — `G = Γ(1/4)²/(2π)^(3/2)` and Chudnovsky (1976) proved `π`
and `Γ(1/4)` algebraically independent — but this is the CM case of the deep theorem behind the
general AGM, with no simpler irrationality proof known and nothing in Mathlib, so the loop has
fuel and the specification is "correctly rounded or `NaN`" (`Equiv/GaussConstant.lean`); the fuel
runs out only if `G` is within about `2^(−16(p+64))` of a rounding boundary.
-/

namespace Azurite.AzFloat

/-- The two ends of the bracket of `G = 1/AGM(1, √2)` at working precision `w`. -/
def gaussBracket (w : Nat) : AzFloat × AzFloat :=
  let s2lo := (sqrt2PrecRound w .Floor).1
  let s2hi := (sqrt2PrecRound w .Ceiling).1
  let s := agmIter w (w + 4) (agmStep w ⟨one, one, s2lo, s2hi⟩)
  ((divPrecRound one s.aHi w .Floor).1, (divPrecRound one s.bLo w .Ceiling).1)

/-- The bracket of `G` at working precision `w`, as a pair of `Roundable`s. -/
def gaussApprox (w : Nat) : Roundable × Roundable :=
  (fun p mode => setPrecRound (gaussBracket w).1 p mode,
    fun p mode => setPrecRound (gaussBracket w).2 p mode)

/-- **Gauss's constant** `G = 1/AGM(1, √2)` rounded to precision `p` with `mode`, and the
comparison with the exact value (`NaN` if the fuel runs out). -/
def gaussConstantPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  zivLoop gaussApprox p mode (agmFuel p) (p + zivGuardBits)

/-- Gauss's constant rounded to nearest at precision `p`. -/
def gaussConstant (p : Nat) : AzFloat := (gaussConstantPrecRound p .Nearest).1

end Azurite.AzFloat
