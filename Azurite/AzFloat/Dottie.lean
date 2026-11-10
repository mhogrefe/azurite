/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.DottieBracket

/-!
## The Dottie number

`dottiePrecRound p mode` is the Dottie number `d = 0.7390851332…`, the solution of `cos x = x`,
correctly rounded to precision `p` in `mode`, with the comparison against the exact value;
`dottie p` rounds to nearest.  A certified Ziv loop (`zivLoopCertified`, no fuel) on
`dottieApprox` (`AzFloat/DottieBracket.lean`: Newton's iteration for the candidate, the residual
bound `|n − d| ≤ |n − cos n|` for the verified bracket), total because `d` is irrational
(`irrational_dottie`: a rational `d` would make `cos d = d` rational).  The specification
`dottiePrecRound_eq_liftVal₀` is in `Equiv/Dottie.lean`.
-/

namespace Azurite.AzFloat

/-- The Dottie number rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` for `p = 0`). -/
def dottiePrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified dottieApprox p mode (p + zivGuardBits)
      (dottieApprox_isSome_exists p mode (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- The Dottie number rounded to nearest at precision `p`. -/
def dottie (p : Nat) : AzFloat := (dottiePrecRound p .Nearest).1

end Azurite.AzFloat
