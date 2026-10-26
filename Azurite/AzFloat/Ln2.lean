/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Ln2Bracket

/-!
## The constant `ln 2`

`ln2PrecRound p mode` is `ln 2` correctly rounded to precision `p` in `mode`, with the comparison
against the exact value; `ln2 p` rounds to nearest.  It is the certified Ziv loop
(`zivLoopCertified`) over the float brackets of `Ln2Bracket.lean`, started at the working
precision `p + 64`: each level computes the three `atanh` series once by binary splitting, forms
the two exact ends as unreduced fractions, divides each once with directed rounding, and tests
whether the rounding is determined; the certificate
`ln2Approx_isSome_exists` (from the irrationality of `ln 2`, Hermite's theorem) guarantees that
some level succeeds, so there is no fuel and no `NaN` fallback.  The specification
`ln2PrecRound_eq_liftVal₀` is in `Equiv/Ln2.lean`.
-/

namespace Azurite.AzFloat

/-- `ln 2` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def ln2PrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified ln2Approx p mode (p + zivGuardBits)
      (ln2Approx_isSome_exists p mode (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `ln 2` rounded to nearest at precision `p`. -/
def ln2 (p : Nat) : AzFloat := (ln2PrecRound p .Nearest).1

/-- `log₂ e = 1/ln 2` rounded to precision `p` with `mode`, and the comparison with the exact
value: the certified Ziv loop over the reciprocal brackets of `ln 2`. -/
def log2EPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified log2EApprox p mode (p + zivGuardBits)
      (log2EApprox_isSome_exists p mode (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `log₂ e` rounded to nearest at precision `p`. -/
def log2E (p : Nat) : AzFloat := (log2EPrecRound p .Nearest).1

end Azurite.AzFloat
