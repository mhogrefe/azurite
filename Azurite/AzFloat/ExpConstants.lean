/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Exp
import Azurite.AzFloat.Equiv.Ln10Bracket

/-!
## The constants `e`, `ln 10`, `log₁₀ e`, `log₂ 10` and `log₁₀ 2`

`e = exp 1` is `expPrecRound` at `one`.  The other four are certified Ziv loops (no fuel) over
the brackets of `AzFloat/Ln10Bracket`: `ln 10` by one AGM run at each level,
`log₁₀ e = 1/ln 10`, `log₂ 10 = ln 10 / ln 2` and `log₁₀ 2 = ln 2 / ln 10` by directed divisions
of brackets.  All return `(nan, .eq)` at precision `0` (no float set to round into), like every
`…PrecRound`.  The specifications are in `Equiv/ExpConstants.lean`.
-/

namespace Azurite.AzFloat

/-- `e` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def ePrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if p = 0 then (nan, .eq) else expPrecRound one p mode

/-- `e` rounded to nearest at precision `p`. -/
def e (p : Nat) : AzFloat := (ePrecRound p .Nearest).1

/-- `ln 10` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def ln10PrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified ln10Approx p mode (p + zivGuardBits)
      (ln10Approx_isSome_exists p mode (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `ln 10` rounded to nearest at precision `p`. -/
def ln10 (p : Nat) : AzFloat := (ln10PrecRound p .Nearest).1

/-- `log₁₀ e = 1/ln 10` rounded to precision `p` with `mode`, and the comparison with the exact
value. -/
def log10EPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified log10EApprox p mode (p + zivGuardBits)
      (log10EApprox_isSome_exists p mode (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `log₁₀ e` rounded to nearest at precision `p`. -/
def log10E (p : Nat) : AzFloat := (log10EPrecRound p .Nearest).1

/-- `log₂ 10 = ln 10 / ln 2` rounded to precision `p` with `mode`, and the comparison with the
exact value. -/
def log2TenPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified log2TenApprox p mode (p + zivGuardBits)
      (log2TenApprox_isSome_exists p mode (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `log₂ 10` rounded to nearest at precision `p`. -/
def log2Ten (p : Nat) : AzFloat := (log2TenPrecRound p .Nearest).1

/-- `log₁₀ 2 = ln 2 / ln 10` rounded to precision `p` with `mode`, and the comparison with the
exact value. -/
def log10TwoPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified log10TwoApprox p mode (p + zivGuardBits)
      (log10TwoApprox_isSome_exists p mode (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `log₁₀ 2` rounded to nearest at precision `p`. -/
def log10Two (p : Nat) : AzFloat := (log10TwoPrecRound p .Nearest).1

end Azurite.AzFloat
