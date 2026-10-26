/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Pi
import Azurite.AzFloat.Equiv.PiDiv3Bracket
import Azurite.AzFloat.Equiv.OneDivPiBracket

/-!
## The constants `τ = 2π`, `π/2`, `π/3`, `π/4`, `π/6`, `π/8`, `1/π`, `2/π`

`τ`, `π/2`, `π/4` and `π/8` are exact shifts of the correctly rounded `π` (the float set is
scale-invariant, so the rounding and its comparison carry over: `roundVal_mul_two_zpow`).  `π/3`
is a certified Ziv loop (no fuel) over `piDiv3Approx`, and `π/6` is its exact shift; likewise
`1/π` over `oneDivPiApprox` and `2/π` its exact shift.  All return `(zero, .lt)` at precision
`0`, like `pi`.  The specifications are in `Equiv/PiMultiples.lean`.
-/

namespace Azurite.AzFloat

/-- `τ = 2π` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def tauPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  let r := piPrecRound p mode
  (r.1 <<< AzInt.ofInt 1, r.2)

/-- `τ = 2π` rounded to nearest at precision `p`. -/
def tau (p : Nat) : AzFloat := (tauPrecRound p .Nearest).1

/-- `π/2` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def piDiv2PrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  let r := piPrecRound p mode
  (r.1 <<< AzInt.ofInt (-1), r.2)

/-- `π/2` rounded to nearest at precision `p`. -/
def piDiv2 (p : Nat) : AzFloat := (piDiv2PrecRound p .Nearest).1

/-- `π/4` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def piDiv4PrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  let r := piPrecRound p mode
  (r.1 <<< AzInt.ofInt (-2), r.2)

/-- `π/4` rounded to nearest at precision `p`. -/
def piDiv4 (p : Nat) : AzFloat := (piDiv4PrecRound p .Nearest).1

/-- `π/8` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def piDiv8PrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  let r := piPrecRound p mode
  (r.1 <<< AzInt.ofInt (-3), r.2)

/-- `π/8` rounded to nearest at precision `p`. -/
def piDiv8 (p : Nat) : AzFloat := (piDiv8PrecRound p .Nearest).1

/-- `π/3` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def piDiv3PrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (zero, .lt)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified piDiv3Approx p mode (p + zivGuardBits)
      (piDiv3Approx_isSome_exists p mode (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `π/3` rounded to nearest at precision `p`. -/
def piDiv3 (p : Nat) : AzFloat := (piDiv3PrecRound p .Nearest).1

/-- `π/6` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def piDiv6PrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  let r := piDiv3PrecRound p mode
  (r.1 <<< AzInt.ofInt (-1), r.2)

/-- `π/6` rounded to nearest at precision `p`. -/
def piDiv6 (p : Nat) : AzFloat := (piDiv6PrecRound p .Nearest).1

/-- `1/π` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def oneDivPiPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (zero, .lt)
  else
    haveI : NeZero p := ⟨hp⟩
    zivLoopCertified oneDivPiApprox p mode (p + zivGuardBits)
      (oneDivPiApprox_isSome_exists p mode (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `1/π` rounded to nearest at precision `p`. -/
def oneDivPi (p : Nat) : AzFloat := (oneDivPiPrecRound p .Nearest).1

/-- `2/π` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def twoDivPiPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  let r := oneDivPiPrecRound p mode
  (r.1 <<< AzInt.ofInt 1, r.2)

/-- `2/π` rounded to nearest at precision `p`. -/
def twoDivPi (p : Nat) : AzFloat := (twoDivPiPrecRound p .Nearest).1

end Azurite.AzFloat
