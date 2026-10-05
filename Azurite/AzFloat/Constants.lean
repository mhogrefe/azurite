/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Rsqrt
import Azurite.AzFloat.Shift
import Azurite.AzFloat.Sqrt
import Azurite.AzFloat.Ziv

/-!
# Mathematical constants

Constants as functions of a destination precision and a rounding mode, after the author's
Malachite `Float` constants: each returns the correctly rounded value of the constant and the
comparison of the result with the exact value.  `Equiv/Constants.lean` proves that each is the
nullary lift `liftVal₀` of its real value.

The quadratic irrationals: `√2`, `√3`, `√5` are square roots of exact floats; `√2/2 = 1/√2`,
`√3/3 = 1/√3` and `√5/5 = 1/√5` are reciprocal square roots of exact floats; the golden ratio
`φ = (1 + √5)/2` is the one constant that is not a single correctly rounded primitive, and goes
through Ziv's loop (`Ziv.lean`) with the bracket `(1 + l)/2 ≤ φ ≤ (1 + h)/2`, where `l ≤ √5 ≤ h`
are a truncation of `√5` at the working precision and the next float up; both ends are exact
floats plus one half, rounded by `addPrecRound`.  Rounding is always possible from the working
precision `2p + 6` on, because `φ` is irrational and so at distance at least `2^(−2p−4)` from
every boundary at precision `p` (`phiApprox_possible`).

Each `cPrecRound p mode` has a companion `c p` rounding to nearest.
-/

namespace Azurite.AzFloat

/-- `√2` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def sqrt2PrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  sqrtPrecRound two p mode

/-- `√2` rounded to nearest at precision `p`. -/
def sqrt2 (p : Nat) : AzFloat := (sqrt2PrecRound p .Nearest).1

/-- `√3` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def sqrt3PrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  sqrtPrecRound (ofAzNat (AzNat.ofNat 3)) p mode

/-- `√3` rounded to nearest at precision `p`. -/
def sqrt3 (p : Nat) : AzFloat := (sqrt3PrecRound p .Nearest).1

/-- `√5` rounded to precision `p` with `mode`, and the comparison with the exact value. -/
def sqrt5PrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  sqrtPrecRound (ofAzNat (AzNat.ofNat 5)) p mode

/-- `√5` rounded to nearest at precision `p`. -/
def sqrt5 (p : Nat) : AzFloat := (sqrt5PrecRound p .Nearest).1

/-- `√2 / 2 = 1/√2` rounded to precision `p` with `mode`, and the comparison with the exact
value. -/
def sqrt2Over2PrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  rsqrtPrecRound two p mode

/-- `√2 / 2` rounded to nearest at precision `p`. -/
def sqrt2Over2 (p : Nat) : AzFloat := (sqrt2Over2PrecRound p .Nearest).1

/-- `√3 / 3 = 1/√3` rounded to precision `p` with `mode`, and the comparison with the exact
value. -/
def sqrt3Over3PrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  rsqrtPrecRound (ofAzNat (AzNat.ofNat 3)) p mode

/-- `√3 / 3` rounded to nearest at precision `p`. -/
def sqrt3Over3 (p : Nat) : AzFloat := (sqrt3Over3PrecRound p .Nearest).1

/-- `√5 / 5 = 1/√5` rounded to precision `p` with `mode`, and the comparison with the exact
value. -/
def sqrt5Over5PrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  rsqrtPrecRound (ofAzNat (AzNat.ofNat 5)) p mode

/-- `√5 / 5` rounded to nearest at precision `p`. -/
def sqrt5Over5 (p : Nat) : AzFloat := (sqrt5Over5PrecRound p .Nearest).1

/-- The bracket of the golden ratio at working precision `w`: `√5` truncated to `w` bits and
the next float up, each halved and increased by one half, given by their rounding
procedures. -/
def phiApprox (w : Nat) : Roundable × Roundable :=
  let lo := sqrtPrecRound (ofAzNat (AzNat.ofNat 5)) w .Floor
  let hi := (addPrecRound lo.1 (truncError lo) w .Ceiling).1
  (fun p mode => addPrecRound (lo.1 >>> (1 : Nat)) oneHalf p mode,
    fun p mode => addPrecRound (hi >>> (1 : Nat)) oneHalf p mode)

/-- The golden ratio `φ = (1 + √5)/2` rounded to precision `p` with `mode`, and the comparison
with the exact value. -/
def phiPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  zivLoop phiApprox p mode (zivFuel (2 * p + 6)) (p + zivGuardBits)

/-- The golden ratio rounded to nearest at precision `p`. -/
def phi (p : Nat) : AzFloat := (phiPrecRound p .Nearest).1

end Azurite.AzFloat
