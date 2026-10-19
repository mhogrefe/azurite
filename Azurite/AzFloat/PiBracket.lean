/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Agm
import Azurite.AzFloat.Constants
import Azurite.AzFloat.Div
import Azurite.AzInt.Instances
import Azurite.BrentZimmermann.Chapter4.BrentSalamin

/-!
## The Brent–Salamin bracket of `π`

The Gauss–Legendre / Brent–Salamin iteration (MCA §4.8.2, `BrentSalamin.lean`):
`a₀ = 1`, `b₀ = 1/√2`, `s₀ = 1/2`, `a' = (a + b)/2`, `b' = √(ab)`,
`s' = s − 2^(n+1) ((a − b)/2)²`, and `π_N = 2 a_{N+1}²/s_N` with `|π_N − π| ≤ 2^(−w)` for
`N = piSteps w = ⌊lg w⌋ + 1` (`abs_salaminApprox_piSteps_sub_pi_le`).

Everything is run on enclosures at working precision `w` with directed rounding (`PiBounds`,
`piStep`): lower ends round down, upper ends round up, and the lower end of `(a − b)²` is clamped
at `0` (`clampNonneg`), since the enclosure of `a − b` may straddle `0` once the AGM has
converged.  The final bracket (`piApprox`) is `[⌊π_N⁻ − 2^(1−w)⌋_w, ⌈π_N⁺ + 2^(1−w)⌉_w]` (the
widening `2^(1−w)` exceeds the truncation error `2^(−w)`, so the lower end is strictly below
`π`); its width is `O(w³ 2^(−w))` (`Equiv/PiBracket.lean`), and `π` is irrational, so Ziv's
loop needs no fuel (`Pi.lean`).
-/

namespace Azurite.AzFloat

/-- The enclosures of `a_n`, `b_n`, `s_n`. -/
structure PiBounds where
  aLo : AzFloat
  aHi : AzFloat
  bLo : AzFloat
  bHi : AzFloat
  sLo : AzFloat
  sHi : AzFloat

/-- `max(x, 0)` for a lower bound of a nonnegative quantity. -/
def clampNonneg (x : AzFloat) : AzFloat := if x.isNegative then zero else x

/-- One Brent–Salamin step from index `n` at working precision `w`. -/
def piStep (w n : Nat) (s : PiBounds) : PiBounds :=
  let dLo := clampNonneg (subPrecRound s.aLo s.bHi w .Floor).1
  let dHi := (subPrecRound s.aHi s.bLo w .Ceiling).1
  let tLo := (sqrPrecRound dLo w .Floor).1 <<< ((n : AzInt) - 1)
  let tHi := (sqrPrecRound dHi w .Ceiling).1 <<< ((n : AzInt) - 1)
  { aLo := (addPrecRound s.aLo s.bLo w .Floor).1 >>> (1 : Nat)
    aHi := (addPrecRound s.aHi s.bHi w .Ceiling).1 >>> (1 : Nat)
    bLo := (sqrtPrecRound (mulPrecRound s.aLo s.bLo w .Floor).1 w .Floor).1
    bHi := (sqrtPrecRound (mulPrecRound s.aHi s.bHi w .Ceiling).1 w .Ceiling).1
    sLo := (subPrecRound s.sLo tHi w .Floor).1
    sHi := (subPrecRound s.sHi tLo w .Ceiling).1 }

/-- Steps `0, …, n − 1`. -/
def piIter (w : Nat) : Nat → PiBounds → PiBounds
  | 0, s => s
  | n + 1, s => piStep w n (piIter w n s)

/-- `a₀ = 1`, `b₀ ∈ [⌊1/√2⌋_w, ⌈1/√2⌉_w]`, `s₀ = 1/2`. -/
def piInit (w : Nat) : PiBounds :=
  { aLo := one, aHi := one, bLo := (sqrt2Over2PrecRound w .Floor).1,
    bHi := (sqrt2Over2PrecRound w .Ceiling).1, sLo := oneHalf, sHi := oneHalf }

/-- The two ends of the bracket of `π` at working precision `w`. -/
def piBracket (w : Nat) : AzFloat × AzFloat :=
  let s := piIter w (BZ.piSteps w) (piInit w)
  let aLo := (addPrecRound s.aLo s.bLo w .Floor).1 >>> (1 : Nat)
  let aHi := (addPrecRound s.aHi s.bHi w .Ceiling).1 >>> (1 : Nat)
  let nLo := (sqrPrecRound aLo w .Floor).1 <<< (1 : Nat)
  let nHi := (sqrPrecRound aHi w .Ceiling).1 <<< (1 : Nat)
  let e := powerOf2 (1 - (w : AzInt))
  ((subPrecRound (divPrecRound nLo s.sHi w .Floor).1 e w .Floor).1,
    (addPrecRound (divPrecRound nHi s.sLo w .Ceiling).1 e w .Ceiling).1)

/-- The bracket of `π` at working precision `w`, as a pair of `Roundable`s. -/
def piApprox (w : Nat) : Roundable × Roundable :=
  let b := piBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

end Azurite.AzFloat
