/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Beta
import Azurite.AzFloat.Equiv.BetaRatCertificate
import Azurite.AzFloat.GammaRat

/-!
## The Beta function of two rationals

`betaRatPrecRound a b p mode` is `B(a, b)` for `AzRat`s `a`, `b`, rounded to precision `p` in
`mode` with the comparison against the exact value; `betaRat a b p` rounds to nearest.  The
bracket is that of the float function (`lnAbsBetaEncl`, `AzFloat/BetaBracket.lean`) with the
arguments entering by enclosures: the roundings of `a`, of `b` and of the exact rational
`a + b`, and for the sines the roundings of their distances to the nearest integer
(`gammaRatFrac`).

* **Special values**, as for floats: `NaN` when `a` or `b` is a negative integer; `+∞` when one
  of them is `0`; **`0` exactly when `a + b` is a non-positive integer** — here the sum is
  simply formed.
* **Exact values**: for a positive integer `b ≤ 64` (`b = 1` included) and an `a` of moderate
  size, `B(a, b)` is the rational `(b − 1)! Dᵇ / ∏ (N + j D)` for `a = N/D`, rounded by one
  division (`betaIntQuot`).
* **Fuel**, as for floats: `betaRatPrecRoundFuel` has the fuel as an argument, and the
  specification is `betaRatPrecRoundFuel_zivSpec` (`Equiv/BetaRat.lean`).  **No fuel where
  the value is known to be irrational** (`betaRatSpecial`, `AzFloat/BetaRatBracket.lean`):
  `a`, `b` not integers and `a + b` a positive integer, or the denominators of `a` and `b`
  both in `{2, 4}` or both in `{2, 3, 6}` (Chudnovsky's theorem on `Γ(1/4)` and `Γ(1/3)`).
-/

namespace Azurite.AzFloat

/-- Is `q` a negative integer? -/
def betaRatPole (q : AzRat) : Bool :=
  decide (q.num ≠ 0) && decide (q.den = 1) && !q.sign

/-- **`B(a, n)` for a positive integer `b = n ≤ 64`** and an `a` whose numerator and
denominator have at most `2p + 1024` bits together; `none` otherwise. -/
def betaRatSmallInt? (a b : AzRat) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if b.den = 1 ∧ b.sign = true ∧ b.num ≠ 0 ∧ b.num ≤ AzNat.ofNat 64
      ∧ a.num.size + a.den.size ≤ 2 * p + 1024 then
    some (betaIntQuot (AzInt.mkNorm a.sign a.num) a.den.toAzInt b.num.toNat p mode)
  else none

/-- **`B(a, b)` rounded to precision `p` with `mode`, with the fuel of the Ziv loop
explicit**, and the comparison with the exact value.  At the arguments recognized by
`betaRatSpecial` the value is irrational and the loop is backed by a certified one
(`betaRatApprox_cert`): no fuel is involved there.  The specification is
`betaRatPrecRoundFuel_zivSpec` (`Equiv/BetaRat.lean`). -/
def betaRatPrecRoundFuel (fuel : Nat) (a b : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if betaRatPole a || betaRatPole b then (nan, .eq)
  else if a.num = 0 ∨ b.num = 0 then (infinity true, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    match betaRatSmallInt? a b p mode with
    | some r => r
    | none =>
      match betaRatSmallInt? b a p mode with
      | some r => r
      | none =>
        if hs : (a + b).den = 1 ∧ ((a + b).num = 0 ∨ (a + b).sign = false) then (zero, .eq)
        else if hc : betaRatSpecial a b (a + b) = true then
          haveI : NeZero p := ⟨hp⟩
          zivLoopBacked (betaRatApprox a b (a + b)) p mode fuel (max 64 (p + 32))
            (betaRatApprox_cert hc hs p mode _ (by omega))
        else zivLoop (betaRatApprox a b (a + b)) p mode fuel (max 64 (p + 32))

/-- `B(a, b)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` at a negative integer, for `p = 0` unless the value is `+∞`, or if the fuel runs
out): `betaRatPrecRoundFuel` at the fuel `gammaFuel p`. -/
def betaRatPrecRound (a b : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  betaRatPrecRoundFuel (gammaFuel p) a b p mode

/-- `B(a, b)` rounded to nearest at precision `p`. -/
def betaRat (a b : AzRat) (p : Nat) : AzFloat := (betaRatPrecRound a b p .Nearest).1

end Azurite.AzFloat
