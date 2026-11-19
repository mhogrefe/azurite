/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Beta
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
* **Fuel**, as for floats: `betaRatPrecRound_eq_or` (`Equiv/BetaRat.lean`) is "correctly
  rounded, or `NaN`".
-/

namespace Azurite.AzFloat

/-- The integer `k` nearest to `q`, the sign of `q − k` (`true`: negative) and a positive
enclosure of `|q − k|`; `none` when `q` is an integer. -/
def gammaRatFrac (q : AzRat) (W : Nat) : Option (Bool × AzInt × Encl) :=
  let k := (q.round .Nearest).1
  let d := q - k.toAzRat
  if d.num = 0 then none
  else some (!d.sign, k, lnGammaRatEncl (if d.sign then d else -d) W)

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

/-- The bracket of `B(a, b)` as a pair of `Roundable`s (`s = a + b`), strict on both sides; the
dummy bracket `[−1, 1]` when the pieces give nothing. -/
def betaRatApprox (a b s : AzRat) (w : Nat) : Roundable × Roundable :=
  gammaApproxOf
    (betaEnclOf (lnGammaRatEncl a) (lnGammaRatEncl b) (lnGammaRatEncl s) (gammaRatExp a)
      (gammaRatExp b) (gammaRatExp s) (gammaRatFrac a) (gammaRatFrac b) (gammaRatFrac s) w) w

/-- `B(a, b)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` at a negative integer, for `p = 0` unless the value is `+∞`, or if the fuel runs
out). -/
def betaRatPrecRound (a b : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if betaRatPole a || betaRatPole b then (nan, .eq)
  else if a.num = 0 ∨ b.num = 0 then (infinity true, .eq)
  else if p = 0 then (nan, .eq)
  else
    match betaRatSmallInt? a b p mode with
    | some r => r
    | none =>
      match betaRatSmallInt? b a p mode with
      | some r => r
      | none =>
        if (a + b).den = 1 ∧ ((a + b).num = 0 ∨ (a + b).sign = false) then (zero, .eq)
        else zivLoop (betaRatApprox a b (a + b)) p mode (gammaFuel p) (max 64 (p + 32))

/-- `B(a, b)` rounded to nearest at precision `p`. -/
def betaRat (a b : AzRat) (p : Nat) : AzFloat := (betaRatPrecRound a b p .Nearest).1

end Azurite.AzFloat
