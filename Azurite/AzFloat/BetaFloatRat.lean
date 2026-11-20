/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BetaRat
import Azurite.AzFloat.LnBetaRat
import Azurite.AzFloat.Conversion

/-!
## The Beta function of a float and a rational

`betaFloatRatPrecRound a b p mode` is `B(a, b)` for an `AzFloat` `a` and an `AzRat` `b`,
rounded to precision `p` in `mode` with the comparison against the exact value;
`betaFloatRat a b p` rounds to nearest.  (`B` is symmetric: there is one order of the
arguments.)  With them `lnAbsBetaFloatRatPrecRound` (`ln |B(a, b)|` and the sign of `B`),
`lnBetaFloatRatPrecRound` (`ln B(a, b)`, `NaN` where `B < 0`), and `lnAbsBetaFloatRat`,
`lnBetaFloatRat`.

A finite float is a rational number, exactly (`toAzRat?`), so these are the functions of two
rationals (`AzFloat/BetaRat.lean`, `AzFloat/LnBetaRat.lean`) at that rational: the same
special values (`NaN` at a negative integer, `+∞` at `0`, `B = 0` exactly where `a + b` is a
non-positive integer — the sum is formed exactly), the same exact values (`B(a, n)` and
`B(n, b)` for a positive integer `n ≤ 64`), and no fuel where the value is known to be
irrational (`betaRatSpecial`: `a + b` a positive integer; `a`, `b` both with denominators in
`{2, 4}`, or both in `{2, 3, 6}`).  Rounding `b` to a float first and calling `betaPrecRound`
would give `B` of another number.

* **Not finite**: `NaN` for a `NaN` and for `−∞`; `B(+∞, b) = 0` for `b > 0`, `NaN` otherwise
  (`ln |B| = ln B = −∞` there).
* **Cost.**  The rational has the bits of the significand and those of the exponent's
  distance from it: an `a` below `2^(−10⁸)` in absolute value is a rational with a
  denominator of that many bits, and is slow.  (For a large `a` the Beta function itself
  needs as many bits as the exponent.)

The specifications (`betaFloatRatPrecRoundFuel_zivSpec`, …) are in
`Equiv/BetaFloatRat.lean`.
-/

namespace Azurite.AzFloat

/-- Is the rational `b` positive? -/
def ratIsPos (b : AzRat) : Bool := b.sign && decide (b.num ≠ 0)

/-- `B(a, b)` for a float `a` that is not finite: `0` for `a = +∞` and `b > 0`, else `NaN`. -/
def betaFloatRatInfinite (a : AzFloat) (b : AzRat) : AzFloat × Ordering :=
  match a with
  | infinity true => if ratIsPos b then (zero, .eq) else (nan, .eq)
  | _ => (nan, .eq)

/-- `ln |B(a, b)|` for a float `a` that is not finite: `−∞` for `a = +∞` and `b > 0`, else
`NaN`. -/
def lnAbsBetaFloatRatInfinite (a : AzFloat) (b : AzRat) : AzFloat × Ordering :=
  match a with
  | infinity true => if ratIsPos b then (infinity false, .eq) else (nan, .eq)
  | _ => (nan, .eq)

/-- **`B(a, b)` for a float `a` and a rational `b`, rounded to precision `p` with `mode`, with
the fuel of the Ziv loop explicit**, and the comparison with the exact value:
`betaRatPrecRoundFuel` at the rational `a`.  The specification is
`betaFloatRatPrecRoundFuel_zivSpec` (`Equiv/BetaFloatRat.lean`). -/
def betaFloatRatPrecRoundFuel (fuel : Nat) (a : AzFloat) (b : AzRat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  match a.toAzRat? with
  | some q => betaRatPrecRoundFuel fuel q b p mode
  | none => betaFloatRatInfinite a b

/-- `B(a, b)` for a float `a` and a rational `b`, rounded to precision `p` with `mode`, and
the comparison with the exact value (`(nan, .eq)` at a negative integer, for `p = 0` unless
the value is `0` or `+∞`, or if the fuel runs out): `betaFloatRatPrecRoundFuel` at the fuel
`gammaFuel p`. -/
def betaFloatRatPrecRound (a : AzFloat) (b : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  betaFloatRatPrecRoundFuel (gammaFuel p) a b p mode

/-- `B(a, b)` for a float `a` and a rational `b`, rounded to nearest at precision `p`. -/
def betaFloatRat (a : AzFloat) (b : AzRat) (p : Nat) : AzFloat :=
  (betaFloatRatPrecRound a b p .Nearest).1

/-- **`ln |B(a, b)|` for a float `a` and a rational `b`, rounded to precision `p` with `mode`,
the comparison with the exact value, and the sign of `B(a, b)`** (`true`: positive), with the
fuel of the loop explicit: `lnAbsBetaRatPrecRoundFuel` at the rational `a`. -/
def lnAbsBetaFloatRatPrecRoundFuel (fuel : Nat) (a : AzFloat) (b : AzRat) (p : Nat)
    (mode : RoundingMode) : (AzFloat × Ordering) × Bool :=
  match a.toAzRat? with
  | some q => lnAbsBetaRatPrecRoundFuel fuel q b p mode
  | none => (lnAbsBetaFloatRatInfinite a b, true)

/-- `ln |B(a, b)|` for a float `a` and a rational `b`, rounded to precision `p` with `mode`,
the comparison with the exact value, and the sign of `B(a, b)`:
`lnAbsBetaFloatRatPrecRoundFuel` at the fuel `gammaFuel p`. -/
def lnAbsBetaFloatRatPrecRound (a : AzFloat) (b : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsBetaFloatRatPrecRoundFuel (gammaFuel p) a b p mode

/-- `ln |B(a, b)|` rounded to nearest at precision `p`, and the sign of `B(a, b)`. -/
def lnAbsBetaFloatRat (a : AzFloat) (b : AzRat) (p : Nat) : AzFloat × Bool :=
  let r := lnAbsBetaFloatRatPrecRound a b p .Nearest
  (r.1.1, r.2)

/-- **`ln B(a, b)` for a float `a` and a rational `b`**, rounded to precision `p` with `mode`,
and the comparison with the exact value, with the fuel explicit:
`lnAbsBetaFloatRatPrecRoundFuel` where `B(a, b) ≥ 0`, `(nan, .eq)` where `B(a, b) < 0`. -/
def lnBetaFloatRatPrecRoundFuel (fuel : Nat) (a : AzFloat) (b : AzRat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  let r := lnAbsBetaFloatRatPrecRoundFuel fuel a b p mode
  if r.2 then r.1 else (nan, .eq)

/-- `ln B(a, b)` for a float `a` and a rational `b`: `lnBetaFloatRatPrecRoundFuel` at the
fuel `gammaFuel p`. -/
def lnBetaFloatRatPrecRound (a : AzFloat) (b : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  lnBetaFloatRatPrecRoundFuel (gammaFuel p) a b p mode

/-- `ln B(a, b)` rounded to nearest at precision `p`. -/
def lnBetaFloatRat (a : AzFloat) (b : AzRat) (p : Nat) : AzFloat :=
  (lnBetaFloatRatPrecRound a b p .Nearest).1

end Azurite.AzFloat
