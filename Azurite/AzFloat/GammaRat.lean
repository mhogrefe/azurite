/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gamma
import Azurite.AzFloat.LnGamma
import Azurite.AzFloat.Conversion
import Azurite.AzRat.Sub
import Azurite.AzRat.Instances
import Azurite.AzRat.Round
import Azurite.AzRat.Unary
import Azurite.AzRat.Mul
import Azurite.AzRat.Conversion

/-!
## `Γ(q)` and `1/Γ(q)` for a rational `q`

`gammaRatPrecRound q p mode` is `Γ(q)` and `reciprocalGammaRatPrecRound q p mode` is `1/Γ(q)`
for an `AzRat` `q`, rounded to precision `p` in `mode`, with the comparison against the exact
value; `gammaRat q p` and `reciprocalGammaRat q p` round to nearest.

* **Special values**, as for the float functions (`AzFloat/Gamma.lean`): `Γ(0) = +∞`, `NaN` at
  the poles `q = −1, −2, …`; `1/Γ(q) = 0` at `q = 0, −1, −2, …`.
* **Positive integers.**  `Γ(n) = (n − 1)!` exactly, rounded once, when
  `n ≤ gammaIntBound p`; `1/Γ(n)` by one correctly rounded division.
* **Tiny arguments** (`gammaRatTiny?`, `reciprocalGammaRatTiny?`): `−Γ(q)` lies in
  `(−1/q, −1/q + 2)` and `1/Γ(q)` in `(q, q + q²)`; the ends are rationals, rounded outwards,
  and one test of `roundingPossible` settles the rounding.  The test fails when a rounding
  boundary lies within `2` of `1/q` (say `q = 1/(2^200 + 1)` at 53 bits); then the value has
  to be known to about `|e|` bits beyond the precision, and the loop starts there.
* **Everything else.**  Ziv's loop with the fuel of the float functions on the pieces of
  `AzFloat/GammaBracket.lean`, the argument entering by enclosures of rationals: the roundings
  of `q` (or of `1 − q`, an exact rational, for `q < 0`) for the bracket of `ln Γ`, and those
  of `|q − k|`, `k` the integer nearest to `q`, for the sine of the reflection formula.

The specifications `gammaRatPrecRound_eq_or` and `reciprocalGammaRatPrecRound_eq_or`
("correctly rounded, or `NaN`") are in `Equiv/GammaRat.lean`.
-/

namespace Azurite.AzFloat

/-- An exponent `e` with `|q| < 2^e`, from the rounding of `q` away from zero. -/
def gammaRatExp (q : AzRat) : AzInt :=
  expOf (ofAzRatRound q 32 (if q.sign then .Ceiling else .Floor)).1

/-- `(neg, S)` with `S` a positive enclosure of `|sin (π q)|` and `neg` the sign of
`sin (π q)` (`true`: negative); `none` when `q` is an integer or the enclosure is not
positive. -/
def gammaRatSinEncl (q : AzRat) (W w : Nat) : Option (Bool × Encl) :=
  let k := (q.round .Nearest).1
  let d := q - k.toAzRat
  if d.num = 0 then none
  else gammaSinOfFrac (!d.sign) k (lnGammaRatEncl (if d.sign then d else -d) W) W w

/-- `gammaCore` for a rational `q ≠ 0` that is positive (`pos`) or negative and not an
integer, with `|q| < 2^e`. -/
def gammaRatCore (recip : Bool) (q : AzRat) (e : AzInt) (pos : Bool) (w : Nat) :
    Option (Bool × Encl) :=
  if pos then
    let wL := w + gammaLnBits e
    (gammaExpEncl recip (lnGammaBracketEncl (lnGammaRatEncl q wL) e wL) w).map
      fun b => (false, b)
  else
    let e' := (if e.sign then e else 0) + 1
    let wL := w + gammaLnBits e'
    gammaReflect recip
      (gammaExpEncl false (lnGammaBracketEncl (lnGammaRatEncl (1 - q) wL) e' wL) w)
      (gammaRatSinEncl q (w + 16) w) w

/-- The bracket of `Γ(q)` or `1/Γ(q)` as a pair of `Roundable`s. -/
def gammaRatApprox (recip : Bool) (q : AzRat) (e : AzInt) (pos : Bool) (w : Nat) :
    Roundable × Roundable :=
  gammaApproxOf (gammaRatCore recip q e pos w) w

/-- Is `q` tiny at precision `p`: `|q| < 2^e` with `e ≤ −(p + 72)`, and `|q| ≤ 1/2` by its
roundings at 64 bits (the latter is what the proofs use). -/
def gammaRatIsTiny (q : AzRat) (e : AzInt) (p : Nat) : Bool :=
  !e.sign && decide (p + zivGuardBits + 8 ≤ e.abs.toNat)
    && le (ofAzRatRound q 64 .Ceiling).1 (one <<< AzInt.ofInt (-1))
    && le (-(one <<< AzInt.ofInt (-1))) (ofAzRatRound q 64 .Floor).1

/-- **The tiny-argument path of `Γ(q)`**: `−Γ(q)` lies in `(−1/q, −1/q + 2)`, rounded in the
negated mode from the outward roundings of the two rational ends. -/
def gammaRatTiny? (q : AzRat) (e : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if gammaRatIsTiny q e p then
    let W := p + zivGuardBits + 8
    let r := -q⁻¹
    let lo := (ofAzRatRound r W .Floor).1
    let hi := (ofAzRatRound (r + 1 + 1) W .Ceiling).1
    (roundingPossible (fun P M => setPrecRound lo P M) (fun P M => setPrecRound hi P M) p
      (-mode)).map fun r => (-r.1, r.2.swap)
  else none

/-- **The tiny-argument path of `1/Γ(q)`**: the value lies in `(q, q + q²)`. -/
def reciprocalGammaRatTiny? (q : AzRat) (e : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if gammaRatIsTiny q e p then
    let W := p + zivGuardBits + 8
    let lo := (ofAzRatRound q W .Floor).1
    let hi := (ofAzRatRound (q + q * q) W .Ceiling).1
    roundingPossible (fun P M => setPrecRound lo P M) (fun P M => setPrecRound hi P M) p mode
  else none

/-- The first working precision of the loops: `p + 32`, and `|e|` more for a tiny argument
whose one-test path failed. -/
def gammaRatStart (q : AzRat) (e : AzInt) (p : Nat) : Nat :=
  max 64 (p + 32 + (if gammaRatIsTiny q e p then e.abs.toNat else 0))

/-- Is `q` a positive integer at most `bound`? -/
def gammaRatSmallInt (q : AzRat) (bound : Nat) : Bool :=
  decide (q.den = 1) && q.sign && decide (q.num ≤ AzNat.ofNat bound)

/-- `Γ(q)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` at the poles, for `p = 0` unless the value is `+∞`, or if the fuel runs out). -/
def gammaRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if q.num = 0 then (infinity true, .eq)
  else if q.den = 1 ∧ q.sign = false then (nan, .eq)
  else if p = 0 then (nan, .eq)
  else if gammaRatSmallInt q (gammaIntBound p) then
    setPrecRound (ofAzNat (AzNat.factorial (q.num.toNat - 1))) p mode
  else
    let e := gammaRatExp q
    match gammaRatTiny? q e p mode with
    | some r => r
    | none => zivLoop (gammaRatApprox false q e q.sign) p mode gammaFuel (gammaRatStart q e p)

/-- `Γ(q)` rounded to nearest at precision `p`. -/
def gammaRat (q : AzRat) (p : Nat) : AzFloat := (gammaRatPrecRound q p .Nearest).1

/-- `1/Γ(q)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0`, or if the fuel runs out). -/
def reciprocalGammaRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if q.num = 0 then (zero, .eq)
  else if q.den = 1 ∧ q.sign = false then (zero, .eq)
  else if p = 0 then (nan, .eq)
  else if gammaRatSmallInt q (gammaIntBound p) then
    divPrecRound one (ofAzNat (AzNat.factorial (q.num.toNat - 1))) p mode
  else
    let e := gammaRatExp q
    match reciprocalGammaRatTiny? q e p mode with
    | some r => r
    | none => zivLoop (gammaRatApprox true q e q.sign) p mode gammaFuel (gammaRatStart q e p)

/-- `1/Γ(q)` rounded to nearest at precision `p`. -/
def reciprocalGammaRat (q : AzRat) (p : Nat) : AzFloat :=
  (reciprocalGammaRatPrecRound q p .Nearest).1

end Azurite.AzFloat
