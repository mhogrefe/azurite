/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gamma
import Azurite.AzFloat.GammaRatBracket
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

* **Denominators `2, 3, 4, 6`** (`gammaRatSpecial`): closed forms in `√π`, `Γ(1/4)`, `Γ(1/3)`
  with an exact rational factor (`gammaSpecialFast?`, `AzFloat/GammaSpecial.lean`), and behind
  them a certified loop without fuel (`gammaRatCertified`), since `Γ(q)` is irrational there
  by Chudnovsky's theorem.

The specifications `gammaRatPrecRound_eq_or` and `reciprocalGammaRatPrecRound_eq_or`
("correctly rounded, or `NaN`") and `gammaRatPrecRound_eq_of_special`,
`reciprocalGammaRatPrecRound_eq_of_special` ("correctly rounded") are in
`Equiv/GammaRat.lean`.
-/

namespace Azurite.AzFloat

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

/-- Is `q = 1/d`? -/
def isUnitFraction (q : AzRat) (d : Nat) : Bool :=
  q.sign && decide (q.num = 1) && decide (q.den = AzNat.ofNat d)

/-- The certified Ziv loop of `Γ(q)` (`recip = false`) or `1/Γ(q)` for a rational `q` with
denominator `2, 3, 4` or `6`: no fuel (`gammaRatApprox_cert`). -/
def gammaRatCertified (recip : Bool) (q : AzRat) (hc : gammaRatSpecial q = true) (p : Nat)
    [NeZero p] (mode : RoundingMode) : AzFloat × Ordering :=
  zivLoopCertified (gammaRatApprox recip q (gammaRatExp q) q.sign) p mode (max 64 (p + 32))
    (gammaRatApprox_cert recip hc _ p mode _ (by omega))

/-- **`Γ(q)` with the fuel of its Ziv loop as an argument**: `Γ(q)` rounded to precision `p`
with `mode`, and the comparison with the exact value (`(nan, .eq)` at the poles, for `p = 0`
unless the value is `+∞`, or if the fuel runs out).  The specification is
`gammaRatPrecRoundFuel_zivSpec` (`Equiv/GammaRat.lean`).

* **The denominators `2, 3, 4, 6`** (`gammaRatSpecial`) go through `√π` and the AGM constants
  `Γ(1/4)`, `Γ(1/3)` (`gammaSpecialFast?`, `AzFloat/GammaSpecial.lean`).  There `Γ(q)` is
  irrational by Chudnovsky's theorem, so behind the constants stands a certified loop without
  fuel (`gammaRatCertified`).
* **Positive integers** beyond `gammaIntBound p`: `(n − 1)!` is no rounding boundary, and the
  loop is a certified one (`gammaRatApprox_cert_int`). -/
def gammaRatPrecRoundFuel (fuel : Nat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if h0 : q.num = 0 then (infinity true, .eq)
  else if hpole : q.den = 1 ∧ q.sign = false then (nan, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    if hsm : gammaRatSmallInt q (gammaIntBound p) = true then
      setPrecRound (ofAzNat (AzNat.factorial (q.num.toNat - 1))) p mode
    else if hc : gammaRatSpecial q = true then
      match gammaSpecialFast? false q.sign q.num q.den.toNat p mode with
      | some r => nanOrElse r fun _ => gammaRatCertified false q hc p mode
      | none => gammaRatCertified false q hc p mode
    else if hI : q.den = 1 then
      zivLoopCertified (gammaRatApprox false q (gammaRatExp q) q.sign) p mode (max 64 (p + 32))
        (gammaRatApprox_cert_int false h0 hpole hsm hI _ mode _ (by omega))
    else
      let e := gammaRatExp q
      match gammaRatTiny? q e p mode with
      | some r => r
      | none => zivLoop (gammaRatApprox false q e q.sign) p mode fuel (gammaRatStart q e p)

/-- `Γ(q)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` at the poles, for `p = 0` unless the value is `+∞`, or if the fuel runs out):
`gammaRatPrecRoundFuel` at the fuel `gammaFuel p`.  No fuel is involved at the integers and
for the denominators `2, 3, 4, 6`, where the result is always the correctly rounded value
(`gammaRatPrecRound_eq_of_special`, `gammaRatPrecRound_eq_of_den_one`). -/
def gammaRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  gammaRatPrecRoundFuel (gammaFuel p) q p mode

/-- `Γ(q)` rounded to nearest at precision `p`. -/
def gammaRat (q : AzRat) (p : Nat) : AzFloat := (gammaRatPrecRound q p .Nearest).1

/-- **`1/Γ(q)` with the fuel of its Ziv loop as an argument** (`(nan, .eq)` for `p = 0`
unless the value is `0`, or if the fuel runs out).  The branches are those of
`gammaRatPrecRoundFuel`; the specification is `reciprocalGammaRatPrecRoundFuel_zivSpec`. -/
def reciprocalGammaRatPrecRoundFuel (fuel : Nat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if h0 : q.num = 0 then (zero, .eq)
  else if hpole : q.den = 1 ∧ q.sign = false then (zero, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    if hsm : gammaRatSmallInt q (gammaIntBound p) = true then
      divPrecRound one (ofAzNat (AzNat.factorial (q.num.toNat - 1))) p mode
    else if hc : gammaRatSpecial q = true then
      match gammaSpecialFast? true q.sign q.num q.den.toNat p mode with
      | some r => nanOrElse r fun _ => gammaRatCertified true q hc p mode
      | none => gammaRatCertified true q hc p mode
    else if hI : q.den = 1 then
      zivLoopCertified (gammaRatApprox true q (gammaRatExp q) q.sign) p mode (max 64 (p + 32))
        (gammaRatApprox_cert_int true h0 hpole hsm hI _ mode _ (by omega))
    else
      let e := gammaRatExp q
      match reciprocalGammaRatTiny? q e p mode with
      | some r => r
      | none => zivLoop (gammaRatApprox true q e q.sign) p mode fuel (gammaRatStart q e p)

/-- `1/Γ(q)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0`, or if the fuel runs out):
`reciprocalGammaRatPrecRoundFuel` at the fuel `gammaFuel p`.  No fuel at the integers and for
the denominators `2, 3, 4, 6`, as for `gammaRatPrecRound`. -/
def reciprocalGammaRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  reciprocalGammaRatPrecRoundFuel (gammaFuel p) q p mode

/-- `1/Γ(q)` rounded to nearest at precision `p`. -/
def reciprocalGammaRat (q : AzRat) (p : Nat) : AzFloat :=
  (reciprocalGammaRatPrecRound q p .Nearest).1

end Azurite.AzFloat
