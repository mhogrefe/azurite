/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaBracket
import Azurite.AzFloat.Conversion
import Azurite.AzRat.Sub
import Azurite.AzRat.Instances
import Azurite.AzRat.Round
import Azurite.AzRat.Unary
import Azurite.AzRat.Mul
import Azurite.AzRat.Conversion

/-!
## The brackets of `Γ(q)` and `1/Γ(q)` for a rational `q`

The pieces of `AzFloat/GammaBracket.lean` with the argument entering by enclosures of
rationals: the roundings of `q` (or of `1 − q`, an exact rational, for `q < 0`) for the bracket
of `ln Γ`, and those of `|q − k|`, `k` the integer nearest to `q`, for the sine of the
reflection formula.  `AzFloat/GammaRat.lean` runs Ziv's loop on `gammaRatApprox`.

`gammaRatSpecial q` recognizes the denominators `2, 3, 4, 6`, where `Γ(q)` is irrational
(`Azurite.Chudnovsky.irrational_gamma_of_den`, by Chudnovsky's theorem) and the loop needs no
fuel.

The proofs are in `Equiv/GammaRatBracket.lean`.
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

/-- Is the denominator of `q` one of `2, 3, 4, 6`?  Then `Γ(q)` is irrational. -/
def gammaRatSpecial (q : AzRat) : Bool :=
  decide (q.den = AzNat.ofNat 2) || decide (q.den = AzNat.ofNat 3)
    || decide (q.den = AzNat.ofNat 4) || decide (q.den = AzNat.ofNat 6)

/-- Is `q` a positive integer at most `bound`? -/
def gammaRatSmallInt (q : AzRat) (bound : Nat) : Bool :=
  decide (q.den = 1) && q.sign && decide (q.num ≤ AzNat.ofNat bound)

end Azurite.AzFloat
