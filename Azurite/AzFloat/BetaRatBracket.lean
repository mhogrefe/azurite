/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BetaBracket
import Azurite.AzFloat.GammaRatBracket

/-!
## The bracket of the Beta function of two rationals

The bracket of `B(a, b)` for `AzRat`s is that of the float function (`betaEnclOf`,
`AzFloat/BetaBracket.lean`) with the arguments entering by the enclosures `lnGammaRatEncl` and
the distances to the nearest integer `gammaRatFrac`; `betaRatSpecial` recognizes the arguments
where `B(a, b)` is known to be irrational.  The functions are in `AzFloat/BetaRat.lean`.
-/

namespace Azurite.AzFloat

/-- The integer `k` nearest to `q`, the sign of `q − k` (`true`: negative) and a positive
enclosure of `|q − k|`; `none` when `q` is an integer. -/
def gammaRatFrac (q : AzRat) (W : Nat) : Option (Bool × AzInt × Encl) :=
  let k := (q.round .Nearest).1
  let d := q - k.toAzRat
  if d.num = 0 then none
  else some (!d.sign, k, lnGammaRatEncl (if d.sign then d else -d) W)

/-- The bracket of `B(a, b)` as a pair of `Roundable`s (`s = a + b`), strict on both sides; the
dummy bracket `[−1, 1]` when the pieces give nothing. -/
def betaRatApprox (a b s : AzRat) (w : Nat) : Roundable × Roundable :=
  gammaApproxOf
    (betaEnclOf (lnGammaRatEncl a) (lnGammaRatEncl b) (lnGammaRatEncl s) (gammaRatExp a)
      (gammaRatExp b) (gammaRatExp s) (gammaRatFrac a) (gammaRatFrac b) (gammaRatFrac s) w) w

/-- Arguments where `B(a, b)` is known to be irrational (`s = a + b`), so that Ziv's loop
needs no fuel (`betaRatApprox_cert`, `Equiv/BetaRatCertificate.lean`): `a` and `b` are not
integers, and `a + b` is an integer — `B(a, b)` is then a rational multiple of
`π / sin (π a)` — or the denominators of `a` and `b` are both in `{2, 4}`, or both in
`{2, 3, 6}`: `B(a, b)` is then `Γ(1/4)^(±2)`, or `Γ(1/3)^(±3)`, times a number algebraic over
`ℤ[π]` (Chudnovsky's theorem; `Azurite.Chudnovsky.irrational_beta_of_den`).  To be used off
the zeros of `B`, where `a + b` is a non-positive integer. -/
def betaRatSpecial (a b s : AzRat) : Bool :=
  decide (a.den ≠ 1) && decide (b.den ≠ 1) &&
    (decide (s.den = 1)
      || ((decide (a.den = AzNat.ofNat 2) || decide (a.den = AzNat.ofNat 4))
        && (decide (b.den = AzNat.ofNat 2) || decide (b.den = AzNat.ofNat 4)))
      || ((decide (a.den = AzNat.ofNat 2) || decide (a.den = AzNat.ofNat 3)
          || decide (a.den = AzNat.ofNat 6))
        && (decide (b.den = AzNat.ofNat 2) || decide (b.den = AzNat.ofNat 3)
          || decide (b.den = AzNat.ofNat 6))))

end Azurite.AzFloat
