/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnAbsGamma
import Azurite.AzFloat.LnGammaRat
import Azurite.AzFloat.GammaRat
import Azurite.AzNat.Parity

/-!
## `ln |Γ(q)|` and the sign of `Γ(q)` for an `AzRat`

`lnAbsGammaRatPrecRound q p mode` is `ln |Γ(q)|` rounded to precision `p` in `mode`, with the
comparison against the exact value, together with the sign of `Γ(q)` (`true`: positive);
`lnAbsGammaRat q p` rounds to nearest.  It is `lnAbsGammaPrecRound`
(`AzFloat/LnAbsGamma.lean`) at a rational argument:

* **Special values.**  `+∞` at the poles `q = 0, −1, −2, …` (sign `true`); `0` exactly at `1`
  and `2`.
* **`q > 0`**: `lnGammaRatPrecRound`.
* **`q < 0`** (not an integer): the reflection formula `lnAbsGammaReflect` with the sine of
  `gammaRatSinEncl` (the exact rational `q − k` for the integer `k` nearest `q`) and the
  bracket of `ln Γ` at the enclosure of the exact rational `1 − q`.
* **The sign** for a negative non-integer: `Γ(q) > 0` exactly when `⌊|q|⌋ = num / den` is odd.
* **Fuel.**  As for the float argument; the specification `lnAbsGammaRatPrecRound_eq_or`
  (`Equiv/LnAbsGammaRat.lean`) is "correctly rounded, or `NaN`".
-/

namespace Azurite.AzFloat

/-- An enclosure of `ln |Γ(q)|` at Ziv level `w` for a rational `q < 0`, `|q| < 2^e`, that is
not an integer; `none` when the sine has no positive enclosure at this level. -/
def lnAbsGammaRatNegEncl (q : AzRat) (e : AzInt) (w : Nat) : Option Encl :=
  let e' := (if e.sign then e else 0) + 1
  lnAbsGammaReflect (gammaRatSinEncl q (w + 16) w)
    (lnGammaBracketEncl (lnGammaRatEncl (1 - q) w) e' w) w

/-- The bracket of `ln |Γ(q)|`, `q < 0`, as a pair of `Roundable`s. -/
def lnAbsGammaRatApprox (q : AzRat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  lnAbsGammaApproxOf (lnAbsGammaRatNegEncl q e w) w

/-- Is `Γ(q)` positive?  `true` for `q > 0`; for a negative `q` that is not an integer, whether
`⌊|q|⌋` is odd; `true` at the poles. -/
def gammaRatSign (q : AzRat) : Bool :=
  if q.num = 0 then true
  else if q.sign then true
  else if q.den = 1 then true
  else (q.num / q.den).isOdd

/-- `ln |Γ(q)|` rounded to precision `p` with `mode`, the comparison with the exact value, and
the sign of `Γ(q)` (`true`: positive).  The first component is `(nan, .eq)` for `p = 0` unless
the value is `0` or `+∞`, or if the fuel runs out. -/
def lnAbsGammaRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  if q.num = 0 then ((infinity true, .eq), true)
  else if q.sign then (lnGammaRatPrecRound q p mode, true)
  else if q.den = 1 then ((infinity true, .eq), true)
  else
    (if p = 0 then (nan, .eq)
      else
        let e := gammaRatExp q
        zivLoop (lnAbsGammaRatApprox q e) p mode lnGammaFuel (max 64 (p + 32)),
      (q.num / q.den).isOdd)

/-- `ln |Γ(q)|` rounded to nearest at precision `p`, and the sign of `Γ(q)`. -/
def lnAbsGammaRat (q : AzRat) (p : Nat) : AzFloat × Bool :=
  let r := lnAbsGammaRatPrecRound q p .Nearest
  (r.1.1, r.2)

end Azurite.AzFloat
