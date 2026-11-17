/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnGamma
import Azurite.AzFloat.Conversion
import Azurite.AzRat.Sub

/-!
## `ln Γ(q)` for a rational `q > 0`

`lnGammaRatPrecRound q p mode` is `ln Γ(q)` for an `AzRat` `q`, rounded to precision `p` in
`mode`, with the comparison against the exact value; `lnGammaRat q p` rounds to nearest.

* **Special values**, as for the float function (`AzFloat/LnGamma.lean`): `ln Γ(1) = ln Γ(2) = 0`
  exactly; `ln Γ(0) = +∞`; `NaN` for `q < 0`.
* **The bracket.**  `lnGammaBracketEncl` (`AzFloat/LnGammaBracket.lean`) on the enclosure of `q`
  by its two directed roundings at `w + 32` bits (`lnGammaRatEncl`): the argument shift and
  Stirling's series run on enclosures anyway, so the rational costs nothing more than the float.
  For a dyadic `q` that fits, the enclosure is exact and the bracket is that of the float.
* **Rounding.**  Ziv's loop with the fuel of the float function, started at `p + 32` bits plus
  the bits lost near the zeros `q = 1` and `q = 2`, read off the exact differences `q − 1` and
  `q − 2` (`lnGammaRatCancelBits`).

The specification `lnGammaRatPrecRound_eq_or` ("correctly rounded, or `NaN`") is in
`Equiv/LnGammaRat.lean`.
-/

namespace Azurite.AzFloat

/-- The enclosure of a rational `q` by its roundings down and up at `w + 32` bits. -/
def lnGammaRatEncl (q : AzRat) (w : Nat) : Encl :=
  ((ofAzRatRound q (w + 32) .Floor).1, (ofAzRatRound q (w + 32) .Ceiling).1)

/-- The bracket of `ln Γ(q)` at Ziv level `w` for a rational `q > 0`. -/
def lnGammaRatBracket (q : AzRat) (w : Nat) : Encl :=
  lnGammaBracketEncl (lnGammaRatEncl q w)
    ((lnGammaRatEncl q w).2.exponent?.getD (AzInt.ofInt 0)) w

/-- The bracket of `ln Γ(q)` as a pair of `Roundable`s, the lower end strictly below the
value. -/
def lnGammaRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  lnGammaApproxOf (lnGammaRatBracket q w) w

/-- The bits lost near the zeros `q = 1` and `q = 2` of `ln Γ`: `k` when `q − 1` or `q − 2` is
about `2^(−k)`. -/
def lnGammaRatCancelBits (q : AzRat) : Nat :=
  let f := fun (d : AzRat) => match (ofAzRatRound d 2 .Nearest).1.exponent? with
    | some e => if e.sign then 0 else e.abs.toNat
    | none => 0
  max (f (q - 1)) (f (q - 1 - 1))

/-- `ln Γ(q)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0` or `+∞`, for `q < 0`, or if the fuel runs
out). -/
def lnGammaRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if q.num = 0 then (infinity true, .eq)
  else if q.sign = false then (nan, .eq)
  else if (q - 1).num = 0 ∨ (q - 1 - 1).num = 0 then (zero, .eq)
  else if p = 0 then (nan, .eq)
  else
    zivLoop (lnGammaRatApprox q) p mode lnGammaFuel (max 64 (p + 32 + lnGammaRatCancelBits q))

/-- `ln Γ(q)` rounded to nearest at precision `p`. -/
def lnGammaRat (q : AzRat) (p : Nat) : AzFloat := (lnGammaRatPrecRound q p .Nearest).1

end Azurite.AzFloat
