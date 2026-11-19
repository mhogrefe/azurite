/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnGamma
import Azurite.AzFloat.Conversion
import Azurite.AzRat.Sub
import Azurite.AzFloat.GammaRat
import Azurite.AzNat.Parity

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

/-- The bits lost near the zeros `q = 1` and `q = 2` of `ln Γ`: `k` when `q − 1` or `q − 2` is
about `2^(−k)`. -/
def lnGammaRatCancelBits (q : AzRat) : Nat :=
  let f := fun (d : AzRat) => match (ofAzRatRound d 2 .Nearest).1.exponent? with
    | some e => if e.sign then 0 else e.abs.toNat
    | none => 0
  max (f (q - 1)) (f (q - 1 - 1))

/-- **`ln Γ(q)` with the fuel of its Ziv loop as an argument** (`(nan, .eq)` for `p = 0`
unless the value is `0` or `+∞`, for `q < 0`, or if the fuel runs out).  At an integer
`n ≥ 3` the value `ln (n − 1)!` is irrational, and the loop is a certified one
(`lnGammaRatApprox_cert_int`).  The specification is `lnGammaRatPrecRoundFuel_zivSpec`
(`Equiv/LnGammaRat.lean`). -/
def lnGammaRatPrecRoundFuel (fuel : Nat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if h0 : q.num = 0 then (infinity true, .eq)
  else if hs : q.sign = false then (nan, .eq)
  else if h12 : (q - 1).num = 0 ∨ (q - 1 - 1).num = 0 then (zero, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    if hI : q.den = 1 then
      zivLoopCertified (lnGammaRatApprox q) p mode
        (max 64 (p + 32 + lnGammaRatCancelBits q))
        (lnGammaRatApprox_cert_int h0 (by simpa using hs) h12 hI p mode _ (by omega))
    else
      zivLoop (lnGammaRatApprox q) p mode fuel (max 64 (p + 32 + lnGammaRatCancelBits q))

/-- `ln Γ(q)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0` or `+∞`, for `q < 0`, or if the fuel runs
out): `lnGammaRatPrecRoundFuel` at the fuel `lnGammaFuel p`. -/
def lnGammaRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  lnGammaRatPrecRoundFuel (lnGammaFuel p) q p mode

/-- `ln Γ(q)` rounded to nearest at precision `p`. -/
def lnGammaRat (q : AzRat) (p : Nat) : AzFloat := (lnGammaRatPrecRound q p .Nearest).1

/-!
## `ln |Γ(q)|` and the sign of `Γ(q)` for an `AzRat`

`lnAbsGammaRatPrecRound q p mode` is `ln |Γ(q)|` rounded to precision `p` in `mode`, with the
comparison against the exact value, together with the sign of `Γ(q)` (`true`: positive);
`lnAbsGammaRat q p` rounds to nearest.  It is `lnAbsGammaPrecRound`
(`AzFloat/LnGamma.lean`) at a rational argument:

* **Special values.**  `+∞` at the poles `q = 0, −1, −2, …` (sign `true`); `0` exactly at `1`
  and `2`.
* **`q > 0`**: `lnGammaRatPrecRound`.
* **`q < 0`** (not an integer): the reflection formula `lnAbsGammaReflect` with the sine of
  `gammaRatSinEncl` (the exact rational `q − k` for the integer `k` nearest `q`) and the
  bracket of `ln Γ` at the enclosure of the exact rational `1 − q`.
* **The sign** for a negative non-integer: `Γ(q) > 0` exactly when `⌊|q|⌋ = num / den` is odd.
* **Fuel.**  As for the float argument; the specification `lnAbsGammaRatPrecRound_eq_or`
  (`Equiv/LnGammaRat.lean`) is "correctly rounded, or `NaN`".
-/

section

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

/-- **`ln |Γ(q)|` with the fuel of its Ziv loop as an argument**: `ln |Γ(q)|` rounded to
precision `p` with `mode`, the comparison with the exact value, and the sign of `Γ(q)` (`true`:
positive).  The first component is `(nan, .eq)` for `p = 0` unless the value is `0` or `+∞`, or
if the fuel runs out.  The specification is `lnAbsGammaRatPrecRoundFuel_zivSpec`. -/
def lnAbsGammaRatPrecRoundFuel (fuel : Nat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  if q.num = 0 then ((infinity true, .eq), true)
  else if q.sign then (lnGammaRatPrecRoundFuel fuel q p mode, true)
  else if q.den = 1 then ((infinity true, .eq), true)
  else
    (if p = 0 then (nan, .eq)
      else
        let e := gammaRatExp q
        zivLoop (lnAbsGammaRatApprox q e) p mode fuel (max 64 (p + 32)),
      (q.num / q.den).isOdd)

/-- `ln |Γ(q)|` rounded to precision `p` with `mode`, the comparison with the exact value, and
the sign of `Γ(q)` (`true`: positive): `lnAbsGammaRatPrecRoundFuel` at the fuel
`lnGammaFuel p`. -/
def lnAbsGammaRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsGammaRatPrecRoundFuel (lnGammaFuel p) q p mode

/-- `ln |Γ(q)|` rounded to nearest at precision `p`, and the sign of `Γ(q)`. -/
def lnAbsGammaRat (q : AzRat) (p : Nat) : AzFloat × Bool :=
  let r := lnAbsGammaRatPrecRound q p .Nearest
  (r.1.1, r.2)

end

end Azurite.AzFloat
