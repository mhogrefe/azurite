/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaBracket
import Azurite.AzFloat.Ziv
import Azurite.AzFloat.Div
import Azurite.AzFloat.RoundToInteger
import Azurite.AzNat.Factorial

/-!
## The gamma function `Γ(x)` and its reciprocal `1/Γ(x)`

`gammaPrecRound x p mode` is `Γ(x)` (DLMF §5.2) and `reciprocalGammaPrecRound x p mode` is
`1/Γ(x)`, rounded to precision `p` in `mode`, with the comparison against the exact value;
`gamma x` and `reciprocalGamma x` round to nearest at the precision of `x`.

* **Special values of `Γ`.**  `Γ(+∞) = +∞`; `Γ(0) = +∞` (the limit from the right; there is no
  negative zero); `NaN` at the poles `x = −1, −2, …`, at `−∞` and at `NaN`.
* **Special values of `1/Γ`.**  `1/Γ(+∞) = 0`; `1/Γ(x) = 0` exactly at `x = 0, −1, −2, …` (the
  reciprocal is entire); `NaN` at `−∞`, where it oscillates, and at `NaN`.
* **Positive integers.**  `Γ(n) = (n − 1)!` is computed exactly and rounded once when
  `n ≤ p + 65`, so the comparison is `.eq` whenever the factorial fits the precision; so is
  `1/(n − 1)!`, by one correctly rounded division.  (Beyond that bound the odd part of
  `(n − 1)!` has more than `p + 1` bits, so the value is not a rounding boundary and the
  general path decides.)
* **Tiny arguments.**  `Γ(x) ≈ 1/x` and `1/Γ(x) ≈ x` are rounded by `gammaTiny?` and
  `reciprocalGammaTiny?` at a cost independent of the exponent.
* **Everything else.**  Ziv's loop on `gammaApprox` (`AzFloat/GammaBracket.lean`: the
  exponential of the bracket of `ln Γ`, and the reflection formula for `x < 0`), from
  `max 64 (p + 32)` bits.
* **Fuel.**  The loops have fuel (`gammaFuel`, ten doublings): a termination certificate would
  need `Γ(x)` to be irrational at the float `x`, which is known only in special cases.  The
  specifications `gammaPrecRound_eq_or` and `reciprocalGammaPrecRound_eq_or`
  (`Equiv/Gamma.lean`) are "correctly rounded, or `NaN`".

There is no overflow: the exponent of an `AzFloat` is unbounded.  The cost grows with the size
of the result — `Γ(x)` for `x ≈ 2^k` needs `ln Γ(x)` to `k + lg k` bits beyond the precision.
-/

namespace Azurite.AzFloat

/-- `Γ(x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` at the poles, for `p = 0` unless the value is `+∞`, or if the fuel runs out). -/
def gammaPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (nan, .eq)
  | zero => (infinity true, .eq)
  | finite s e q m hv =>
    if isInteger (finite s e q m hv) && !s then (nan, .eq)
    else if p = 0 then (nan, .eq)
    else
      match gammaTiny? (finite s e q m hv) e q p mode with
      | some r => r
      | none =>
        if gammaSmallInt (finite s e q m hv) (p + 65) then
          setPrecRound (ofAzNat (AzNat.factorial
            ((truncToAzInt (finite s e q m hv)).abs.toNat - 1))) p mode
        else
          zivLoop (gammaApprox false (finite s e q m hv) e s) p mode gammaFuel (max 64 (p + 32))

/-- `Γ(x)` rounded to nearest at the precision of `x`. -/
def gamma (x : AzFloat) : AzFloat := (gammaPrecRound x (x.precision?.getD 1) .Nearest).1

/-- `1/Γ(x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0`, or if the fuel runs out). -/
def reciprocalGammaPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (zero, .eq) else (nan, .eq)
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if isInteger (finite s e q m hv) && !s then (zero, .eq)
    else if p = 0 then (nan, .eq)
    else
      match reciprocalGammaTiny? (finite s e q m hv) e q p mode with
      | some r => r
      | none =>
        if gammaSmallInt (finite s e q m hv) (p + 65) then
          divPrecRound one (ofAzNat (AzNat.factorial
            ((truncToAzInt (finite s e q m hv)).abs.toNat - 1))) p mode
        else
          zivLoop (gammaApprox true (finite s e q m hv) e s) p mode gammaFuel (max 64 (p + 32))

/-- `1/Γ(x)` rounded to nearest at the precision of `x`. -/
def reciprocalGamma (x : AzFloat) : AzFloat :=
  (reciprocalGammaPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
