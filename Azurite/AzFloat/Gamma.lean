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
import Azurite.AzFloat.GammaConstants
import Azurite.AzFloat.GammaSpecial
import Azurite.AzFloat.Equiv.GammaCertificate

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
  `n ≤ gammaIntBound p = 8p + 2048`, so the comparison is `.eq` whenever the factorial fits
  the precision; so is `1/(n − 1)!`, by one correctly rounded division.  (Beyond `p + 65` the
  odd part of `(n − 1)!` has more than `p + 1` bits, so the value is not a rounding boundary
  and the general path decides; the bound is larger because the factorial is cheaper than
  the loop up to there.)
* **Tiny arguments.**  `Γ(x) ≈ 1/x` and `1/Γ(x) ≈ x` are rounded by `gammaTiny?` and
  `reciprocalGammaTiny?` at a cost independent of the exponent.
* **Everything else.**  Ziv's loop on `gammaApprox` (`AzFloat/GammaBracket.lean`: the
  exponential of the bracket of `ln Γ`, and the reflection formula for `x < 0`), from
  `max 64 (p + 32)` bits.
* **Fuel.**  The loops have fuel (`gammaFuel p`, the common `zivDefaultFuel`): a termination
  certificate would need `Γ(x)` to be irrational at the float `x`, which is known only in
  special cases.  The
  specifications `gammaPrecRound_eq_or` and `reciprocalGammaPrecRound_eq_or`
  (`Equiv/Gamma.lean`) are "correctly rounded, or `NaN`".
* **No fuel at the quarter-integers** `x = n/4`, not integers (`gammaSpecial`): `Γ(x)` is
  irrational there by Chudnovsky's theorem (`Azurite/Chudnovsky`), the brackets converge
  (`Equiv/GammaWidth.lean`), and the loop is a certified one (`gammaApprox_cert`,
  `Equiv/GammaCertificate.lean`).  The specifications `gammaPrecRound_eq_of_special` and
  `reciprocalGammaPrecRound_eq_of_special` are "correctly rounded".  The values themselves
  come from `√π` and the AGM constant `Γ(1/4)` with an exact rational factor
  (`gammaSpecialFast?`, `AzFloat/GammaSpecial.lean`), which is 4 to 100 times faster; the
  certified loop is the fallback (a shift beyond `gammaIntBound p`, or the fuel of the AGM
  loop running out).

There is no overflow: the exponent of an `AzFloat` is unbounded.  The cost grows with the size
of the result — `Γ(x)` for `x ≈ 2^k` needs `ln Γ(x)` to `k + lg k` bits beyond the precision.
-/

namespace Azurite.AzFloat

/-- Is `x = 1/4`? -/
def isQuarter (x : AzFloat) : Bool :=
  le x (one <<< AzInt.ofInt (-2)) && le (one <<< AzInt.ofInt (-2)) x

/-- **`Γ(x)` with the fuel of its Ziv loop as an argument**: `Γ(x)` rounded to precision `p`
with `mode`, and the comparison with the exact value (`(nan, .eq)` at the poles, for `p = 0`
unless the value is `+∞`, or if the fuel runs out).  `gammaPrecRound` is this function at the
fuel `gammaFuel p`; the specification (`gammaPrecRoundFuel_zivSpec`, `Equiv/Gamma.lean`) is
stated for every fuel.

* **Positive integers**: the exact factorial up to `gammaIntBound p`; beyond it `(n − 1)!` is
  no rounding boundary (its odd part has more than `p + 1` bits), so the loop is a certified
  one (`gammaApprox_cert_int`).
* **The quarter-integers** (`gammaSpecial`: `x = n/4`, not an integer) go through the
  constants `√π` and `Γ(1/4)` (`gammaSpecialFast?`, `AzFloat/GammaSpecial.lean`).  There
  `Γ(x)` is irrational by Chudnovsky's theorem, so behind the constants stands a certified
  loop (`gammaApprox_cert`).
* **Everything else**: the loop with fuel. -/
def gammaPrecRoundFuel (fuel : Nat) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (nan, .eq)
  | zero => (infinity true, .eq)
  | finite s e q m hv =>
    if hpole : (isInteger (finite s e q m hv) && !s) = true then (nan, .eq)
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match gammaTiny? (finite s e q m hv) e q p mode with
      | some r => r
      | none =>
        if hsm : gammaSmallInt (finite s e q m hv) (gammaIntBound p) = true then
          setPrecRound (ofAzNat (AzNat.factorial
            ((truncToAzInt (finite s e q m hv)).abs.toNat - 1))) p mode
        else if hc : gammaSpecial (finite s e q m hv) = true then
          match gammaSpecialFast? false s
              (truncToAzInt (finite s e q m hv <<< AzInt.ofInt 2)).abs 4 p mode with
          | some r =>
            nanOrElse r fun _ =>
              zivLoopCertified (gammaApprox false (finite s e q m hv) e s) p mode
                (max 64 (p + 32)) (gammaApprox_cert false hv hc p mode _ (by omega))
          | none =>
            zivLoopCertified (gammaApprox false (finite s e q m hv) e s) p mode
              (max 64 (p + 32)) (gammaApprox_cert false hv hc p mode _ (by omega))
        else if hI : isInteger (finite s e q m hv) = true then
          zivLoopCertified (gammaApprox false (finite s e q m hv) e s) p mode
            (max 64 (p + 32)) (gammaApprox_cert_int hv p hpole hsm hI mode _ (by omega))
        else
          zivLoop (gammaApprox false (finite s e q m hv) e s) p mode fuel (max 64 (p + 32))

/-- `Γ(x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` at the poles, for `p = 0` unless the value is `+∞`, or if the fuel runs out):
`gammaPrecRoundFuel` at the fuel `gammaFuel p`.  No fuel is involved at the integers and at
the quarter-integers, where the result is always the correctly rounded value
(`gammaPrecRound_eq_of_special`, `gammaPrecRound_eq_of_isInteger`). -/
def gammaPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  gammaPrecRoundFuel (gammaFuel p) x p mode

/-- `Γ(x)` rounded to nearest at the precision of `x`. -/
def gamma (x : AzFloat) : AzFloat := (gammaPrecRound x (x.precision?.getD 1) .Nearest).1

/-- **`1/Γ(x)` with the fuel of its Ziv loop as an argument**: `1/Γ(x)` rounded to precision
`p` with `mode`, and the comparison with the exact value (`(nan, .eq)` for `p = 0` unless the
value is `0`, or if the fuel runs out).  The branches are those of `gammaPrecRoundFuel`; at a
positive integer beyond `gammaIntBound p` the value `1/(n − 1)!` is not dyadic, so the loop is a
certified one (`gammaApprox_cert_int_recip`).  The specification is
`reciprocalGammaPrecRoundFuel_zivSpec` (`Equiv/Gamma.lean`). -/
def reciprocalGammaPrecRoundFuel (fuel : Nat) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (zero, .eq) else (nan, .eq)
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if hpole : (isInteger (finite s e q m hv) && !s) = true then (zero, .eq)
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match reciprocalGammaTiny? (finite s e q m hv) e q p mode with
      | some r => r
      | none =>
        if hsm : gammaSmallInt (finite s e q m hv) (gammaIntBound p) = true then
          divPrecRound one (ofAzNat (AzNat.factorial
            ((truncToAzInt (finite s e q m hv)).abs.toNat - 1))) p mode
        else if hc : gammaSpecial (finite s e q m hv) = true then
          match gammaSpecialFast? true s
              (truncToAzInt (finite s e q m hv <<< AzInt.ofInt 2)).abs 4 p mode with
          | some r =>
            nanOrElse r fun _ =>
              zivLoopCertified (gammaApprox true (finite s e q m hv) e s) p mode
                (max 64 (p + 32)) (gammaApprox_cert true hv hc p mode _ (by omega))
          | none =>
            zivLoopCertified (gammaApprox true (finite s e q m hv) e s) p mode
              (max 64 (p + 32)) (gammaApprox_cert true hv hc p mode _ (by omega))
        else if hI : isInteger (finite s e q m hv) = true then
          zivLoopCertified (gammaApprox true (finite s e q m hv) e s) p mode
            (max 64 (p + 32)) (gammaApprox_cert_int_recip hv p hpole hsm hI mode _ (by omega))
        else
          zivLoop (gammaApprox true (finite s e q m hv) e s) p mode fuel (max 64 (p + 32))

/-- `1/Γ(x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0`, or if the fuel runs out):
`reciprocalGammaPrecRoundFuel` at the fuel `gammaFuel p`.  No fuel is involved at the integers
and at the quarter-integers (`gammaSpecial`), as for `gammaPrecRound`. -/
def reciprocalGammaPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  reciprocalGammaPrecRoundFuel (gammaFuel p) x p mode

/-- `1/Γ(x)` rounded to nearest at the precision of `x`. -/
def reciprocalGamma (x : AzFloat) : AzFloat :=
  (reciprocalGammaPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
