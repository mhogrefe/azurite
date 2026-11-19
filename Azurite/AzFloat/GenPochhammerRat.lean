/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GenPochhammer
import Azurite.AzFloat.PochhammerRat
import Azurite.AzFloat.BetaRat

/-!
## The generalized Pochhammer symbol of two rationals

`genPochhammerRatPrecRound x y p mode` is `Γ(x + y)/Γ(x)` for `AzRat`s `x`, `y`, rounded to
precision `p` in `mode` with the comparison against the exact value; `genPochhammerRat x y p`
rounds to nearest.  The cases are those of the float function (`AzFloat/GenPochhammer.lean`):

* **an integer `y ≥ 0`**: `pochhammerRatPrecRound x y`;
* **an integer `y < 0`**, `n = −y`: `1/((x − 1) ⋯ (x − n))` — `NaN` at `x = 1, …, n`
  (`genPochRatPole`), the exact quotient for a short `x` and a cheap product, otherwise the
  reciprocal of the enclosure of `(x − n)ₙ` (`recipPochCoreOf`) at the roundings of the exact
  rational `x − n`;
* **otherwise**: `0` at `x = 0, −1, …`; `NaN` at `x + y = 0, −1, …` — the sum is simply
  formed —; elsewhere Ziv's loop with fuel on `gammaQuotEnclOf` at the roundings of `x` and
  of `x + y`.

**Contract** (`Equiv/GenPochhammerRat.lean`): `genPochhammerRatPrecRound_eq_or`.
-/

namespace Azurite.AzFloat

/-- Is `x` an integer with `1 ≤ x ≤ n`? -/
def genPochRatPole (x : AzRat) (n : Nat) : Bool :=
  decide (x.den = 1) && x.sign && decide (x.num ≠ 0)
    && !(AzNat.compare x.num (AzNat.ofNat n) == .gt)

/-- The bracket of `1/((x − n)ₙ)` as a pair of `Roundable`s (`s = x − n`). -/
def recipPochRatApprox (s : AzRat) (n w : Nat) : Roundable × Roundable :=
  gammaApproxOf
    (recipPochCoreOf (lnGammaRatEncl s) (pochRatSplit s n) n
      (gammaLnBits (expOf (addPrecRound (ofAzRatRound s.abs 64 .Ceiling).1
        (ofAzNat (AzNat.ofNat n)) 64 .Ceiling).1)) w) w

/-- `Γ(x − n)/Γ(x) = 1 / ((x − 1) ⋯ (x − n))` for a rational `x`. -/
def genPochRatNegInt (x : AzRat) (n p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if genPochRatPole x n then (nan, .eq)
  else if p = 0 then (nan, .eq)
  else if (n ≤ 128 ∧ x.num.size + x.den.size ≤ 2 * p + 1024)
      ∨ pochExactCheap (x.num.size + x.den.size) n p = true then
    recipPochIntQuot (AzInt.mkNorm x.sign x.num) x.den.toAzInt n p mode
  else zivLoop (recipPochRatApprox (x - (n : AzRat)) n) p mode gammaFuel (max 64 (p + 32))

/-- The bracket of `Γ(s)/Γ(x)` as a pair of `Roundable`s (`s = x + y`). -/
def genPochRatApprox (x s : AzRat) (w : Nat) : Roundable × Roundable :=
  gammaApproxOf
    (gammaQuotEnclOf (lnGammaRatEncl x) (lnGammaRatEncl s) (gammaRatExp x) (gammaRatExp s)
      (gammaRatFrac x) (gammaRatFrac s) w) w

/-- `Γ(x + y)/Γ(x)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` at a pole, for `p = 0` unless the value is `0`, or if the fuel runs
out). -/
def genPochhammerRatPrecRound (x y : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if y.den = 1 then
    if y.sign = true ∨ y.num = 0 then pochhammerRatPrecRound x y.num.toNat p mode
    else genPochRatNegInt x y.num.toNat p mode
  else if x.den = 1 ∧ (x.num = 0 ∨ x.sign = false) then (zero, .eq)
  else if (x + y).den = 1 ∧ ((x + y).num = 0 ∨ (x + y).sign = false) then (nan, .eq)
  else if p = 0 then (nan, .eq)
  else zivLoop (genPochRatApprox x (x + y)) p mode gammaFuel (max 64 (p + 32))

/-- `Γ(x + y)/Γ(x)` rounded to nearest at precision `p`. -/
def genPochhammerRat (x y : AzRat) (p : Nat) : AzFloat :=
  (genPochhammerRatPrecRound x y p .Nearest).1

end Azurite.AzFloat
