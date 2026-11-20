/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PochhammerRat
import Azurite.AzFloat.BetaRat
import Azurite.AzFloat.Equiv.GenPochhammerRatCertificate

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

**No fuel for an integer `y`** when the denominator of `x` is not a power of two (and `n ≥ 4`
for `y < 0`, `recipPochRatSpecial`): the value is a fraction that is not dyadic, so the loop
is backed by the certified one.  For other `y` nothing is known about the value in general,
and the loop keeps its fuel.

**Contract** (`Equiv/GenPochhammerRat.lean`): `genPochhammerRatPrecRoundFuel_zivSpec`.
-/

namespace Azurite.AzFloat

/-- `Γ(x − n)/Γ(x) = 1 / ((x − 1) ⋯ (x − n))` for a rational `x`, with the fuel of the Ziv
loop explicit. -/
def genPochRatNegIntFuel (fuel : Nat) (x : AzRat) (n p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if genPochRatPole x n then (nan, .eq)
  else if hp : p = 0 then (nan, .eq)
  else if (n ≤ 128 ∧ x.num.size + x.den.size ≤ 2 * p + 1024)
      ∨ pochExactCheap (x.num.size + x.den.size) n p = true then
    recipPochIntQuot (AzInt.mkNorm x.sign x.num) x.den.toAzInt n p mode
  else if hc : recipPochRatSpecial x n = true then
    haveI : NeZero p := ⟨hp⟩
    zivLoopBacked (recipPochRatApprox (x - (n : AzRat)) n) p mode fuel (max 64 (p + 32))
      (recipPochRatApprox_cert hc p mode _
        (Nat.lt_of_lt_of_le (by norm_num) (le_max_left 64 _)))
  else zivLoop (recipPochRatApprox (x - (n : AzRat)) n) p mode fuel (max 64 (p + 32))

/-- `Γ(x + y)/Γ(x)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` at a pole, for `p = 0` unless the value is `0`, or if the fuel runs
out), with the fuel of the Ziv loops explicit. -/
def genPochhammerRatPrecRoundFuel (fuel : Nat) (x y : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if y.den = 1 then
    if y.sign = true ∨ y.num = 0 then pochhammerRatPrecRoundFuel fuel x y.num.toNat p mode
    else genPochRatNegIntFuel fuel x y.num.toNat p mode
  else if x.den = 1 ∧ (x.num = 0 ∨ x.sign = false) then (zero, .eq)
  else if (x + y).den = 1 ∧ ((x + y).num = 0 ∨ (x + y).sign = false) then (nan, .eq)
  else if p = 0 then (nan, .eq)
  else zivLoop (genPochRatApprox x (x + y)) p mode fuel (max 64 (p + 32))

/-- `Γ(x + y)/Γ(x)` rounded to precision `p` with `mode`, and the comparison with the exact
value: `genPochhammerRatPrecRoundFuel` at the fuel `gammaFuel p`.  The specification is
`genPochhammerRatPrecRoundFuel_zivSpec` (`Equiv/GenPochhammerRat.lean`). -/
def genPochhammerRatPrecRound (x y : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  genPochhammerRatPrecRoundFuel (gammaFuel p) x y p mode

/-- `Γ(x + y)/Γ(x)` rounded to nearest at precision `p`. -/
def genPochhammerRat (x y : AzRat) (p : Nat) : AzFloat :=
  (genPochhammerRatPrecRound x y p .Nearest).1

end Azurite.AzFloat
