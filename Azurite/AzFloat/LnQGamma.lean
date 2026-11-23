/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.QGamma
import Azurite.AzFloat.LnBeta
import Azurite.AzFloat.LnGamma
import Azurite.AzFloat.LnGammaRat
import Azurite.AzFloat.LnRat

/-!
## `ln Γ_q(x)`, and `ln |Γ_q(x)|` with the sign of `Γ_q(x)`

The logarithms of the `q`-gamma function (`AzFloat/QGamma.lean`), for the base and the
argument each a float or a rational:

| base | argument | `ln \|Γ_q(x)\|` and the sign | `ln Γ_q(x)` |
|---|---|---|---|
| `AzFloat` | `AzFloat` | `lnAbsQGammaPrecRound`, `lnAbsQGamma` | `lnQGammaPrecRound`, `lnQGamma` |
| `AzFloat` | `AzRat` | `lnAbsQGammaFloatRat…` | `lnQGammaFloatRat…` |
| `AzRat` | `AzFloat` | `lnAbsQGammaRatFloat…` | `lnQGammaRatFloat…` |
| `AzRat` | `AzRat` | `lnAbsQGammaRat…` | `lnQGammaRat…` |

each with a `…Fuel` variant.  The `lnAbs` functions return the rounding of `ln |Γ_q(x)|` with
the comparison against the exact value, and the sign of `Γ_q(x)` (`true`: positive).

The bracket of `Γ_q` is the exponential of an enclosure of `ln |Γ_q|` with the sign
(`qGammaLnEnclOf`, `AzFloat/QGammaBracket.lean`); here that enclosure is rounded itself, by the
loop of `ln |B|` (`lnAbsLoop`, `AzFloat/LnBeta.lean`).

* **Conventions: those of `ln Γ`** (`AzFloat/LnGamma.lean`), which the functions are at the
  base `1` (`lnAbsGammaPrecRoundFuel`, `lnGammaPrecRoundFuel` and the rational versions).
  `NaN` for a base that is `NaN`, `≤ 0` or `+∞`.  `ln |Γ_q|` is `+∞` at `x = ±∞` and at the
  poles `0, −1, −2, …`, with the sign `true` there.  `ln Γ_q` is `ln |Γ_q|` for `x ≥ 0` and
  `NaN` for every `x < 0`.
* **Exact case**: at a positive integer `n` whose value `Γ_q(n)` is formed as a rational
  (`qGammaExact?`), the logarithm of that rational (`lnRatPrecRound`, no fuel): `0` at
  `n = 1, 2`, irrational beyond.
* **Fuel** as for `Γ_q` (`qGammaFuel`).  Where `|Γ_q(x)| = 1` at a non-integer the value `0`
  is a rounding boundary and only the fuel ends the loop.

The specifications (`lnAbsQGammaPrecRoundFuel_zivSpec`, …) are in `Equiv/LnQGamma.lean`.
-/

namespace Azurite.AzFloat

/-- **`ln |Γ_q(x)|` and the sign of `Γ_q(x)` for a base and an argument given by their
data**, with the fuel of the loop explicit. -/
def lnAbsQGammaOf (Q : QBase) (S : QArg) (fuel p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  match S.kind with
  | .zero => ((infinity true, .eq), true)
  | .pole => ((infinity true, .eq), true)
  | .posInt n =>
    if p = 0 then ((nan, .eq), true)
    else
      match qGammaExact? Q n p with
      | some r => (lnRatPrecRound r p mode, true)
      | none => lnAbsLoop (qGammaLnEnclOf (qGammaInOf Q S)) p mode fuel (max 64 (p + 32))
  | .general =>
    if p = 0 then ((nan, .eq), true)
    else lnAbsLoop (qGammaLnEnclOf (qGammaInOf Q S)) p mode fuel (max 64 (p + 32))

/-- Is the rational negative? -/
def ratIsNeg (x : AzRat) : Bool := !x.sign && !decide (x.num = 0)

/-! ### A float base and a float argument -/

/-- **`ln |Γ_q(x)|` for floats `q` and `x`, rounded to precision `p` with `mode`, the
comparison with the exact value, and the sign of `Γ_q(x)`** (`true`: positive), with the fuel
of the loop explicit.  The specification is `lnAbsQGammaPrecRoundFuel_zivSpec`. -/
def lnAbsQGammaPrecRoundFuel (fuel : Nat) (q x : AzFloat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  if q.isFinite && lt zero q then
    if le q one && le one q then lnAbsGammaPrecRoundFuel fuel x p mode
    else
      match x with
      | nan => ((nan, .eq), true)
      | infinity _ => ((infinity true, .eq), true)
      | x => lnAbsQGammaOf (qBaseFloat q) (qArgFloat x) fuel p mode
  else ((nan, .eq), true)

/-- `ln |Γ_q(x)|` and the sign of `Γ_q(x)`, at the fuel of `Γ_q`. -/
def lnAbsQGammaPrecRound (q x : AzFloat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsQGammaPrecRoundFuel (qGammaFuel (lt x zero) p) q x p mode

/-- `ln |Γ_q(x)|` rounded to nearest at the larger of the precisions of `q` and `x`, and the
sign of `Γ_q(x)`. -/
def lnAbsQGamma (q x : AzFloat) : AzFloat × Bool :=
  let r := lnAbsQGammaPrecRound q x (max (q.precision?.getD 1) (x.precision?.getD 1)) .Nearest
  (r.1.1, r.2)

/-- **`ln Γ_q(x)` for floats**, with the fuel explicit: `ln |Γ_q(x)|` for `x ≥ 0`,
`(nan, .eq)` for `x < 0`. -/
def lnQGammaPrecRoundFuel (fuel : Nat) (q x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if lt x zero then (nan, .eq) else (lnAbsQGammaPrecRoundFuel fuel q x p mode).1

/-- `ln Γ_q(x)` rounded to precision `p` with `mode`. -/
def lnQGammaPrecRound (q x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  lnQGammaPrecRoundFuel (qGammaFuel false p) q x p mode

/-- `ln Γ_q(x)` rounded to nearest at the larger of the precisions of `q` and `x`. -/
def lnQGamma (q x : AzFloat) : AzFloat :=
  (lnQGammaPrecRound q x (max (q.precision?.getD 1) (x.precision?.getD 1)) .Nearest).1

/-! ### A float base and a rational argument -/

/-- **`ln |Γ_q(x)|` for a float `q` and a rational `x`**, and the sign of `Γ_q(x)`, with the
fuel explicit.  The specification is `lnAbsQGammaFloatRatPrecRoundFuel_zivSpec`. -/
def lnAbsQGammaFloatRatPrecRoundFuel (fuel : Nat) (q : AzFloat) (x : AzRat) (p : Nat)
    (mode : RoundingMode) : (AzFloat × Ordering) × Bool :=
  if q.isFinite && lt zero q then
    if le q one && le one q then lnAbsGammaRatPrecRoundFuel fuel x p mode
    else lnAbsQGammaOf (qBaseFloat q) (qArgRat x) fuel p mode
  else ((nan, .eq), true)

/-- `ln |Γ_q(x)|` for a float `q` and a rational `x`, and the sign of `Γ_q(x)`. -/
def lnAbsQGammaFloatRatPrecRound (q : AzFloat) (x : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsQGammaFloatRatPrecRoundFuel (qGammaFuel (!x.sign) p) q x p mode

/-- `ln |Γ_q(x)|` rounded to nearest at precision `p`, and the sign of `Γ_q(x)`. -/
def lnAbsQGammaFloatRat (q : AzFloat) (x : AzRat) (p : Nat) : AzFloat × Bool :=
  let r := lnAbsQGammaFloatRatPrecRound q x p .Nearest
  (r.1.1, r.2)

/-- **`ln Γ_q(x)` for a float `q` and a rational `x`**, with the fuel explicit. -/
def lnQGammaFloatRatPrecRoundFuel (fuel : Nat) (q : AzFloat) (x : AzRat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  if ratIsNeg x then (nan, .eq) else (lnAbsQGammaFloatRatPrecRoundFuel fuel q x p mode).1

/-- `ln Γ_q(x)` for a float `q` and a rational `x`, rounded to precision `p` with `mode`. -/
def lnQGammaFloatRatPrecRound (q : AzFloat) (x : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  lnQGammaFloatRatPrecRoundFuel (qGammaFuel false p) q x p mode

/-- `ln Γ_q(x)` for a float `q` and a rational `x`, rounded to nearest at precision `p`. -/
def lnQGammaFloatRat (q : AzFloat) (x : AzRat) (p : Nat) : AzFloat :=
  (lnQGammaFloatRatPrecRound q x p .Nearest).1

/-! ### A rational base and a float argument -/

/-- **`ln |Γ_q(x)|` for a rational `q` and a float `x`**, and the sign of `Γ_q(x)`, with the
fuel explicit.  The specification is `lnAbsQGammaRatFloatPrecRoundFuel_zivSpec`. -/
def lnAbsQGammaRatFloatPrecRoundFuel (fuel : Nat) (q : AzRat) (x : AzFloat) (p : Nat)
    (mode : RoundingMode) : (AzFloat × Ordering) × Bool :=
  if q.sign = true ∧ q.num ≠ 0 then
    if q.num = q.den then lnAbsGammaPrecRoundFuel fuel x p mode
    else
      match x with
      | nan => ((nan, .eq), true)
      | infinity _ => ((infinity true, .eq), true)
      | x => lnAbsQGammaOf (qBaseRat q) (qArgFloat x) fuel p mode
  else ((nan, .eq), true)

/-- `ln |Γ_q(x)|` for a rational `q` and a float `x`, and the sign of `Γ_q(x)`. -/
def lnAbsQGammaRatFloatPrecRound (q : AzRat) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsQGammaRatFloatPrecRoundFuel (qGammaFuel (lt x zero) p) q x p mode

/-- `ln |Γ_q(x)|` rounded to nearest at precision `p`, and the sign of `Γ_q(x)`. -/
def lnAbsQGammaRatFloat (q : AzRat) (x : AzFloat) (p : Nat) : AzFloat × Bool :=
  let r := lnAbsQGammaRatFloatPrecRound q x p .Nearest
  (r.1.1, r.2)

/-- **`ln Γ_q(x)` for a rational `q` and a float `x`**, with the fuel explicit. -/
def lnQGammaRatFloatPrecRoundFuel (fuel : Nat) (q : AzRat) (x : AzFloat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  if lt x zero then (nan, .eq) else (lnAbsQGammaRatFloatPrecRoundFuel fuel q x p mode).1

/-- `ln Γ_q(x)` for a rational `q` and a float `x`, rounded to precision `p` with `mode`. -/
def lnQGammaRatFloatPrecRound (q : AzRat) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  lnQGammaRatFloatPrecRoundFuel (qGammaFuel false p) q x p mode

/-- `ln Γ_q(x)` for a rational `q` and a float `x`, rounded to nearest at precision `p`. -/
def lnQGammaRatFloat (q : AzRat) (x : AzFloat) (p : Nat) : AzFloat :=
  (lnQGammaRatFloatPrecRound q x p .Nearest).1

/-! ### A rational base and a rational argument -/

/-- **`ln |Γ_q(x)|` for rationals `q` and `x`**, and the sign of `Γ_q(x)`, with the fuel
explicit.  The specification is `lnAbsQGammaRatPrecRoundFuel_zivSpec`. -/
def lnAbsQGammaRatPrecRoundFuel (fuel : Nat) (q x : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  if q.sign = true ∧ q.num ≠ 0 then
    if q.num = q.den then lnAbsGammaRatPrecRoundFuel fuel x p mode
    else lnAbsQGammaOf (qBaseRat q) (qArgRat x) fuel p mode
  else ((nan, .eq), true)

/-- `ln |Γ_q(x)|` for rationals `q` and `x`, and the sign of `Γ_q(x)`. -/
def lnAbsQGammaRatPrecRound (q x : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsQGammaRatPrecRoundFuel (qGammaFuel (!x.sign) p) q x p mode

/-- `ln |Γ_q(x)|` rounded to nearest at precision `p`, and the sign of `Γ_q(x)`. -/
def lnAbsQGammaRat (q x : AzRat) (p : Nat) : AzFloat × Bool :=
  let r := lnAbsQGammaRatPrecRound q x p .Nearest
  (r.1.1, r.2)

/-- **`ln Γ_q(x)` for rationals `q` and `x`**, with the fuel explicit. -/
def lnQGammaRatPrecRoundFuel (fuel : Nat) (q x : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if ratIsNeg x then (nan, .eq) else (lnAbsQGammaRatPrecRoundFuel fuel q x p mode).1

/-- `ln Γ_q(x)` for rationals `q` and `x`, rounded to precision `p` with `mode`. -/
def lnQGammaRatPrecRound (q x : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  lnQGammaRatPrecRoundFuel (qGammaFuel false p) q x p mode

/-- `ln Γ_q(x)` for rationals `q` and `x`, rounded to nearest at precision `p`. -/
def lnQGammaRat (q x : AzRat) (p : Nat) : AzFloat := (lnQGammaRatPrecRound q x p .Nearest).1

end Azurite.AzFloat
