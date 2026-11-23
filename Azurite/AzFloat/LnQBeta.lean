/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.QBeta
import Azurite.AzFloat.LnBeta
import Azurite.AzFloat.LnBetaRat
import Azurite.AzFloat.LnRat

/-!
## `ln B_q(a, b)`, and `ln |B_q(a, b)|` with the sign of `B_q(a, b)`

The logarithms of the `q`-beta function (`AzFloat/QBeta.lean`), for the base a float or a
rational and the arguments two floats, a float and a rational, or two rationals:

| base | arguments | `ln \|B_q\|` and the sign | `ln B_q` |
|---|---|---|---|
| `AzFloat` | `AzFloat`, `AzFloat` | `lnAbsQBeta` | `lnQBeta` |
| `AzFloat` | `AzFloat`, `AzRat` | `lnAbsQBetaFloatFloatRat` | `lnQBetaFloatFloatRat` |
| `AzFloat` | `AzRat`, `AzRat` | `lnAbsQBetaFloatRatRat` | `lnQBetaFloatRatRat` |
| `AzRat` | `AzFloat`, `AzFloat` | `lnAbsQBetaRatFloatFloat` | `lnQBetaRatFloatFloat` |
| `AzRat` | `AzFloat`, `AzRat` | `lnAbsQBetaRatFloatRat` | `lnQBetaRatFloatRat` |
| `AzRat` | `AzRat`, `AzRat` | `lnAbsQBetaRat` | `lnQBetaRat` |

each with `…PrecRound` and `…PrecRoundFuel`.  The `lnAbs` functions return the rounding of
`ln |B_q(a, b)|` with the comparison against the exact value, and the sign of `B_q(a, b)`
(`true`: not negative); the `ln` functions are the logarithm of `B_q` itself: the same value
where `B_q(a, b) ≥ 0`, `NaN` where `B_q(a, b) < 0`.

The bracket of `B_q` is the exponential of an enclosure of `ln |B_q|` with the sign
(`qBetaLnEnclOf`, `AzFloat/QBeta.lean`); here that enclosure is rounded itself, by the loop
of `ln |B|` (`lnAbsLoop`, `AzFloat/LnBeta.lean`).

* **Conventions: those of `ln |B|` and `ln B`** (`AzFloat/LnBeta.lean`), which the functions
  are at the base `1`: the logarithm of the value of `B_q`.  `NaN` where `B_q` is `NaN` (a
  base that is not positive and finite, a pole, `−∞`, and `+∞` for `q < 1`); `+∞` where
  `B_q = +∞` (`a = 0` or `b = 0`); **`−∞` at the zeros of `B_q`** (`a + b` a non-positive
  integer, and `+∞` for `q > 1`).
* **Exact case**: at positive integers whose value `B_q(m, n)` is formed as a rational
  (`qBetaExact?`), the logarithm of that rational (`lnRatPrecRound`, no fuel).
* **Fuel** as for `B_q` (`qGammaFuel`).

The specifications (`lnAbsQBetaPrecRoundFuel_zivSpec`, …) are in `Equiv/LnQBeta.lean`.
-/

namespace Azurite.AzFloat

/-- **`ln |B_q(a, b)|` and the sign of `B_q(a, b)` for a base, two arguments and their sum
given by their data**, with the fuel of the loop explicit. -/
def lnAbsQBetaOf (Q : QBase) (Sa Sb Ss : QArg) (fuel p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  if Sa.kind.isPole || Sb.kind.isPole then ((nan, .eq), true)
  else if Sa.kind.isZero || Sb.kind.isZero then ((infinity true, .eq), true)
  else if p = 0 then ((nan, .eq), true)
  else if Ss.kind.isZero || Ss.kind.isPole then ((infinity false, .eq), true)
  else
    match qBetaExact? Q Sa.kind Sb.kind p with
    | some r => (lnRatPrecRound r p mode, true)
    | none =>
      lnAbsLoop (qBetaLnEnclOf (qGammaInOf Q Sa) (qGammaInOf Q Sb) (qGammaInOf Q Ss)) p mode
        fuel (max 64 (p + 32))

/-- The logarithm of a result of `B_q` that is `0` or `NaN`: `−∞` or `NaN`. -/
def lnOfZeroOrNan (r : AzFloat × Ordering) : AzFloat × Ordering :=
  if isZeroVal r.1 then (infinity false, .eq) else (nan, .eq)

/-- `ln |B_q(a, b)|` with the sign on a base given by its data and two floats. -/
def lnAbsQBetaFloatArgs (Q : QBase) (fuel : Nat) (a b : AzFloat) (p : Nat)
    (mode : RoundingMode) : (AzFloat × Ordering) × Bool :=
  if a.isFinite && b.isFinite then
    lnAbsQBetaOf Q (qArgFloat a) (qArgFloat b) (qArgSumFloat a b) fuel p mode
  else (lnOfZeroOrNan (qBetaFloatArgs Q 0 a b 1 .Nearest), true)

/-- `ln |B_q(a, b)|` with the sign on a base given by its data and two rationals. -/
def lnAbsQBetaRatArgs (Q : QBase) (fuel : Nat) (a b : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsQBetaOf Q (qArgRat a) (qArgRat b) (qArgRat (a + b)) fuel p mode

/-- `ln |B_q(a, b)|` with the sign on a base given by its data, a float and a rational. -/
def lnAbsQBetaMixedArgs (Q : QBase) (fuel : Nat) (a : AzFloat) (b : AzRat) (p : Nat)
    (mode : RoundingMode) : (AzFloat × Ordering) × Bool :=
  match a.toAzRat? with
  | some r => lnAbsQBetaRatArgs Q fuel r b p mode
  | none => (lnOfZeroOrNan (qBetaMixedArgs Q 0 a b 1 .Nearest), true)

/-- `ln v` from `ln |v|` and the sign: `(nan, .eq)` where the sign is negative. -/
def lnOfSigned (r : (AzFloat × Ordering) × Bool) : AzFloat × Ordering :=
  if r.2 then r.1 else (nan, .eq)

/-! ### Floats `q`, `a`, `b` -/

/-- **`ln |B_q(a, b)|` for floats `q`, `a`, `b`**, rounded to precision `p` with `mode`, the
comparison with the exact value, and the sign of `B_q(a, b)` (`true`: not negative), with the fuel
of the loop explicit.  The specification is `lnAbsQBetaPrecRoundFuel_zivSpec`. -/
def lnAbsQBetaPrecRoundFuel (fuel : Nat) (q a b : AzFloat) (p : Nat)
    (mode : RoundingMode) : (AzFloat × Ordering) × Bool :=
  if q.isFinite && lt zero q then
    if le q one && le one q then lnAbsBetaPrecRoundFuel fuel a b p mode
    else lnAbsQBetaFloatArgs (qBaseFloat q) fuel a b p mode
  else ((nan, .eq), true)

/-- `ln |B_q(a, b)|` and the sign of `B_q(a, b)` for floats `q`, `a`, `b`, at the fuel of `B_q`. -/
def lnAbsQBetaPrecRound (q a b : AzFloat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsQBetaPrecRoundFuel (qGammaFuel (lt a zero || lt b zero) p) q a b p mode

/-- `ln |B_q(a, b)|` rounded to nearest, and the sign of `B_q(a, b)`. -/
def lnAbsQBeta (q a b : AzFloat) : AzFloat × Bool :=
  let r := lnAbsQBetaPrecRound q a b
    (max (q.precision?.getD 1) (max (a.precision?.getD 1) (b.precision?.getD 1))) .Nearest
  (r.1.1, r.2)

/-- **`ln B_q(a, b)` for floats `q`, `a`, `b`**, with the fuel explicit: `ln |B_q(a, b)|` where
`B_q(a, b) ≥ 0`, `(nan, .eq)` where `B_q(a, b) < 0`. -/
def lnQBetaPrecRoundFuel (fuel : Nat) (q a b : AzFloat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  if q.isFinite && lt zero q then
    if le q one && le one q then lnBetaPrecRoundFuel fuel a b p mode
    else lnOfSigned (lnAbsQBetaFloatArgs (qBaseFloat q) fuel a b p mode)
  else (nan, .eq)

/-- `ln B_q(a, b)` for floats `q`, `a`, `b`, rounded to precision `p` with `mode`. -/
def lnQBetaPrecRound (q a b : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  lnQBetaPrecRoundFuel (qGammaFuel (lt a zero || lt b zero) p) q a b p mode

/-- `ln B_q(a, b)` rounded to nearest. -/
def lnQBeta (q a b : AzFloat) : AzFloat :=
  (lnQBetaPrecRound q a b
    (max (q.precision?.getD 1) (max (a.precision?.getD 1) (b.precision?.getD 1))) .Nearest).1

/-! ### A float `q`, a float `a` and a rational `b` -/

/-- **`ln |B_q(a, b)|` for a float `q`, a float `a` and a rational `b`**, rounded to precision `p`
with `mode`, the comparison with the exact value, and the sign of `B_q(a, b)` (`true`: not
negative), with the fuel of the loop explicit.  The specification is
`lnAbsQBetaFloatFloatRatPrecRoundFuel_zivSpec`. -/
def lnAbsQBetaFloatFloatRatPrecRoundFuel (fuel : Nat) (q a : AzFloat) (b : AzRat) (p : Nat)
    (mode : RoundingMode) : (AzFloat × Ordering) × Bool :=
  if q.isFinite && lt zero q then
    if le q one && le one q then lnAbsBetaFloatRatPrecRoundFuel fuel a b p mode
    else lnAbsQBetaMixedArgs (qBaseFloat q) fuel a b p mode
  else ((nan, .eq), true)

/-- `ln |B_q(a, b)|` and the sign of `B_q(a, b)` for a float `q`, a float `a` and a rational `b`,
at the fuel of `B_q`. -/
def lnAbsQBetaFloatFloatRatPrecRound (q a : AzFloat) (b : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsQBetaFloatFloatRatPrecRoundFuel (qGammaFuel (lt a zero || !b.sign) p) q a b p mode

/-- `ln |B_q(a, b)|` rounded to nearest, and the sign of `B_q(a, b)`. -/
def lnAbsQBetaFloatFloatRat (q a : AzFloat) (b : AzRat) (p : Nat) : AzFloat × Bool :=
  let r := lnAbsQBetaFloatFloatRatPrecRound q a b
    p .Nearest
  (r.1.1, r.2)

/-- **`ln B_q(a, b)` for a float `q`, a float `a` and a rational `b`**, with the fuel explicit:
`ln |B_q(a, b)|` where `B_q(a, b) ≥ 0`, `(nan, .eq)` where `B_q(a, b) < 0`. -/
def lnQBetaFloatFloatRatPrecRoundFuel (fuel : Nat) (q a : AzFloat) (b : AzRat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  if q.isFinite && lt zero q then
    if le q one && le one q then lnBetaFloatRatPrecRoundFuel fuel a b p mode
    else lnOfSigned (lnAbsQBetaMixedArgs (qBaseFloat q) fuel a b p mode)
  else (nan, .eq)

/-- `ln B_q(a, b)` for a float `q`, a float `a` and a rational `b`, rounded to precision `p` with
`mode`. -/
def lnQBetaFloatFloatRatPrecRound (q a : AzFloat) (b : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  lnQBetaFloatFloatRatPrecRoundFuel (qGammaFuel (lt a zero || !b.sign) p) q a b p mode

/-- `ln B_q(a, b)` rounded to nearest. -/
def lnQBetaFloatFloatRat (q a : AzFloat) (b : AzRat) (p : Nat) : AzFloat :=
  (lnQBetaFloatFloatRatPrecRound q a b
    p .Nearest).1

/-! ### A float `q` and rationals `a`, `b` -/

/-- **`ln |B_q(a, b)|` for a float `q` and rationals `a`, `b`**, rounded to precision `p` with
`mode`, the comparison with the exact value, and the sign of `B_q(a, b)` (`true`: not negative),
with the fuel of the loop explicit.  The specification is
`lnAbsQBetaFloatRatRatPrecRoundFuel_zivSpec`. -/
def lnAbsQBetaFloatRatRatPrecRoundFuel (fuel : Nat) (q : AzFloat) (a b : AzRat) (p : Nat)
    (mode : RoundingMode) : (AzFloat × Ordering) × Bool :=
  if q.isFinite && lt zero q then
    if le q one && le one q then lnAbsBetaRatPrecRoundFuel fuel a b p mode
    else lnAbsQBetaRatArgs (qBaseFloat q) fuel a b p mode
  else ((nan, .eq), true)

/-- `ln |B_q(a, b)|` and the sign of `B_q(a, b)` for a float `q` and rationals `a`, `b`, at the
fuel of `B_q`. -/
def lnAbsQBetaFloatRatRatPrecRound (q : AzFloat) (a b : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsQBetaFloatRatRatPrecRoundFuel (qGammaFuel (!a.sign || !b.sign) p) q a b p mode

/-- `ln |B_q(a, b)|` rounded to nearest, and the sign of `B_q(a, b)`. -/
def lnAbsQBetaFloatRatRat (q : AzFloat) (a b : AzRat) (p : Nat) : AzFloat × Bool :=
  let r := lnAbsQBetaFloatRatRatPrecRound q a b
    p .Nearest
  (r.1.1, r.2)

/-- **`ln B_q(a, b)` for a float `q` and rationals `a`, `b`**, with the fuel explicit: `ln |B_q(a,
b)|` where `B_q(a, b) ≥ 0`, `(nan, .eq)` where `B_q(a, b) < 0`. -/
def lnQBetaFloatRatRatPrecRoundFuel (fuel : Nat) (q : AzFloat) (a b : AzRat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  if q.isFinite && lt zero q then
    if le q one && le one q then lnBetaRatPrecRoundFuel fuel a b p mode
    else lnOfSigned (lnAbsQBetaRatArgs (qBaseFloat q) fuel a b p mode)
  else (nan, .eq)

/-- `ln B_q(a, b)` for a float `q` and rationals `a`, `b`, rounded to precision `p` with `mode`. -/
def lnQBetaFloatRatRatPrecRound (q : AzFloat) (a b : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  lnQBetaFloatRatRatPrecRoundFuel (qGammaFuel (!a.sign || !b.sign) p) q a b p mode

/-- `ln B_q(a, b)` rounded to nearest. -/
def lnQBetaFloatRatRat (q : AzFloat) (a b : AzRat) (p : Nat) : AzFloat :=
  (lnQBetaFloatRatRatPrecRound q a b
    p .Nearest).1

/-! ### A rational `q` and floats `a`, `b` -/

/-- **`ln |B_q(a, b)|` for a rational `q` and floats `a`, `b`**, rounded to precision `p` with
`mode`, the comparison with the exact value, and the sign of `B_q(a, b)` (`true`: not negative),
with the fuel of the loop explicit.  The specification is
`lnAbsQBetaRatFloatFloatPrecRoundFuel_zivSpec`. -/
def lnAbsQBetaRatFloatFloatPrecRoundFuel (fuel : Nat) (q : AzRat) (a b : AzFloat) (p : Nat)
    (mode : RoundingMode) : (AzFloat × Ordering) × Bool :=
  if q.sign = true ∧ q.num ≠ 0 then
    if q.num = q.den then lnAbsBetaPrecRoundFuel fuel a b p mode
    else lnAbsQBetaFloatArgs (qBaseRat q) fuel a b p mode
  else ((nan, .eq), true)

/-- `ln |B_q(a, b)|` and the sign of `B_q(a, b)` for a rational `q` and floats `a`, `b`, at the
fuel of `B_q`. -/
def lnAbsQBetaRatFloatFloatPrecRound (q : AzRat) (a b : AzFloat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsQBetaRatFloatFloatPrecRoundFuel (qGammaFuel (lt a zero || lt b zero) p) q a b p mode

/-- `ln |B_q(a, b)|` rounded to nearest, and the sign of `B_q(a, b)`. -/
def lnAbsQBetaRatFloatFloat (q : AzRat) (a b : AzFloat) (p : Nat) : AzFloat × Bool :=
  let r := lnAbsQBetaRatFloatFloatPrecRound q a b
    p .Nearest
  (r.1.1, r.2)

/-- **`ln B_q(a, b)` for a rational `q` and floats `a`, `b`**, with the fuel explicit: `ln |B_q(a,
b)|` where `B_q(a, b) ≥ 0`, `(nan, .eq)` where `B_q(a, b) < 0`. -/
def lnQBetaRatFloatFloatPrecRoundFuel (fuel : Nat) (q : AzRat) (a b : AzFloat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  if q.sign = true ∧ q.num ≠ 0 then
    if q.num = q.den then lnBetaPrecRoundFuel fuel a b p mode
    else lnOfSigned (lnAbsQBetaFloatArgs (qBaseRat q) fuel a b p mode)
  else (nan, .eq)

/-- `ln B_q(a, b)` for a rational `q` and floats `a`, `b`, rounded to precision `p` with `mode`. -/
def lnQBetaRatFloatFloatPrecRound (q : AzRat) (a b : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  lnQBetaRatFloatFloatPrecRoundFuel (qGammaFuel (lt a zero || lt b zero) p) q a b p mode

/-- `ln B_q(a, b)` rounded to nearest. -/
def lnQBetaRatFloatFloat (q : AzRat) (a b : AzFloat) (p : Nat) : AzFloat :=
  (lnQBetaRatFloatFloatPrecRound q a b
    p .Nearest).1

/-! ### A rational `q`, a float `a` and a rational `b` -/

/-- **`ln |B_q(a, b)|` for a rational `q`, a float `a` and a rational `b`**, rounded to precision
`p` with `mode`, the comparison with the exact value, and the sign of `B_q(a, b)` (`true`: not
negative), with the fuel of the loop explicit.  The specification is
`lnAbsQBetaRatFloatRatPrecRoundFuel_zivSpec`. -/
def lnAbsQBetaRatFloatRatPrecRoundFuel (fuel : Nat) (q : AzRat) (a : AzFloat) (b : AzRat) (p : Nat)
    (mode : RoundingMode) : (AzFloat × Ordering) × Bool :=
  if q.sign = true ∧ q.num ≠ 0 then
    if q.num = q.den then lnAbsBetaFloatRatPrecRoundFuel fuel a b p mode
    else lnAbsQBetaMixedArgs (qBaseRat q) fuel a b p mode
  else ((nan, .eq), true)

/-- `ln |B_q(a, b)|` and the sign of `B_q(a, b)` for a rational `q`, a float `a` and a rational
`b`, at the fuel of `B_q`. -/
def lnAbsQBetaRatFloatRatPrecRound (q : AzRat) (a : AzFloat) (b : AzRat) (p : Nat) (mode
    : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsQBetaRatFloatRatPrecRoundFuel (qGammaFuel (lt a zero || !b.sign) p) q a b p mode

/-- `ln |B_q(a, b)|` rounded to nearest, and the sign of `B_q(a, b)`. -/
def lnAbsQBetaRatFloatRat (q : AzRat) (a : AzFloat) (b : AzRat) (p : Nat) : AzFloat × Bool :=
  let r := lnAbsQBetaRatFloatRatPrecRound q a b
    p .Nearest
  (r.1.1, r.2)

/-- **`ln B_q(a, b)` for a rational `q`, a float `a` and a rational `b`**, with the fuel explicit:
`ln |B_q(a, b)|` where `B_q(a, b) ≥ 0`, `(nan, .eq)` where `B_q(a, b) < 0`. -/
def lnQBetaRatFloatRatPrecRoundFuel (fuel : Nat) (q : AzRat) (a : AzFloat) (b : AzRat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  if q.sign = true ∧ q.num ≠ 0 then
    if q.num = q.den then lnBetaFloatRatPrecRoundFuel fuel a b p mode
    else lnOfSigned (lnAbsQBetaMixedArgs (qBaseRat q) fuel a b p mode)
  else (nan, .eq)

/-- `ln B_q(a, b)` for a rational `q`, a float `a` and a rational `b`, rounded to precision `p`
with `mode`. -/
def lnQBetaRatFloatRatPrecRound (q : AzRat) (a : AzFloat) (b : AzRat) (p : Nat) (mode
    : RoundingMode) :
    AzFloat × Ordering :=
  lnQBetaRatFloatRatPrecRoundFuel (qGammaFuel (lt a zero || !b.sign) p) q a b p mode

/-- `ln B_q(a, b)` rounded to nearest. -/
def lnQBetaRatFloatRat (q : AzRat) (a : AzFloat) (b : AzRat) (p : Nat) : AzFloat :=
  (lnQBetaRatFloatRatPrecRound q a b
    p .Nearest).1

/-! ### Rationals `q`, `a`, `b` -/

/-- **`ln |B_q(a, b)|` for rationals `q`, `a`, `b`**, rounded to precision `p` with `mode`, the
comparison with the exact value, and the sign of `B_q(a, b)` (`true`: not negative), with the fuel
of the loop explicit.  The specification is `lnAbsQBetaRatPrecRoundFuel_zivSpec`. -/
def lnAbsQBetaRatPrecRoundFuel (fuel : Nat) (q a b : AzRat) (p : Nat)
    (mode : RoundingMode) : (AzFloat × Ordering) × Bool :=
  if q.sign = true ∧ q.num ≠ 0 then
    if q.num = q.den then lnAbsBetaRatPrecRoundFuel fuel a b p mode
    else lnAbsQBetaRatArgs (qBaseRat q) fuel a b p mode
  else ((nan, .eq), true)

/-- `ln |B_q(a, b)|` and the sign of `B_q(a, b)` for rationals `q`, `a`, `b`, at the fuel of
`B_q`. -/
def lnAbsQBetaRatPrecRound (q a b : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × Bool :=
  lnAbsQBetaRatPrecRoundFuel (qGammaFuel (!a.sign || !b.sign) p) q a b p mode

/-- `ln |B_q(a, b)|` rounded to nearest, and the sign of `B_q(a, b)`. -/
def lnAbsQBetaRat (q a b : AzRat) (p : Nat) : AzFloat × Bool :=
  let r := lnAbsQBetaRatPrecRound q a b
    p .Nearest
  (r.1.1, r.2)

/-- **`ln B_q(a, b)` for rationals `q`, `a`, `b`**, with the fuel explicit: `ln |B_q(a, b)|` where
`B_q(a, b) ≥ 0`, `(nan, .eq)` where `B_q(a, b) < 0`. -/
def lnQBetaRatPrecRoundFuel (fuel : Nat) (q a b : AzRat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  if q.sign = true ∧ q.num ≠ 0 then
    if q.num = q.den then lnBetaRatPrecRoundFuel fuel a b p mode
    else lnOfSigned (lnAbsQBetaRatArgs (qBaseRat q) fuel a b p mode)
  else (nan, .eq)

/-- `ln B_q(a, b)` for rationals `q`, `a`, `b`, rounded to precision `p` with `mode`. -/
def lnQBetaRatPrecRound (q a b : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  lnQBetaRatPrecRoundFuel (qGammaFuel (!a.sign || !b.sign) p) q a b p mode

/-- `ln B_q(a, b)` rounded to nearest. -/
def lnQBetaRat (q a b : AzRat) (p : Nat) : AzFloat :=
  (lnQBetaRatPrecRound q a b
    p .Nearest).1

end Azurite.AzFloat
