/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.QGamma
import Azurite.AzFloat.Beta
import Azurite.AzFloat.BetaRat
import Azurite.AzFloat.BetaFloatRat
import Azurite.AzRat.Add
import Azurite.AzRat.Mul

/-!
## The `q`-beta function

`B_q(a, b) = Γ_q(a) Γ_q(b) / Γ_q(a + b)` (DLMF 5.18.11) for a base `q > 0` and real `a`, `b`,
rounded to precision `p` in `mode` with the comparison against the exact value; `Γ_q` is the
`q`-gamma function of `AzFloat/QGamma.lean` (`Γ` at `q = 1`, continued to `q > 1`).

**Six functions**: the base a float or a rational, and the two arguments — in which the
function is symmetric — two floats, a float and a rational, or two rationals:

| base | arguments | function |
|---|---|---|
| `AzFloat` | `AzFloat`, `AzFloat` | `qBetaPrecRound q a b p mode`, `qBeta q a b` |
| `AzFloat` | `AzFloat`, `AzRat` | `qBetaFloatFloatRatPrecRound`, `qBetaFloatFloatRat` |
| `AzFloat` | `AzRat`, `AzRat` | `qBetaFloatRatRatPrecRound`, `qBetaFloatRatRat` |
| `AzRat` | `AzFloat`, `AzFloat` | `qBetaRatFloatFloatPrecRound`, `qBetaRatFloatFloat` |
| `AzRat` | `AzFloat`, `AzRat` | `qBetaRatFloatRatPrecRound`, `qBetaRatFloatRat` |
| `AzRat` | `AzRat`, `AzRat` | `qBetaRatPrecRound`, `qBetaRat` |

each with a `…Fuel` variant that has the fuel of the Ziv loop as an argument.

* **The base.**  `NaN` for a base that is `NaN`, `≤ 0` or `+∞`; at the base `1` the function
  is `B` (`betaPrecRoundFuel`, `betaFloatRatPrecRoundFuel`, `betaRatPrecRoundFuel`).
* **Special values**, as for `B` (`AzFloat/Beta.lean`).  `NaN` when `a` or `b` is `NaN`,
  `−∞` or a negative integer; `+∞` when `a` or `b` is `0`; **`0` exactly when `a + b` is a
  non-positive integer** and neither `a` nor `b` is one.  At `+∞`: for `q > 1`,
  `B_q(+∞, b) = 0` for `b > 0` as for `B`; **for `q < 1` the limit is not `0`** —
  `B_q(a, b) → Γ_q(b) (1 − q)^b` as `a → +∞` — and the function answers `NaN` there.
* **Exact values**: at positive integers `m`, `n` the value is the rational number
  `Γ_q(m) Γ_q(n) / Γ_q(m + n)`, formed and rounded when the three `q`-factorials are
  (`qGammaExact?`).
* **Rounding.**  Everywhere else Ziv's loop with fuel (`qGammaFuel`) on the bracket
  `qBetaApproxOf`: the three enclosures of `ln |Γ_q|` (`qGammaLnEnclOf`,
  `AzFloat/QGammaBracket.lean`) at `a`, `b` and `a + b`, added, and the exponential.  The
  specifications are the six `…_zivSpec` (`Equiv/QBeta.lean`).
* **A float and a rational argument**: the float is taken as the rational it is
  (`toAzRat?`), as for `betaFloatRat`; an argument below `2^(−10⁸)` in absolute value is a
  long rational and slow.
* **Cost**: three `Γ_q`.  A bracket of its own — one product
  `∏ (1 − p^(k+1)) (1 − p^(a+b+k)) / ((1 − p^(a+k)) (1 − p^(b+k)))`, in which the powers of
  `1 − p` cancel — would be about twice as fast; not done.
* **Values that are rounding boundaries off the integers** exist and end only with the fuel:
  `B_q(1, b) = (1 − q)/(1 − q^b)` is `3/2` at `q = 1/4`, `b = 1/2`.
-/

namespace Azurite.AzFloat

/-- Is the class a pole `−1, −2, …`? -/
def QArgKind.isPole : QArgKind → Bool
  | .pole => true
  | _ => false

/-- Is the class `0`? -/
def QArgKind.isZero : QArgKind → Bool
  | .zero => true
  | _ => false

/-- The enclosure of `ln |B_q(a, b)|` with the sign of `B_q(a, b)`, from the three
enclosures of `ln |Γ_q|`. -/
def qBetaLnEnclOf (A B C : QGammaIn) (w : Nat) : Option (Bool × Encl) :=
  (qGammaLnEnclOf A w).bind fun ra =>
    (qGammaLnEnclOf B w).bind fun rb =>
      (qGammaLnEnclOf C w).map fun rc =>
        ((ra.1 != rb.1) != rc.1, Encl.sub (w + 64) (Encl.add (w + 64) ra.2 rb.2) rc.2)

/-- The sign of a value and a positive enclosure of its absolute value at Ziv level `w`, from
an enclosure of the logarithm of the absolute value with the sign. -/
def lnCoreExp (l : Nat → Option (Bool × Encl)) (w : Nat) : Option (Bool × Encl) :=
  (l w).bind fun r => (gammaExpEncl false r.2 w).map fun g => (r.1, g)

/-- The bracket of `B_q(a, b)` as a pair of `Roundable`s. -/
def qBetaApproxOf (Q : QBase) (Sa Sb Ss : QArg) (w : Nat) : Roundable × Roundable :=
  gammaApproxOf (lnCoreExp
    (qBetaLnEnclOf (qGammaInOf Q Sa) (qGammaInOf Q Sb) (qGammaInOf Q Ss)) w) w

/-- The exact value `B_q(m, n)` at positive integers, when it is formed at precision `p`. -/
def qBetaExact? (Q : QBase) (ka kb : QArgKind) (p : Nat) : Option AzRat :=
  match ka, kb with
  | .posInt m, .posInt n =>
    (qGammaExact? Q m p).bind fun ra =>
      (qGammaExact? Q n p).bind fun rb =>
        (qGammaExact? Q (m + n) p).map fun rc => ra * rb / rc
  | _, _ => none

/-- **`B_q(a, b)` for a base, two arguments and their sum given by their data**, with the
fuel of the Ziv loop explicit. -/
def qBetaOf (Q : QBase) (Sa Sb Ss : QArg) (fuel p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if Sa.kind.isPole || Sb.kind.isPole then (nan, .eq)
  else if Sa.kind.isZero || Sb.kind.isZero then (infinity true, .eq)
  else if p = 0 then (nan, .eq)
  else if Ss.kind.isZero || Ss.kind.isPole then (zero, .eq)
  else
    match qBetaExact? Q Sa.kind Sb.kind p with
    | some r => ofAzRatRound r p mode
    | none => zivLoop (qBetaApproxOf Q Sa Sb Ss) p mode fuel (max 64 (p + 32))

/-- The sum of two finite floats as an argument: its enclosures by the rounded sums, and the
class `zero` exactly when the sum is a non-positive integer (`sumIsNonposInt`). -/
def qArgSumFloat (a b : AzFloat) : QArg where
  X := fun V => Encl.add V (Encl.exact a) (Encl.exact b)
  absX := fun V =>
    let s := Encl.add V (Encl.exact a) (Encl.exact b)
    if le (-a) b then (clampNonneg s.1, s.2)
    else (clampNonneg (Encl.neg s).1, (Encl.neg s).2)
  shift := (qArgFloat a).shift + (qArgFloat b).shift
  eb := (qArgFloat a).eb + (qArgFloat b).eb + 2
  kind := if sumIsNonposInt a b then .zero else .general

/-- `B_q(+∞, y)` for a float `y`: `0` for a base `q > 1` and `y > 0`, `NaN` otherwise. -/
def qBetaInfinite (inv : Bool) (y : AzFloat) : AzFloat × Ordering :=
  if inv && lt zero y then (zero, .eq) else (nan, .eq)

/-- `B_q(a, b)` on a base given by its data and two floats. -/
def qBetaFloatArgs (Q : QBase) (fuel : Nat) (a b : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match a, b with
  | nan, _ => (nan, .eq)
  | _, nan => (nan, .eq)
  | infinity s, b => if s then qBetaInfinite Q.inv b else (nan, .eq)
  | a, infinity s => if s then qBetaInfinite Q.inv a else (nan, .eq)
  | a, b => qBetaOf Q (qArgFloat a) (qArgFloat b) (qArgSumFloat a b) fuel p mode

/-- `B_q(a, b)` on a base given by its data and two rationals. -/
def qBetaRatArgs (Q : QBase) (fuel : Nat) (a b : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  qBetaOf Q (qArgRat a) (qArgRat b) (qArgRat (a + b)) fuel p mode

/-- `B_q(a, b)` on a base given by its data, a float and a rational: the float as the
rational it is. -/
def qBetaMixedArgs (Q : QBase) (fuel : Nat) (a : AzFloat) (b : AzRat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  match a.toAzRat? with
  | some r => qBetaRatArgs Q fuel r b p mode
  | none =>
    match a with
    | infinity true => if Q.inv && ratIsPos b then (zero, .eq) else (nan, .eq)
    | _ => (nan, .eq)

/-! ### A float base -/

/-- **`B_q(a, b)` for floats `q`, `a`, `b`, rounded to precision `p` with `mode`, with the
fuel of the Ziv loop explicit**, and the comparison with the exact value.  The specification
is `qBetaPrecRoundFuel_zivSpec` (`Equiv/QBeta.lean`). -/
def qBetaPrecRoundFuel (fuel : Nat) (q a b : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if q.isFinite && lt zero q then
    if le q one && le one q then betaPrecRoundFuel fuel a b p mode
    else qBetaFloatArgs (qBaseFloat q) fuel a b p mode
  else (nan, .eq)

/-- `B_q(a, b)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for a base that is not positive and finite, at the poles, for `p = 0` unless
the value is `0` or `+∞`, or if the fuel runs out). -/
def qBetaPrecRound (q a b : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  qBetaPrecRoundFuel (qGammaFuel (lt a zero || lt b zero) p) q a b p mode

/-- `B_q(a, b)` rounded to nearest at the largest of the precisions of `q`, `a` and `b`. -/
def qBeta (q a b : AzFloat) : AzFloat :=
  (qBetaPrecRound q a b
    (max (q.precision?.getD 1) (max (a.precision?.getD 1) (b.precision?.getD 1))) .Nearest).1

/-- **`B_q(a, b)` for a float `q`, a float `a` and a rational `b`**, with the fuel of the Ziv
loop explicit.  The specification is `qBetaFloatFloatRatPrecRoundFuel_zivSpec`. -/
def qBetaFloatFloatRatPrecRoundFuel (fuel : Nat) (q a : AzFloat) (b : AzRat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  if q.isFinite && lt zero q then
    if le q one && le one q then betaFloatRatPrecRoundFuel fuel a b p mode
    else qBetaMixedArgs (qBaseFloat q) fuel a b p mode
  else (nan, .eq)

/-- `B_q(a, b)` for a float `q`, a float `a` and a rational `b`, rounded to precision `p` with
`mode`. -/
def qBetaFloatFloatRatPrecRound (q a : AzFloat) (b : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  qBetaFloatFloatRatPrecRoundFuel (qGammaFuel (lt a zero || !b.sign) p) q a b p mode

/-- `B_q(a, b)` for a float `q`, a float `a` and a rational `b`, rounded to nearest at
precision `p`. -/
def qBetaFloatFloatRat (q a : AzFloat) (b : AzRat) (p : Nat) : AzFloat :=
  (qBetaFloatFloatRatPrecRound q a b p .Nearest).1

/-- **`B_q(a, b)` for a float `q` and rationals `a`, `b`**, with the fuel of the Ziv loop
explicit.  The specification is `qBetaFloatRatRatPrecRoundFuel_zivSpec`. -/
def qBetaFloatRatRatPrecRoundFuel (fuel : Nat) (q : AzFloat) (a b : AzRat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  if q.isFinite && lt zero q then
    if le q one && le one q then betaRatPrecRoundFuel fuel a b p mode
    else qBetaRatArgs (qBaseFloat q) fuel a b p mode
  else (nan, .eq)

/-- `B_q(a, b)` for a float `q` and rationals `a`, `b`, rounded to precision `p` with
`mode`. -/
def qBetaFloatRatRatPrecRound (q : AzFloat) (a b : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  qBetaFloatRatRatPrecRoundFuel (qGammaFuel (!a.sign || !b.sign) p) q a b p mode

/-- `B_q(a, b)` for a float `q` and rationals `a`, `b`, rounded to nearest at precision
`p`. -/
def qBetaFloatRatRat (q : AzFloat) (a b : AzRat) (p : Nat) : AzFloat :=
  (qBetaFloatRatRatPrecRound q a b p .Nearest).1

/-! ### A rational base -/

/-- **`B_q(a, b)` for a rational `q` and floats `a`, `b`**, with the fuel of the Ziv loop
explicit.  The specification is `qBetaRatFloatFloatPrecRoundFuel_zivSpec`. -/
def qBetaRatFloatFloatPrecRoundFuel (fuel : Nat) (q : AzRat) (a b : AzFloat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  if q.sign = true ∧ q.num ≠ 0 then
    if q.num = q.den then betaPrecRoundFuel fuel a b p mode
    else qBetaFloatArgs (qBaseRat q) fuel a b p mode
  else (nan, .eq)

/-- `B_q(a, b)` for a rational `q` and floats `a`, `b`, rounded to precision `p` with
`mode`. -/
def qBetaRatFloatFloatPrecRound (q : AzRat) (a b : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  qBetaRatFloatFloatPrecRoundFuel (qGammaFuel (lt a zero || lt b zero) p) q a b p mode

/-- `B_q(a, b)` for a rational `q` and floats `a`, `b`, rounded to nearest at precision
`p`. -/
def qBetaRatFloatFloat (q : AzRat) (a b : AzFloat) (p : Nat) : AzFloat :=
  (qBetaRatFloatFloatPrecRound q a b p .Nearest).1

/-- **`B_q(a, b)` for a rational `q`, a float `a` and a rational `b`**, with the fuel of the
Ziv loop explicit.  The specification is `qBetaRatFloatRatPrecRoundFuel_zivSpec`. -/
def qBetaRatFloatRatPrecRoundFuel (fuel : Nat) (q : AzRat) (a : AzFloat) (b : AzRat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  if q.sign = true ∧ q.num ≠ 0 then
    if q.num = q.den then betaFloatRatPrecRoundFuel fuel a b p mode
    else qBetaMixedArgs (qBaseRat q) fuel a b p mode
  else (nan, .eq)

/-- `B_q(a, b)` for a rational `q`, a float `a` and a rational `b`, rounded to precision `p`
with `mode`. -/
def qBetaRatFloatRatPrecRound (q : AzRat) (a : AzFloat) (b : AzRat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  qBetaRatFloatRatPrecRoundFuel (qGammaFuel (lt a zero || !b.sign) p) q a b p mode

/-- `B_q(a, b)` for a rational `q`, a float `a` and a rational `b`, rounded to nearest at
precision `p`. -/
def qBetaRatFloatRat (q : AzRat) (a : AzFloat) (b : AzRat) (p : Nat) : AzFloat :=
  (qBetaRatFloatRatPrecRound q a b p .Nearest).1

/-- **`B_q(a, b)` for rationals `q`, `a`, `b`**, with the fuel of the Ziv loop explicit.  The
specification is `qBetaRatPrecRoundFuel_zivSpec`. -/
def qBetaRatPrecRoundFuel (fuel : Nat) (q a b : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if q.sign = true ∧ q.num ≠ 0 then
    if q.num = q.den then betaRatPrecRoundFuel fuel a b p mode
    else qBetaRatArgs (qBaseRat q) fuel a b p mode
  else (nan, .eq)

/-- `B_q(a, b)` for rationals `q`, `a`, `b`, rounded to precision `p` with `mode`. -/
def qBetaRatPrecRound (q a b : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  qBetaRatPrecRoundFuel (qGammaFuel (!a.sign || !b.sign) p) q a b p mode

/-- `B_q(a, b)` for rationals `q`, `a`, `b`, rounded to nearest at precision `p`. -/
def qBetaRat (q a b : AzRat) (p : Nat) : AzFloat := (qBetaRatPrecRound q a b p .Nearest).1

end Azurite.AzFloat
