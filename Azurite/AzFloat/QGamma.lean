/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.QGammaBracket
import Azurite.AzFloat.Gamma
import Azurite.AzFloat.GammaRat
import Azurite.AzFloat.Conversion
import Azurite.AzRat.Div

/-!
## The `q`-gamma function

`Γ_q(x)` (DLMF §5.18) for a base `q > 0` and a real `x`, rounded to precision `p` in `mode`
with the comparison against the exact value.  For `0 < q < 1`

  `Γ_q(x) = (1 − q)^(1−x) ∏_{k ≥ 0} (1 − q^(k+1)) / (1 − q^(x+k))`,

at `q = 1` it is `Γ(x)`, and for `q > 1` it is `Γ_{1/q}(x) q^((x−1)(x−2)/2)`; in every base
`Γ_q(x + 1) = (q^x − 1)/(q − 1) Γ_q(x)`, `Γ_q(1) = 1`, so `Γ_q(n + 1)` is the `q`-factorial
`∏_{k=1}^{n} (1 + q + ⋯ + q^(k−1))`.

**Four functions**, for the base and the argument each a float or a rational:

| base | argument | function |
|---|---|---|
| `AzFloat` | `AzFloat` | `qGammaPrecRound q x p mode`, `qGamma q x` |
| `AzFloat` | `AzRat` | `qGammaFloatRatPrecRound`, `qGammaFloatRat q x p` |
| `AzRat` | `AzFloat` | `qGammaRatFloatPrecRound`, `qGammaRatFloat q x p` |
| `AzRat` | `AzRat` | `qGammaRatPrecRound`, `qGammaRat q x p` |

each with a `…Fuel` variant that has the fuel of the Ziv loop as an argument.

* **Special values.**  `NaN` for a base that is `NaN`, `≤ 0` or `+∞`; at the base `1` the
  function is `Γ` (`gammaPrecRoundFuel`, `gammaRatPrecRoundFuel`).  Otherwise, as for `Γ`:
  `Γ_q(+∞) = +∞`, `Γ_q(−∞) = NaN`, `Γ_q(0) = +∞`, and `NaN` at the poles `−1, −2, …`.
* **Exact values**: at a positive integer `n` the value is the rational number
  `∏_{k<n−1} (1 + q + ⋯ + q^k)`.  It is formed and rounded (`qGammaExact?`) for `n ≤ 2`
  (the value `1`), and for `n ≤ 2^20` when the product is short: `(n−1)(n−2)/2` times the
  bits of the numerator and the denominator of `q` at most `4p + 2^17` (and for a float `q`
  an exponent of at most `2^17` in absolute value).
* **Rounding.**  Everywhere else Ziv's loop with fuel on the bracket of
  `AzFloat/QGammaBracket.lean`.  The specifications are the four `…_zivSpec`
  (`Equiv/QGamma.lean`): correctly rounded or `NaN` at every fuel, correctly rounded for
  every large enough fuel wherever the value is no rounding boundary, and correct at every
  fuel on the special and the exact values.
* **Cost.**  The bracket multiplies `≈ 0.7 w / |ln q|` factors: fast for a base away from
  `1`, slow near it, and for a negative `x` the cost grows with `|x|`.  The fuel of a negative
  argument is practically unbounded (`qGammaFuel`).
-/

namespace Azurite.AzFloat

/-- The class of the argument: `0`, a pole `−1, −2, …`, a positive integer (up to `2^20`), or
anything else. -/
inductive QArgKind where
  | zero
  | pole
  | posInt (n : Nat)
  | general

/-- **The base of the bracket**: `inv` (`q > 1`, and `P` encloses `1/q`; else `P` encloses
`q < 1`), the padding `eb` of the precision, and `q` itself as a rational where exact values
may be formed from it. -/
structure QBase where
  inv : Bool
  P : Nat → Encl
  eb : Nat
  rat : Option AzRat

/-- **The argument of the bracket**: enclosures of `x` and `|x|`, a shift, the padding of the
precision, and the class. -/
structure QArg where
  X : Nat → Encl
  absX : Nat → Encl
  shift : Nat
  eb : Nat
  kind : QArgKind

/-- A base and an argument as the input of the bracket. -/
def qGammaInOf (Q : QBase) (S : QArg) : QGammaIn where
  inv := Q.inv
  P := Q.P
  X := S.X
  absX := S.absX
  shift := S.shift
  eb := Q.eb + S.eb

/-- After `k` more steps from `s = 1 + q + ⋯ + q^m` and `g = ∏_{i<m} (1 + ⋯ + q^i)`. -/
def qFactorialRatAux (q : AzRat) : Nat → AzRat → AzRat → AzRat
  | 0, _, g => g
  | k + 1, s, g => qFactorialRatAux q k (s * q + 1) (g * s)

/-- The `q`-factorial `∏_{k<n} (1 + q + ⋯ + q^k)` of a rational `q`. -/
def qFactorialRat (q : AzRat) (n : Nat) : AzRat := qFactorialRatAux q n 1 1

/-- The exact value `Γ_q(n)` at a positive integer `n`, when it is formed at precision `p`. -/
def qGammaExact? (Q : QBase) (n p : Nat) : Option AzRat :=
  if n ≤ 2 then some 1
  else
    match Q.rat with
    | some r =>
      if (n - 1) * (n - 2) / 2 * (r.num.size + r.den.size) ≤ 4 * p + 131072 then
        some (qFactorialRat r (n - 1))
      else none
    | none => none

/-- **`Γ_q(x)` for a base and an argument given by their data**, with the fuel of the Ziv loop
explicit. -/
def qGammaOf (Q : QBase) (S : QArg) (fuel p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match S.kind with
  | .zero => (infinity true, .eq)
  | .pole => (nan, .eq)
  | .posInt n =>
    if p = 0 then (nan, .eq)
    else
      match qGammaExact? Q n p with
      | some r => ofAzRatRound r p mode
      | none => zivLoop (qGammaApproxOf (qGammaInOf Q S)) p mode fuel (max 64 (p + 32))
  | .general =>
    if p = 0 then (nan, .eq)
    else zivLoop (qGammaApproxOf (qGammaInOf Q S)) p mode fuel (max 64 (p + 32))

/-- The padding of the working precision from the base `p` (enclosed by `P64` at `64` bits):
three times the bits of `1/(1 − p)` (the cancellation in `1 − p^k` and the number of
factors), and the bits of `ln(1/p)`. -/
def qBasePad (P64 : Encl) : Nat :=
  let Q1 := Encl.sub 64 (Encl.exact one) P64
  (if lt zero Q1.1 then 3 * (azIntPos (-(expOf Q1.1)) + 1) else 0)
    + (azIntPos (-(expOf P64.1)) + 2).log2

/-- A finite float `q > 0`, `q ≠ 1`, as the base. -/
def qBaseFloat (q : AzFloat) : QBase :=
  let P : Nat → Encl :=
    if lt one q then fun V => Encl.div V (Encl.exact one) (Encl.exact q)
    else fun _ => Encl.exact q
  { inv := lt one q
    P := P
    eb := qBasePad (P 64)
    rat := if azIntPos (expOf q) ≤ 131072 ∧ azIntPos (-(expOf q)) ≤ 131072 then q.toAzRat?
      else none }

/-- A rational `q > 0`, `q ≠ 1`, as the base. -/
def qBaseRat (q : AzRat) : QBase :=
  let r := if lt (ofAzNat q.den) (ofAzNat q.num) then q⁻¹ else q
  { inv := lt (ofAzNat q.den) (ofAzNat q.num)
    P := fun V => lnGammaRatEncl r V
    eb := qBasePad (lnGammaRatEncl r 64)
    rat := some q }

/-- The class of a finite float. -/
def qArgKindFloat (x : AzFloat) : QArgKind :=
  if isInteger x then
    if lt zero x then
      if le x (ofAzNat (AzNat.ofNat 1048576)) then .posInt (truncToAzInt x).abs.toNat
      else .general
    else if lt x zero then .pole
    else .zero
  else .general

/-- A finite float as the argument. -/
def qArgFloat (x : AzFloat) : QArg where
  X := fun _ => Encl.exact x
  absX := fun _ => Encl.exact x.abs
  shift := azIntPos (-(truncToAzInt x)) + 1
  eb := 2 * azIntPos (expOf x)
  kind := qArgKindFloat x

/-- The class of a rational. -/
def qArgKindRat (x : AzRat) : QArgKind :=
  if x.den = 1 then
    if x.num = 0 then .zero
    else if x.sign = false then .pole
    else if le (ofAzNat x.num) (ofAzNat (AzNat.ofNat 1048576)) then .posInt x.num.toNat
    else .general
  else .general

/-- A rational as the argument. -/
def qArgRat (x : AzRat) : QArg where
  X := fun V => lnGammaRatEncl x V
  absX := fun V => lnGammaRatEncl x.abs V
  shift := if x.sign then 1 else (x.num / x.den).toNat + 2
  eb := 2 * azIntPos (expOf (ofAzNat (x.num / x.den + 1)))
  kind := qArgKindRat x

/-- The fuel of `Γ_q`: that of `Γ`, and for a negative argument `64` more doublings of the
working precision — practically unbounded, so that a negative argument is never answered with
a `NaN` for want of fuel. -/
def qGammaFuel (neg : Bool) (p : Nat) : Nat := if neg then gammaFuel p + 64 else gammaFuel p

/-! ### A float base and a float argument -/

/-- **`Γ_q(x)` for floats `q` and `x`, rounded to precision `p` with `mode`, with the fuel of
the Ziv loop explicit**, and the comparison with the exact value.  The specification is
`qGammaPrecRoundFuel_zivSpec` (`Equiv/QGamma.lean`). -/
def qGammaPrecRoundFuel (fuel : Nat) (q x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if q.isFinite && lt zero q then
    if le q one && le one q then gammaPrecRoundFuel fuel x p mode
    else
      match x with
      | nan => (nan, .eq)
      | infinity s => if s then (infinity true, .eq) else (nan, .eq)
      | x => qGammaOf (qBaseFloat q) (qArgFloat x) fuel p mode
  else (nan, .eq)

/-- `Γ_q(x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for a base that is not positive and finite, at the poles, for `p = 0` unless
the value is `+∞`, or if the fuel runs out). -/
def qGammaPrecRound (q x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  qGammaPrecRoundFuel (qGammaFuel (lt x zero) p) q x p mode

/-- `Γ_q(x)` rounded to nearest at the larger of the precisions of `q` and `x`. -/
def qGamma (q x : AzFloat) : AzFloat :=
  (qGammaPrecRound q x (max (q.precision?.getD 1) (x.precision?.getD 1)) .Nearest).1

/-! ### A float base and a rational argument -/

/-- **`Γ_q(x)` for a float `q` and a rational `x`**, with the fuel of the Ziv loop explicit.
The specification is `qGammaFloatRatPrecRoundFuel_zivSpec`. -/
def qGammaFloatRatPrecRoundFuel (fuel : Nat) (q : AzFloat) (x : AzRat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  if q.isFinite && lt zero q then
    if le q one && le one q then gammaRatPrecRoundFuel fuel x p mode
    else qGammaOf (qBaseFloat q) (qArgRat x) fuel p mode
  else (nan, .eq)

/-- `Γ_q(x)` for a float `q` and a rational `x`, rounded to precision `p` with `mode`. -/
def qGammaFloatRatPrecRound (q : AzFloat) (x : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  qGammaFloatRatPrecRoundFuel (qGammaFuel (!x.sign) p) q x p mode

/-- `Γ_q(x)` for a float `q` and a rational `x`, rounded to nearest at precision `p`. -/
def qGammaFloatRat (q : AzFloat) (x : AzRat) (p : Nat) : AzFloat :=
  (qGammaFloatRatPrecRound q x p .Nearest).1

/-! ### A rational base and a float argument -/

/-- **`Γ_q(x)` for a rational `q` and a float `x`**, with the fuel of the Ziv loop explicit.
The specification is `qGammaRatFloatPrecRoundFuel_zivSpec`. -/
def qGammaRatFloatPrecRoundFuel (fuel : Nat) (q : AzRat) (x : AzFloat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  if q.sign = true ∧ q.num ≠ 0 then
    if q.num = q.den then gammaPrecRoundFuel fuel x p mode
    else
      match x with
      | nan => (nan, .eq)
      | infinity s => if s then (infinity true, .eq) else (nan, .eq)
      | x => qGammaOf (qBaseRat q) (qArgFloat x) fuel p mode
  else (nan, .eq)

/-- `Γ_q(x)` for a rational `q` and a float `x`, rounded to precision `p` with `mode`. -/
def qGammaRatFloatPrecRound (q : AzRat) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  qGammaRatFloatPrecRoundFuel (qGammaFuel (lt x zero) p) q x p mode

/-- `Γ_q(x)` for a rational `q` and a float `x`, rounded to nearest at precision `p`. -/
def qGammaRatFloat (q : AzRat) (x : AzFloat) (p : Nat) : AzFloat :=
  (qGammaRatFloatPrecRound q x p .Nearest).1

/-! ### A rational base and a rational argument -/

/-- **`Γ_q(x)` for rationals `q` and `x`**, with the fuel of the Ziv loop explicit.  The
specification is `qGammaRatPrecRoundFuel_zivSpec`. -/
def qGammaRatPrecRoundFuel (fuel : Nat) (q x : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if q.sign = true ∧ q.num ≠ 0 then
    if q.num = q.den then gammaRatPrecRoundFuel fuel x p mode
    else qGammaOf (qBaseRat q) (qArgRat x) fuel p mode
  else (nan, .eq)

/-- `Γ_q(x)` for rationals `q` and `x`, rounded to precision `p` with `mode`. -/
def qGammaRatPrecRound (q x : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  qGammaRatPrecRoundFuel (qGammaFuel (!x.sign) p) q x p mode

/-- `Γ_q(x)` for rationals `q` and `x`, rounded to nearest at precision `p`. -/
def qGammaRat (q x : AzRat) (p : Nat) : AzFloat := (qGammaRatPrecRound q x p .Nearest).1

end Azurite.AzFloat
