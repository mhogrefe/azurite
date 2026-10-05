/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AddSubRat
import Azurite.AzFloat.Mul
import Azurite.AzNat.Div
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.TrailingZeros

/-!
# Multiplication of an `AzFloat` by an `AzRat`

`x · q` for a float `x` and a rational `q`, correctly rounded to a destination precision `p`,
by Ziv's strategy (`Ziv.lean`), with the same bracket as the addition: `lo ≤ q ≤ hi` with `lo`
the `w`-bit truncation of `q` (the only division) and `hi` the next float up, so that `x · q`
lies between `x · lo` and `x · hi` — in that order for `x > 0`, reversed for `x < 0` — and the
two ends are rounded on demand by `mulPrecRound` (`Roundable`).

Unlike a sum, a product can be a boundary of the rounding (hence hopeless for the bracket, which
always straddles it) without `q` being dyadic: `3 · (1/3) = 1`.  The exact product
`± m · num · 2^(e − |m|) / den` is dyadic exactly when the odd part of `den` divides the
significand `m`; this is tested first (`oddDen`, one small `divMod`, whose quotient the exact
path then uses), and then the product is built exactly and re-rounded (MCA §3.1.10's exactness
pre-test).  Otherwise the product is not
dyadic, so not a boundary, and `mulRatFuel` is proven sufficient (`Equiv/MulRat.lean`): from
the working precision `p + |num| + 2|den| + |m| + 2|e| + 2` on, rounding is always possible.

The `*` instances between an `AzFloat` and an `AzRat` round to nearest at the float's precision
(`ratOpPrecision`).  `Equiv/MulRat.lean` proves `mulRatPrecRound x q p mode = liftVal (fun a =>
Spec.mul a q) x p mode`.
-/

namespace Azurite.AzFloat

/-- The bracket of `x · q` at working precision `w`: `x` times the `w`-bit truncation of `q` and
`x` times the next float up, in increasing order, given by their rounding procedures. -/
def mulRatApprox (x : AzFloat) (q : AzRat) (w : Nat) : Roundable × Roundable :=
  let lo := ofAzRatRound q w .Floor
  let hi := (addPrecRound lo.1 (truncError lo) w .Ceiling).1
  if x.isNegative then
    (fun p mode => mulPrecRound x hi p mode, fun p mode => mulPrecRound x lo.1 p mode)
  else
    (fun p mode => mulPrecRound x lo.1 p mode, fun p mode => mulPrecRound x hi p mode)

/-- The number of trailing zero bits of the denominator of `q`. -/
def denTrailingZeros (q : AzRat) : Nat := q.den.trailingZeros.getD 0

/-- The odd part of the denominator of `q`. -/
def oddDen (q : AzRat) : AzNat := q.den >>> denTrailingZeros q

/-- The fuel of Ziv's loop for `x · q` at precision `p`: enough doublings to reach the working
precision `p + |num| + 2|den| + |m| + 2|e| + 2`, from which rounding is always possible when
the product is not dyadic (`mulRatApprox_possible`). -/
def mulRatFuel (x : AzFloat) (q : AzRat) (p : Nat) : Nat :=
  match x with
  | finite _ e _ m _ => zivFuel (p + q.num.size + 2 * q.den.size + m.size + 2) + e.abs.size + 2
  | _ => 0

/-- The exact product `± c₀ · num · 2^(e − |m| − t)` of a finite `x` and `q`, where
`c₀ = m / oddDen q` is the quotient of the significand by the odd part of the denominator (which
divides it), re-rounded to `p`. -/
def mulRatExact (s : Bool) (e : AzInt) (m c₀ : AzNat) (q : AzRat) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  let c := c₀ * q.num
  setPrecRound
    (mkFinite (s == q.sign)
      (e - (AzNat.ofNat (m.size + denTrailingZeros q)).toAzInt + (AzNat.ofNat c.size).toAzInt)
      c.size c)
    p mode

/-- `x · q` rounded to precision `p` with `mode`, and the comparison with the exact product. -/
def mulRatPrecRound (x : AzFloat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if q.num = 0 then (nan, .eq) else (infinity (s == q.sign), .eq)
  | zero => (zero, .eq)
  | finite s e _ m _ =>
    if q.num = 0 then (zero, .eq)
    else
      let qr := m.divMod (oddDen q)
      if qr.2 = 0 then mulRatExact s e m qr.1 q p mode
      else zivLoop (mulRatApprox x q) p mode (mulRatFuel x q p) (zivStart q p)

instance : HMul AzFloat AzRat AzFloat :=
  ⟨fun x q => (mulRatPrecRound x q (ratOpPrecision x) .Nearest).1⟩

instance : HMul AzRat AzFloat AzFloat :=
  ⟨fun q x => (mulRatPrecRound x q (ratOpPrecision x) .Nearest).1⟩

end Azurite.AzFloat
