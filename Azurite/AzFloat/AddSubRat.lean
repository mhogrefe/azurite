/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Ziv
import Azurite.AzNat.Pow2
import Azurite.AzRat.Unary

/-!
# Addition and subtraction of an `AzFloat` and an `AzRat`

`x + q` for a float `x` and a rational `q`, correctly rounded to a destination precision `p`,
by Ziv's strategy (`Ziv.lean`).  The exact sum is a rational whose denominator is that of `q`;
computing it exactly means a shift of `q`'s numerator by the exponent gap and a division, which
is wasteful for a result of `p` bits and impossible when the exponent of `x` is huge.  Instead,
one approximation per working precision `w`:

1. `lo`, the truncation of `q` toward `−∞` to `w` bits (one division, the only expensive step),
   and `hi`, the next float up (`lo` plus its `truncError`; `hi = lo` when the truncation was
   exact), so that `lo ≤ q ≤ hi`;
2. the bracket `x + lo ≤ x + q ≤ x + hi`, whose ends are exact dyadic numbers that are not
   materialized but *rounded* on demand by `addPrecRound`, which is cheap in every regime
   (`Roundable`).

`roundingPossible` compares the `(p + 1)`-bit truncations of the two ends and, when they
agree, returns the rounding of `x + hi`.  The first working precision is `p + 64` bits, or the
bit length of `q`'s numerator when `q` is dyadic (then `lo = q` exactly — the exactness
pre-test of MCA §3.1.10).  The fuel `addRatFuel` is proven sufficient
(`Equiv/AddSubRat.lean`): from a working precision of about `p` plus the bit lengths of `q`'s
numerator, of `q`'s denominator twice and of `x`'s significand, plus the magnitude of `x`'s
exponent, rounding is always possible, because `x + q` is either a boundary itself — then `q`
is dyadic and the bracket is a point — or at a distance of at least `1/(den · 2^a)` from every
boundary, while the bracket's width `hi − lo` shrinks like `2^-w`.

`subRatPrecRound x q = addRatPrecRound x (−q)` and `ratSubPrecRound q x = addRatPrecRound
(−x) q`.  The `+` and `−` instances between an `AzFloat` and an `AzRat` round to nearest at the
float's precision (`1` for a special float, as `combinedPrecision` does for two floats; so
`zero + 1/3` is `1/4`).  `Equiv/AddSubRat.lean` proves that all three operations are the lifts
of `EReal` addition and subtraction with the value of `q`.
-/

namespace Azurite.AzFloat

/-- The first working precision for an operation with the rational `q` at destination precision
`p`: `p + zivGuardBits`, raised to the bit length of `q`'s numerator when `q` is dyadic, so
that `q` is represented exactly from the start. -/
def zivStart (q : AzRat) (p : Nat) : Nat :=
  if q.den.isPowerOfTwo then max (p + zivGuardBits) q.num.size else p + zivGuardBits

/-- The bracket of `x + q` at working precision `w`: `q` truncated to `w` bits and the next
float up, each added to `x`, given by their rounding procedures. -/
def addRatApprox (x : AzFloat) (q : AzRat) (w : Nat) : Roundable × Roundable :=
  let lo := ofAzRatRound q w .Floor
  let hi := (addPrecRound lo.1 (truncError lo) w .Ceiling).1
  (fun p mode => addPrecRound x lo.1 p mode, fun p mode => addPrecRound x hi p mode)

/-- The fuel of Ziv's loop for `x + q` at precision `p`: enough doublings to reach the working
precision `p + |num| + 2|den| + |m| + |e| + 2` (bit lengths of `q`'s numerator and denominator
and of `x`'s significand `m`, and the magnitude of `x`'s exponent `e`), from which rounding is
always possible (`addRatApprox_possible`). -/
def addRatFuel (x : AzFloat) (q : AzRat) (p : Nat) : Nat :=
  match x with
  | finite _ e _ m _ => zivFuel (p + q.num.size + 2 * q.den.size + m.size + 2) + e.abs.size + 1
  | _ => 0

/-- `x + q` rounded to precision `p` with `mode`, and the comparison with the exact sum. -/
def addRatPrecRound (x : AzFloat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => (infinity s, .eq)
  | zero => ofAzRatRound q p mode
  | finite .. => zivLoop (addRatApprox x q) p mode (addRatFuel x q p) (zivStart q p)

/-- `x − q` rounded to precision `p` with `mode`, and the comparison with the exact
difference. -/
def subRatPrecRound (x : AzFloat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  addRatPrecRound x (-q) p mode

/-- `q − x` rounded to precision `p` with `mode`, and the comparison with the exact
difference. -/
def ratSubPrecRound (q : AzRat) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  addRatPrecRound (-x) q p mode

/-- The precision of a mixed operation: the float's, `1` for a special float. -/
def ratOpPrecision (x : AzFloat) : Nat := x.precision?.getD 1

instance : HAdd AzFloat AzRat AzFloat :=
  ⟨fun x q => (addRatPrecRound x q (ratOpPrecision x) .Nearest).1⟩

instance : HAdd AzRat AzFloat AzFloat :=
  ⟨fun q x => (addRatPrecRound x q (ratOpPrecision x) .Nearest).1⟩

instance : HSub AzFloat AzRat AzFloat :=
  ⟨fun x q => (subRatPrecRound x q (ratOpPrecision x) .Nearest).1⟩

instance : HSub AzRat AzFloat AzFloat :=
  ⟨fun q x => (ratSubPrecRound q x (ratOpPrecision x) .Nearest).1⟩

end Azurite.AzFloat
