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

1. `lo`, the truncation of `q` toward `−∞` to `w` bits (one division, the only expensive step);
2. `y`, the truncation of the exact dyadic sum `x + lo` toward `−∞` to `w + 2` bits;
3. the error bound `ε`, the sum of the two truncation errors (one ulp each, or `0` for an exact
   truncation, `truncError`), rounded up to two bits.

Then `y ≤ x + q ≤ y + ε`, with `ε = 0` when `y = x + q`, and `roundingPossible` decides from
the `(p + 1)`-bit truncation of `y + ε` whether the result is determined.  The first working
precision is `p + 64` bits, or the bit length of `q`'s numerator when `q` is dyadic (then
`lo = q` exactly — the exactness pre-test of MCA §3.1.10).  The fuel `addRatFuel` is proven
sufficient (`Equiv/AddSubRat.lean`): from a working precision of about `p` plus the bit
lengths of `q`'s numerator, of `q`'s denominator twice and of `x`'s significand, plus twice
the magnitude of `x`'s exponent, rounding is always possible, because `x + q` is either a
boundary itself — then `q` is dyadic and both truncations are exact — or at a distance of at
least `1/(den · 2^a)` from every boundary, while the error bound shrinks like `2^-w`.

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

/-- One approximation of `x + q` at working precision `w`: `q` truncated to `w` bits, added to
`x` and truncated to `w + 2` bits, with the sum of the two truncation errors as the bound. -/
def addRatApprox (x : AzFloat) (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  let lo := ofAzRatRound q w .Floor
  let y := addPrecRound x lo.1 (w + 2) .Floor
  (y.1, (addPrecRound (truncError lo) (truncError y) 2 .Ceiling).1)

/-- The fuel of Ziv's loop for `x + q` at precision `p`: enough doublings to reach the working
precision `p + |num| + 2|den| + |m| + 2|e| + 4` (bit lengths of `q`'s numerator and
denominator and of `x`'s significand `m`, and the magnitude of `x`'s exponent `e`), from which
rounding is always possible (`addRatApprox_possible`). -/
def addRatFuel (x : AzFloat) (q : AzRat) (p : Nat) : Nat :=
  match x with
  | finite _ e _ m _ => (p + q.num.size + 2 * q.den.size + m.size + 4).log2 + e.abs.size + 3
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
