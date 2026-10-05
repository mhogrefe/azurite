/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Ziv
import Azurite.AzNat.Pow2
import Azurite.AzRat.Add
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
3. the error bound `ε`, the sum of the two truncation errors (one ulp each, `truncError`),
   rounded up to two bits.

Then `y ≤ x + q ≤ y + ε`, and `roundingPossible` decides from the two cheap roundings of `y`
and `y + ε` whether the result is determined.  The first working precision is `p + 64` bits,
or the bit length of `q`'s numerator when `q` is dyadic (then `lo = q` exactly and the first
attempt succeeds whenever `x + q` fits in `w + 2` bits — the exactness pre-test of MCA
§3.1.10); the fallback after `zivFuel` doublings computes the exact rational sum.

`subRatPrecRound x q = addRatPrecRound x (−q)` and `ratSubPrecRound q x = addRatPrecRound
(−x) q`.  The `+` and `−` instances between an `AzFloat` and an `AzRat` round to nearest at the
float's precision (`1` for a special float, as `combinedPrecision` does for two floats; so
`zero + 1/3` is `1/4`).  `Equiv/AddRat.lean` proves that all three operations are the lifts of
`EReal` addition and subtraction with the value of `q`.
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
  let lo := (ofAzRatRound q w .Floor).1
  let y := (addPrecRound x lo (w + 2) .Floor).1
  (y, (addPrecRound (truncError lo) (truncError y) 2 .Ceiling).1)

/-- The exact fallback: the rational sum, rounded. -/
def addRatExact (x : AzFloat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x.toAzRat? with
  | some r => ofAzRatRound (r + q) p mode
  | none => (nan, .eq)

/-- `x + q` rounded to precision `p` with `mode`, and the comparison with the exact sum. -/
def addRatPrecRound (x : AzFloat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => (infinity s, .eq)
  | zero => ofAzRatRound q p mode
  | finite .. =>
    zivLoop (addRatApprox x q) (fun _ => addRatExact x q p mode) p mode
      (zivFuel p (q.num.size + q.den.size)) (zivStart q p)

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
