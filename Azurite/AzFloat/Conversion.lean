/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Basic
import Azurite.AzInt.Conversion
import Azurite.AzInt.Equiv.Basic
import Azurite.AzInt.Sub
import Azurite.AzNat.ShiftRight
import Azurite.AzRat.Conversion
import Azurite.AzRat.LogBase
import Azurite.AzRat.Shift
import Azurite.AzRat.ToSci

/-!
# Conversions between `AzFloat` and the exact types

* `ofAzNat` / `ofAzInt`: exact, at the precision of the input's bit length (`0 ↦ zero`).
* `ofAzRatRound q p mode`: `q` rounded to precision `p` with the given mode, together with the
  `Ordering` of the result against `q`; `ofAzRat` rounds to nearest.  Derived from first
  principles: with `e = ⌊log₂ |q|⌋` the `p`-bit significand is the rounding of `q · 2^(p−1−e)`
  to an integer (one signed division, `AzRat.scaledRound`); when that rounds up to `2^p` the
  significand is halved and the exponent raised (`Equiv/Conversion.lean` proves the result
  is `round (precisionSet 2 p) mode q`).
* `toAzRat?`: the exact rational value of a finite value, `none` for `NaN` and `±∞`.
-/

namespace Azurite.AzFloat

/-- A natural number as a float, exactly, at the precision of its bit length. -/
def ofAzNat (n : AzNat) : AzFloat :=
  mkFinite true (AzNat.ofNat n.size).toAzInt n.size n

/-- An integer as a float, exactly, at the precision of its bit length. -/
def ofAzInt (z : AzInt) : AzFloat :=
  mkFinite z.sign (AzNat.ofNat z.abs.size).toAzInt z.abs.size z.abs

/-- `q` rounded to precision `p` with mode `mode`, and how the result compares with `q`.
A zero precision gives `NaN`. -/
def ofAzRatRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if p = 0 then (nan, .eq)
  else if q.num = 0 then (zero, .eq)
  else
    let e := AzRat.floorLogBaseAbs 2 q
    let r := AzRat.scaledRound q 2 ((p : ℤ) - 1 - e) mode
    let n := r.1.abs
    if n.size = p + 1 then
      -- rounded up to `2^p`: one bit too many
      (mkFinite r.1.sign (AzInt.ofInt (e + 2)) p (n.shiftRight 1), r.2)
    else
      (mkFinite r.1.sign (AzInt.ofInt (e + 1)) p n, r.2)

/-- `q` rounded to nearest at precision `p`. -/
def ofAzRat (q : AzRat) (p : Nat) : AzFloat := (ofAzRatRound q p .Nearest).1

/-- The exact value of a finite float as a rational (`none` for `NaN` and `±∞`).  The shift
count is the exponent's magnitude as a `Nat`, so this is only usable when the exponent is
small enough for the result to be materialized. -/
def toAzRat? : AzFloat → Option AzRat
  | zero => some 0
  | finite s e _ m _ =>
    let d := e - (AzNat.ofNat m.size).toAzInt
    let base := (AzInt.mkNorm s m).toAzRat
    some (if d.sign then base <<< d.abs.toNat else base >>> d.abs.toNat)
  | _ => none

end Azurite.AzFloat
