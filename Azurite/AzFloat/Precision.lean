/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Basic
import Azurite.AzInt.Conversion
import Azurite.AzInt.Equiv.Basic
import Azurite.AzInt.ShiftRightRound
import Azurite.AzInt.Sub
import Azurite.AzNat.ShiftRight

/-!
# Changing the precision of an `AzFloat`

* `setPrecRound x p mode`: `x` rounded to precision `p` with `mode`, with the `Ordering` of the
  result against `x`.  Raising the precision is exact (the significand is re-aligned);
  lowering it rounds the `q`-bit significand to `p` bits with `AzInt.shiftRightRound` (one
  signed shift), a carry to `2^p` being halved with the exponent raised.  First principles;
  `Equiv/Precision.lean` proves it is the lift of the identity (`setPrecRound_eq_liftE`).
* `setPrec`: to nearest.
* `ulp?`: the unit in the last place `2^(exponent − precision)` of a finite nonzero value, as a
  float of precision `1`.
-/

namespace Azurite.AzFloat

/-- The significand without its alignment padding: exactly `precision` bits. -/
def coreSignificand (q : Nat) (m : AzNat) : AzNat := m.shiftRight (alignedBits q - q)

/-- `x` rounded to precision `p` with `mode`, and how the result compares with `x`.  A zero
precision gives `NaN`; the special values are returned unchanged. -/
def setPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if p = 0 then (nan, .eq)
  else
    match x with
    | finite s e q m _ =>
      let n := coreSignificand q m
      if q ≤ p then (mkFinite s e p n, .eq)
      else
        let r := AzInt.shiftRightRound (AzInt.mkNorm s n) mode (q - p)
        let a := r.1.abs
        if a.size = p + 1 then
          -- rounded up to `2^p`: one bit too many
          (mkFinite r.1.sign (e + 1) p (a.shiftRight 1), r.2)
        else (mkFinite r.1.sign e p a, r.2)
    | x => (x, .eq)

/-- `x` rounded to nearest at precision `p`. -/
def setPrec (x : AzFloat) (p : Nat) : AzFloat := (setPrecRound x p .Nearest).1

/-- The unit in the last place of a finite nonzero value, `2^(exponent − precision)` at
precision `1`; `none` otherwise. -/
def ulp? : AzFloat → Option AzFloat
  | finite _ e p _ _ => some (powerOf2 (e - (AzNat.ofNat p).toAzInt))
  | _ => none

end Azurite.AzFloat
