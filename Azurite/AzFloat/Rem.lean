/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Precision
import Azurite.AzFloat.Sum
import Azurite.AzNat.Div
import Azurite.AzNat.Equiv.Basic
import Azurite.AzZMod.Pow

/-!
# Remainder

`remPrecRound x y p mode` is the remainder of `x` by `y` with the quotient rounded toward zero
(`%` on primitive floats, C's `fmod`): `x − y · trunc (x / y)`, rounded to precision `p` with
`mode`, with the comparison against the exact remainder.  The exact remainder of two floats is
itself a float (a multiple of the smaller of the two ulps, below `|y|`), so it is formed exactly
(`remExact`) and rounded once.

Special values: `NaN` for a `NaN`, an infinite `x`, or a zero `y`; `x` for an infinite `y`;
zero for a zero `x`.  An exact zero remainder is `zero` (`AzFloat` has a single zero; the sign
of `x` is not carried).  `x % y` is the remainder to nearest at the larger of the precisions.

Writing `|x| = X · 2^a` and `|y| = Y · 2^b` with integer significands: if `|x| < |y|` the
remainder is `x`; otherwise the two are brought to the smaller exponent and the remainder is
`sign x · (X' mod Y') · 2^min(a,b)`.  When `b ≤ a` the shifted significand `X · 2^(a−b)` is
not formed: `(X · 2^k) mod Y = ((X mod Y)(2^k mod Y)) mod Y` with `2^k mod Y` by modular
exponentiation (`shiftLeftMod`), so a huge exponent gap costs `O(log k)` multiplications.  When
`a < b`, `|y| ≤ |x|` bounds the shift of `Y` by the size of `X`.
-/

namespace Azurite

/-- `(a · 2^k) mod n` without forming the shift (for `n = 0` the shift itself). -/
def AzNat.shiftLeftMod (a : AzNat) (k : Nat) (n : AzNat) : AzNat :=
  if h : n = 0 then a <<< k
  else
    haveI : NeZero n.toNat := ⟨fun h0 => h (AzNat.toNat_injective (by rw [h0]; rfl))⟩
    (AzZMod.ofAzNat n a * AzZMod.pow (AzZMod.ofAzNat n (AzNat.ofNat 2)) k).val

namespace AzFloat

/-- The exact remainder `x − y · trunc (x / y)` (`NaN` for a `NaN`, an infinite `x`, or a zero
`y`; `x` for an infinite `y`; zero for a zero `x`). -/
def remExact (x y : AzFloat) : AzFloat :=
  match x, y with
  | nan, _ => nan
  | _, nan => nan
  | infinity _, _ => nan
  | _, zero => nan
  | _, infinity _ => x
  | zero, _ => zero
  | finite sx ex _ mx _, finite _ ey _ my _ =>
    if absLt x y.abs then x
    else
      let ax := ex - (AzNat.ofNat mx.size).toAzInt
      let ay := ey - (AzNat.ofNat my.size).toAzInt
      if ay ≤ ax then
        let r := mx.shiftLeftMod (ax - ay).abs.toNat my
        mkFinite sx (ay + (AzNat.ofNat r.size).toAzInt) r.size r
      else
        let r := mx % (my <<< (ay - ax).abs.toNat)
        mkFinite sx (ax + (AzNat.ofNat r.size).toAzInt) r.size r

/-- The remainder `x − y · trunc (x / y)` rounded to precision `p` with `mode`, with the
comparison against the exact remainder. -/
def remPrecRound (x y : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  setPrecRound (remExact x y) p mode

instance : Mod AzFloat := ⟨fun x y => (remPrecRound x y (combinedPrecision x y) .Nearest).1⟩

end AzFloat

end Azurite
