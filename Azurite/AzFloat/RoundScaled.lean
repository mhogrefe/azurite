/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Precision
import Azurite.AzInt.Parity
import Azurite.AzInt.ShiftRight
import Azurite.AzInt.ShiftRightRound
import Azurite.AzNat.Add
import Azurite.AzNat.ShiftRight

/-!
# Rounding primitives shared by the `AzFloat` operations

`roundScaled` rounds an exact integer times a power of two to `p` bits with
`AzInt.shiftRightRound` (the single rounding step of addition, subtraction and multiplication);
`normalizeCarry` folds a carry to `2^p` into the exponent; `roundFromFloor` rounds a real known
through its floor, its exactness and its position relative to the midpoint (division, square
root, reciprocal square root); `combinedPrecision` is the destination precision of the `+`, `*`
and `/` instances.  Correctness: `Equiv/RoundScaled.lean`.
-/

namespace Azurite.AzFloat

/-- Round the exact value `(−1)^(¬s) · S · 2^w` to precision `p`, with the comparison of the
result against it.  `S = 0` gives `zero`; a zero precision gives `NaN`. -/
def roundScaled (s : Bool) (S : AzNat) (w : AzInt) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if p = 0 then (nan, .eq)
  else if S = 0 then (zero, .eq)
  else
    let ex := w + (AzNat.ofNat S.size).toAzInt
    if S.size ≤ p then (mkFinite s ex p S, .eq)
    else
      let r := AzInt.shiftRightRound (AzInt.mkNorm s S) mode (S.size - p)
      let a := r.1.abs
      if a.size = p + 1 then (mkFinite r.1.sign (ex + 1) p (a.shiftRight 1), r.2)
      else (mkFinite r.1.sign ex p a, r.2)

/-- The precision for `+` and `−`: the larger of the operands' (`1` if neither has one). -/
def combinedPrecision (x y : AzFloat) : Nat :=
  max (x.precision?.getD 1) (y.precision?.getD 1)

/-- Normalize a signed integer `r` with `2^(p−1) ≤ |r| ≤ 2^p` into the precision-`p` float of
value `r · 2^(e − p)`: a carry to `2^p` is halved with the exponent raised. -/
def normalizeCarry (r : AzInt) (e : AzInt) (p : Nat) : AzFloat :=
  if r.abs.size = p + 1 then mkFinite r.sign (e + 1) p (r.abs.shiftRight 1)
  else mkFinite r.sign e p r.abs

/-- Round a real `y ∈ [s, s + 1)` to an integer, given its floor `s`, whether `y = s`, and the
comparison of `y` with the midpoint `s + 1/2`; the tag compares the result with `y`. -/
def roundFromFloor (s : AzNat) (exact : Bool) (cmpMid : Ordering) (mode : RoundingMode) :
    AzNat × Ordering :=
  if exact then (s, .eq) else
  match mode with
  | .Floor | .Down => (s, .lt)
  | .Ceiling | .Up => (s.addUInt64 1, .gt)
  | .Nearest =>
    match cmpMid with
    | .lt => (s, .lt)
    | .gt => (s.addUInt64 1, .gt)
    | .eq => if s.isOdd then (s.addUInt64 1, .gt) else (s, .lt)

end Azurite.AzFloat
