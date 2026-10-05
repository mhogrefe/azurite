/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.RoundScaled
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.SqrtRem
import Azurite.AzNat.Square

/-!
# Square root

MCA §3.5, Algorithm FPSqrt, extended to round-to-nearest (Exercise 3.14): for `x = n · 2^(e − q)`
with core `n` of `q` bits, write `e − q = t + 2w` with `t = 2p − q − δ`, `δ = e mod 2`, so that
`M = n · 2^t ∈ [2^(2p−2), 2^(2p))` and `√x = √M · 2^w` with `√M ∈ [2^(p−1), 2^p)`.  The integer
square root `s = ⌊√⌊M⌋⌋` has `p` bits; `√M` is exactly `s` iff the remainder vanishes and no bits
of `n` were shifted out, and its position relative to the midpoint `s + 1/2` is the exact integer
comparison of `4M = n · 2^(t+2)` with `(2s + 1)²`.  Those three facts determine the rounding in
every mode (`roundFromFloor`), and a carry to `2^p` is normalized as for division.

Correctness: `Equiv/Sqrt.lean` (`sqrtPrecRound_eq_liftVal`).
-/

namespace Azurite.AzFloat

/-- Compare `n · 2^t` with `c` exactly (`t` may be negative). -/
def compareScaled (n : AzNat) (t : AzInt) (c : AzNat) : Ordering :=
  if t.sign then compare (n.shiftLeft t.abs.toNat) c else compare n (c.shiftLeft t.abs.toNat)

/-- The rounded square root of `n · 2^(e − q)` (core `n` of `q` bits) to precision `p`. -/
def sqrtCore (e : AzInt) (n : AzNat) (q : Nat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  let δ : Nat := if e.isOdd then 1 else 0
  let t : AzInt := (AzNat.ofNat (2 * p)).toAzInt - (AzNat.ofNat (q + δ)).toAzInt
  let M := if t.sign then n.shiftLeft t.abs.toNat else n.shiftRight t.abs.toNat
  let sr := AzNat.sqrtRem M
  let exact := decide (sr.2 = 0) && (t.sign || n.isMultipleOfPow2 t.abs.toNat)
  let cmpMid := compareScaled n (t + (AzNat.ofNat 2).toAzInt)
    (AzNat.square ((sr.1.shiftLeft 1).addUInt64 1))
  let ro := roundFromFloor sr.1 exact cmpMid mode
  let w := (e - (AzNat.ofNat (2 * p)).toAzInt + (AzNat.ofNat δ).toAzInt).shiftRight 1
  (normalizeCarry (AzInt.mkNorm true ro.1) (w + (AzNat.ofNat p).toAzInt) p, ro.2)

/-- `√x` rounded to precision `p` with `mode`, and the comparison with the exact root; negative
inputs (including `−∞`) give `NaN`. -/
def sqrtPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (nan, .eq)
  | zero => (zero, .eq)
  | finite s e q m _ => if s then sqrtCore e (coreSignificand q m) q p mode else (nan, .eq)

/-- `√x` rounded to nearest at the precision of `x`. -/
def sqrt (x : AzFloat) : AzFloat := (sqrtPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
