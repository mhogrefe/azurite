/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.RoundScaled
import Azurite.AzNat.Div
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.SqrtRem
import Azurite.AzNat.Square

/-!
# Reciprocal square root

MCA §3.5.1 gives a Newton iteration for `a^(−1/2)` with a rigorous error bound (Algorithm 3.9,
Lemma 3.15), an approximation that would need a correction step to round correctly.  The
correctly rounded primitive instead reuses the square-root method: for `x = n · 2^(e − q)` with
core `n` of `q` bits, `1/√x = √(2^D / n) · 2^w` with `D + 2w = q − e`, and the scaling `D` is chosen
so that `√(2^D / n)` has exactly `p` bits — `D = 2p + q − 2` for even `e`, `2p + q − 1` for odd `e`,
and `2p + q − 3` when `e` is odd and `n = 2^(q−1)`, where `x` is an even power of two and the
result's exponent is one higher.  Then `s = ⌊√⌊2^D / n⌋⌋ = ⌊√(2^D / n)⌋`, exactness is
`s² · n = 2^D`, the midpoint test is `2^(D+2) ⋚ (2s + 1)² · n`, and `roundFromFloor` finishes.

Correctness: `Equiv/Rsqrt.lean` (`rsqrtPrecRound_eq_liftVal`).
-/

namespace Azurite.AzFloat

/-- The rounded reciprocal square root of `n · 2^(e − q)` (core `n` of `q` bits) to precision
`p`. -/
def rsqrtCore (e : AzInt) (n : AzNat) (q : Nat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  let odd := e.isOdd
  let bnd := odd && decide (n = (1 : AzNat).shiftLeft (q - 1))
  let D : Nat := if odd then (if bnd then 2 * p + q - 3 else 2 * p + q - 1) else 2 * p + q - 2
  let f : AzInt := (if !odd || bnd then (1 : AzInt) else 0) - e.shiftRight 1
  let w := f - (AzNat.ofNat p).toAzInt
  let pow := (1 : AzNat).shiftLeft D
  let sr := AzNat.sqrtRem (pow / n)
  let exact := compare (AzNat.square sr.1 * n) pow == .eq
  let cmpMid := compare ((1 : AzNat).shiftLeft (D + 2))
    (AzNat.square ((sr.1.shiftLeft 1).addUInt64 1) * n)
  let ro := roundFromFloor sr.1 exact cmpMid mode
  (normalizeCarry (AzInt.mkNorm true ro.1) (w + (AzNat.ofNat p).toAzInt) p, ro.2)

/-- `1/√x` rounded to precision `p` with `mode`, and the comparison with the exact value;
negative inputs (including `−∞`) give `NaN`, `0` gives `+∞`, `+∞` gives `0`. -/
def rsqrtPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (zero, .eq) else (nan, .eq)
  | zero => (infinity true, .eq)
  | finite s e q m _ => if s then rsqrtCore e (coreSignificand q m) q p mode else (nan, .eq)

/-- `1/√x` rounded to nearest at the precision of `x`. -/
def rsqrt (x : AzFloat) : AzFloat := (rsqrtPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
