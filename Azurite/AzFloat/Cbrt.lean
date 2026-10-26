/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Sqrt
import Azurite.AzInt.DivMod
import Azurite.AzNat.Pow
import Azurite.AzNat.RootInt

/-!
# Cube root

The cube-root analogue of `sqrtCore` (MCA §3.5, Algorithm FPSqrt): for `x = n · 2^(e − q)`
with core `n` of `q` bits, write `e − q = t + 3w` with `t = 3p − q − δ`, `δ = (−e) mod 3`, so
that `M = n · 2^t ∈ [2^(3p−3), 2^(3p))` and `∛x = ∛M · 2^w` with `∛M ∈ [2^(p−1), 2^p)`.  The
integer cube root `c = ⌊∛⌊M⌋⌋` (`AzNat.rootInt`) has `p` bits; `∛M` is exactly `c` iff
`c³ = ⌊M⌋` and no bits of `n` were shifted out, and its position relative to the midpoint
`c + 1/2` is the exact integer comparison of `8M = n · 2^(t+3)` with `(2c + 1)³`.  Those three
facts determine the rounding in every mode (`roundFromFloor`), and a carry to `2^p` is
normalized as for the square root.  A negative `x` is handled by symmetry: `∛(−x) = −∛x`, with
the rounding mode negated (`RoundingMode.neg`) and the comparison swapped.
Correctness: `Equiv/Cbrt.lean` (`cbrtPrecRound_eq_liftVal`).
-/

namespace Azurite.AzFloat

/-- The rounded cube root of `n · 2^(e − q)` (core `n` of `q` bits) to precision `p`. -/
def cbrtCore (e : AzInt) (n : AzNat) (q : Nat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  let three : AzInt := (AzNat.ofNat 3).toAzInt
  let δ : Nat := ((-e) % three).abs.toNat
  let t : AzInt := (AzNat.ofNat (3 * p)).toAzInt - (AzNat.ofNat (q + δ)).toAzInt
  let M := if t.sign then n.shiftLeft t.abs.toNat else n.shiftRight t.abs.toNat
  let c := AzNat.rootInt M 3
  let exact := decide (c.pow 3 = M) && (t.sign || n.isMultipleOfPow2 t.abs.toNat)
  let cmpMid := compareScaled n (t + three) (((c.shiftLeft 1).addUInt64 1).pow 3)
  let ro := roundFromFloor c exact cmpMid mode
  let w := (e - (AzNat.ofNat (3 * p)).toAzInt + (AzNat.ofNat δ).toAzInt) / three
  (normalizeCarry (AzInt.mkNorm true ro.1) (w + (AzNat.ofNat p).toAzInt) p, ro.2)

/-- `∛x` rounded to precision `p` with `mode`, and the comparison with the exact root; the
infinities and zero are their own cube roots. -/
def cbrtPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => (infinity s, .eq)
  | zero => (zero, .eq)
  | finite s e q m _ =>
    if p = 0 then (nan, .eq)
    else if s then cbrtCore e (coreSignificand q m) q p mode
    else
      let r := cbrtCore e (coreSignificand q m) q p (-mode)
      (-r.1, r.2.swap)

/-- `∛x` rounded to nearest at the precision of `x`. -/
def cbrt (x : AzFloat) : AzFloat := (cbrtPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
