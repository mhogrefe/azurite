/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul.ToomCook3
import Azurite.AzNat.ExactDivOdd
import Azurite.AzInt.MulSmall
import Azurite.AzInt.Sub
import Azurite.AzInt.ShiftLeft
import Azurite.AzInt.ShiftRight

/-!
# The signed evaluation framework for Toom–Cook multiplication

Shared pieces for the Toom–Cook variants of `docs/toom_cook_plan.md`.  An operand slice is cut
into `r` blocks of `k` limbs (the last one `m ≤ k` limbs), read as signed values, evaluated at
the interpolation points by Horner's rule, multiplied pointwise by the recursive multiplication,
interpolated in `AzInt`, and the nonnegative coefficients are assembled back into limbs.

* `blocks a lo k r m`: the `r` blocks as `AzInt`s (all nonnegative).
* `hornerInt64 c bs`: `Σ bs[i] · c^i` for a small signed `c`.  Evaluation at `±1` and `±2` is
  `hornerInt64 (±1) bs` and `hornerInt64 (±2) bs`; the scaled evaluation at `±1/2`,
  `Σ bs[i] · (±1)^i · 2^(r−1−i)`, is `hornerInt64 (±2) bs.reverse`.
* `signedMulWith n mulN u v`: the product of two signed values whose magnitudes fit in `n`
  limbs, with the magnitudes multiplied by `mulN` (the recursive Toom call on `n`-limb buffers);
  `signedSquareWith n sqN u` is the squaring analogue.
* `AzInt.exactDivOdd d dinv z`: exact division of a signed value by an odd limb.
* `assemble k cs`: `Σ cs[i] · β^(k·i)` for nonnegative coefficients, as an `AzNat`.

The correctness lemmas are in `Equiv/Mul/ToomEval.lean`; every variant's algebra is then a
polynomial identity over `ℤ` between `hornerInt64` values.
-/

namespace Azurite.AzNat

/-- The `j`-th block of the slice `a[lo, lo + len)` cut into `k`-limb blocks: `k` limbs from
`lo + j·k`, clipped at `lo + len`. -/
def block (a : Array UInt64) (lo len k j : Nat) : AzNat :=
  ofLimbs (a.extract (lo + j * k) (min (lo + (j + 1) * k) (lo + len)))

/-- The first `r` blocks of the slice, as nonnegative `AzInt`s (block `0` first). -/
def blocks (a : Array UInt64) (lo len k r : Nat) : List AzInt :=
  (List.range r).map fun j => (block a lo len k j).toAzInt

/-- `Σ bs[i] · c^i` by Horner's rule (`bs[0]` is the constant term). -/
def hornerInt64 (c : Int64) (bs : List AzInt) : AzInt :=
  bs.foldr (fun b acc => acc.mulInt64 c + b) 0

/-- Multiply two signed values whose magnitudes fit in `n` limbs.  `mulN` multiplies two
`n`-limb buffers (it is the recursive Toom–Cook call); the sign is the product of the signs. -/
def signedMulWith (n : Nat)
    (mulN : (x y : Array UInt64) → 0 + n ≤ x.size → 0 + n ≤ y.size → Array UInt64)
    (u v : AzInt) : AzInt :=
  AzInt.mkNorm (u.sign == v.sign) (ofLimbs (mulN (truncatePad u.abs.limbs n)
    (truncatePad v.abs.limbs n) (by rw [truncatePad_size]; omega) (by rw [truncatePad_size]; omega)))

/-- Square a signed value whose magnitude fits in `n` limbs, with `sqN` squaring `n`-limb
buffers (the recursive squaring call).  The result is nonnegative. -/
def signedSquareWith (n : Nat) (sqN : (x : Array UInt64) → 0 + n ≤ x.size → Array UInt64)
    (u : AzInt) : AzInt :=
  (ofLimbs (sqN (truncatePad u.abs.limbs n) (by rw [truncatePad_size]; omega))).toAzInt

/-- The `AzNat` magnitude of a nonnegative `AzInt` (the sign is dropped). -/
def toAzNatAbs (z : AzInt) : AzNat := z.abs

/-- `Σ cs[i] · 2^(64·k·i)`: assemble the coefficients of the product polynomial. -/
def assemble (k : Nat) (cs : List AzNat) : AzNat :=
  cs.foldr (fun c acc => c + (acc <<< (64 * k))) 0

end Azurite.AzNat

namespace Azurite.AzInt

/-- Exact division of a signed value by the odd limb `d` with inverse `dinv` (see
`AzNat.exactDivOdd`); only meaningful when `d` divides the value. -/
def exactDivOdd (d dinv : UInt64) (z : AzInt) : AzInt :=
  mkNorm z.sign (AzNat.exactDivOdd d dinv z.abs)

end Azurite.AzInt
