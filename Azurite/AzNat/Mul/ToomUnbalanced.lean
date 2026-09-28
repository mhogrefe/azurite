/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul.ToomCook4

/-!
# Unbalanced multiplication: Toom-(3,2), Toom-(4,2), and the chunk loop

When the operands have different lengths, padding the shorter one to the longer wastes a full
balanced multiplication at the larger size.  Toom-(r, s) cuts `A` into `r` blocks and `B` into
`s` blocks of a common size `k = max ⌈lenA/r⌉ ⌈lenB/s⌉` and needs `r + s − 1` pointwise
products of `k + 1` limbs, which go to the *balanced* multiplication (a `BalancedMul`, the
dispatcher's balanced ladder); there is no self-recursion.

* `toom32MulLimbs`: ratio near 3/2, four products at `0, 1, −1, ∞` (`toomInterp4`).
* `toom42MulLimbs`: ratio near 2, five products at `0, 1, −1, 2, ∞` (`toomInterp5`, the
  Toom-3 point set on a `4 × 2` block structure).
* `mulChunksLimbs`: for larger ratios, the longer operand in `lenB`-limb blocks each multiplied
  by the shorter one; the products are assembled without interpolation.

Correctness is in `Equiv/Mul/ToomUnbalanced.lean`.
-/

namespace Azurite.AzNat

/-- A balanced multiplier: two `n`-limb buffers to their `2n`-limb product. -/
abbrev BalancedMul :=
  (n : Nat) → (x y : Array UInt64) → 0 + n ≤ x.size → 0 + n ≤ y.size → Array UInt64

/-- Interpolation through `0, 1, −1, ∞` for a cubic `c_0 + c_1 x + c_2 x² + c_3 x³`. -/
def toomInterp4 (v0 v1 vm1 vinf : AzInt) : List AzInt :=
  let e := (v1 + vm1) >>> 1
  let o := (v1 - vm1) >>> 1
  [v0, o - vinf, e - v0, vinf]

/-- Interpolation through `0, 1, −1, 2, ∞` for a quartic (the Toom-3 formulas in `AzInt`):
`t_2 = (v_1 + v_{-1})/2`, `t_1 = (3v_0 + v_2 + 2v_{-1})/6 − 2v_∞`, and
`c = [v_0, v_1 − t_1, t_2 − v_0 − v_∞, t_1 − t_2, v_∞]`. -/
def toomInterp5 (v0 v1 vm1 v2 vinf : AzInt) : List AzInt :=
  let t2 := (v1 + vm1) >>> 1
  let t1 := AzInt.exactDivOdd 3 inv3 ((v0.mulUInt64 3 + v2 + vm1.mulUInt64 2) >>> 1)
    - (vinf <<< 1)
  [v0, v1 - t1, t2 - v0 - vinf, t1 - t2, vinf]

/-- **Toom-(3,2)**: `A` in three blocks, `B` in two. -/
def toom32MulLimbs (mulBal : BalancedMul) (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (_hA : loA + lenA ≤ a.size) (_hB : loB + lenB ≤ b.size) : Array UInt64 :=
  let k := max ((lenA + 2) / 3) ((lenB + 1) / 2)
  let bsA := blocks a loA lenA k 3
  let bsB := blocks b loB lenB k 2
  let mulK1 := mulBal (k + 1)
  let v0 := signedMulWith (k + 1) mulK1 (hornerInt64 0 bsA) (hornerInt64 0 bsB)
  let v1 := signedMulWith (k + 1) mulK1 (hornerInt64 1 bsA) (hornerInt64 1 bsB)
  let vm1 := signedMulWith (k + 1) mulK1 (hornerInt64 (-1) bsA) (hornerInt64 (-1) bsB)
  let vinf := signedMulWith (k + 1) mulK1 (hornerInt64 0 bsA.reverse) (hornerInt64 0 bsB.reverse)
  truncatePad (assemble k ((toomInterp4 v0 v1 vm1 vinf).map AzInt.abs)).limbs (lenA + lenB)

/-- **Toom-(4,2)**: `A` in four blocks, `B` in two. -/
def toom42MulLimbs (mulBal : BalancedMul) (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (_hA : loA + lenA ≤ a.size) (_hB : loB + lenB ≤ b.size) : Array UInt64 :=
  let k := max ((lenA + 3) / 4) ((lenB + 1) / 2)
  let bsA := blocks a loA lenA k 4
  let bsB := blocks b loB lenB k 2
  let mulK1 := mulBal (k + 1)
  let v0 := signedMulWith (k + 1) mulK1 (hornerInt64 0 bsA) (hornerInt64 0 bsB)
  let v1 := signedMulWith (k + 1) mulK1 (hornerInt64 1 bsA) (hornerInt64 1 bsB)
  let vm1 := signedMulWith (k + 1) mulK1 (hornerInt64 (-1) bsA) (hornerInt64 (-1) bsB)
  let v2 := signedMulWith (k + 1) mulK1 (hornerInt64 2 bsA) (hornerInt64 2 bsB)
  let vinf := signedMulWith (k + 1) mulK1 (hornerInt64 0 bsA.reverse) (hornerInt64 0 bsB.reverse)
  truncatePad (assemble k ((toomInterp5 v0 v1 vm1 v2 vinf).map AzInt.abs)).limbs (lenA + lenB)

/-- **The chunk loop**: `A` in `lenB`-limb blocks, each multiplied by `B` (balanced), then
assembled.  For ratios beyond the Toom variants. -/
def mulChunksLimbs (mulBal : BalancedMul) (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (_hA : loA + lenA ≤ a.size) (_hB : loB + lenB ≤ b.size) : Array UInt64 :=
  if lenB = 0 then Array.replicate (lenA + lenB) 0
  else
    let r := (lenA + lenB - 1) / lenB
    let bz := (ofLimbs (b.extract loB (loB + lenB))).toAzInt
    let prods := (blocks a loA lenA lenB r).map fun aj => signedMulWith lenB (mulBal lenB) aj bz
    truncatePad (assemble lenB (prods.map AzInt.abs)).limbs (lenA + lenB)

theorem toom32MulLimbs_size (mulBal : BalancedMul) (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) :
    (toom32MulLimbs mulBal a b loA lenA loB lenB hA hB).size = lenA + lenB := truncatePad_size _ _

theorem toom42MulLimbs_size (mulBal : BalancedMul) (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) :
    (toom42MulLimbs mulBal a b loA lenA loB lenB hA hB).size = lenA + lenB := truncatePad_size _ _

theorem mulChunksLimbs_size (mulBal : BalancedMul) (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) :
    (mulChunksLimbs mulBal a b loA lenA loB lenB hA hB).size = lenA + lenB := by
  unfold mulChunksLimbs
  split_ifs
  · exact Array.size_replicate
  · exact truncatePad_size _ _

end Azurite.AzNat
