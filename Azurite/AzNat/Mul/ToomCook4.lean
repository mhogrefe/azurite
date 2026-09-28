/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul.ToomEval

/-!
# Toom–Cook 4-way multiplication for AzNat

For `A, B < β^n` with `β = 2^64` and `k = ⌈n/4⌉`, split each operand into four `k`-limb blocks
(the framework of `Mul/ToomEval.lean`; the last block is shorter) and reduce one `n`-limb product
to **seven** products of `k + 1` limbs, at the points `0, 1, −1, 2, −2, 1/2, ∞` of Bodrato and
Zanoni.  Asymptotically `Θ(n^{log_4 7}) ≈ Θ(n^{1.404})`.

Writing `C = A·B = Σ c_i x^i` (degree 6) in the block base, the point values are

  v_0 = c_0,   v_∞ = c_6,
  v_1  = c_0 + c_1 + c_2 + c_3 + c_4 + c_5 + c_6,        v_{-1} with alternating signs,
  v_2  = c_0 + 2c_1 + 4c_2 + 8c_3 + 16c_4 + 32c_5 + 64c_6,  v_{-2} with alternating signs,
  v_h  = 64 C(1/2) = 64c_0 + 32c_1 + 16c_2 + 8c_3 + 4c_4 + 2c_5 + c_6,

and the interpolation (`toomCook4Interpolate`, all divisions exact) is

  e_1 = (v_1 + v_{-1})/2 − v_0 − v_∞ = c_2 + c_4          o_1 = (v_1 − v_{-1})/2 = c_1 + c_3 + c_5
  e_2 = (v_2 + v_{-2})/2 − v_0 − 64 v_∞ = 4c_2 + 16c_4    o_2 = (v_2 − v_{-2})/4 = c_1 + 4c_3 + 16c_5
  c_4 = (e_2 − 4 e_1)/12,   c_2 = e_1 − c_4
  h   = (v_h − 64 v_0 − v_∞ − 16 c_2 − 4 c_4)/2 = 16c_1 + 4c_3 + c_5
  c_3 = (17 o_1 − o_2 − h)/9,   c_5 = ((o_2 − o_1)/3 − c_3)/5,   c_1 = ((h − o_1)/3 − c_3)/5.

Every intermediate is a signed `AzInt`; the seven products are formed by `signedMulWith` with
the recursive call as the magnitude multiplier.  Correctness is `toomCook4MulLimbs_toNat` in
`Equiv/Mul/ToomCook4.lean`.
-/

namespace Azurite.AzNat

/-- The Toom-4 interpolation: the coefficients `[c_0, …, c_6]` from the seven point values. -/
def toomCook4Interpolate (v0 v1 vm1 v2 vm2 vh vinf : AzInt) : List AzInt :=
  let e1 := ((v1 + vm1) >>> 1) - v0 - vinf
  let o1 := (v1 - vm1) >>> 1
  let e2 := ((v2 + vm2) >>> 1) - v0 - (vinf <<< 6)
  let o2 := (v2 - vm2) >>> 2
  let c4 := AzInt.exactDivOdd 3 inv3 ((e2 - (e1 <<< 2)) >>> 2)
  let c2 := e1 - c4
  let h := (vh - (v0 <<< 6) - vinf - (c2 <<< 4) - (c4 <<< 2)) >>> 1
  let c3 := AzInt.exactDivOdd 9 inv9 (o1.mulUInt64 17 - o2 - h)
  let c5 := AzInt.exactDivOdd 5 inv5 (AzInt.exactDivOdd 3 inv3 (o2 - o1) - c3)
  let c1 := AzInt.exactDivOdd 5 inv5 (AzInt.exactDivOdd 3 inv3 (h - o1) - c3)
  [v0, c1, c2, c3, c4, c5, vinf]

/-- Recursive Toom-4 multiplication of two equal-length slices.  Falls back to Toom-3 (which
falls back to Karatsuba, then schoolbook) when `len < toom4Threshold`. -/
def toomCook4MulLimbsRec (toom4Threshold toom3Threshold karaThreshold : Nat)
    (a b : Array UInt64) (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    { c : Array UInt64 // c.size = 2 * len } :=
  if h_base : len < toom4Threshold ∨ len < 4 then
    ⟨toomCook3MulLimbs toom3Threshold karaThreshold a b loA loB len hA hB, by
      rw [toomCook3MulLimbs_size]⟩
  else
    have hlen : 4 ≤ len := by omega
    let k := (len + 3) / 4
    have hk1_lt : k + 1 < len := by show (len + 3) / 4 + 1 < len; omega
    -- the recursive call on `(k + 1)`-limb buffers
    let mulK1 : (x y : Array UInt64) → 0 + (k + 1) ≤ x.size → 0 + (k + 1) ≤ y.size →
        Array UInt64 := fun x y hx hy =>
      (toomCook4MulLimbsRec toom4Threshold toom3Threshold karaThreshold x y 0 0 (k + 1) hx hy).1
    let bsA := blocks a loA len k 4
    let bsB := blocks b loB len k 4
    -- the seven evaluations of each operand
    let v0 := signedMulWith (k + 1) mulK1 (hornerInt64 0 bsA) (hornerInt64 0 bsB)
    let v1 := signedMulWith (k + 1) mulK1 (hornerInt64 1 bsA) (hornerInt64 1 bsB)
    let vm1 := signedMulWith (k + 1) mulK1 (hornerInt64 (-1) bsA) (hornerInt64 (-1) bsB)
    let v2 := signedMulWith (k + 1) mulK1 (hornerInt64 2 bsA) (hornerInt64 2 bsB)
    let vm2 := signedMulWith (k + 1) mulK1 (hornerInt64 (-2) bsA) (hornerInt64 (-2) bsB)
    let vh := signedMulWith (k + 1) mulK1 (hornerInt64 2 bsA.reverse) (hornerInt64 2 bsB.reverse)
    let vinf := signedMulWith (k + 1) mulK1 (hornerInt64 0 bsA.reverse) (hornerInt64 0 bsB.reverse)
    let cs := toomCook4Interpolate v0 v1 vm1 v2 vm2 vh vinf
    let result := assemble k (cs.map AzInt.abs)
    ⟨truncatePad result.limbs (2 * len), truncatePad_size _ _⟩
  termination_by len
  decreasing_by
    all_goals omega

/-- Toom-4 multiplication of two equal-length slices, in `2 · len` limbs. -/
def toomCook4MulLimbs (toom4Threshold toom3Threshold karaThreshold : Nat)
    (a b : Array UInt64) (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) : Array UInt64 :=
  (toomCook4MulLimbsRec toom4Threshold toom3Threshold karaThreshold a b loA loB len hA hB).1

theorem toomCook4MulLimbs_size (toom4Threshold toom3Threshold karaThreshold : Nat)
    (a b : Array UInt64) (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    (toomCook4MulLimbs toom4Threshold toom3Threshold karaThreshold a b loA loB len hA hB).size
      = 2 * len :=
  (toomCook4MulLimbsRec toom4Threshold toom3Threshold karaThreshold a b loA loB len hA hB).2

/-- Multiply two `AzNat`s with Toom-4 forced at every level down to the given thresholds
(the operands are padded to a common length).  For tests and benchmarks. -/
def mulToomCook4 (toom4Threshold toom3Threshold karaThreshold : Nat) (a b : AzNat) : AzNat :=
  let n := max a.limbs.size b.limbs.size
  ofLimbs (toomCook4MulLimbs toom4Threshold toom3Threshold karaThreshold
    (truncatePad a.limbs n) (truncatePad b.limbs n) 0 0 n
    (by rw [truncatePad_size]; omega) (by rw [truncatePad_size]; omega))

end Azurite.AzNat
