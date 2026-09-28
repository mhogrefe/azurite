/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul.ToomCook4
import Azurite.AzNat.Square.ToomCook3

/-!
# Toom–Cook 4-way squaring for AzNat

`toomCook4MulLimbsRec` with one operand: the seven evaluations are those of `A` alone, the
pointwise products are squares (`signedSquareWith` with the recursive squaring call), and the
interpolation `toomCook4Interpolate` is reused unchanged.  Falls back to Toom-3 squaring.
Correctness is `toomCook4SquareLimbs_toNat` in `Equiv/Square/ToomCook4.lean`.
-/

namespace Azurite.AzNat

/-- Recursive Toom-4 squaring of a slice. -/
def toomCook4SquareLimbsRec (toom4Threshold toom3Threshold karaThreshold : Nat)
    (a : Array UInt64) (loA len : Nat) (hA : loA + len ≤ a.size) :
    { c : Array UInt64 // c.size = 2 * len } :=
  if h_base : len < toom4Threshold ∨ len < 4 then
    ⟨toomCook3SquareLimbs toom3Threshold karaThreshold a loA len hA, by
      rw [toomCook3SquareLimbs_size]⟩
  else
    have hlen : 4 ≤ len := by omega
    let k := (len + 3) / 4
    have hk1_lt : k + 1 < len := by show (len + 3) / 4 + 1 < len; omega
    let sqK1 : (x : Array UInt64) → 0 + (k + 1) ≤ x.size → Array UInt64 := fun x hx =>
      (toomCook4SquareLimbsRec toom4Threshold toom3Threshold karaThreshold x 0 (k + 1) hx).1
    let bs := blocks a loA len k 4
    let v0 := signedSquareWith (k + 1) sqK1 (hornerInt64 0 bs)
    let v1 := signedSquareWith (k + 1) sqK1 (hornerInt64 1 bs)
    let vm1 := signedSquareWith (k + 1) sqK1 (hornerInt64 (-1) bs)
    let v2 := signedSquareWith (k + 1) sqK1 (hornerInt64 2 bs)
    let vm2 := signedSquareWith (k + 1) sqK1 (hornerInt64 (-2) bs)
    let vh := signedSquareWith (k + 1) sqK1 (hornerInt64 2 bs.reverse)
    let vinf := signedSquareWith (k + 1) sqK1 (hornerInt64 0 bs.reverse)
    let cs := toomCook4Interpolate v0 v1 vm1 v2 vm2 vh vinf
    ⟨truncatePad (assemble k (cs.map AzInt.abs)).limbs (2 * len), truncatePad_size _ _⟩
  termination_by len
  decreasing_by
    all_goals omega

/-- Toom-4 squaring of a slice, in `2 · len` limbs. -/
def toomCook4SquareLimbs (toom4Threshold toom3Threshold karaThreshold : Nat)
    (a : Array UInt64) (loA len : Nat) (hA : loA + len ≤ a.size) : Array UInt64 :=
  (toomCook4SquareLimbsRec toom4Threshold toom3Threshold karaThreshold a loA len hA).1

theorem toomCook4SquareLimbs_size (toom4Threshold toom3Threshold karaThreshold : Nat)
    (a : Array UInt64) (loA len : Nat) (hA : loA + len ≤ a.size) :
    (toomCook4SquareLimbs toom4Threshold toom3Threshold karaThreshold a loA len hA).size
      = 2 * len :=
  (toomCook4SquareLimbsRec toom4Threshold toom3Threshold karaThreshold a loA len hA).2

/-- Square an `AzNat` with Toom-4 forced down to the given thresholds (tests, benchmarks). -/
def squareToomCook4 (toom4Threshold toom3Threshold karaThreshold : Nat) (a : AzNat) : AzNat :=
  ofLimbs (toomCook4SquareLimbs toom4Threshold toom3Threshold karaThreshold a.limbs 0
    a.limbs.size (by simp))

end Azurite.AzNat
