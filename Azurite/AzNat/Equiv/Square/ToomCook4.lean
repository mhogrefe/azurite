/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Square.ToomCook4
import Azurite.AzNat.Equiv.Mul.ToomCook4
import Azurite.AzNat.Equiv.Square.ToomCook3

/-!
# Correctness of Toom–Cook 4-way squaring

`toomCook4SquareLimbs_toNat`: the result is the square of the slice.  The algebra is
`toomCook4_assemble_toNat` with both block lists equal; the products come from
`toInt_signedSquareWith` with the recursive call as the squarer.
-/

namespace Azurite.AzNat

/-- **The core of Toom-4 squaring.** -/
theorem toomCook4_core_sq_toNat (k : Nat)
    (sqK1 : (x : Array UInt64) → 0 + (k + 1) ≤ x.size → Array UInt64)
    (hsq : ∀ x hx, toNatLimbsList (sqK1 x hx).toList = sliceVal x 0 (k + 1) * sliceVal x 0 (k + 1))
    (a0 a1 a2 a3 : AzNat)
    (ha0 : a0.toNat < 2 ^ (64 * k)) (ha1 : a1.toNat < 2 ^ (64 * k))
    (ha2 : a2.toNat < 2 ^ (64 * k)) (ha3 : a3.toNat < 2 ^ (64 * k)) :
    let bs := [a0.toAzInt, a1.toAzInt, a2.toAzInt, a3.toAzInt]
    let v0 := signedSquareWith (k + 1) sqK1 (hornerInt64 0 bs)
    let v1 := signedSquareWith (k + 1) sqK1 (hornerInt64 1 bs)
    let vm1 := signedSquareWith (k + 1) sqK1 (hornerInt64 (-1) bs)
    let v2 := signedSquareWith (k + 1) sqK1 (hornerInt64 2 bs)
    let vm2 := signedSquareWith (k + 1) sqK1 (hornerInt64 (-2) bs)
    let vh := signedSquareWith (k + 1) sqK1 (hornerInt64 2 bs.reverse)
    let vinf := signedSquareWith (k + 1) sqK1 (hornerInt64 0 bs.reverse)
    (assemble k ((toomCook4Interpolate v0 v1 vm1 v2 vm2 vh vinf).map AzInt.abs)).toNat
      = polyEvalNat (2 ^ (64 * k)) [a0.toNat, a1.toNat, a2.toNat, a3.toNat]
        * polyEvalNat (2 ^ (64 * k)) [a0.toNat, a1.toNat, a2.toNat, a3.toNat] := by
  intro bs v0 v1 vm1 v2 vm2 vh vinf
  have hA : ∀ (c : Int64), c.toInt.natAbs ≤ 2 →
      (hornerInt64 c [a0.toAzInt, a1.toAzInt, a2.toAzInt, a3.toAzInt]).abs.toNat
        < 2 ^ (64 * (k + 1)) :=
    fun c hc => toomCook4_eval_abs_lt k _ _ _ _ ha0 ha1 ha2 ha3 c hc
  have hA' : ∀ (c : Int64), c.toInt.natAbs ≤ 2 →
      (hornerInt64 c [a3.toAzInt, a2.toAzInt, a1.toAzInt, a0.toAzInt]).abs.toNat
        < 2 ^ (64 * (k + 1)) :=
    fun c hc => toomCook4_eval_abs_lt k _ _ _ _ ha3 ha2 ha1 ha0 c hc
  have hrev : bs.reverse = [a3.toAzInt, a2.toAzInt, a1.toAzInt, a0.toAzInt] := rfl
  have hv0 : v0.toInt = (hornerInt64 0 bs).toInt * (hornerInt64 0 bs).toInt :=
    toInt_signedSquareWith _ _ hsq _ (hA 0 int64_natAbs_le_two_zero)
  have hv1 : v1.toInt = (hornerInt64 1 bs).toInt * (hornerInt64 1 bs).toInt :=
    toInt_signedSquareWith _ _ hsq _ (hA 1 int64_natAbs_le_two_one)
  have hvm1 : vm1.toInt = (hornerInt64 (-1) bs).toInt * (hornerInt64 (-1) bs).toInt :=
    toInt_signedSquareWith _ _ hsq _ (hA (-1) int64_natAbs_le_two_neg_one)
  have hv2 : v2.toInt = (hornerInt64 2 bs).toInt * (hornerInt64 2 bs).toInt :=
    toInt_signedSquareWith _ _ hsq _ (hA 2 int64_natAbs_le_two_two)
  have hvm2 : vm2.toInt = (hornerInt64 (-2) bs).toInt * (hornerInt64 (-2) bs).toInt :=
    toInt_signedSquareWith _ _ hsq _ (hA (-2) int64_natAbs_le_two_neg_two)
  have hvh : vh.toInt = (hornerInt64 2 bs.reverse).toInt * (hornerInt64 2 bs.reverse).toInt := by
    rw [hrev] at *
    exact toInt_signedSquareWith _ _ hsq _ (hA' 2 int64_natAbs_le_two_two)
  have hvinf : vinf.toInt = (hornerInt64 0 bs.reverse).toInt * (hornerInt64 0 bs.reverse).toInt := by
    rw [hrev] at *
    exact toInt_signedSquareWith _ _ hsq _ (hA' 0 int64_natAbs_le_two_zero)
  rw [hrev] at hvh hvinf
  exact toomCook4_assemble_toNat k a0 a1 a2 a3 a0 a1 a2 a3 v0 v1 vm1 v2 vm2 vh vinf
    hv0 hv1 hvm1 hv2 hvm2 hvh hvinf

/-- **Correctness of the Toom-4 squaring recursion.** -/
theorem toomCook4SquareLimbsRec_toNat (toom4Threshold toom3Threshold karaThreshold : Nat) :
    ∀ (len : Nat) (a : Array UInt64) (loA : Nat) (hA : loA + len ≤ a.size),
    toNatLimbsList (toomCook4SquareLimbsRec toom4Threshold toom3Threshold karaThreshold
        a loA len hA).val.toList
      = sliceVal a loA len ^ 2 := by
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
    intro a loA hA
    unfold toomCook4SquareLimbsRec
    by_cases h_base : len < toom4Threshold ∨ len < 4
    · simp only [h_base, ↓reduceDIte]
      exact toomCook3SquareLimbs_toNat toom3Threshold karaThreshold a loA len hA
    · simp only [h_base, ↓reduceDIte]
      have hk1_lt : (len + 3) / 4 + 1 < len := by omega
      have hlen_le : len ≤ 4 * ((len + 3) / 4) := by omega
      have hsq : ∀ (x : Array UInt64) (hx : 0 + ((len + 3) / 4 + 1) ≤ x.size),
          toNatLimbsList (toomCook4SquareLimbsRec toom4Threshold toom3Threshold karaThreshold
              x 0 ((len + 3) / 4 + 1) hx).1.toList
            = sliceVal x 0 ((len + 3) / 4 + 1) * sliceVal x 0 ((len + 3) / 4 + 1) :=
        fun x hx => by rw [ih _ hk1_lt x 0 hx, sq]
      have hcore := toomCook4_core_sq_toNat ((len + 3) / 4)
        (fun x hx => (toomCook4SquareLimbsRec toom4Threshold toom3Threshold karaThreshold
          x 0 ((len + 3) / 4 + 1) hx).1) hsq
        (block a loA len _ 0) (block a loA len _ 1) (block a loA len _ 2) (block a loA len _ 3)
        (toNat_block_lt _ _ _ _ _) (toNat_block_lt _ _ _ _ _) (toNat_block_lt _ _ _ _ _)
        (toNat_block_lt _ _ _ _ _)
      rw [polyEvalNat_blocks_four a loA len _ hlen_le hA] at hcore
      rw [blocks_four, truncatePad_toNat]
      · rw [sq]; exact hcore
      · change AzNat.toNat _ < _
        rw [hcore, show 64 * (2 * len) = 64 * len + 64 * len by ring, pow_add]
        exact Nat.mul_lt_mul'' (sliceVal_lt_pow _ _ _) (sliceVal_lt_pow _ _ _)

/-- Correctness of `toomCook4SquareLimbs`. -/
theorem toomCook4SquareLimbs_toNat (toom4Threshold toom3Threshold karaThreshold : Nat)
    (a : Array UInt64) (loA len : Nat) (hA : loA + len ≤ a.size) :
    toNatLimbsList (toomCook4SquareLimbs toom4Threshold toom3Threshold karaThreshold
        a loA len hA).toList = sliceVal a loA len ^ 2 :=
  toomCook4SquareLimbsRec_toNat toom4Threshold toom3Threshold karaThreshold len a loA hA

/-- `AzNat`-level correctness of `squareToomCook4`. -/
theorem toNat_squareToomCook4 (toom4Threshold toom3Threshold karaThreshold : Nat) (a : AzNat) :
    (squareToomCook4 toom4Threshold toom3Threshold karaThreshold a).toNat = a.toNat ^ 2 := by
  unfold squareToomCook4
  rw [toNat_ofLimbs, toomCook4SquareLimbs_toNat, sliceVal_self _ _ rfl]
  rfl

end Azurite.AzNat
