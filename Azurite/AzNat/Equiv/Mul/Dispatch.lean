/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul
import Azurite.AzNat.Equiv.Mul.ToomCook4
import Azurite.AzNat.Equiv.Mul.ToomUnbalanced

/-!
# Correctness of the multiplication dispatcher

`mulLimbs_toNat` and `toNat_mul`: the production `AzNat` multiplication agrees with `Nat`
multiplication whatever branch it takes (schoolbook, the balanced ladder on padded slices,
Toom-(3,2), Toom-(4,2), or the chunk loop).
-/

namespace Azurite.AzNat

/-- The balanced ladder is correct at every size. -/
theorem balancedMulLimbs_toNat (th : MulThresholds) (a b : Array UInt64) (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    toNatLimbsList (balancedMulLimbs th a b loA loB len hA hB).toList
      = sliceVal a loA len * sliceVal b loB len := by
  unfold balancedMulLimbs
  split_ifs
  · exact toomCook4MulLimbs_toNat _ _ _ _ _ _ _ _ _ _
  · exact toomCook3MulLimbs_toNat _ _ _ _ _ _ _ _ _
  · exact karatsubaMulLimbs_toNat _ _ _ _ _ _ _ _
  · exact schoolbookMulLimbs_toNat _ _ _ _ _ _ _ _

theorem balancedMul_spec (th : MulThresholds) :
    ∀ n x y hx hy, toNatLimbsList (balancedMul th n x y hx hy).toList
      = sliceVal x 0 n * sliceVal y 0 n :=
  fun n x y hx hy => balancedMulLimbs_toNat th x y 0 0 n hx hy

theorem mulLimbsOrdered_toNat (th : MulThresholds) (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) (hle : lenB ≤ lenA) :
    toNatLimbsList (mulLimbsOrdered th a b loA lenA loB lenB hA hB).toList
      = sliceVal a loA lenA * sliceVal b loB lenB := by
  unfold mulLimbsOrdered
  split_ifs
  · exact schoolbookMulLimbs_toNat _ _ _ _ _ _ _ _
  · simp only []
    have hbz : toNatLimbsList (b.extract loB (loB + lenB)).toList < 2 ^ (64 * lenA) := by
      rw [toNatLimbsList_extract]
      exact lt_of_lt_of_le (sliceVal_lt_pow _ _ _)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [balancedMulLimbs_toNat, sliceVal_self _ _ (by rw [Array.size_extract]; omega),
      sliceVal_self _ _ (truncatePad_size _ _), toNatLimbsList_extract, truncatePad_toNat _ _ hbz,
      toNatLimbsList_extract]
  · exact schoolbookMulLimbs_toNat _ _ _ _ _ _ _ _
  · exact toom32MulLimbs_toNat _ (balancedMul_spec th) _ _ _ _ _ _ _ _
  · exact toom42MulLimbs_toNat _ (balancedMul_spec th) _ _ _ _ _ _ _ _
  · exact mulChunksLimbs_toNat _ (balancedMul_spec th) _ _ _ _ _ _ _ _

theorem mulLimbsWith_toNat (th : MulThresholds) (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) :
    toNatLimbsList (mulLimbsWith th a b loA lenA loB lenB hA hB).toList
      = sliceVal a loA lenA * sliceVal b loB lenB := by
  unfold mulLimbsWith
  split_ifs with h
  · exact mulLimbsOrdered_toNat th a b loA lenA loB lenB hA hB h
  · rw [Nat.mul_comm]
    exact mulLimbsOrdered_toNat th b a loB lenB loA lenA hB hA (by omega)

/-- **Correctness of `mulLimbs`.** -/
theorem mulLimbs_toNat (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) :
    toNatLimbsList (mulLimbs a b loA lenA loB lenB hA hB).toList
      = toNatLimbsList ((a.toList.drop loA).take lenA)
        * toNatLimbsList ((b.toList.drop loB).take lenB) :=
  mulLimbsWith_toNat _ a b loA lenA loB lenB hA hB

/-- Correctness of `mul` (the dispatched AzNat multiplication, used by `*`). -/
theorem toNat_mul (a b : AzNat) : (a * b).toNat = a.toNat * b.toNat := by
  show (mul a b).toNat = _
  unfold mul
  rw [toNat_ofLimbs, mulLimbs_toNat]
  show toNatLimbsList ((a.limbs.toList.drop 0).take a.limbs.size)
        * toNatLimbsList ((b.limbs.toList.drop 0).take b.limbs.size) = a.toNat * b.toNat
  rw [List.drop_zero, List.drop_zero]
  rw [List.take_of_length_le (by rw [Array.length_toList])]
  rw [List.take_of_length_le (by rw [Array.length_toList])]
  rfl

/-- `ofNat`-version of `toNat_mul`. -/
theorem ofNat_mul (m n : Nat) : ofNat (m * n) = ofNat m * ofNat n := by
  apply toNat_injective
  rw [toNat_ofNat, toNat_mul, toNat_ofNat, toNat_ofNat]

end Azurite.AzNat
