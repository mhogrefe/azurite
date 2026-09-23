/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Parity
import Azurite.AzNat.Equiv.Basic
import Mathlib.Algebra.Ring.Parity

namespace Azurite.AzNat

private lemma uint64_land_one_toNat (x : UInt64) : (x &&& 1).toNat = x.toNat % 2 := by
  show (x.toBitVec &&& 1#64).toNat = x.toBitVec.toNat % 2
  rw [BitVec.toNat_and]
  have : (1#64).toNat = 1 := by decide
  rw [this, Nat.and_one_is_mod]

private lemma uint64_land_one_eq_zero_iff (x : UInt64) : x &&& 1 = 0 ↔ x.toNat % 2 = 0 := by
  constructor
  · intro h
    have h1 := uint64_land_one_toNat x
    rw [h] at h1; exact h1.symm
  · intro h
    apply UInt64.eq_of_toNat_eq
    have h1 := uint64_land_one_toNat x
    simp only [UInt64.toNat_zero]; omega

private lemma toNatLimbsList_mod_two_cons (x : UInt64) (xs : List UInt64) :
    toNatLimbsList (x :: xs) % 2 = x.toNat % 2 := by
  rw [toNatLimbsList_cons]; omega

theorem isEven_iff (n : AzNat) : n.isEven = true ↔ Even n.toNat := by
  rw [Nat.even_iff]
  unfold isEven toNat
  cases h : n.limbs.toList with
  | nil =>
    have h_size : n.limbs.size = 0 := by
      have := congr_arg List.length h; simp at this; simp [this]
    simp [show ¬(n.limbs.size > 0) from by omega, toNatLimbsList]
  | cons x xs =>
    have h_pos : n.limbs.size > 0 := by
      have := congr_arg List.length h; simp at this; omega
    simp only [show (n.limbs.size > 0) = True from by simp [h_pos], dite_true, beq_iff_eq]
    simp only [show n.limbs[0] = n.limbs.toList[(0 : Nat)]'(by omega) from
      Array.getElem_toList (by omega), h]
    simp only [List.getElem_cons_zero, uint64_land_one_eq_zero_iff, toNatLimbsList_mod_two_cons]

theorem isOdd_iff (n : AzNat) : n.isOdd = true ↔ Odd n.toNat := by
  unfold isOdd
  rw [Bool.not_eq_true', Bool.eq_false_iff, ← Nat.not_even_iff_odd]
  exact Iff.not (isEven_iff n)

theorem isEven_ofNat (n : Nat) : (ofNat n).isEven = true ↔ Even n := by
  rw [isEven_iff, toNat_ofNat]

theorem isOdd_ofNat (n : Nat) : (ofNat n).isOdd = true ↔ Odd n := by
  rw [isOdd_iff, toNat_ofNat]

end Azurite.AzNat
