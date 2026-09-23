/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Add
import Azurite.AzInt.Equiv.Basic
import Azurite.AzInt.Equiv.Conversion
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.Compare

namespace Azurite.AzInt

/-- `mkNorm true a` represents `a` nonnegatively. -/
lemma toInt_mkNorm_true (a : AzNat) : (mkNorm true a).toInt = (a.toNat : Int) := by
  unfold mkNorm
  by_cases h : a = 0
  · simp only [h, ↓reduceDIte]
    show ((0 : AzInt)).toInt = ((0 : AzNat).toNat : Int)
    rfl
  · simp only [h, ↓reduceDIte]
    show (if true then (a.toNat : Int) else _) = _
    simp

/-- `mkNorm false a` represents `-a` when `a ≠ 0`. -/
lemma toInt_mkNorm_false (a : AzNat) (h : a ≠ 0) :
    (mkNorm false a).toInt = -(a.toNat : Int) := by
  unfold mkNorm
  simp only [h, ↓reduceDIte]
  show (if false then _ else -(a.toNat : Int)) = _
  simp

/-- `mkNonzero false a h` represents `-a`. -/
lemma toInt_mkNonzero_false (a : AzNat) (h : a ≠ 0) :
    (mkNonzero false a h).toInt = -(a.toNat : Int) := by
  show (if false then _ else -(a.toNat : Int)) = _
  simp

/-- `mkNonzero true a h` represents `a`. -/
lemma toInt_mkNonzero_true (a : AzNat) (h : a ≠ 0) :
    (mkNonzero true a h).toInt = (a.toNat : Int) := by
  show (if true then (a.toNat : Int) else _) = _
  simp

/-- Correctness of `AzInt.addUInt64`. -/
theorem toInt_addUInt64 (z : AzInt) (u : UInt64) :
    (z.addUInt64 u).toInt = z.toInt + (u.toNat : Int) := by
  unfold addUInt64
  have h_tz : z.toInt = if z.sign then (z.abs.toNat : Int) else -(z.abs.toNat : Int) := rfl
  rw [h_tz]
  by_cases hs : z.sign
  · simp only [hs, ↓reduceIte]
    rw [Azurite.AzNat.toInt_toAzInt, AzNat.toNat_addUInt64]
    push_cast; ring
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    have h_eq := AzNat.compareUInt64_eq z.abs u
    split <;> rename_i h_cmp
    · -- .lt
      rw [h_cmp] at h_eq
      have h_lt : z.abs.toNat < u.toNat := Nat.compare_eq_lt.mp h_eq.symm
      rw [Azurite.AzNat.toInt_toAzInt, AzNat.toNat_sub, UInt64.toNat_toAzNat]
      omega
    · -- .eq
      rw [h_cmp] at h_eq
      have h_e : z.abs.toNat = u.toNat := Nat.compare_eq_eq.mp h_eq.symm
      rw [toInt_zero]; omega
    · -- .gt
      rw [h_cmp] at h_eq
      have h_gt : u.toNat < z.abs.toNat := Nat.compare_eq_gt.mp h_eq.symm
      have h_sub_pos : z.abs.subUInt64 u ≠ 0 := by
        intro hc
        have hc' : (z.abs.subUInt64 u).toNat = 0 := by rw [hc]; rfl
        rw [AzNat.toNat_subUInt64] at hc'; omega
      rw [toInt_mkNonzero_false _ h_sub_pos, AzNat.toNat_subUInt64]
      omega

/-- `ofInt`-version of `toInt_addUInt64`. -/
theorem ofInt_addUInt64 (i : Int) (u : UInt64) :
    ofInt (i + (u.toNat : Int)) = (ofInt i).addUInt64 u := by
  have h : (ofInt (i + (u.toNat : Int))).toInt = ((ofInt i).addUInt64 u).toInt := by
    rw [toInt_ofInt, toInt_addUInt64, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

/-- Helper: relate `AzNat.compare` to `Ord.compare` on `toNat`. -/
private lemma azNat_compare_eq (a b : AzNat) :
    AzNat.compare a b = Ord.compare a.toNat b.toNat :=
  AzNat.compare_eq_compare_toNat a b

/-- Correctness of `AzInt.add`. -/
theorem toInt_add (a b : AzInt) : (a + b).toInt = a.toInt + b.toInt := by
  show (add a b).toInt = a.toInt + b.toInt
  unfold add
  have h_ta : a.toInt = if a.sign then (a.abs.toNat : Int) else -(a.abs.toNat : Int) := rfl
  have h_tb : b.toInt = if b.sign then (b.abs.toNat : Int) else -(b.abs.toNat : Int) := rfl
  rw [h_ta, h_tb]
  have h_cmp_eq := AzNat.compare_eq_compare_toNat a.abs b.abs
  by_cases hsa : a.sign = true
  · by_cases hsb : b.sign = true
    · -- true, true
      simp only [hsa, hsb, ↓reduceDIte, ↓reduceIte]
      rw [Azurite.AzNat.toInt_toAzInt, AzNat.toNat_add]
      push_cast; ring
    · -- true, false
      simp only [hsa, hsb, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
      split <;> rename_i h_cmp
      · rw [h_cmp] at h_cmp_eq
        have h_lt : a.abs.toNat < b.abs.toNat := Nat.compare_eq_lt.mp h_cmp_eq.symm
        have h_sub_ne : b.abs - a.abs ≠ 0 := by
          intro hc
          have : (b.abs - a.abs).toNat = 0 := by rw [hc]; rfl
          rw [AzNat.toNat_sub] at this; omega
        rw [toInt_mkNonzero_false _ h_sub_ne, AzNat.toNat_sub]
        omega
      · rw [h_cmp] at h_cmp_eq
        have h_eq : a.abs.toNat = b.abs.toNat := Nat.compare_eq_eq.mp h_cmp_eq.symm
        rw [toInt_zero]; omega
      · rw [h_cmp] at h_cmp_eq
        have h_gt : b.abs.toNat < a.abs.toNat := Nat.compare_eq_gt.mp h_cmp_eq.symm
        rw [Azurite.AzNat.toInt_toAzInt, AzNat.toNat_sub]
        omega
  · have hanz : a.abs ≠ 0 := fun h0 => by
      rw [a.zero_sign h0] at hsa; exact hsa rfl
    by_cases hsb : b.sign = true
    · -- false, true
      simp only [hsa, hsb, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
      split <;> rename_i h_cmp
      · rw [h_cmp] at h_cmp_eq
        have h_lt : a.abs.toNat < b.abs.toNat := Nat.compare_eq_lt.mp h_cmp_eq.symm
        rw [Azurite.AzNat.toInt_toAzInt, AzNat.toNat_sub]
        omega
      · rw [h_cmp] at h_cmp_eq
        have h_eq : a.abs.toNat = b.abs.toNat := Nat.compare_eq_eq.mp h_cmp_eq.symm
        rw [toInt_zero]; omega
      · rw [h_cmp] at h_cmp_eq
        have h_gt : b.abs.toNat < a.abs.toNat := Nat.compare_eq_gt.mp h_cmp_eq.symm
        have h_sub_ne : a.abs - b.abs ≠ 0 := by
          intro hc
          have : (a.abs - b.abs).toNat = 0 := by rw [hc]; rfl
          rw [AzNat.toNat_sub] at this; omega
        rw [toInt_mkNonzero_false _ h_sub_ne, AzNat.toNat_sub]
        omega
    · -- false, false
      simp only [hsa, hsb, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
      have h_sum_ne : a.abs + b.abs ≠ 0 := by
        intro hc
        have : (a.abs + b.abs).toNat = 0 := by rw [hc]; rfl
        rw [AzNat.toNat_add] at this
        have : a.abs.toNat = 0 := by omega
        exact hanz (AzNat.toNat_injective (by rw [this, AzNat.toNat_zero]))
      rw [toInt_mkNonzero_false _ h_sum_ne, AzNat.toNat_add]
      push_cast; ring

/-- `ofInt`-version of `toInt_add`. -/
theorem ofInt_add (i j : Int) : ofInt (i + j) = ofInt i + ofInt j := by
  have h : (ofInt (i + j)).toInt = (ofInt i + ofInt j).toInt := by
    rw [toInt_ofInt, toInt_add, toInt_ofInt, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

/-- Correctness of `AzInt.neg`. -/
@[simp] theorem toInt_neg (z : AzInt) : (-z).toInt = -z.toInt := by
  show (neg z).toInt = -z.toInt
  unfold neg
  by_cases h : z.abs = 0
  · have h_z : z.toInt = 0 := by
      show (if z.sign then (z.abs.toNat : Int) else -(z.abs.toNat : Int)) = 0
      rw [h]; simp
    rw [h_z, neg_zero]
    unfold mkNorm; simp [h]; rfl
  · cases hs : z.sign
    · rw [Bool.not_false, toInt_mkNorm_true]
      show _ = -(if z.sign then (z.abs.toNat : Int) else -(z.abs.toNat : Int))
      rw [hs]; simp
    · rw [Bool.not_true, toInt_mkNorm_false _ h]
      show _ = -(if z.sign then (z.abs.toNat : Int) else -(z.abs.toNat : Int))
      rw [hs]; simp

/-- `ofInt`-version of `toInt_neg`. -/
theorem ofInt_neg (i : Int) : ofInt (-i) = -ofInt i := by
  have h : (ofInt (-i)).toInt = (-ofInt i).toInt := by
    rw [toInt_ofInt, toInt_neg, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

end Azurite.AzInt
