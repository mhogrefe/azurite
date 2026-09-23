/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Basic
import Azurite.AzNat.Equiv.Basic

namespace Azurite.AzInt

/-- Convert an `AzInt` to the exact mathematical `Int` that it represents. -/
def toInt (z : AzInt) : Int :=
  if z.sign then (z.abs.toNat : Int) else -(z.abs.toNat : Int)

/-- Compute the corresponding `AzInt` from a mathematical `Int`. -/
def ofInt (i : Int) : AzInt where
  sign := decide (0 ≤ i)
  abs := AzNat.ofNat i.natAbs
  zero_sign := by
    intro h
    have h1 : (AzNat.ofNat i.natAbs).toNat = (0 : AzNat).toNat := congrArg AzNat.toNat h
    rw [Azurite.AzNat.toNat_ofNat] at h1
    have h2 : i.natAbs = 0 := h1
    have h3 : i = 0 := Int.natAbs_eq_zero.mp h2
    subst h3
    exact rfl

-- Provide a default canonical evaluation linking `toInt` and `ofInt` natively.
lemma toInt_ofInt (i : Int) : (ofInt i).toInt = i := by
  unfold ofInt toInt
  simp
  split_ifs with h
  · have h1 : i.natAbs = i := Int.natAbs_of_nonneg h
    rw [Azurite.AzNat.toNat_ofNat, h1]
  · have h_lt : i < 0 := not_le.mp h
    have h1 : (i.natAbs : Int) = -i := Int.ofNat_natAbs_of_nonpos (le_of_lt h_lt)
    rw [Azurite.AzNat.toNat_ofNat, h1, neg_neg]

lemma ofInt_toInt (z : AzInt) : ofInt z.toInt = z := by
  cases z with
  | mk sign abs zero_sign =>
    dsimp [ofInt, toInt]
    split_ifs with h_sign
    · simp
      exact ⟨h_sign, Azurite.AzNat.ofNat_toNat abs⟩
    · simp at h_sign
      simp
      have h1 : abs ≠ 0 := fun h => by simp [zero_sign h] at h_sign
      have h2 : abs.toNat ≠ 0 := fun h =>
        h1 (Azurite.AzNat.toNat_injective (h.trans Azurite.AzNat.toNat_zero.symm))
      rw [decide_eq_false h2]
      exact ⟨h_sign.symm, Azurite.AzNat.ofNat_toNat abs⟩

@[simp] lemma toInt_zero : (0 : AzInt).toInt = 0 := by
  change (if (0 : AzInt).sign then _ else _) = 0
  have hs : (0 : AzInt).sign = true := rfl
  rw [ite_eq_left hs]
  change ↑(0 : AzNat).toNat = (0 : Int)
  rfl

@[simp] lemma toInt_one : (1 : AzInt).toInt = 1 := by
  change (if (1 : AzInt).sign then _ else _) = 1
  have hs : (1 : AzInt).sign = true := rfl
  rw [ite_eq_left hs]
  change ↑(1 : AzNat).toNat = (1 : Int)
  rfl

@[simp] lemma ofInt_zero : ofInt 0 = 0 := by
  have hz : (0 : AzInt).toInt = 0 := toInt_zero
  rw [← hz, ofInt_toInt]

@[simp] lemma ofInt_one : ofInt 1 = 1 := by
  have h1 : (1 : AzInt).toInt = 1 := toInt_one
  rw [← h1, ofInt_toInt]

/-- The mathematical equivalence between `AzInt` and the standard Lean 4 `Int`. -/
def equivInt : AzInt ≃ Int where
  toFun := toInt
  invFun := ofInt
  left_inv := ofInt_toInt
  right_inv := toInt_ofInt

lemma Int64.toInt_of_nonneg {i : Int64} (hi : i ≥ 0) : i.toInt = (i.toBitVec.toNat : Int) := by
  revert hi
  change (decide ((0 : Int64).toBitVec.toInt ≤ i.toBitVec.toInt) = true) → i.toInt = (i.toBitVec.toNat : Int)
  intro he
  have he2 := of_decide_eq_true he
  have h0 : (0 : Int64).toBitVec.toInt = 0 := rfl
  rw [h0] at he2
  have hd : i.toInt = i.toBitVec.toInt := rfl
  rw [hd]
  unfold BitVec.toInt at *
  split_ifs at he2 ⊢
  · rfl
  · omega

lemma Int64.toInt_of_neg {i : Int64} (hi : ¬i ≥ 0) : i.toInt = (i.toBitVec.toNat : Int) - 2^64 := by
  revert hi
  change ¬(decide ((0 : Int64).toBitVec.toInt ≤ i.toBitVec.toInt) = true) → i.toInt = (i.toBitVec.toNat : Int) - 2^64
  intro he
  have h_dec : decide ((0 : Int64).toBitVec.toInt ≤ i.toBitVec.toInt) = false := Bool.eq_false_of_not_eq_true he
  have he2 : ¬((0:Int64).toBitVec.toInt ≤ i.toBitVec.toInt) := of_decide_eq_false h_dec
  have h0 : (0 : Int64).toBitVec.toInt = 0 := rfl
  rw [h0] at he2
  have hd : i.toInt = i.toBitVec.toInt := rfl
  rw [hd]
  unfold BitVec.toInt at *
  split_ifs at he2 ⊢
  · omega
  · rfl

@[simp] theorem beqUInt64_eq (z : Azurite.AzInt) (u : UInt64) : z.beqUInt64 u = true ↔ z.toInt = (u.toNat : Int) := by
  unfold beqUInt64
  dsimp [toInt]
  split_ifs with h
  · simp [h]
  · rw [Bool.and_eq_true]
    simp [h]
    intro hc
    have ht : (z.abs.toNat : Int) = -(u.toNat : Int) := by omega
    have hz1 : z.abs.toNat = 0 := by omega
    have hza : z.abs = 0 := Azurite.AzNat.toNat_injective (by rw [hz1, Azurite.AzNat.toNat_zero])
    have hzs : z.sign = true := z.zero_sign hza
    rw [hzs] at h
    contradiction

@[simp] theorem beqAzNat_eq (z : Azurite.AzInt) (a : Azurite.AzNat) : z.beqAzNat a = true ↔ z.toInt = (a.toNat : Int) := by
  unfold beqAzNat
  dsimp [toInt]
  split_ifs with h
  · rw [Bool.and_eq_true]
    simp [h]
    apply Iff.intro
    · intro he
      rw [he]
    · intro ht
      exact Azurite.AzNat.toNat_injective ht
  · rw [Bool.and_eq_true]
    simp [h]
    intro hc
    have ht : (z.abs.toNat : Int) = -(a.toNat : Int) := by omega
    have hz1 : z.abs.toNat = 0 := by omega
    have hza : z.abs = 0 := Azurite.AzNat.toNat_injective (by rw [hz1, Azurite.AzNat.toNat_zero])
    have hzs : z.sign = true := z.zero_sign hza
    rw [hzs] at h
    contradiction

@[simp] theorem beqInt64_eq (z : Azurite.AzInt) (i : Int64) : z.beqInt64 i = true ↔ z.toInt = i.toInt := by
  unfold beqInt64
  split_ifs with hi
  · change z.beqUInt64 i.toUInt64 = true ↔ z.toInt = i.toInt
    rw [beqUInt64_eq]
    have ht : (i.toUInt64.toNat : Int) = i.toBitVec.toNat := rfl
    rw [ht, Int64.toInt_of_nonneg hi]
  · rw [Bool.and_eq_true]
    dsimp [toInt]
    have hi_neg : i.toInt = (i.toBitVec.toNat : Int) - 2^64 := Int64.toInt_of_neg hi
    have h_iLt : i.toBitVec.toNat < 2^64 := i.toBitVec.isLt
    split_ifs with hz
    · simp [hz]
      intro hc
      omega
    · simp [hz]
      have ht_mod : (UInt64.size - i.toUInt64.toNat) % UInt64.size = (2^64 - i.toBitVec.toNat) % 2^64 := rfl
      rw [ht_mod]
      have hh_neg_int : ¬0 ≤ i.toBitVec.toInt := by
        revert hi
        change ¬(decide ((0 : Int64).toBitVec.toInt ≤ i.toBitVec.toInt) = true) → ¬(0 ≤ i.toBitVec.toInt)
        intro he
        have h_dec : decide ((0 : Int64).toBitVec.toInt ≤ i.toBitVec.toInt) = false := Bool.eq_false_of_not_eq_true he
        have he2 := of_decide_eq_false h_dec
        have h0 : (0 : Int64).toBitVec.toInt = 0 := rfl
        rw [h0] at he2
        exact he2
      unfold BitVec.toInt at hh_neg_int
      have h_pos : i.toBitVec.toNat > 0 := by
        split_ifs at hh_neg_int
        · omega
        · omega
      have h_mod : (2^64 - i.toBitVec.toNat) % 2^64 = 2^64 - i.toBitVec.toNat := by
        apply Nat.mod_eq_of_lt
        omega
      rw [h_mod]
      omega

end Azurite.AzInt
