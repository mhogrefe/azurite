/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.SetBit
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.TestBit
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.UInt64.Equiv.SetBit

namespace Azurite.AzNat

/-- A limb-indexed view of `n.toNat.testBit`, mirroring the structure of
`AzNat.testBit`: bit `j` of `n.toNat` is bit `j % 64` of limb `j / 64`, or `false`
if that limb is absent. -/
lemma testBit_toNat_limbs (n : AzNat) (j : Nat) :
    n.toNat.testBit j =
      if h : j / 64 < n.limbs.toList.length then
        Nat.testBit (n.limbs.toList[j / 64]'h).toNat (j % 64)
      else false := by
  have hj_decomp : j = (j % 64) + 64 * (j / 64) := by omega
  show Nat.testBit (toNatLimbsList _) _ = _
  nth_rewrite 1 [hj_decomp]
  rw [testBit_toNatLimbsList_aux _ _ (Nat.mod_lt _ (by omega))]

/-- The new top limb pushed onto the array in the extension case has numeric
value `2 ^ (i % 64)`. -/
private lemma newLimb_toNat (i : Nat) :
    ((1 : UInt64) <<< UInt64.ofNat (i % 64)).toNat = 2 ^ (i % 64) := by
  have hi_lt : i % 64 < 64 := Nat.mod_lt _ (by omega)
  rw [UInt64.toNat_shiftLeft, show ((1 : UInt64).toNat = 1) from rfl]
  have hofNat : (UInt64.ofNat (i % 64)).toNat = i % 64 :=
    Nat.mod_eq_of_lt (by omega)
  rw [hofNat, Nat.one_shiftLeft, Nat.mod_eq_of_lt hi_lt]
  exact Nat.mod_eq_of_lt
    (Nat.pow_lt_pow_right (by norm_num : (1 : Nat) < 2) hi_lt)

/-- Equality of decidable propositions: when `i / 64 = j / 64`, comparing `i % 64`
with `j % 64` is the same as comparing `i` with `j`. -/
lemma decide_mod_eq_of_div_eq {i j : Nat} (h : i / 64 = j / 64) :
    decide (i % 64 = j % 64) = decide (i = j) := by
  by_cases h' : i = j
  · simp [h']
  · have : i % 64 ≠ j % 64 := by
      intro hmod
      apply h'
      omega
    simp [this, h']

theorem toNat_setBit (n : AzNat) (i : Nat) :
    (n.setBit i).toNat = n.toNat ||| 2 ^ i := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  conv_rhs => rw [testBit_toNat_limbs]
  have hr_lt : j % 64 < 64 := Nat.mod_lt _ (by omega)
  have his_lt : i % 64 < 64 := Nat.mod_lt _ (by omega)
  have hj_decomp : j = (j % 64) + 64 * (j / 64) := by omega
  have h_size_eq : n.limbs.toList.length = n.limbs.size := rfl
  by_cases h_in_range : i / 64 < n.limbs.size
  · -- Case A: i / 64 < n.limbs.size — one existing limb is modified in place.
    simp only [setBit, dite_eq_left h_in_range]
    rw [toNat_ofLimbs, Array.toList_set]
    conv_lhs => rw [hj_decomp]
    rw [testBit_toNatLimbsList_aux _ _ hr_lt]
    simp only [List.length_set]
    by_cases hq : j / 64 < n.limbs.toList.length
    · rw [dite_eq_left hq, dite_eq_left hq, List.getElem_set]
      by_cases hqi : i / 64 = j / 64
      · rw [ite_eq_left hqi, UInt64.toNat_setBit _ _ his_lt,
            Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
            decide_mod_eq_of_div_eq hqi]
        simp [hqi]
      · rw [ite_eq_right hqi]
        have h_ij : i ≠ j := fun h => hqi (by rw [h])
        rw [decide_eq_false h_ij, Bool.or_false]
    · rw [dite_eq_right hq, dite_eq_right hq]
      have h_ij : i ≠ j := by
        intro h
        apply hq
        rw [← h, h_size_eq]
        exact h_in_range
      rw [decide_eq_false h_ij, Bool.false_or]
  · -- Case B: i / 64 ≥ n.limbs.size — array is extended with zero padding.
    simp only [setBit, dite_eq_right h_in_range]
    push Not at h_in_range
    rw [toNat_ofLimbs]
    have h_arr_toList :
        ((n.limbs ++ Array.replicate (i / 64 - n.limbs.size) (0 : UInt64)).push
            ((1 : UInt64) <<< UInt64.ofNat (i % 64))).toList
          = n.limbs.toList ++ List.replicate (i / 64 - n.limbs.size) 0 ++
              [((1 : UInt64) <<< UInt64.ofNat (i % 64))] := by
      simp [Array.toList_push, Array.toList_append, Array.toList_replicate]
    rw [h_arr_toList]
    conv_lhs => rw [hj_decomp]
    rw [testBit_toNatLimbsList_aux _ _ hr_lt]
    have h_len :
        (n.limbs.toList ++ List.replicate (i / 64 - n.limbs.size) 0 ++
          [((1 : UInt64) <<< UInt64.ofNat (i % 64))]).length = i / 64 + 1 := by
      simp [List.length_append, List.length_replicate]
      omega
    by_cases hjtop_lst : j / 64 < (n.limbs.toList ++
        List.replicate (i / 64 - n.limbs.size) 0 ++
          [((1 : UInt64) <<< UInt64.ofNat (i % 64))]).length
    · -- j / 64 ≤ i / 64
      rw [dite_eq_left hjtop_lst]
      have hjtop : j / 64 < i / 64 + 1 := h_len ▸ hjtop_lst
      by_cases hjleft : j / 64 < n.limbs.toList.length
      · -- Sub B1: j / 64 < n.limbs.size (so j ≠ i because i / 64 ≥ n.limbs.size).
        rw [dite_eq_left hjleft]
        have h_get :
            (n.limbs.toList ++ List.replicate (i / 64 - n.limbs.size) 0 ++
                [((1 : UInt64) <<< UInt64.ofNat (i % 64))])[j / 64]'hjtop_lst
              = n.limbs.toList[j / 64]'hjleft := by
          have h_outer_lt :
              j / 64 < (n.limbs.toList ++
                List.replicate (i / 64 - n.limbs.size) 0).length := by
            simp [List.length_append, List.length_replicate]; omega
          rw [List.getElem_append_left h_outer_lt]
          rw [List.getElem_append_left hjleft]
        rw [h_get]
        have h_ij : i ≠ j := by
          intro h
          rw [h_size_eq] at hjleft
          omega
        rw [decide_eq_false h_ij, Bool.or_false]
      · -- j / 64 ≥ n.limbs.size
        rw [dite_eq_right hjleft]
        push Not at hjleft
        rw [h_size_eq] at hjleft
        by_cases hji : j / 64 = i / 64
        · -- Sub B3: j / 64 = i / 64 — the pushed top limb.
          have h_idx_eq :
              j / 64 = (n.limbs.toList ++ List.replicate (i / 64 - n.limbs.size) 0).length := by
            simp [List.length_append, List.length_replicate]
            omega
          have h_get :
              (n.limbs.toList ++ List.replicate (i / 64 - n.limbs.size) 0 ++
                  [((1 : UInt64) <<< UInt64.ofNat (i % 64))])[j / 64]'hjtop_lst
                = (1 : UInt64) <<< UInt64.ofNat (i % 64) := by
            rw [List.getElem_append_right (h_idx_eq ▸ Nat.le_refl _)]
            exact List.getElem_singleton _
          rw [h_get, newLimb_toNat, Nat.testBit_two_pow]
          rw [show decide (i = j) = decide (i % 64 = j % 64) from
            (decide_mod_eq_of_div_eq hji.symm).symm]
          rw [Bool.false_or]
        · -- Sub B2: n.limbs.size ≤ j / 64 < i / 64 — a zero limb in the middle.
          have hji_lt : j / 64 < i / 64 := by omega
          have h_idx_in_middle :
              j / 64 < (n.limbs.toList ++
                List.replicate (i / 64 - n.limbs.size) 0).length := by
            simp [List.length_append, List.length_replicate]
            omega
          have h_idx_ge_left : n.limbs.toList.length ≤ j / 64 := hjleft
          have h_get :
              (n.limbs.toList ++ List.replicate (i / 64 - n.limbs.size) 0 ++
                  [((1 : UInt64) <<< UInt64.ofNat (i % 64))])[j / 64]'hjtop_lst
                = (0 : UInt64) := by
            rw [List.getElem_append_left h_idx_in_middle]
            rw [List.getElem_append_right h_idx_ge_left]
            exact List.getElem_replicate _
          rw [h_get]
          show (0 : UInt64).toNat.testBit (j % 64) = _
          rw [show ((0 : UInt64).toNat = 0) from rfl, Nat.zero_testBit]
          have h_ij : i ≠ j := by
            intro h; apply hji; rw [h]
          rw [decide_eq_false h_ij, Bool.or_false]
    · -- j / 64 > i / 64: out of range of the extended array and of n.
      rw [dite_eq_right hjtop_lst]
      push Not at hjtop_lst
      have hjtop : i / 64 + 1 ≤ j / 64 := h_len ▸ hjtop_lst
      have hjleft_not : ¬ j / 64 < n.limbs.toList.length := by
        rw [h_size_eq]; omega
      rw [dite_eq_right hjleft_not]
      have h_ij : i ≠ j := by
        intro h
        rw [h] at hjtop
        omega
      rw [decide_eq_false h_ij, Bool.or_false]

theorem setBit_ofNat (n i : Nat) : setBit (ofNat n) i = ofNat (n ||| 2 ^ i) := by
  apply toNat_injective
  rw [toNat_setBit, toNat_ofNat, toNat_ofNat]

end Azurite.AzNat
