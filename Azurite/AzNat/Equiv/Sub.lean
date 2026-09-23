/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Sub
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Compare
import Azurite.UInt64.Equiv.SubWithBorrow

namespace Azurite.AzNat

/-- `subLimb.go` preserves the prefix `[0, i)`. -/
theorem subLimb.go_toList_take (hi : Nat) (a : Array UInt64) (i : Nat)
    (borrow : UInt64) (h_size : hi ≤ a.size) :
    (subLimb.go hi a i borrow h_size).1.toList.take i = a.toList.take i := by
  induction hi_sub_i : hi - i generalizing a i borrow with
  | zero =>
    have h_ge : hi ≤ i := by omega
    rw [subLimb.go]
    by_cases hb : borrow = 0
    · simp [hb]
    · simp [hb, Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < hi := by omega
    have h_i_size : i < a.size := Nat.lt_of_lt_of_le h_lt h_size
    rw [subLimb.go]
    by_cases hb : borrow = 0
    · simp [hb]
    · simp only [hb, ↓reduceIte, h_lt, ↓reduceDIte]
      have h_rec : hi - (i + 1) = n := by omega
      set diff := a[i] - borrow with hdiff_def
      set newBorrow : UInt64 := if a[i] < borrow then 1 else 0 with hnb_def
      have h_take_succ : List.take i
          ((subLimb.go hi (a.set i diff) (i + 1) newBorrow
              (by rw [Array.size_set]; exact h_size)).1.toList.take (i + 1))
            = (subLimb.go hi (a.set i diff) (i + 1) newBorrow
                (by rw [Array.size_set]; exact h_size)).1.toList.take i := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
      rw [← h_take_succ, ih _ _ _ _ h_rec, List.take_take, Nat.min_eq_left (by omega)]
      rw [Array.toList_set, List.take_set]
      rw [List.set_eq_of_length_le]
      rw [List.length_take, Array.length_toList]
      omega

/-- `subLimb` preserves the prefix `[0, lo)`. -/
theorem subLimb_toList_take (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) :
    (subLimb a lo hi b hlo hhi).1.toList.take lo = a.toList.take lo :=
  subLimb.go_toList_take hi a lo b hhi

/-- Single-limb sub step: subtracting a borrow from a UInt64 produces a
    difference and a new borrow-out bit that together preserve the
    numerical value. -/
lemma limb_sub_step (x borrow : UInt64) :
    x.toNat + (if x < borrow then (1 : UInt64) else 0).toNat * 2 ^ 64
      = (x - borrow).toNat + borrow.toNat := by
  have hxlt : x.toNat < 2 ^ 64 := UInt64.toNat_lt x
  have hblt : borrow.toNat < 2 ^ 64 := UInt64.toNat_lt borrow
  have h_sub : (x - borrow).toNat = (2 ^ 64 - borrow.toNat + x.toNat) % 2 ^ 64 :=
    UInt64.toNat_sub x borrow
  have h_lt_iff : x < borrow ↔ x.toNat < borrow.toNat :=
    UInt64.lt_iff_toNat_lt
  by_cases h_uf : x < borrow
  · have h_lt : x.toNat < borrow.toNat := h_lt_iff.mp h_uf
    have h_mod : (2 ^ 64 - borrow.toNat + x.toNat) % 2 ^ 64
                  = 2 ^ 64 - borrow.toNat + x.toNat := by
      rw [Nat.mod_eq_of_lt]; omega
    simp only [h_uf, ↓reduceIte]
    show x.toNat + 1 * 2 ^ 64 = (x - borrow).toNat + borrow.toNat
    rw [h_sub, h_mod]; omega
  · have h_ge : borrow.toNat ≤ x.toNat := by
      by_contra h_lt
      push Not at h_lt
      exact h_uf (h_lt_iff.mpr h_lt)
    have h_mod : (2 ^ 64 - borrow.toNat + x.toNat) % 2 ^ 64
                  = x.toNat - borrow.toNat := by
      rw [show 2 ^ 64 - borrow.toNat + x.toNat
            = (x.toNat - borrow.toNat) + 1 * 2 ^ 64 from by omega]
      rw [Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [h_uf, ↓reduceIte]
    show x.toNat + 0 * 2 ^ 64 = (x - borrow).toNat + borrow.toNat
    rw [h_sub, h_mod]; omega

/-- Invariant of `subLimb.go`: starting from `(a, i, borrow)`, the original
    slice `[i, hi)` plus the incoming `borrow` equals the resulting modified
    slice plus the final borrow bit at position `hi`.  Valid whenever
    `borrow ≤ 1` or the loop can still advance. -/
private lemma subLimb.go_correct (hi : Nat) (a : Array UInt64) (i : Nat)
    (borrow : UInt64) (h_size : hi ≤ a.size)
    (hborrow : borrow.toNat ≤ 1 ∨ i < hi) :
    toNatLimbsList ((a.toList.drop i).take (hi - i))
        + (subLimb.go hi a i borrow h_size).2.toNat * 2 ^ (64 * (hi - i))
      = toNatLimbsList (((subLimb.go hi a i borrow h_size).1.toList.drop i).take (hi - i))
        + borrow.toNat := by
  induction hi_sub_i : hi - i generalizing a i borrow with
  | zero =>
    have h_ge : hi ≤ i := by omega
    by_cases hb : borrow = 0
    · have h_eq : subLimb.go hi a i borrow h_size = (a, false) := by
        conv_lhs => rw [subLimb.go]
        simp [hb]
      rw [h_eq, hb]
      simp [toNatLimbsList]
    · have h_borrow_ne : borrow.toNat ≠ 0 := by
        intro h
        exact hb (UInt64.toNat_inj.mp (show borrow.toNat = (0 : UInt64).toNat from h))
      have h_borrow_le : borrow.toNat ≤ 1 :=
        hborrow.resolve_right (fun h => absurd h (Nat.not_lt.mpr h_ge))
      have h_borrow_eq : borrow.toNat = 1 := by omega
      have h_eq : subLimb.go hi a i borrow h_size = (a, true) := by
        conv_lhs => rw [subLimb.go]
        simp [hb, Nat.not_lt.mpr h_ge]
      rw [h_eq]
      simp [toNatLimbsList, h_borrow_eq]
  | succ n ih =>
    have h_lt : i < hi := by omega
    have h_i_size : i < a.size := Nat.lt_of_lt_of_le h_lt h_size
    by_cases hb : borrow = 0
    · have h_eq : subLimb.go hi a i borrow h_size = (a, false) := by
        conv_lhs => rw [subLimb.go]
        simp [hb]
      rw [h_eq, hb]
      simp [toNatLimbsList]
    · set x := a[i] with hx_def
      set diff := x - borrow with hdiff_def
      set newBorrow : UInt64 := if x < borrow then 1 else 0 with hnb_def
      set a' := a.set i diff h_i_size with ha'_def
      have h_size' : hi ≤ a'.size := by rw [ha'_def, Array.size_set]; exact h_size
      have h_eq : subLimb.go hi a i borrow h_size
                  = subLimb.go hi a' (i + 1) newBorrow h_size' := by
        conv_lhs => rw [subLimb.go]
        simp [hb, h_lt, hx_def, hdiff_def, hnb_def, ha'_def]
      have h_rec : hi - (i + 1) = n := by omega
      have h_nb_le : newBorrow.toNat ≤ 1 := by
        rw [hnb_def]
        by_cases huf : x < borrow
        · simp [huf]
        · simp [huf]
      have h_ih := ih a' (i + 1) newBorrow h_size' (Or.inl h_nb_le) h_rec
      have h_limb : x.toNat + newBorrow.toNat * 2 ^ 64 = diff.toNat + borrow.toNat := by
        rw [hdiff_def, hnb_def]
        exact limb_sub_step x borrow
      have h_res_size :
          (subLimb.go hi a' (i + 1) newBorrow h_size').1.size = a.size := by
        rw [subLimb.go_size, ha'_def, Array.size_set]
      have h_res_i_size : i < (subLimb.go hi a' (i + 1) newBorrow h_size').1.size := by
        rw [h_res_size]; exact h_i_size
      have h_res_i : (subLimb.go hi a' (i + 1) newBorrow h_size').1[i]'h_res_i_size
                      = diff := by
        have h_prefix :=
          subLimb.go_toList_take hi a' (i + 1) newBorrow h_size'
        have h_len_L : ((subLimb.go hi a' (i + 1) newBorrow h_size').1.toList).length = a.size := by
          rw [Array.length_toList]; exact h_res_size
        have h_i_lt_L_take :
            i < ((subLimb.go hi a' (i + 1) newBorrow h_size').1.toList.take (i + 1)).length := by
          rw [List.length_take, h_len_L]; omega
        have h_i_lt_R_take : i < (a'.toList.take (i + 1)).length := by
          rw [List.length_take, Array.length_toList, ha'_def, Array.size_set]; omega
        have h_get_eq :
            ((subLimb.go hi a' (i + 1) newBorrow h_size').1.toList.take (i + 1))[i]'h_i_lt_L_take
              = (a'.toList.take (i + 1))[i]'h_i_lt_R_take := by
          congr 1
        rw [List.getElem_take, List.getElem_take] at h_get_eq
        rw [← Array.getElem_toList h_res_i_size, h_get_eq]
        have h_i_lt : i < (a.set i diff h_i_size).toList.length := by
          rw [Array.length_toList, Array.size_set]; exact h_i_size
        show (a.set i diff h_i_size).toList[i]'h_i_lt = diff
        simp [Array.toList_set, List.getElem_set_self]
      have h_drop_eq : a'.toList.drop (i + 1) = a.toList.drop (i + 1) := by
        rw [ha'_def, Array.toList_set, List.drop_set]; simp
      rw [h_eq]
      rw [show (n + 1) = hi - i from hi_sub_i.symm]
      rw [toNatLimbsList_take_succ (subLimb.go hi a' (i + 1) newBorrow h_size').1 i hi
            h_res_i_size h_lt]
      rw [h_res_i]
      rw [toNatLimbsList_take_succ a i hi h_i_size h_lt]
      have h_pow : (2 : Nat) ^ (64 * (hi - i))
                  = 2 ^ (64 * (hi - (i + 1))) * 2 ^ 64 := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [h_pow]
      rw [← h_drop_eq]
      rw [← h_rec] at h_ih
      set P := toNatLimbsList ((a'.toList.drop (i + 1)).take (hi - (i + 1))) with hP_def
      set Q := toNatLimbsList
          (((subLimb.go hi a' (i + 1) newBorrow h_size').1.toList.drop (i + 1)).take (hi - (i + 1)))
        with hQ_def
      set R := (subLimb.go hi a' (i + 1) newBorrow h_size').2.toNat with hR_def
      change x.toNat + P * 2 ^ 64 + R * (2 ^ (64 * (hi - (i + 1))) * 2 ^ 64)
           = diff.toNat + Q * 2 ^ 64 + borrow.toNat
      have h1 : x.toNat + P * 2 ^ 64 + R * (2 ^ (64 * (hi - (i + 1))) * 2 ^ 64)
              = x.toNat + (P + R * 2 ^ (64 * (hi - (i + 1)))) * 2 ^ 64 := by ring
      rw [h1, h_ih]
      have h2 : x.toNat + (Q + newBorrow.toNat) * 2 ^ 64
              = (x.toNat + newBorrow.toNat * 2 ^ 64) + Q * 2 ^ 64 := by ring
      rw [h2, h_limb]
      ring

/-- Correctness of `subLimb`: the original slice `[lo, hi)` plus `b` equals
    the modified slice plus the returned borrow at the top. -/
theorem subLimb_toNat (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) (h_lo_lt : lo < hi) :
    let (a', c) := subLimb a lo hi b hlo hhi
    toNatLimbsList ((a.toList.drop lo).take (hi - lo))
        + c.toNat * 2 ^ (64 * (hi - lo))
      = toNatLimbsList ((a'.toList.drop lo).take (hi - lo)) + b.toNat := by
  have h := subLimb.go_correct hi a lo b hhi (Or.inr h_lo_lt)
  exact h

/-! ### Correctness of `subSameLengthLimbs` -/

/-- `subSameLengthLimbs.go` preserves any prefix up to `loA + k`. -/
theorem subSameLengthLimbs.go_toList_take_le (b : Array UInt64) (loA loB len : Nat)
    (a : Array UInt64) (k : Nat) (borrow : Bool)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size)
    (m : Nat) (hm : m ≤ loA + k) :
    (subSameLengthLimbs.go b loA loB len a k borrow hA hB).1.toList.take m
      = a.toList.take m := by
  induction h_sub : len - k generalizing a k borrow with
  | zero =>
    have h_ge : len ≤ k := by omega
    rw [subSameLengthLimbs.go]
    simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : k < len := by omega
    have h_rec : len - (k + 1) = n := by omega
    rw [subSameLengthLimbs.go]
    simp only [h_lt, ↓reduceDIte]
    rw [ih _ _ _ _ (by omega) h_rec]
    rw [Array.toList_set, List.take_set_of_le (by omega)]

/-- `subSameLengthLimbs.go` preserves the prefix of `a` up to `loA + k`. -/
theorem subSameLengthLimbs.go_toList_take (b : Array UInt64) (loA loB len : Nat)
    (a : Array UInt64) (k : Nat) (borrow : Bool)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    (subSameLengthLimbs.go b loA loB len a k borrow hA hB).1.toList.take (loA + k)
      = a.toList.take (loA + k) :=
  subSameLengthLimbs.go_toList_take_le b loA loB len a k borrow hA hB (loA + k) (Nat.le_refl _)

/-- `subSameLengthLimbs.go` preserves the suffix of `a` from `loA + len`. -/
theorem subSameLengthLimbs.go_toList_drop (b : Array UInt64) (loA loB len : Nat)
    (a : Array UInt64) (k : Nat) (borrow : Bool)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    (subSameLengthLimbs.go b loA loB len a k borrow hA hB).1.toList.drop (loA + len)
      = a.toList.drop (loA + len) := by
  induction h_sub : len - k generalizing a k borrow with
  | zero =>
    have h_ge : len ≤ k := by omega
    rw [subSameLengthLimbs.go]
    simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : k < len := by omega
    rw [subSameLengthLimbs.go]
    simp only [h_lt, ↓reduceDIte]
    have h_rec : len - (k + 1) = n := by omega
    rw [ih _ _ _ _ h_rec]
    rw [Array.toList_set, List.drop_set]
    simp
    omega

/-- Invariant of `subSameLengthLimbs.go` at step `k`. -/
private lemma subSameLengthLimbs.go_correct (b : Array UInt64) (loA loB len : Nat)
    (a : Array UInt64) (k : Nat) (borrow : Bool)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    toNatLimbsList ((a.toList.drop (loA + k)).take (len - k))
      + (subSameLengthLimbs.go b loA loB len a k borrow hA hB).2.toNat * 2 ^ (64 * (len - k))
      = toNatLimbsList
          (((subSameLengthLimbs.go b loA loB len a k borrow hA hB).1.toList.drop (loA + k)).take
            (len - k))
        + toNatLimbsList ((b.toList.drop (loB + k)).take (len - k))
        + borrow.toNat := by
  induction h_sub : len - k generalizing a k borrow with
  | zero =>
    have h_ge : len ≤ k := by omega
    have h_eq : subSameLengthLimbs.go b loA loB len a k borrow hA hB = (a, borrow) := by
      rw [subSameLengthLimbs.go]
      simp [Nat.not_lt.mpr h_ge]
    rw [h_eq]
    simp [toNatLimbsList]
  | succ n ih =>
    have h_lt : k < len := by omega
    have h_iA : loA + k < a.size := by omega
    have h_iB : loB + k < b.size := by omega
    set swb := UInt64.subWithBorrow a[loA + k] b[loB + k] borrow with hswb_def
    set diff := swb.1 with hdiff_def
    set newBorrow := swb.2 with hnb_def
    set a' := a.set (loA + k) diff h_iA with ha'_def
    have hA' : loA + len ≤ a'.size := by rw [ha'_def, Array.size_set]; exact hA
    have h_eq : subSameLengthLimbs.go b loA loB len a k borrow hA hB
              = subSameLengthLimbs.go b loA loB len a' (k + 1) newBorrow hA' hB := by
      conv_lhs => rw [subSameLengthLimbs.go]
      simp [h_lt, hswb_def, hdiff_def, hnb_def, ha'_def]
    have h_rec : len - (k + 1) = n := by omega
    have h_ih := ih a' (k + 1) newBorrow hA' h_rec
    have h_swb := UInt64.subWithBorrow_eq a[loA + k] b[loB + k] borrow
    rw [← hswb_def] at h_swb
    have h_res_size :
        (subSameLengthLimbs.go b loA loB len a' (k + 1) newBorrow hA' hB).1.size = a.size := by
      rw [subSameLengthLimbs.go_size, ha'_def, Array.size_set]
    have h_res_iA_size :
        loA + k < (subSameLengthLimbs.go b loA loB len a' (k + 1) newBorrow hA' hB).1.size := by
      rw [h_res_size]; exact h_iA
    have h_res_i :
        (subSameLengthLimbs.go b loA loB len a' (k + 1) newBorrow hA' hB).1[loA + k]'h_res_iA_size
          = diff := by
      have h_prefix :=
        subSameLengthLimbs.go_toList_take b loA loB len a' (k + 1) newBorrow hA' hB
      have h_len_L :
          ((subSameLengthLimbs.go b loA loB len a' (k + 1) newBorrow hA' hB).1.toList).length
            = a.size := by rw [Array.length_toList]; exact h_res_size
      have h_i_lt_L_take :
          loA + k
            < ((subSameLengthLimbs.go b loA loB len a' (k + 1) newBorrow hA' hB).1.toList.take
                (loA + (k + 1))).length := by
        rw [List.length_take, h_len_L]; omega
      have h_i_lt_R_take : loA + k < (a'.toList.take (loA + (k + 1))).length := by
        rw [List.length_take, Array.length_toList, ha'_def, Array.size_set]; omega
      have h_get_eq :
          ((subSameLengthLimbs.go b loA loB len a' (k + 1) newBorrow hA' hB).1.toList.take
              (loA + (k + 1)))[loA + k]'h_i_lt_L_take
            = (a'.toList.take (loA + (k + 1)))[loA + k]'h_i_lt_R_take := by
        congr 1
      rw [List.getElem_take, List.getElem_take] at h_get_eq
      rw [← Array.getElem_toList h_res_iA_size, h_get_eq]
      have h_i_lt : loA + k < (a.set (loA + k) diff h_iA).toList.length := by
        rw [Array.length_toList, Array.size_set]; exact h_iA
      show (a.set (loA + k) diff h_iA).toList[loA + k]'h_i_lt = diff
      simp [Array.toList_set, List.getElem_set_self]
    have h_drop_eq : a'.toList.drop (loA + (k + 1)) = a.toList.drop (loA + (k + 1)) := by
      rw [ha'_def, Array.toList_set, List.drop_set]; simp
    rw [h_eq]
    have split_arr : ∀ (A : Array UInt64) (i m : Nat) (hi_size : i < A.size),
        toNatLimbsList ((A.toList.drop i).take (m + 1))
          = A[i].toNat + toNatLimbsList ((A.toList.drop (i + 1)).take m) * 2 ^ 64 := by
      intro A i m hi_size
      have h_lt_list : i < A.toList.length := hi_size
      rw [List.drop_eq_getElem_cons h_lt_list, List.take_succ_cons, toNatLimbsList_cons]
      rw [show A.toList[i] = A[i] from (Array.getElem_toList hi_size).symm]
      ring
    have h_len_split : len - k = (len - (k + 1)) + 1 := by omega
    rw [show (n + 1) = len - k from h_sub.symm, h_len_split]
    rw [split_arr
          (subSameLengthLimbs.go b loA loB len a' (k + 1) newBorrow hA' hB).1
          (loA + k) (len - (k + 1)) h_res_iA_size]
    rw [h_res_i]
    rw [split_arr a (loA + k) (len - (k + 1)) h_iA]
    rw [split_arr b (loB + k) (len - (k + 1)) h_iB]
    have h_pow : (2 : Nat) ^ (64 * ((len - (k + 1)) + 1))
                = 2 ^ (64 * (len - (k + 1))) * 2 ^ 64 := by
      rw [show 64 * ((len - (k + 1)) + 1) = 64 * (len - (k + 1)) + 64 from by ring, Nat.pow_add]
    rw [h_pow]
    rw [show loA + k + 1 = loA + (k + 1) from by ring]
    rw [show loB + k + 1 = loB + (k + 1) from by ring]
    rw [← h_drop_eq]
    rw [← h_rec] at h_ih
    set P := toNatLimbsList ((a'.toList.drop (loA + (k + 1))).take (len - (k + 1))) with hP_def
    set Q := toNatLimbsList
        (((subSameLengthLimbs.go b loA loB len a' (k + 1) newBorrow hA' hB).1.toList.drop
            (loA + (k + 1))).take (len - (k + 1))) with hQ_def
    set S := toNatLimbsList ((b.toList.drop (loB + (k + 1))).take (len - (k + 1))) with hS_def
    set R := (subSameLengthLimbs.go b loA loB len a' (k + 1) newBorrow hA' hB).2.toNat with hR_def
    change a[loA + k].toNat + P * 2 ^ 64 + R * (2 ^ (64 * (len - (k + 1))) * 2 ^ 64)
         = diff.toNat + Q * 2 ^ 64
           + (b[loB + k].toNat + S * 2 ^ 64) + borrow.toNat
    have h1 : a[loA + k].toNat + P * 2 ^ 64 + R * (2 ^ (64 * (len - (k + 1))) * 2 ^ 64)
            = a[loA + k].toNat + (P + R * 2 ^ (64 * (len - (k + 1)))) * 2 ^ 64 := by ring
    rw [h1, h_ih]
    have h_limb : a[loA + k].toNat + (if newBorrow then 1 else 0) * 2 ^ 64
                = diff.toNat + b[loB + k].toNat + (if borrow then 1 else 0) := by
      rw [hdiff_def, hnb_def]; omega
    have h_bN : newBorrow.toNat = (if newBorrow then 1 else 0) := by cases newBorrow <;> simp
    have h_b : borrow.toNat = (if borrow then 1 else 0) := by cases borrow <;> simp
    rw [h_bN, h_b]
    have goal_eq : a[loA + k].toNat + (Q + S + (if newBorrow = true then 1 else 0)) * 2 ^ 64
                = (a[loA + k].toNat + (if newBorrow = true then 1 else 0) * 2 ^ 64)
                  + Q * 2 ^ 64 + S * 2 ^ 64 := by ring
    rw [goal_eq, h_limb]
    ring

/-- Correctness of `subSameLengthLimbs`: original-`a` subrange plus final borrow at
    the top equals modified-`a` subrange plus `b` subrange. -/
theorem subSameLengthLimbs_toNat (a b : Array UInt64) (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    let (a', c) := subSameLengthLimbs a b loA loB len hA hB
    toNatLimbsList ((a.toList.drop loA).take len) + c.toNat * 2 ^ (64 * len)
      = toNatLimbsList ((a'.toList.drop loA).take len)
        + toNatLimbsList ((b.toList.drop loB).take len) := by
  have h := subSameLengthLimbs.go_correct b loA loB len a 0 false hA hB
  simpa [subSameLengthLimbs] using h

/-! ### Correctness of `subGeqLimbs` -/

/-- Correctness of `subGeqLimbs`: agrees with `Nat` subtraction over the slices. -/
theorem subGeqLimbs_toNat (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (h_ge : lenB ≤ lenA) (h_posA : 0 < lenA) (h_posB : 0 < lenB) :
    let (a', c) := subGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB
    toNatLimbsList ((a.toList.drop loA).take lenA) + c.toNat * 2 ^ (64 * lenA)
      = toNatLimbsList ((a'.toList.drop loA).take lenA)
        + toNatLimbsList ((b.toList.drop loB).take lenB) := by
  set lo := subSameLengthLimbs a b loA loB lenB (by omega) hB with hlo_def
  have h_lo_size : lo.1.size = a.size := by
    rw [hlo_def]; exact subSameLengthLimbs_size a b loA loB lenB _ _
  have h_unfold : subGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB =
      if lo.2 then subLimb lo.1 (loA + lenB) (loA + lenA) 1 (by omega)
                    (by rw [h_lo_size]; exact hA)
              else (lo.1, false) := rfl
  show toNatLimbsList ((a.toList.drop loA).take lenA)
        + (subGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB).2.toNat * 2 ^ (64 * lenA)
      = toNatLimbsList ((((subGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB).1.toList).drop loA).take lenA)
        + toNatLimbsList ((b.toList.drop loB).take lenB)
  rw [h_unfold]
  have h_low := subSameLengthLimbs_toNat a b loA loB lenB (by omega) hB
  rw [← hlo_def] at h_low
  simp only at h_low
  -- High slice of lo.1 is unchanged
  have h_high_unchanged :
      (lo.1.toList.drop (loA + lenB)).take (lenA - lenB)
        = (a.toList.drop (loA + lenB)).take (lenA - lenB) := by
    rw [hlo_def]
    show (((subSameLengthLimbs.go b loA loB lenB a 0 false _ _).1.toList).drop _).take _ = _
    have h_drop_eq :
        (subSameLengthLimbs.go b loA loB lenB a 0 false (by omega) hB).1.toList.drop
            (loA + lenB)
          = a.toList.drop (loA + lenB) :=
      subSameLengthLimbs.go_toList_drop b loA loB lenB a 0 false (by omega) hB
    rw [h_drop_eq]
  by_cases h_lt : lenB < lenA
  swap
  · have h_eq : lenA = lenB := by omega
    have h_subLimb_empty : subLimb lo.1 (loA + lenB) (loA + lenA) 1 (by omega)
                           (by rw [h_lo_size]; exact hA) = (lo.1, true) := by
      unfold subLimb subLimb.go
      simp [show ¬ (loA + lenB < loA + lenA) from by omega]
    have h_result :
        (if lo.2 then subLimb lo.1 (loA + lenB) (loA + lenA) 1 (by omega)
                        (by rw [h_lo_size]; exact hA) else (lo.1, false))
          = (lo.1, lo.2) := by
      by_cases hc : lo.2 = true
      · rw [ite_eq_left hc, h_subLimb_empty, hc]
      · have hcf : lo.2 = false := by cases h : lo.2 <;> simp_all
        rw [hcf]; rfl
    rw [h_result]
    rw [h_eq]
    exact h_low
  rw [toNatLimbsList_drop_take_split a loA lenA lenB h_ge hA]
  by_cases hc : lo.2 = true
  · simp only [hc, ↓reduceIte]
    set hi := subLimb lo.1 (loA + lenB) (loA + lenA) 1
              (by omega) (by rw [h_lo_size]; exact hA) with hhi_def
    have h_high := subLimb_toNat lo.1 (loA + lenB) (loA + lenA) 1 (by omega)
                    (by rw [h_lo_size]; exact hA) (by omega)
    rw [← hhi_def] at h_high
    simp only at h_high
    have h_len_sub : loA + lenA - (loA + lenB) = lenA - lenB := by omega
    rw [h_len_sub] at h_high
    have h_hi_low :
        (hi.1.toList.drop loA).take lenB = (lo.1.toList.drop loA).take lenB := by
      have h_take :=
        subLimb_toList_take lo.1 (loA + lenB) (loA + lenA) 1
          (by omega) (by rw [h_lo_size]; exact hA)
      rw [← hhi_def] at h_take
      rw [show lenB = (loA + lenB) - loA from by omega,
          ← List.drop_take, ← List.drop_take, h_take]
    have h_hi_size : hi.1.size = a.size := by
      rw [hhi_def, subLimb_size, h_lo_size]
    rw [toNatLimbsList_drop_take_split hi.1 loA lenA lenB h_ge (by rw [h_hi_size]; exact hA)]
    rw [h_hi_low]
    have h_pow : (2 : Nat) ^ (64 * lenA)
                = 2 ^ (64 * (lenA - lenB)) * 2 ^ (64 * lenB) := by
      rw [← Nat.pow_add]; congr 1
      rw [show 64 * (lenA - lenB) + 64 * lenB = 64 * lenA from by
        rw [← Nat.mul_add]; congr 1; omega]
    rw [h_pow]
    have h1_toNat : (1 : UInt64).toNat = 1 := rfl
    rw [h1_toNat] at h_high
    have h_lo_borrow : lo.2.toNat = 1 := by rw [hc]; rfl
    rw [h_lo_borrow] at h_low
    set L1 := toNatLimbsList ((hi.1.toList.drop (loA + lenB)).take (lenA - lenB)) with hL1
    set L2 := toNatLimbsList ((lo.1.toList.drop (loA + lenB)).take (lenA - lenB)) with hL2
    set Lalow := toNatLimbsList ((lo.1.toList.drop loA).take lenB) with hLalow
    set Aorig := toNatLimbsList ((a.toList.drop loA).take lenB) with hAorig
    set Ahi := toNatLimbsList ((a.toList.drop (loA + lenB)).take (lenA - lenB)) with hAhi
    set Bs := toNatLimbsList ((b.toList.drop loB).take lenB) with hBs
    have hL2_eq : L2 = Ahi := by rw [hL2, hAhi, h_high_unchanged]
    rw [hL2_eq] at h_high
    -- h_low : Aorig + 1 * 2^(64*lenB) = Lalow + Bs
    -- h_high : Ahi + hi.2.toNat * 2^(64*(lenA-lenB)) = L1 + 1
    -- Goal: Aorig + Ahi * 2^(64*lenB) + hi.2.toNat * (2^(64*(lenA-lenB)) * 2^(64*lenB))
    --       = Lalow + L1 * 2^(64*lenB) + Bs
    have step1 :
        Aorig + Ahi * 2 ^ (64 * lenB) + hi.2.toNat * (2 ^ (64 * (lenA - lenB)) * 2 ^ (64 * lenB))
          = Aorig + (Ahi + hi.2.toNat * 2 ^ (64 * (lenA - lenB))) * 2 ^ (64 * lenB) := by ring
    rw [step1, h_high]
    have step2 :
        Aorig + (L1 + 1) * 2 ^ (64 * lenB)
          = (Aorig + 1 * 2 ^ (64 * lenB)) + L1 * 2 ^ (64 * lenB) := by ring
    rw [step2, h_low]
    ring
  · have hc' : lo.2 = false := by cases h : lo.2 <;> simp_all
    simp only [hc', Bool.false_eq_true, ↓reduceIte]
    rw [toNatLimbsList_drop_take_split lo.1 loA lenA lenB h_ge (by rw [h_lo_size]; exact hA)]
    have h_low_low :
        toNatLimbsList ((lo.1.toList.drop (loA + lenB)).take (lenA - lenB))
          = toNatLimbsList ((a.toList.drop (loA + lenB)).take (lenA - lenB)) := by
      rw [h_high_unchanged]
    rw [h_low_low]
    rw [hc'] at h_low
    have h_zero : (false : Bool).toNat = 0 := rfl
    rw [h_zero] at h_low
    simp only [Nat.zero_mul, Nat.add_zero] at h_low
    rw [h_low, h_zero]
    ring

/-- Auxiliary: `subSameLengthLimbs.go` starting at step `k` with any incoming
    borrow produces a result whose suffix from `loA + k` is bounded by the input's
    suffix, provided the final borrow is 0.  This is the core inductive step:
    `go_correct` gives `A_high + 0*β = R_high + B_high + borrow`, hence
    `R_high ≤ A_high`. -/
private theorem subSameLengthLimbs.go_high_le (b : Array UInt64) (loA loB len : Nat)
    (a : Array UInt64) (k : Nat) (borrow : Bool)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size)
    (h_no_borrow : (subSameLengthLimbs.go b loA loB len a k borrow hA hB).2 = false) :
    toNatLimbsList (((subSameLengthLimbs.go b loA loB len a k borrow hA hB).1.toList.drop
        (loA + k)).take (len - k))
      ≤ toNatLimbsList ((a.toList.drop (loA + k)).take (len - k)) := by
  have h := subSameLengthLimbs.go_correct b loA loB len a k borrow hA hB
  rw [h_no_borrow] at h; simp at h
  -- h : sliceVal a (loA+k) (len-k) = sliceVal result (loA+k) (len-k) + B_high + borrow
  omega

/-- When `subSameLengthLimbs` produces no final borrow, the high portion
    of the result (from position `loA + split` onward) is bounded by the
    corresponding portion of the original array.

    For `split = 0` this follows directly from `subSameLengthLimbs_toNat`.
    For `split > 0`, positions `[loA + split, loA + len)` of the intermediate
    array at step `split` agree with the original (only positions below `split`
    have been modified), so `go_high_le` applied at step `split` gives the bound. -/
theorem subSameLengthLimbs_high_le (a b : Array UInt64) (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size)
    (split : Nat) (h_split : split ≤ len)
    (h_no_borrow : (subSameLengthLimbs a b loA loB len hA hB).2 = false) :
    toNatLimbsList (((subSameLengthLimbs a b loA loB len hA hB).1.toList.drop
        (loA + split)).take (len - split))
      ≤ toNatLimbsList ((a.toList.drop (loA + split)).take (len - split)) := by
  -- `subSameLengthLimbs a b loA loB len hA hB = go b loA loB len a 0 false hA hB`.
  -- We proceed by induction on `split`, peeling one step at a time.
  -- At step `split`, the intermediate array's suffix [loA+split, loA+len)
  -- equals the original `a`'s suffix (since only positions < loA+split have been set).
  -- Then `go_high_le` at step `split` gives the result.
  unfold subSameLengthLimbs at h_no_borrow ⊢
  -- We need to show: going from step 0, the suffix from loA+split is ≤ original.
  -- Strategy: peel off `split` steps and use go_high_le on the tail.
  induction split generalizing a with
  | zero =>
    -- split = 0: directly use go_high_le at step 0.
    exact subSameLengthLimbs.go_high_le b loA loB len a 0 false hA hB h_no_borrow
  | succ s ih =>
    -- Need: s+1 ≤ len.
    have h_lt : s < len := by omega
    -- Unfold one step of go: processes position loA+0, recurses at step 1.
    -- Actually, we unfold `s+1` steps total. The key is that go at step 0
    -- processes position loA, sets a[loA] to the diff, then calls go at step 1
    -- on the modified array. After `s+1` steps, positions [loA+s+1, loA+len)
    -- in the intermediate array are unchanged from `a`.
    --
    -- Rather than manually unfolding, use the fact that:
    -- (1) The final result (go a 0 false) at positions [loA+s+1, loA+len) equals
    --     the result of (go intermediate (s+1) carry_s_plus_1) at those positions.
    -- (2) The intermediate array has [loA+s+1, loA+len) = a's [loA+s+1, loA+len).
    -- (3) `go_high_le` at step s+1 gives the bound.
    --
    -- But this requires decomposing the go call. Instead, use the simpler fact:
    -- The final output's suffix from loA+len is the same as a's (go_toList_drop),
    -- and we can use `go_correct` at step 0 (the full conservation) plus
    -- the observation that `go_get_outside` preserves positions outside [loA, loA+len).
    -- The suffix from (loA+s+1) includes positions INSIDE the modified range.
    --
    -- Cleanest approach: prove the result from go_correct directly.
    -- go_correct at step 0 gives: A + 0 = R + B + 0 (borrow_in=false, borrow_out=false).
    -- Split everything at position s+1:
    --   A = A_lo + A_hi * β^(s+1)
    --   R = R_lo + R_hi * β^(s+1)
    --   B = B_lo + B_hi * β^(s+1)
    -- where all "lo" parts are (s+1)-limb values and "hi" parts are (len-s-1)-limb values.
    -- From A = R + B:
    --   A_lo + A_hi * β^(s+1) = R_lo + R_hi * β^(s+1) + B_lo + B_hi * β^(s+1)
    -- Group: (A_hi - R_hi - B_hi) * β^(s+1) = R_lo + B_lo - A_lo
    -- The RHS is bounded: R_lo, B_lo, A_lo < β^(s+1).
    -- If A_hi - R_hi - B_hi ≥ 1: LHS ≥ β^(s+1) but RHS < 2*β^(s+1). So it's 0 or 1.
    -- Actually: from A = R + B: A_hi * β + A_lo = (R_hi + B_hi) * β + (R_lo + B_lo).
    -- Since R_lo + B_lo < 2*β^(s+1), we can write R_lo + B_lo = carry * β^(s+1) + rem
    -- where carry ∈ {0, 1} and rem < β^(s+1).
    -- Then: A_hi * β + A_lo = (R_hi + B_hi + carry) * β^(s+1) + rem.
    -- Since A_lo < β^(s+1) and rem < β^(s+1): A_lo = rem and A_hi = R_hi + B_hi + carry.
    -- Therefore: R_hi = A_hi - B_hi - carry ≤ A_hi (since B_hi ≥ 0, carry ≥ 0).
    --
    -- This is the argument! Let me formalize it.
    have h := subSameLengthLimbs.go_correct b loA loB len a 0 false hA hB
    rw [h_no_borrow] at h; simp at h
    -- h : sliceVal a loA len = sliceVal result loA len + sliceVal b loB len
    -- Now we need the suffix bound. Use toNatLimbsList split lemmas.
    -- Let's denote the result as `res`.
    set res := (subSameLengthLimbs.go b loA loB len a 0 false hA hB).1
    have h_res_size : res.size = a.size := subSameLengthLimbs.go_size b loA loB len a 0 false hA hB
    -- Split a at position s+1.
    have h_split_a := toNatLimbsList_drop_take_split a loA len (s + 1) h_split hA
    -- Split res at position s+1.
    have h_split_r := toNatLimbsList_drop_take_split res loA len (s + 1) h_split
      (by rw [h_res_size]; exact hA)
    -- Split b at position s+1 (using min(s+1, len) = s+1 since s+1 ≤ len).
    have h_split_b := toNatLimbsList_drop_take_split b loB len (s + 1) h_split hB
    rw [h_split_a, h_split_r, h_split_b] at h
    -- h now has the form: A_lo + A_hi * β = (R_lo + R_hi * β) + (B_lo + B_hi * β)
    -- where β = 2^(64*(s+1)).
    -- Extract: A_hi = R_hi + B_hi + (R_lo + B_lo - A_lo) / β^(s+1)
    -- Since all terms are Nat and the equation holds, we can derive R_hi ≤ A_hi.
    -- The "carry" (R_lo + B_lo - A_lo) / β^(s+1) is ≥ 0, so:
    -- A_hi * β^(s+1) ≥ R_hi * β^(s+1) + B_hi * β^(s+1)
    -- iff A_hi ≥ R_hi + B_hi ≥ R_hi.
    -- But this is wrong: in Nat arithmetic, A_lo + A_hi * β = R_lo + R_hi * β + B_lo + B_hi * β
    -- doesn't directly give A_hi ≥ R_hi.
    -- The correct deduction: since the equation holds in Nat:
    --   A_hi * β = R_hi * β + B_hi * β + (R_lo + B_lo - A_lo) (where RHS term could be negative)
    -- In Nat: A_lo + A_hi * β = R_lo + B_lo + (R_hi + B_hi) * β
    -- So: A_hi * β - (R_hi + B_hi) * β = R_lo + B_lo - A_lo
    -- (A_hi - R_hi - B_hi) * β = R_lo + B_lo - A_lo
    -- If A_hi < R_hi + B_hi: LHS < 0 in integers, impossible in Nat.
    -- Actually in Nat subtraction: if A_hi < R_hi + B_hi, then
    --   A_lo + A_hi * β < R_lo + B_lo + (R_hi + B_hi) * β which contradicts h.
    -- So A_hi ≥ R_hi + B_hi ≥ R_hi.
    have h_β_pos : 0 < 2 ^ (64 * (s + 1)) := Nat.two_pow_pos _
    -- From h: A_lo + A_hi * β = R_lo + R_hi * β + B_lo + B_hi * β
    -- Rewrite: A_hi * β = R_hi * β + B_hi * β + (R_lo + B_lo - A_lo)
    -- Since this is Nat equality: A_hi * β ≥ (R_hi + B_hi) * β
    -- (because R_lo + B_lo ≥ A_lo follows from the rearrangement being non-negative in Nat)
    -- Actually: from h, (R_hi + B_hi) * β ≤ (R_hi + B_hi) * β + R_lo + B_lo
    --           = A_lo + A_hi * β ≤ A_hi * β + β (since A_lo < β^(s+1) = β)
    -- Hmm, not quite. Let me just use nlinarith with the right supporting facts.
    set β := 2 ^ (64 * (s + 1))
    set A_hi := toNatLimbsList ((a.toList.drop (loA + (s + 1))).take (len - (s + 1)))
    set R_hi := toNatLimbsList ((res.toList.drop (loA + (s + 1))).take (len - (s + 1)))
    set B_hi := toNatLimbsList ((b.toList.drop (loB + (s + 1))).take (len - (s + 1)))
    set A_lo := toNatLimbsList ((a.toList.drop loA).take (s + 1))
    set R_lo := toNatLimbsList ((res.toList.drop loA).take (s + 1))
    set B_lo := toNatLimbsList ((b.toList.drop loB).take (s + 1))
    -- h : A_lo + A_hi * β = R_lo + R_hi * β + (B_lo + B_hi * β)
    -- From h: (R_hi + B_hi) * β ≤ A_lo + A_hi * β (since R_lo + B_lo ≥ 0... wait
    -- the equation says A_lo + A_hi * β = R_lo + R_hi * β + B_lo + B_hi * β)
    -- So: (R_hi + B_hi) * β = A_lo + A_hi * β - R_lo - B_lo ≤ A_hi * β + A_lo
    -- But (R_hi + B_hi) * β ≤ A_hi * β + A_lo < A_hi * β + β = (A_hi + 1) * β
    -- So (R_hi + B_hi) < A_hi + 1, i.e., R_hi + B_hi ≤ A_hi.
    -- Therefore R_hi ≤ A_hi. QED.
    have h_A_lo_lt : A_lo < β := by
      have ht := toNatLimbsList_lt_pow ((a.toList.drop loA).take (s + 1))
      have h_len : ((a.toList.drop loA).take (s + 1)).length = s + 1 := by
        rw [List.length_take, List.length_drop, Array.length_toList]; omega
      rw [h_len] at ht; exact ht
    -- From h: A_lo + A_hi * β = R_lo + R_hi * β + (B_lo + B_hi * β)
    -- Rearrange: R_hi * β + B_hi * β ≤ A_hi * β + A_lo < (A_hi + 1) * β
    -- Hence (R_hi + B_hi) * β < (A_hi + 1) * β, giving R_hi + B_hi ≤ A_hi.
    suffices h_le : R_hi + B_hi ≤ A_hi by omega
    by_contra h_neg
    push Not at h_neg
    -- R_hi + B_hi ≥ A_hi + 1, so (R_hi + B_hi) * β ≥ (A_hi + 1) * β > A_hi * β + A_lo
    have h1 : (A_hi + 1) * β ≤ (R_hi + B_hi) * β :=
      Nat.mul_le_mul_right β h_neg
    have h2 : A_lo + A_hi * β < (A_hi + 1) * β := by
      calc A_lo + A_hi * β < β + A_hi * β := by omega
        _ = (A_hi + 1) * β := by ring
    -- But from h: (R_hi + B_hi) * β ≤ R_lo + R_hi * β + (B_lo + B_hi * β) = A_lo + A_hi * β
    have h3 : (R_hi + B_hi) * β ≤ A_lo + A_hi * β := by
      have : (R_hi + B_hi) * β = R_hi * β + B_hi * β := Nat.add_mul R_hi B_hi β
      omega
    omega

/-- When `subGeqLimbs` produces no final borrow, the high portion of the
    result (from position `loA + split` onward, within the full `lenA`
    range) is bounded by the corresponding portion of the original array.

    This extends `subSameLengthLimbs_high_le` to handle the borrow
    propagation phase (via `subLimb`) that occurs when `lenB < lenA`. -/
theorem subGeqLimbs_high_le (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (h_ge : lenB ≤ lenA) (h_posA : 0 < lenA) (h_posB : 0 < lenB)
    (split : Nat) (h_split : split ≤ lenA)
    (h_no_borrow : (subGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB).2 = false) :
    toNatLimbsList (((subGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB).1.toList.drop
        (loA + split)).take (lenA - split))
      ≤ toNatLimbsList ((a.toList.drop (loA + split)).take (lenA - split)) := by
  -- From subGeqLimbs_toNat with borrow = 0:
  --   sliceVal a loA lenA = sliceVal result loA lenA + sliceVal b loB lenB
  -- Decompose at split using the same argument as subSameLengthLimbs_high_le.
  have h := subGeqLimbs_toNat a b loA lenA loB lenB hA hB h_ge h_posA h_posB
  simp only at h
  rw [h_no_borrow] at h; simp at h
  -- h : sliceVal a loA lenA = sliceVal result loA lenA + sliceVal b loB lenB
  set res := (subGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB).1
  have h_res_size : res.size = a.size := subGeqLimbs_size a b loA lenA loB lenB hA hB h_ge h_posA h_posB
  rcases Nat.eq_or_lt_of_le (Nat.zero_le split) with h0 | h_pos
  · -- split = 0: directly from h.
    subst h0; simp at h ⊢; omega
  · -- split > 0: decompose at split.
    have h_split_a := toNatLimbsList_drop_take_split a loA lenA split h_split hA
    have h_split_r := toNatLimbsList_drop_take_split res loA lenA split h_split
      (by rw [h_res_size]; exact hA)
    rw [h_split_a, h_split_r] at h
    set β := 2 ^ (64 * split)
    set A_hi := toNatLimbsList ((a.toList.drop (loA + split)).take (lenA - split))
    set R_hi := toNatLimbsList ((res.toList.drop (loA + split)).take (lenA - split))
    set A_lo := toNatLimbsList ((a.toList.drop loA).take split)
    set R_lo := toNatLimbsList ((res.toList.drop loA).take split)
    set B := toNatLimbsList ((b.toList.drop loB).take lenB)
    -- h : A_lo + A_hi * β = R_lo + R_hi * β + B
    have h_A_lo_lt : A_lo < β := by
      have ht := toNatLimbsList_lt_pow ((a.toList.drop loA).take split)
      have h_len : ((a.toList.drop loA).take split).length = split := by
        rw [List.length_take, List.length_drop, Array.length_toList]; omega
      rw [h_len] at ht; exact ht
    -- Same argument: (R_hi) * β ≤ (R_hi + B/β?) * β ≤ A_hi * β + A_lo < (A_hi + 1) * β
    -- More directly: R_hi * β ≤ R_lo + R_hi * β ≤ R_lo + R_hi * β + B = A_lo + A_hi * β < β + A_hi * β
    suffices h_le : R_hi ≤ A_hi by omega
    by_contra h_neg
    push Not at h_neg
    -- R_hi ≥ A_hi + 1
    have h1 : (A_hi + 1) * β ≤ R_hi * β := Nat.mul_le_mul_right β h_neg
    have h2 : A_lo + A_hi * β < (A_hi + 1) * β := by
      calc A_lo + A_hi * β < β + A_hi * β := by omega
        _ = (A_hi + 1) * β := by ring
    -- But R_hi * β ≤ R_lo + R_hi * β + B = A_lo + A_hi * β
    have h3 : R_hi * β ≤ A_lo + A_hi * β := by omega
    omega

/-- Correctness of `AzNat.subUInt64`: agrees with truncated `Nat` subtraction. -/
theorem toNat_subUInt64 (a : AzNat) (b : UInt64) :
    (a.subUInt64 b).toNat = a.toNat - b.toNat := by
  unfold subUInt64
  by_cases hsz : a.limbs.size = 0
  · have h_nil : a.limbs.toList = [] := by
      have : a.limbs.toList.length = 0 := hsz
      exact List.length_eq_zero_iff.mp this
    have h_a_zero : a.toNat = 0 := by
      show toNatLimbsList a.limbs.toList = 0
      rw [h_nil]; rfl
    simp [hsz, h_a_zero]
  · simp only [hsz, ↓reduceIte]
    set n := a.limbs.size with hn_def
    have h_pos : 0 < n := Nat.pos_of_ne_zero hsz
    have h_size : (subLimb a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _)).1.size = n :=
      subLimb_size a.limbs 0 n b _ _
    have h_main := subLimb_toNat a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _) h_pos
    simp only [List.drop_zero, Nat.sub_zero] at h_main
    have h_take_arr : a.limbs.toList.take n = a.limbs.toList := by
      rw [List.take_of_length_le]; rw [Array.length_toList]
    have h_take_r : (subLimb a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _)).1.toList.take n
                  = (subLimb a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _)).1.toList := by
      rw [List.take_of_length_le]; rw [Array.length_toList, h_size]
    rw [h_take_arr, h_take_r] at h_main
    set r := subLimb a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _)
    have h_a : a.toNat = toNatLimbsList a.limbs.toList := rfl
    have h_r_lt : toNatLimbsList r.1.toList < 2 ^ (64 * n) := by
      have ht := toNatLimbsList_lt_pow r.1.toList
      rw [Array.length_toList, h_size] at ht
      exact ht
    rcases hc : r.2 with _ | _
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [toNat_ofLimbs]
      rw [hc] at h_main
      simp at h_main
      rw [h_a]; omega
    · simp only [↓reduceIte]
      rw [hc] at h_main
      change toNatLimbsList a.limbs.toList + 1 * 2 ^ (64 * n) = _ + b.toNat at h_main
      show (0 : AzNat).toNat = a.toNat - b.toNat
      have h0 : (0 : AzNat).toNat = 0 := rfl
      rw [h0, h_a]; omega

/-- Correctness of `AzNat.sub`: agrees with truncated `Nat` subtraction. -/
theorem toNat_sub (a b : AzNat) : (a - b).toNat = a.toNat - b.toNat := by
  show (sub a b).toNat = a.toNat - b.toNat
  unfold sub
  by_cases ha : a.limbs.size = 0
  · simp only [ha, ↓reduceDIte]
    have h_a_zero : a.toNat = 0 := by
      show toNatLimbsList a.limbs.toList = 0
      have : a.limbs.toList = [] :=
        List.length_eq_zero_iff.mp (by rw [Array.length_toList]; exact ha)
      rw [this]; rfl
    rw [h_a_zero]; show (0 : AzNat).toNat = 0 - b.toNat; simp
  · simp only [ha, ↓reduceDIte]
    by_cases hb : b.limbs.size = 0
    · simp only [hb, ↓reduceDIte]
      have h_b_zero : b.toNat = 0 := by
        show toNatLimbsList b.limbs.toList = 0
        have : b.limbs.toList = [] :=
          List.length_eq_zero_iff.mp (by rw [Array.length_toList]; exact hb)
        rw [this]; rfl
      rw [h_b_zero, Nat.sub_zero]
    · simp only [hb, ↓reduceDIte]
      by_cases hgt : b.limbs.size > a.limbs.size
      · simp only [hgt, ↓reduceDIte]
        have h_alt : a.toNat < b.toNat := by
          have ha_lt := toNatLimbsList_lt_pow a.limbs.toList
          rw [Array.length_toList] at ha_lt
          have hb_not_empty : b.limbs.toList ≠ [] := by
            intro h_empty
            have : b.limbs.toList.length = 0 := by rw [h_empty]; rfl
            rw [Array.length_toList] at this
            exact hb this
          have hbl : b.limbs.toList.getLast? ≠ some 0 := by
            have := b.last_ne_zero
            rw [← Array.getLast?_toList] at this
            exact this
          have hb_ge := pow_le_toNatLimbsList b.limbs.toList hb_not_empty hbl
          rw [Array.length_toList] at hb_ge
          have h_le : a.limbs.size ≤ b.limbs.size - 1 := by omega
          have h_pow_le : 2 ^ (64 * a.limbs.size) ≤ 2 ^ (64 * (b.limbs.size - 1)) :=
            Nat.pow_le_pow_right (by decide) (by omega)
          show toNatLimbsList a.limbs.toList < toNatLimbsList b.limbs.toList
          omega
        show (0 : AzNat).toNat = a.toNat - b.toNat
        have h0 : (0 : AzNat).toNat = 0 := rfl
        rw [h0]; omega
      · simp only [hgt, ↓reduceDIte]
        have h_ge : b.limbs.size ≤ a.limbs.size := Nat.not_lt.mp hgt
        have h_posA : 0 < a.limbs.size := Nat.pos_of_ne_zero ha
        have h_posB : 0 < b.limbs.size := Nat.pos_of_ne_zero hb
        set r := subGeqLimbs a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size
                  (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _)
                  h_ge h_posA h_posB with hr_def
        have h_main := subGeqLimbs_toNat a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size
                        (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _)
                        h_ge h_posA h_posB
        rw [← hr_def] at h_main
        simp only [List.drop_zero] at h_main
        have h_r_size : r.1.size = a.limbs.size := by
          rw [hr_def]
          exact subGeqLimbs_size a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size _ _ _ _ _
        have h_take_r : r.1.toList.take a.limbs.size = r.1.toList := by
          rw [List.take_of_length_le]; rw [Array.length_toList, h_r_size]
        have h_take_a : a.limbs.toList.take a.limbs.size = a.limbs.toList := by
          rw [List.take_of_length_le]; rw [Array.length_toList]
        have h_take_b : b.limbs.toList.take b.limbs.size = b.limbs.toList := by
          rw [List.take_of_length_le]; rw [Array.length_toList]
        rw [h_take_r, h_take_a, h_take_b] at h_main
        have h_a_eq : a.toNat = toNatLimbsList a.limbs.toList := rfl
        have h_b_eq : b.toNat = toNatLimbsList b.limbs.toList := rfl
        have h_r_lt : toNatLimbsList r.1.toList < 2 ^ (64 * a.limbs.size) := by
          have ht := toNatLimbsList_lt_pow r.1.toList
          rw [Array.length_toList, h_r_size] at ht
          exact ht
        rcases hc : r.2 with _ | _
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [toNat_ofLimbs]
          rw [hc] at h_main
          simp at h_main
          rw [h_a_eq, h_b_eq]; omega
        · simp only [↓reduceIte]
          rw [hc] at h_main
          change toNatLimbsList a.limbs.toList + 1 * 2 ^ (64 * a.limbs.size)
                  = _ + toNatLimbsList b.limbs.toList at h_main
          show (0 : AzNat).toNat = a.toNat - b.toNat
          have h0 : (0 : AzNat).toNat = 0 := rfl
          rw [h0, h_a_eq, h_b_eq]; omega

/-- `ofNat`-version of `toNat_subUInt64`. -/
theorem ofNat_subUInt64 (n : Nat) (b : UInt64) :
    ofNat (n - b.toNat) = (ofNat n).subUInt64 b := by
  apply toNat_injective
  rw [toNat_ofNat, toNat_subUInt64, toNat_ofNat]

/-- `ofNat`-version of `toNat_sub`. -/
theorem ofNat_sub (m n : Nat) : ofNat (m - n) = ofNat m - ofNat n := by
  apply toNat_injective
  rw [toNat_ofNat, toNat_sub, toNat_ofNat, toNat_ofNat]

end Azurite.AzNat
