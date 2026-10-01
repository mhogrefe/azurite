/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul.Karatsuba
import Azurite.AzNat.Equiv.Mul.Basic
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Sub

/-!
# Correctness of `karatsubaMulLimbs`

This file proves `karatsubaMulLimbs_toNat`: the Karatsuba implementation
agrees with multiplication of the corresponding limb-slice integers.

The proof structure mirrors Theorem 1.2 of *Modern Computer Arithmetic*:
writing `s_X` for the sign of `X₀ - X₁` (treated as an integer),
`s_A · |A₀ − A₁| = A₀ − A₁` and similarly for `B`, hence
`s_A s_B · |A₀ − A₁| · |B₀ − B₁| = (A₀ − A₁)(B₀ − B₁)`,
so the middle term `C₀ + C₁ − s_A s_B · C₂` simplifies to
`A₀ B₁ + A₁ B₀`, and the assembled result equals
`A₀ B₀ + (A₀ B₁ + A₁ B₀) β^k + A₁ B₁ β^{2k} = A · B`.

## Proof outline (`karatsubaMulLimbs_toNat`)

By strong induction on `len`:

* **Base case** (`len < max 2 threshold`): direct application of
  `schoolbookMulLimbs_toNat`.
* **Recursive case**:
  - Let `k = ⌈len/2⌉`, `m = len - k`, so `k + m = len` and `m ≤ k`.
  - Set `A = toNat ((a.drop loA).take len)`, `B = toNat ((b.drop loB).take len)`,
    and the half-slice values `A₀, A₁, B₀, B₁` similarly.
    By `toNat_slice_split`, `A = A₀ + A₁ β^k` and `B = B₀ + B₁ β^k`.
  - By IH, `toNat C₀ = A₀ B₀`, `toNat C₁ = A₁ B₁`,
    `toNat C₂ = (toNat absA) · (toNat absB)`.
  - By `absSubLimbsKM_toNat`, `toNat absA = |A₀ − A₁|` (with sign `signA`),
    similarly `toNat absB`.  So `toNat C₂ = |A₀ − A₁| |B₀ − B₁|`.
  - Show `toNat middle = A₀ B₁ + A₁ B₀`:
    case-split on `signA == signB`.  When equal, the `(A₀-A₁)(B₀-B₁)`
    cross-product is positive and equals `+toNat C₂`, so
    `middle = C₀ + C₁ - C₂ = A₀ B₀ + A₁ B₁ - (A₀-A₁)(B₀-B₁) = A₀ B₁ + A₁ B₀`.
    When unequal, the cross-product is negative, so
    `middle = C₀ + C₁ + C₂ = A₀ B₁ + A₁ B₀`.
  - Show the high limbs of `middle` past `addLen = min(2k+1, 2*len-k)`
    are zero: from `toNat middle < 2β^(k+m)` (a bound from the formula
    above), and `addLen ≥ k+m+1`.
  - Assemble: `acc₀ = C₀ ++ C₁` has `toNat = A₀ B₀ + A₁ B₁ · β^(2k)`
    (by `toNatLimbsList_append`).  The final `addGeqLimbs` adds
    `middle * β^k`, yielding
    `toNat acc.1 + acc.2 · β^(2*len) = A₀ B₀ + (A₀ B₁ + A₁ B₀) β^k + A₁ B₁ β^(2k) = A B`.
  - Since `A B < β^(2*len)` and `acc.1.size = 2*len`, `acc.2 = 0` and
    `toNat acc.1 = A B`.
-/

namespace Azurite.AzNat

/-! ### Slice helpers -/

/-- The `toNat` of a length-`k+m` slice splits into low (`k` limbs) and high
    (`m` limbs) parts.  Specialization of `toNatLimbsList_drop_take_split`. -/
lemma toNat_slice_split (a : Array UInt64) (lo k m : Nat)
    (h : lo + (k + m) ≤ a.size) :
    toNatLimbsList ((a.toList.drop lo).take (k + m))
      = toNatLimbsList ((a.toList.drop lo).take k)
        + toNatLimbsList ((a.toList.drop (lo + k)).take m) * 2 ^ (64 * k) := by
  have h_split := toNatLimbsList_drop_take_split a lo (k + m) k (by omega) h
  rw [show k + m - k = m from by omega] at h_split
  exact h_split

/-- Bound on a `k`-limb slice value. -/
lemma slice_lt_pow (a : Array UInt64) (lo k : Nat) :
    toNatLimbsList ((a.toList.drop lo).take k) < 2 ^ (64 * k) := by
  have h := toNatLimbsList_lt_pow ((a.toList.drop lo).take k)
  have h_len : ((a.toList.drop lo).take k).length ≤ k := by
    rw [List.length_take]; omega
  have h_pow : 2 ^ (64 * ((a.toList.drop lo).take k).length) ≤ 2 ^ (64 * k) := by
    apply Nat.pow_le_pow_right (by decide); omega
  omega

/-- A length-`k` array's full `toNat` equals its `(0, k)`-slice `toNat`. -/
private lemma toNat_full_eq_slice (a : Array UInt64) (k : Nat) (h : a.size = k) :
    toNatLimbsList a.toList = toNatLimbsList ((a.toList.drop 0).take k) := by
  rw [List.drop_zero, List.take_of_length_le]
  rw [Array.length_toList, h]

/-- A length-`k` zero array has `toNat = 0`. -/
private lemma toNat_replicate_zero (k : Nat) :
    toNatLimbsList ((Array.replicate k (0 : UInt64)).toList) = 0 := by
  rw [Array.toList_replicate]
  induction k with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, toNatLimbsList_cons, ih]; simp

/-! ### Correctness of `absSubLimbsKM` stages

Writing `A₀, A₁` for the low- and high-half slice values, the postcondition of
`absSubLimbsKM` is `r.2 = true ↔ A₁ ≤ A₀` and `toNat r.1.1 = |A₀ − A₁|`.
We build it from `copySub_toNat` (the fused stage 1+2 lemma) and
`negPart_toNat`.
-/

/-- `copySub.go` preserves any prefix `[0, j)` of `r` whenever `j ≤ i`. -/
private theorem absSubLimbsKM.copySub.go_toList_take_le (a : Array UInt64) (loA k m : Nat)
    (i : Nat) (borrow : Bool) (r : Array UInt64)
    (h_a : loA + k + m ≤ a.size) (h_le : m ≤ k)
    (h_r : r.size = k) (h_i : i ≤ k) (j : Nat) (hj : j ≤ i) :
    (absSubLimbsKM.copySub.go a loA k m i borrow r h_a h_le h_r h_i).1.toList.take j
      = r.toList.take j := by
  induction h_sub : k - i generalizing r i borrow with
  | zero =>
    have h_ge : k ≤ i := by omega
    rw [absSubLimbsKM.copySub.go]
    simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < k := by omega
    have h_rec : k - (i + 1) = n := by omega
    rw [absSubLimbsKM.copySub.go]
    simp only [h_lt, ↓reduceDIte]
    by_cases hm : i < m
    · simp only [hm, ↓reduceDIte]
      rw [ih _ _ _ (by rw [Array.size_set, h_r]) (by omega) (by omega) h_rec]
      rw [Array.toList_set, List.take_set_of_le hj]
    · simp only [hm, ↓reduceDIte]
      rw [ih _ _ _ (by rw [Array.size_set, h_r]) (by omega) (by omega) h_rec]
      rw [Array.toList_set, List.take_set_of_le hj]

/-- `copySub.go` preserves the prefix of `r` up to index `i`. -/
private theorem absSubLimbsKM.copySub.go_toList_take (a : Array UInt64) (loA k m : Nat)
    (i : Nat) (borrow : Bool) (r : Array UInt64)
    (h_a : loA + k + m ≤ a.size) (h_le : m ≤ k)
    (h_r : r.size = k) (h_i : i ≤ k) :
    (absSubLimbsKM.copySub.go a loA k m i borrow r h_a h_le h_r h_i).1.toList.take i
      = r.toList.take i :=
  absSubLimbsKM.copySub.go_toList_take_le a loA k m i borrow r h_a h_le h_r h_i i (Nat.le_refl _)

/-- Recursive correctness invariant for `copySub.go`.  Threading the
    "remaining" minuend `A₀[i..k]`, subtrahend `A₁[i..m]`, and the
    accumulator `r`'s positions `[i, k)`:
    `A₀[i..k] + b_out · 2^(64·(k−i)) = r_out[i..k] + A₁[i..m] + b_in`.
    -/
private lemma absSubLimbsKM.copySub.go_correct (a : Array UInt64) (loA k m : Nat)
    (i : Nat) (borrow : Bool) (r : Array UInt64)
    (h_a : loA + k + m ≤ a.size) (h_le : m ≤ k)
    (h_r : r.size = k) (h_i : i ≤ k) :
    toNatLimbsList ((a.toList.drop (loA + i)).take (k - i))
      + (absSubLimbsKM.copySub.go a loA k m i borrow r h_a h_le h_r h_i).2.toNat
        * 2 ^ (64 * (k - i))
    = toNatLimbsList
        (((absSubLimbsKM.copySub.go a loA k m i borrow r h_a h_le h_r h_i).1.toList.drop i).take
          (k - i))
      + toNatLimbsList ((a.toList.drop (loA + k + i)).take (m - i))
      + borrow.toNat := by
  induction h_sub : k - i generalizing r i borrow with
  | zero =>
    have h_ge : k ≤ i := by omega
    have h_eq : absSubLimbsKM.copySub.go a loA k m i borrow r h_a h_le h_r h_i = (r, borrow) := by
      rw [absSubLimbsKM.copySub.go]
      simp [Nat.not_lt.mpr h_ge]
    rw [h_eq]
    have h_mi : m - i = 0 := by omega
    simp [h_mi, toNatLimbsList]
  | succ n ih =>
    have h_lt : i < k := by omega
    have h_iA : loA + i < a.size := by omega
    have h_i_r : i < r.size := by rw [h_r]; exact h_lt
    have h_rec : k - (i + 1) = n := by omega
    -- Helper: split a slice at the head index.
    have split_arr : ∀ (A : Array UInt64) (j p : Nat) (hj : j < A.size),
        toNatLimbsList ((A.toList.drop j).take (p + 1))
          = A[j].toNat + toNatLimbsList ((A.toList.drop (j + 1)).take p) * 2 ^ 64 := by
      intro A j p hj
      have h_lt_list : j < A.toList.length := hj
      rw [List.drop_eq_getElem_cons h_lt_list, List.take_succ_cons, toNatLimbsList_cons]
      rw [show A.toList[j] = A[j] from (Array.getElem_toList hj).symm]
      ring
    -- The recursion descends to (i+1) with a new array `a'` and new borrow.
    by_cases hm : i < m
    · -- Low phase: subtrahend is a[loA+k+i].
      have h_iB : loA + k + i < a.size := by omega
      set swb := UInt64.subWithBorrow a[loA + i] a[loA + k + i] borrow with hswb_def
      set diff := swb.1 with hdiff_def
      set newBorrow := swb.2 with hnb_def
      set r' := r.set i diff h_i_r with hr'_def
      have hr'_sz : r'.size = k := by rw [hr'_def, Array.size_set, h_r]
      have h_i_step : i + 1 ≤ k := by omega
      have h_eq :
          absSubLimbsKM.copySub.go a loA k m i borrow r h_a h_le h_r h_i
            = absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r'
                h_a h_le hr'_sz h_i_step := by
        conv_lhs => rw [absSubLimbsKM.copySub.go]
        simp [h_lt, hm, hswb_def, hdiff_def, hnb_def, hr'_def]
      have h_ih := ih (i + 1) newBorrow r' hr'_sz h_i_step h_rec
      have h_swb := UInt64.subWithBorrow_eq a[loA + i] a[loA + k + i] borrow
      rw [← hswb_def] at h_swb
      have h_res_size :
          (absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).1.size
            = k := absSubLimbsKM.copySub.go_size _ _ _ _ _ _ _ _ _ _ _
      have h_res_i_size :
          i < (absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).1.size := by
        rw [h_res_size]; exact h_lt
      have h_res_i :
          (absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).1[i]'h_res_i_size
            = diff := by
        have h_prefix :=
          absSubLimbsKM.copySub.go_toList_take a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step
        have h_len_L :
            ((absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).1.toList).length
              = k := by rw [Array.length_toList]; exact h_res_size
        have h_i_lt_L_take :
            i < ((absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).1.toList.take
                  (i + 1)).length := by
          rw [List.length_take, h_len_L]; omega
        have h_i_lt_R_take : i < (r'.toList.take (i + 1)).length := by
          rw [List.length_take, Array.length_toList, hr'_def, Array.size_set]; omega
        have h_get_eq :
            ((absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).1.toList.take
                (i + 1))[i]'h_i_lt_L_take
              = (r'.toList.take (i + 1))[i]'h_i_lt_R_take := by
          congr 1
        rw [List.getElem_take, List.getElem_take] at h_get_eq
        rw [← Array.getElem_toList h_res_i_size, h_get_eq]
        have h_i_lt : i < (r.set i diff h_i_r).toList.length := by
          rw [Array.length_toList, Array.size_set]; exact h_i_r
        show (r.set i diff h_i_r).toList[i]'h_i_lt = diff
        simp [Array.toList_set, List.getElem_set_self]
      rw [h_eq]
      rw [show n + 1 = k - i from h_sub.symm]
      have h_k_split : k - i = (k - (i + 1)) + 1 := by omega
      have h_m_split : m - i = (m - (i + 1)) + 1 := by omega
      rw [h_k_split]
      rw [split_arr (absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).1
            i (k - (i + 1)) h_res_i_size]
      rw [h_res_i]
      rw [split_arr a (loA + i) (k - (i + 1)) h_iA]
      rw [h_m_split]
      rw [split_arr a (loA + k + i) (m - (i + 1)) h_iB]
      have h_pow : (2 : Nat) ^ (64 * ((k - (i + 1)) + 1))
                  = 2 ^ (64 * (k - (i + 1))) * 2 ^ 64 := by
        rw [show 64 * ((k - (i + 1)) + 1) = 64 * (k - (i + 1)) + 64 from by ring, Nat.pow_add]
      rw [h_pow]
      rw [show loA + i + 1 = loA + (i + 1) from by ring]
      rw [show loA + k + i + 1 = loA + k + (i + 1) from by ring]
      rw [← h_rec] at h_ih
      set P := toNatLimbsList ((a.toList.drop (loA + (i + 1))).take (k - (i + 1))) with hP_def
      set Q := toNatLimbsList
          (((absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).1.toList.drop
              (i + 1)).take (k - (i + 1))) with hQ_def
      set S := toNatLimbsList ((a.toList.drop (loA + k + (i + 1))).take (m - (i + 1))) with hS_def
      set R := (absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).2.toNat
        with hR_def
      change a[loA + i].toNat + P * 2 ^ 64 + R * (2 ^ (64 * (k - (i + 1))) * 2 ^ 64)
           = diff.toNat + Q * 2 ^ 64
             + (a[loA + k + i].toNat + S * 2 ^ 64) + borrow.toNat
      have h1 : a[loA + i].toNat + P * 2 ^ 64 + R * (2 ^ (64 * (k - (i + 1))) * 2 ^ 64)
              = a[loA + i].toNat + (P + R * 2 ^ (64 * (k - (i + 1)))) * 2 ^ 64 := by ring
      rw [h1, h_ih]
      have h_limb : a[loA + i].toNat + (if newBorrow then 1 else 0) * 2 ^ 64
                  = diff.toNat + a[loA + k + i].toNat + (if borrow then 1 else 0) := by
        rw [hdiff_def, hnb_def]; omega
      have h_bN : newBorrow.toNat = (if newBorrow then 1 else 0) := by cases newBorrow <;> simp
      have h_b : borrow.toNat = (if borrow then 1 else 0) := by cases borrow <;> simp
      rw [h_bN, h_b]
      have goal_eq :
          a[loA + i].toNat + (Q + S + (if newBorrow = true then 1 else 0)) * 2 ^ 64
            = (a[loA + i].toNat + (if newBorrow = true then 1 else 0) * 2 ^ 64)
              + Q * 2 ^ 64 + S * 2 ^ 64 := by ring
      rw [goal_eq, h_limb]
      ring
    · -- High phase: subtrahend is 0.
      set swb := UInt64.subWithBorrow a[loA + i] 0 borrow with hswb_def
      set diff := swb.1 with hdiff_def
      set newBorrow := swb.2 with hnb_def
      set r' := r.set i diff h_i_r with hr'_def
      have hr'_sz : r'.size = k := by rw [hr'_def, Array.size_set, h_r]
      have h_i_step : i + 1 ≤ k := by omega
      have h_eq :
          absSubLimbsKM.copySub.go a loA k m i borrow r h_a h_le h_r h_i
            = absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r'
                h_a h_le hr'_sz h_i_step := by
        conv_lhs => rw [absSubLimbsKM.copySub.go]
        simp [h_lt, hm, hswb_def, hdiff_def, hnb_def, hr'_def]
      have h_ih := ih (i + 1) newBorrow r' hr'_sz h_i_step h_rec
      have h_swb := UInt64.subWithBorrow_eq a[loA + i] 0 borrow
      rw [← hswb_def] at h_swb
      have h_res_size :
          (absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).1.size
            = k := absSubLimbsKM.copySub.go_size _ _ _ _ _ _ _ _ _ _ _
      have h_res_i_size :
          i < (absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).1.size := by
        rw [h_res_size]; exact h_lt
      have h_res_i :
          (absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).1[i]'h_res_i_size
            = diff := by
        have h_prefix :=
          absSubLimbsKM.copySub.go_toList_take a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step
        have h_len_L :
            ((absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).1.toList).length
              = k := by rw [Array.length_toList]; exact h_res_size
        have h_i_lt_L_take :
            i < ((absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).1.toList.take
                  (i + 1)).length := by
          rw [List.length_take, h_len_L]; omega
        have h_i_lt_R_take : i < (r'.toList.take (i + 1)).length := by
          rw [List.length_take, Array.length_toList, hr'_def, Array.size_set]; omega
        have h_get_eq :
            ((absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).1.toList.take
                (i + 1))[i]'h_i_lt_L_take
              = (r'.toList.take (i + 1))[i]'h_i_lt_R_take := by
          congr 1
        rw [List.getElem_take, List.getElem_take] at h_get_eq
        rw [← Array.getElem_toList h_res_i_size, h_get_eq]
        have h_i_lt : i < (r.set i diff h_i_r).toList.length := by
          rw [Array.length_toList, Array.size_set]; exact h_i_r
        show (r.set i diff h_i_r).toList[i]'h_i_lt = diff
        simp [Array.toList_set, List.getElem_set_self]
      rw [h_eq]
      rw [show n + 1 = k - i from h_sub.symm]
      have h_k_split : k - i = (k - (i + 1)) + 1 := by omega
      have h_mi : m - i = 0 := by omega
      have h_mi1 : m - (i + 1) = 0 := by omega
      rw [h_k_split, h_mi]
      rw [split_arr (absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).1
            i (k - (i + 1)) h_res_i_size]
      rw [h_res_i]
      rw [split_arr a (loA + i) (k - (i + 1)) h_iA]
      have h_pow : (2 : Nat) ^ (64 * ((k - (i + 1)) + 1))
                  = 2 ^ (64 * (k - (i + 1))) * 2 ^ 64 := by
        rw [show 64 * ((k - (i + 1)) + 1) = 64 * (k - (i + 1)) + 64 from by ring, Nat.pow_add]
      rw [h_pow]
      rw [show loA + i + 1 = loA + (i + 1) from by ring]
      rw [← h_rec] at h_ih
      set P := toNatLimbsList ((a.toList.drop (loA + (i + 1))).take (k - (i + 1))) with hP_def
      set Q := toNatLimbsList
          (((absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).1.toList.drop
              (i + 1)).take (k - (i + 1))) with hQ_def
      set R := (absSubLimbsKM.copySub.go a loA k m (i + 1) newBorrow r' h_a h_le hr'_sz h_i_step).2.toNat
        with hR_def
      -- The "remaining A₁" slice is empty since m - (i + 1) = 0 in this branch.
      have h_A1_zero :
          toNatLimbsList ((a.toList.drop (loA + k + (i + 1))).take (m - (i + 1))) = 0 := by
        rw [h_mi1]; rfl
      rw [h_A1_zero] at h_ih
      change a[loA + i].toNat + P * 2 ^ 64 + R * (2 ^ (64 * (k - (i + 1))) * 2 ^ 64)
           = diff.toNat + Q * 2 ^ 64 + 0 + borrow.toNat
      have h1 : a[loA + i].toNat + P * 2 ^ 64 + R * (2 ^ (64 * (k - (i + 1))) * 2 ^ 64)
              = a[loA + i].toNat + (P + R * 2 ^ (64 * (k - (i + 1)))) * 2 ^ 64 := by ring
      rw [h1, h_ih]
      have h_limb : a[loA + i].toNat + (if newBorrow then 1 else 0) * 2 ^ 64
                  = diff.toNat + (if borrow then 1 else 0) := by
        have : (0 : UInt64).toNat = 0 := rfl
        rw [hdiff_def, hnb_def]; rw [this] at h_swb; omega
      have h_bN : newBorrow.toNat = (if newBorrow then 1 else 0) := by cases newBorrow <;> simp
      have h_b : borrow.toNat = (if borrow then 1 else 0) := by cases borrow <;> simp
      rw [h_bN, h_b]
      have goal_eq :
          a[loA + i].toNat + (Q + 0 + (if newBorrow = true then 1 else 0)) * 2 ^ 64
            = (a[loA + i].toNat + (if newBorrow = true then 1 else 0) * 2 ^ 64)
              + Q * 2 ^ 64 := by ring
      rw [goal_eq, h_limb]
      ring

/-- Top-level fused stage: `copySub a loA k m` returns `(d, borrow)` where
    `borrow = true ↔ A₀ < A₁`, and
    `toNat d + A₁ = A₀ + borrow · 2^(64·k)`. -/
theorem absSubLimbsKM.copySub_toNat (a : Array UInt64) (loA k m : Nat)
    (h_a : loA + k + m ≤ a.size) (h_le : m ≤ k) (h_kpos : 0 < k) (h_mpos : 0 < m) :
    let r := absSubLimbsKM.copySub a loA k m h_a h_le h_kpos h_mpos
    let A0 := toNatLimbsList ((a.toList.drop loA).take k)
    let A1 := toNatLimbsList ((a.toList.drop (loA + k)).take m)
    (r.2 = true ↔ A0 < A1) ∧
    toNatLimbsList r.1.1.toList + A1 = A0 + r.2.toNat * 2 ^ (64 * k) := by
  -- Reduce to `copySub.go_correct` at i = 0, borrow = false.
  unfold absSubLimbsKM.copySub
  set r₀ : Array UInt64 := Array.replicate k 0 with hr₀_def
  have hr₀_sz : r₀.size = k := by rw [hr₀_def]; exact Array.size_replicate
  set go := absSubLimbsKM.copySub.go a loA k m 0 false r₀ h_a h_le hr₀_sz (Nat.zero_le _) with hgo_def
  have h_go_size : go.1.size = k := by
    rw [hgo_def]; exact absSubLimbsKM.copySub.go_size _ _ _ _ _ _ _ _ _ _ _
  have h_go_correct :=
    absSubLimbsKM.copySub.go_correct a loA k m 0 false r₀ h_a h_le hr₀_sz (Nat.zero_le _)
  rw [show absSubLimbsKM.copySub.go a loA k m 0 false r₀ h_a h_le hr₀_sz (Nat.zero_le _) = go from rfl]
    at h_go_correct
  simp only [Nat.add_zero, Nat.sub_zero, Bool.toNat_false] at h_go_correct
  -- Replace slices with full toList using toNat_full_eq_slice.
  have h_go_full :
      toNatLimbsList ((go.1.toList.drop 0).take k) = toNatLimbsList go.1.toList := by
    rw [← toNat_full_eq_slice _ _ h_go_size]
  rw [h_go_full] at h_go_correct
  set A0 := toNatLimbsList ((a.toList.drop loA).take k) with hA0_def
  set A1 := toNatLimbsList ((a.toList.drop (loA + k)).take m) with hA1_def
  -- Bounds.
  have hA0_lt : A0 < 2 ^ (64 * k) := slice_lt_pow a loA k
  have hA1_lt_pk : A1 < 2 ^ (64 * k) := by
    have h := slice_lt_pow a (loA + k) m
    have hp : 2 ^ (64 * m) ≤ 2 ^ (64 * k) := by
      apply Nat.pow_le_pow_right (by decide); omega
    omega
  have h_go_full_lt : toNatLimbsList go.1.toList < 2 ^ (64 * k) := by
    rw [← h_go_full]; exact slice_lt_pow go.1 0 k
  refine ⟨?_, ?_⟩
  · constructor
    · intro h_carry
      have h_one : go.2.toNat = 1 := by rw [h_carry]; rfl
      rw [h_one] at h_go_correct; omega
    · intro h_lt
      match h : go.2 with
      | false =>
        have h_z : go.2.toNat = 0 := by rw [h]; rfl
        rw [h_z] at h_go_correct
        omega
      | true => rfl
  · linarith [h_go_correct]

/-- Stage 3: `negPart d k` produces an array whose `toNat` is `β^k − toNat d`,
    when `0 < toNat d`. -/
theorem absSubLimbsKM.negPart_toNat (d : Array UInt64) (k : Nat) (hd : d.size = k)
    (hd_pos : 0 < toNatLimbsList d.toList) :
    toNatLimbsList (absSubLimbsKM.negPart d k hd).1.toList
      = 2 ^ (64 * k) - toNatLimbsList d.toList := by
  unfold absSubLimbsKM.negPart
  set zero : Array UInt64 := Array.replicate k 0 with hzero_def
  have hzero_sz : zero.size = k := by rw [hzero_def]; exact Array.size_replicate
  have hzero : 0 + k ≤ zero.size := by rw [hzero_sz]; omega
  have hd' : 0 + k ≤ d.size := by rw [hd]; omega
  -- toNat of zero is 0, and slice equals full.
  have h_zero_zero : toNatLimbsList ((zero.toList.drop 0).take k) = 0 := by
    rw [← toNat_full_eq_slice _ _ hzero_sz, hzero_def]
    exact toNat_replicate_zero k
  set r := subSameLengthLimbs zero d 0 0 k hzero hd' with hr_def
  have h_r_size : r.1.size = k := by rw [hr_def, subSameLengthLimbs_size, hzero_sz]
  have h_eq := subSameLengthLimbs_toNat zero d 0 0 k hzero hd'
  rw [show subSameLengthLimbs zero d 0 0 k hzero hd' = r from rfl] at h_eq
  simp only at h_eq
  rw [h_zero_zero] at h_eq
  have h_d_full :
      toNatLimbsList ((d.toList.drop 0).take k) = toNatLimbsList d.toList := by
    rw [← toNat_full_eq_slice _ _ hd]
  have h_r_full :
      toNatLimbsList ((r.1.toList.drop 0).take k) = toNatLimbsList r.1.toList := by
    rw [← toNat_full_eq_slice _ _ h_r_size]
  rw [h_d_full, h_r_full] at h_eq
  -- The subtraction `0 − d` borrows iff d > 0; since d > 0, carry = 1.
  have h_d_lt : toNatLimbsList d.toList < 2 ^ (64 * k) := by
    rw [← h_d_full]; exact slice_lt_pow d 0 k
  have h_r_lt : toNatLimbsList r.1.toList < 2 ^ (64 * k) := by
    rw [← h_r_full]; exact slice_lt_pow r.1 0 k
  have h_carry_one : r.2.toNat = 1 := by
    match h : r.2 with
    | false =>
      exfalso
      have h_z : r.2.toNat = 0 := by rw [h]; rfl
      rw [h_z] at h_eq; omega
    | true => rfl
  rw [h_carry_one] at h_eq
  simp only [Nat.one_mul, Nat.zero_add] at h_eq
  show toNatLimbsList r.1.toList = 2 ^ (64 * k) - toNatLimbsList d.toList
  omega

/-- Correctness of `absSubLimbsKM`. -/
theorem absSubLimbsKM_toNat (a : Array UInt64) (loA k m : Nat)
    (hA : loA + k + m ≤ a.size) (h_le : m ≤ k) (h_kpos : 0 < k) (h_mpos : 0 < m) :
    let r := absSubLimbsKM a loA k m hA h_le h_kpos h_mpos
    let A0 := toNatLimbsList ((a.toList.drop loA).take k)
    let A1 := toNatLimbsList ((a.toList.drop (loA + k)).take m)
    (r.2 = true ↔ A1 ≤ A0) ∧
    toNatLimbsList r.1.1.toList = (if A1 ≤ A0 then A0 - A1 else A1 - A0) := by
  -- Set up A₀, A₁.
  set A0 := toNatLimbsList ((a.toList.drop loA).take k) with hA0_def
  set A1 := toNatLimbsList ((a.toList.drop (loA + k)).take m) with hA1_def
  have hA0_lt : A0 < 2 ^ (64 * k) := slice_lt_pow a loA k
  have hA1_lt_pk : A1 < 2 ^ (64 * k) := by
    have h := slice_lt_pow a (loA + k) m
    have hp : 2 ^ (64 * m) ≤ 2 ^ (64 * k) := by
      apply Nat.pow_le_pow_right (by decide); omega
    omega
  unfold absSubLimbsKM
  -- Fused stage 1+2: copySub.
  set cs := absSubLimbsKM.copySub a loA k m hA h_le h_kpos h_mpos with hcs_def
  have h_cs_props := absSubLimbsKM.copySub_toNat a loA k m hA h_le h_kpos h_mpos
  rw [show absSubLimbsKM.copySub a loA k m hA h_le h_kpos h_mpos = cs from rfl] at h_cs_props
  simp only at h_cs_props
  obtain ⟨h_cs_iff, h_cs_eq⟩ := h_cs_props
  -- Step: case split on borrow.
  by_cases h_borrow : cs.2 = true
  · -- A₀ < A₁; we negate to get A₁ - A₀.
    have h_lt : A0 < A1 := h_cs_iff.mp h_borrow
    have h_one : cs.2.toNat = 1 := by rw [h_borrow]; rfl
    have h_cs_val : toNatLimbsList cs.1.1.toList = 2 ^ (64 * k) + A0 - A1 := by
      have := h_cs_eq; rw [h_one] at this; omega
    have h_cs_size : cs.1.1.size = k := cs.1.2
    have h_cs_pos : 0 < toNatLimbsList cs.1.1.toList := by
      rw [h_cs_val]; omega
    have h_neg_toNat := absSubLimbsKM.negPart_toNat cs.1.1 k h_cs_size h_cs_pos
    refine ⟨?_, ?_⟩
    · rw [ite_eq_left h_borrow]
      simp only
      constructor
      · intro h; exact absurd h Bool.false_ne_true
      · intro h; omega
    · rw [ite_eq_left h_borrow]
      simp only
      rw [ite_eq_right (by omega : ¬ A1 ≤ A0)]
      rw [h_neg_toNat, h_cs_val]
      omega
  · -- No borrow; A₀ ≥ A₁.
    have h_cs_false : cs.2 = false := by
      cases h : cs.2
      · rfl
      · exact absurd h h_borrow
    have h_z : cs.2.toNat = 0 := by rw [h_cs_false]; rfl
    have h_le_le : A1 ≤ A0 := by
      rcases Nat.lt_or_ge A0 A1 with h | h
      · exfalso
        have h_true : cs.2 = true := h_cs_iff.mpr h
        rw [h_cs_false] at h_true
        exact Bool.false_ne_true h_true
      · exact h
    have h_cs_val : toNatLimbsList cs.1.1.toList = A0 - A1 := by
      have := h_cs_eq; rw [h_z] at this; omega
    refine ⟨?_, ?_⟩
    · rw [ite_eq_right h_borrow]
      refine ⟨fun _ => h_le_le, fun _ => ?_⟩
      rfl
    · rw [ite_eq_right h_borrow]
      rw [ite_eq_left h_le_le]
      exact h_cs_val

/-! ### Correctness of `karatsubaMulLimbsRec` stages -/

/-- `2 ^ (64 * (j + 1)) = 2 ^ (64 * j) * 2 ^ 64`, used to combine bounds. -/
private lemma pow_succ_factor (j : Nat) :
    2 ^ (64 * (j + 1)) = 2 ^ (64 * j) * 2 ^ 64 := by
  rw [show 64 * (j + 1) = 64 * j + 64 from by ring, Nat.pow_add]

/-- If `toNat l < 2^(64·n)`, then taking the first `n` limbs is enough: the
    high zero limbs contribute 0. -/
private lemma toNat_take_eq_full_of_lt_pow (l : List UInt64) (n : Nat)
    (h : toNatLimbsList l < 2 ^ (64 * n)) :
    toNatLimbsList (l.take n) = toNatLimbsList l := by
  by_cases h_le : l.length ≤ n
  · rw [List.take_of_length_le h_le]
  · have h_lt : n < l.length := Nat.lt_of_not_ge h_le
    have h_take_len : (l.take n).length = n := by rw [List.length_take]; omega
    have h_split := toNatLimbsList_append (l.take n) (l.drop n)
    rw [List.take_append_drop n l, h_take_len] at h_split
    have h_drop_zero : toNatLimbsList (l.drop n) = 0 := by
      by_contra h_ne
      have h_ge_one : 1 ≤ toNatLimbsList (l.drop n) :=
        Nat.one_le_iff_ne_zero.mpr h_ne
      have h_lhs : 2 ^ (64 * n) ≤ toNatLimbsList (l.drop n) * 2 ^ (64 * n) := by
        have := Nat.mul_le_mul_right (2 ^ (64 * n)) h_ge_one
        rwa [Nat.one_mul] at this
      omega
    rw [h_drop_zero, Nat.zero_mul, Nat.zero_add] at h_split
    exact h_split.symm

/-- `addGeqLimbs` preserves the prefix `[0, i)` of `a` when `i ≤ loA`. -/
private lemma addGeqLimbs_toList_take_le (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (h_ge : lenB ≤ lenA) (h_posA : 0 < lenA) (h_posB : 0 < lenB)
    (i : Nat) (h_le : i ≤ loA) :
    (addGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB).1.toList.take i
      = a.toList.take i := by
  unfold addGeqLimbs
  set lo := addSameLengthLimbs a b loA loB lenB (by omega) hB with hlo_def
  have h_lo_size : lo.1.size = a.size := by
    rw [hlo_def]; exact addSameLengthLimbs_size a b loA loB lenB _ hB
  have h_lo_take : lo.1.toList.take i = a.toList.take i := by
    rw [hlo_def]
    show (addSameLengthLimbs.go b loA loB lenB a 0 false (by omega) hB).1.toList.take i
          = a.toList.take i
    exact addSameLengthLimbs.go_toList_take_le b loA loB lenB a 0 false (by omega) hB i
            (by omega)
  by_cases h : lo.2 = true
  · rw [ite_eq_left h]
    show (addLimb lo.1 (loA + lenB) (loA + lenA) 1 (by omega)
            (by rw [h_lo_size]; exact hA)).1.toList.take i = a.toList.take i
    have h_addLimb_take :
        (addLimb.go (loA + lenA) lo.1 (loA + lenB) 1
            (by rw [h_lo_size]; exact hA)).1.toList.take (loA + lenB)
          = lo.1.toList.take (loA + lenB) :=
      addLimb.go_toList_take (loA + lenA) lo.1 (loA + lenB) 1
        (by rw [h_lo_size]; exact hA)
    show (addLimb.go (loA + lenA) lo.1 (loA + lenB) 1 _).1.toList.take i = a.toList.take i
    have h_combine :
        (addLimb.go (loA + lenA) lo.1 (loA + lenB) 1
            (by rw [h_lo_size]; exact hA)).1.toList.take i
          = lo.1.toList.take i := by
      have eq1 :
          (addLimb.go (loA + lenA) lo.1 (loA + lenB) 1
              (by rw [h_lo_size]; exact hA)).1.toList.take i
            = ((addLimb.go (loA + lenA) lo.1 (loA + lenB) 1
                    (by rw [h_lo_size]; exact hA)).1.toList.take (loA + lenB)).take i := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
      rw [eq1, h_addLimb_take, List.take_take, Nat.min_eq_left (by omega)]
    rw [h_combine]
    exact h_lo_take
  · rw [ite_eq_right h]
    exact h_lo_take

/-- `2 ^ (64 * (a + b)) = 2 ^ (64 * a) · 2 ^ (64 * b)`. -/
private lemma pow_combine_factor (a b : Nat) :
    2 ^ (64 * (a + b)) = 2 ^ (64 * a) * 2 ^ (64 * b) := by
  rw [← Nat.pow_add]; congr 1; ring

/-- `2 ^ (64 * (2 * k)) = 2 ^ (64 * k) · 2 ^ (64 * k)`. -/
lemma pow_double_factor (k : Nat) :
    2 ^ (64 * (2 * k)) = 2 ^ (64 * k) * 2 ^ (64 * k) := by
  rw [show 2 * k = k + k from by ring]; exact pow_combine_factor k k

/-- For `b ≤ a`: `2 ^ (64 * a) = 2 ^ (64 * (a - b)) · 2 ^ (64 * b)`. -/
private lemma pow_split_factor (a b : Nat) (h : b ≤ a) :
    2 ^ (64 * a) = 2 ^ (64 * (a - b)) * 2 ^ (64 * b) := by
  rw [← Nat.pow_add]; congr 1; omega

/-- `toNat (C₀ ++ C₁) = toNat C₀ + toNat C₁ · β^(2k)` when `C₀.size = 2k`. -/
private lemma toNat_acc₀_append (C₀ C₁ : Array UInt64) (k : Nat)
    (hC₀ : C₀.size = 2 * k) :
    toNatLimbsList (C₀ ++ C₁).toList
      = toNatLimbsList C₀.toList + toNatLimbsList C₁.toList * 2 ^ (64 * (2 * k)) := by
  rw [Array.toList_append, toNatLimbsList_append, Array.length_toList, hC₀]
  omega

/-- Drop-`k` of `(C₀ ++ C₁)` when `k ≤ 2k = C₀.size`. -/
private lemma drop_k_acc₀_eq (C₀ C₁ : Array UInt64) (k : Nat)
    (hC₀ : C₀.size = 2 * k) :
    (C₀ ++ C₁).toList.drop k = C₀.toList.drop k ++ C₁.toList := by
  rw [Array.toList_append, List.drop_append_of_le_length]
  rw [Array.length_toList, hC₀]; omega

/-- toNat of `(C₀ ++ C₁).drop k = toNat C₁ · β^k + toNat (C₀.drop k)`. -/
private lemma toNat_acc₀_drop_k (C₀ C₁ : Array UInt64) (k : Nat)
    (hC₀ : C₀.size = 2 * k) :
    toNatLimbsList ((C₀ ++ C₁).toList.drop k)
      = toNatLimbsList C₁.toList * 2 ^ (64 * k)
        + toNatLimbsList (C₀.toList.drop k) := by
  rw [drop_k_acc₀_eq C₀ C₁ k hC₀, toNatLimbsList_append]
  rw [List.length_drop, Array.length_toList, hC₀,
      show 2 * k - k = k from by omega]

/-- Take-`k` of `(C₀ ++ C₁)` when `k ≤ 2k = C₀.size`. -/
private lemma take_k_acc₀_eq (C₀ C₁ : Array UInt64) (k : Nat)
    (hC₀ : C₀.size = 2 * k) :
    (C₀ ++ C₁).toList.take k = C₀.toList.take k := by
  rw [Array.toList_append, List.take_append_of_le_length]
  rw [Array.length_toList, hC₀]; omega

/-- Split `toNat C₀` into low and high `k`-limb parts. -/
private lemma toNat_C₀_split (C₀ : Array UInt64) (k : Nat) (hC₀ : C₀.size = 2 * k) :
    toNatLimbsList C₀.toList
      = toNatLimbsList (C₀.toList.drop k) * 2 ^ (64 * k)
        + toNatLimbsList (C₀.toList.take k) := by
  have h_split := toNatLimbsList_append (C₀.toList.take k) (C₀.toList.drop k)
  rw [List.take_append_drop k C₀.toList] at h_split
  have h_take_len : (C₀.toList.take k).length = k := by
    rw [List.length_take, Array.length_toList, hC₀]; omega
  rw [h_take_len] at h_split; exact h_split

/-- Split `toNat a` of an array of size `n ≥ k` into low and high parts. -/
private lemma toNat_array_split (a : Array UInt64) (k n : Nat)
    (h_size : a.size = n) (h_le : k ≤ n) :
    toNatLimbsList a.toList
      = toNatLimbsList (a.toList.drop k) * 2 ^ (64 * k)
        + toNatLimbsList (a.toList.take k) := by
  have h_split := toNatLimbsList_append (a.toList.take k) (a.toList.drop k)
  rw [List.take_append_drop k a.toList] at h_split
  have h_take_len : (a.toList.take k).length = k := by
    rw [List.length_take, Array.length_toList, h_size]; omega
  rw [h_take_len] at h_split; exact h_split

/-- `toNat` of a list split at `lo` and `lo + L`. -/
private lemma toNat_split3 (l : List UInt64) (lo L : Nat) (h : lo + L ≤ l.length) :
    toNatLimbsList l
      = toNatLimbsList (l.take lo) + toNatLimbsList ((l.drop lo).take L) * 2 ^ (64 * lo)
        + toNatLimbsList (l.drop (lo + L)) * 2 ^ (64 * (lo + L)) := by
  conv_lhs => rw [← List.take_append_drop (lo + L) l]
  rw [toNatLimbsList_append, List.length_take, Nat.min_eq_left h, List.take_add,
    toNatLimbsList_append, List.length_take, Nat.min_eq_left (by omega)]
  ring

/-- An in-place update of the slice `[lo, lo + L)` lifts to the whole array: the slice
    equation `slice' + e β^L = slice + X` becomes `whole' + e β^(lo+L) = whole + X β^lo`. -/
private lemma toNat_update (a a' : Array UInt64) (lo L X e : Nat)
    (h_size : a'.size = a.size) (hL : lo + L ≤ a.size)
    (h_pre : a'.toList.take lo = a.toList.take lo)
    (h_suf : a'.toList.drop (lo + L) = a.toList.drop (lo + L))
    (h_slice : toNatLimbsList ((a'.toList.drop lo).take L) + e * 2 ^ (64 * L)
      = toNatLimbsList ((a.toList.drop lo).take L) + X) :
    toNatLimbsList a'.toList + e * 2 ^ (64 * (lo + L))
      = toNatLimbsList a.toList + X * 2 ^ (64 * lo) := by
  rw [toNat_split3 a.toList lo L (by rw [Array.length_toList]; exact hL),
    toNat_split3 a'.toList lo L (by rw [Array.length_toList, h_size]; exact hL), h_pre, h_suf]
  have h_pow : (2 : Nat) ^ (64 * (lo + L)) = 2 ^ (64 * lo) * 2 ^ (64 * L) := by
    rw [show 64 * (lo + L) = 64 * lo + 64 * L from by ring, Nat.pow_add]
  rw [h_pow]
  zify at h_slice ⊢
  linear_combination (2 : ℤ) ^ (64 * lo) * h_slice

/-- Equal entries below `lo` give equal `take lo` prefixes. -/
private lemma take_eq_of_getElem (a a' : Array UInt64) (lo : Nat)
    (h_size : a'.size = a.size) (hlo : lo ≤ a.size)
    (h : ∀ (j : Nat) (hj : j < a.size), j < lo → a'[j]'(by rw [h_size]; exact hj) = a[j]'hj) :
    a'.toList.take lo = a.toList.take lo := by
  apply List.ext_getElem
  · rw [List.length_take, List.length_take, Array.length_toList, Array.length_toList, h_size]
  · intro i h₁ h₂
    have hi : i < a.size := by rw [List.length_take, Array.length_toList] at h₂; omega
    have hi_lo : i < lo := by rw [List.length_take] at h₂; omega
    rw [List.getElem_take, List.getElem_take, Array.getElem_toList, Array.getElem_toList]
    exact h i hi hi_lo

/-- `T + a P = V + b P` with `T, V < P` forces `T = V`. -/
private lemma eq_of_add_mul_eq_add_mul (T V a b P : Nat) (hT : T < P) (hV : V < P)
    (h : T + a * P = V + b * P) : T = V := by
  have h' := congrArg (· % P) h
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hT, Nat.mod_eq_of_lt hV] at h'
  exact h'

/-- Drop past the end is empty. -/
private lemma drop_size_eq_nil (a : Array UInt64) (n : Nat) (h : a.size ≤ n) :
    a.toList.drop n = [] :=
  List.drop_eq_nil_of_le (by rw [Array.length_toList]; exact h)

/-- Correctness of `assemble`: the assembled buffer holds
    `C₀ + (C₀ + C₁ ∓ C₂) β^k + C₁ β^(2k)`, given that this value fits in `2 len` limbs (every
    pass is exact modulo `β^(2 len)`). -/
theorem karatsubaMulLimbsRec.assemble_toNat (k m len : Nat)
    (C₀ C₁ C₂ : Array UInt64) (sameSign : Bool)
    (hC₀ : C₀.size = 2 * k) (hC₁ : C₁.size = 2 * m) (hC₂ : C₂.size = 2 * k)
    (hkm : k + m = len) (h_kpos : 0 < k) (h_mpos : 0 < m) (h_le : m ≤ k) (h_k2m : k ≤ 2 * m)
    (h_sub_ok : sameSign = true →
      toNatLimbsList C₂.toList ≤ toNatLimbsList C₀.toList + toNatLimbsList C₁.toList)
    (h_total_bound :
      toNatLimbsList C₀.toList
        + (if sameSign then
            toNatLimbsList C₀.toList + toNatLimbsList C₁.toList - toNatLimbsList C₂.toList
          else
            toNatLimbsList C₀.toList + toNatLimbsList C₁.toList + toNatLimbsList C₂.toList)
          * 2 ^ (64 * k)
        + toNatLimbsList C₁.toList * 2 ^ (64 * (2 * k))
        < 2 ^ (64 * (2 * len))) :
    toNatLimbsList (karatsubaMulLimbsRec.assemble k m len C₀ C₁ C₂ sameSign
                      hC₀ hC₁ hC₂ hkm h_kpos h_mpos h_le h_k2m).1.toList
      = toNatLimbsList C₀.toList
        + (if sameSign then
            toNatLimbsList C₀.toList + toNatLimbsList C₁.toList - toNatLimbsList C₂.toList
          else
            toNatLimbsList C₀.toList + toNatLimbsList C₁.toList + toNatLimbsList C₂.toList)
          * 2 ^ (64 * k)
        + toNatLimbsList C₁.toList * 2 ^ (64 * (2 * k)) := by
  unfold karatsubaMulLimbsRec.assemble
  dsimp only
  -- Names matching the function body.
  set acc₀ := C₀ ++ C₁ with hacc₀_def
  have hacc₀ : acc₀.size = 2 * len := by rw [hacc₀_def, Array.size_append, hC₀, hC₁]; omega
  have h1A : k + 2 * m ≤ acc₀.size := by rw [hacc₀]; omega
  have h1B : 0 + 2 * m ≤ C₀.size := by rw [hC₀]; omega
  have h1C : 0 + 2 * m ≤ C₁.size := by rw [hC₁]; omega
  set r₁ := add3SameLengthLimbs.go C₀ C₁ k 0 0 (2 * m) acc₀ 0 false false h1A h1B h1C
    with hr₁_def
  have hr₁ : r₁.1.size = 2 * len := by rw [hr₁_def, add3SameLengthLimbs.go_size, hacc₀]
  have h2A : (k + 2 * m) + (2 * k - 2 * m) ≤ r₁.1.size := by rw [hr₁]; omega
  have h2B : 2 * m + (2 * k - 2 * m) ≤ C₀.size := by rw [hC₀]; omega
  set r₂ := addSameLengthLimbs.go C₀ (k + 2 * m) (2 * m) (2 * k - 2 * m) r₁.1 0 r₁.2.1 h2A h2B
    with hr₂_def
  have hr₂ : r₂.1.size = 2 * len := by rw [hr₂_def, addSameLengthLimbs.go_size, hr₁]
  have h3lo : k + 2 * m ≤ 2 * len := by omega
  have h3hi : 2 * len ≤ r₂.1.size := by rw [hr₂]
  set b₃ : UInt64 := if r₁.2.2 then 1 else 0 with hb₃_def
  set r₃ := addLimb r₂.1 (k + 2 * m) (2 * len) b₃ h3lo h3hi with hr₃_def
  have hr₃ : r₃.1.size = 2 * len := by rw [hr₃_def, addLimb_size, hr₂]
  have h4lo : 3 * k ≤ 2 * len := by omega
  have h4hi : 2 * len ≤ r₃.1.size := by rw [hr₃]
  set b₄ : UInt64 := if r₂.2 then 1 else 0 with hb₄_def
  set r₄ := addLimb r₃.1 (3 * k) (2 * len) b₄ h4lo h4hi with hr₄_def
  have hr₄ : r₄.1.size = 2 * len := by rw [hr₄_def, addLimb_size, hr₃]
  have h5A : k + (2 * len - k) ≤ r₄.1.size := by rw [hr₄]; omega
  have h5B : 0 + 2 * k ≤ C₂.size := by rw [hC₂]; omega
  have h5ge : 2 * k ≤ 2 * len - k := by omega
  have h5posA : 0 < 2 * len - k := by omega
  have h5posB : 0 < 2 * k := by omega
  -- Whole-array values.
  set T₀ := toNatLimbsList acc₀.toList with hT₀_def
  set T₁ := toNatLimbsList r₁.1.toList with hT₁_def
  set T₂ := toNatLimbsList r₂.1.toList with hT₂_def
  set T₃ := toNatLimbsList r₃.1.toList with hT₃_def
  set T₄ := toNatLimbsList r₄.1.toList with hT₄_def
  set N₀ := toNatLimbsList C₀.toList with hN₀_def
  set N₁ := toNatLimbsList C₁.toList with hN₁_def
  set N₂ := toNatLimbsList C₂.toList with hN₂_def
  set c₁ := r₁.2.1.toNat with hc₁_def
  set c₂ := r₁.2.2.toNat with hc₂_def
  set d := r₂.2.toNat with hd_def
  have hb₃ : b₃.toNat = c₂ := by rw [hb₃_def, hc₂_def]; cases r₁.2.2 <;> rfl
  have hb₄ : b₄.toNat = d := by rw [hb₄_def, hd_def]; cases r₂.2 <;> rfl
  have hT₀ : T₀ = N₀ + N₁ * 2 ^ (64 * (2 * k)) := toNat_acc₀_append C₀ C₁ k hC₀
  -- `C₀` split at `2m`.
  have hC₀_split : N₀ = toNatLimbsList (C₀.toList.take (2 * m))
      + toNatLimbsList ((C₀.toList.drop (2 * m)).take (2 * k - 2 * m)) * 2 ^ (64 * (2 * m)) := by
    have h := toNat_split3 C₀.toList (2 * m) (2 * k - 2 * m)
      (by rw [Array.length_toList, hC₀]; omega)
    rw [drop_size_eq_nil C₀ (2 * m + (2 * k - 2 * m)) (by rw [hC₀]; omega)] at h
    have h0 : toNatLimbsList ([] : List UInt64) = 0 := rfl
    rw [h0, Nat.zero_mul, Nat.add_zero] at h
    exact h
  -- Pass 1a.
  have h₁ : T₁ + (c₁ + c₂) * 2 ^ (64 * (k + 2 * m))
      = T₀ + (toNatLimbsList (C₀.toList.take (2 * m)) + N₁) * 2 ^ (64 * k) := by
    apply toNat_update acc₀ r₁.1 k (2 * m) _ _ (by rw [hr₁, hacc₀]) (by rw [hacc₀]; omega)
    · exact add3SameLengthLimbs.go_toList_take_le C₀ C₁ k 0 0 (2 * m) acc₀ 0 false false
        h1A h1B h1C k (by omega)
    · exact add3SameLengthLimbs.go_toList_drop C₀ C₁ k 0 0 (2 * m) acc₀ 0 false false h1A h1B h1C
    · have h := add3SameLengthLimbs.go_correct C₀ C₁ k 0 0 (2 * m) acc₀ 0 false false h1A h1B h1C
      rw [← hr₁_def] at h
      simp only [Nat.add_zero, Nat.sub_zero, List.drop_zero, Bool.toNat_false] at h
      have h_C₁_take : C₁.toList.take (2 * m) = C₁.toList :=
        List.take_of_length_le (by rw [Array.length_toList, hC₁])
      rw [h_C₁_take] at h
      linarith [h]
  -- Pass 1b.
  have h₂ : T₂ + d * 2 ^ (64 * (3 * k))
      = T₁ + (toNatLimbsList ((C₀.toList.drop (2 * m)).take (2 * k - 2 * m)) + c₁)
          * 2 ^ (64 * (k + 2 * m)) := by
    have h := toNat_update r₁.1 r₂.1 (k + 2 * m) (2 * k - 2 * m)
      (toNatLimbsList ((C₀.toList.drop (2 * m)).take (2 * k - 2 * m)) + c₁) d
      (by rw [hr₂, hr₁]) (by rw [hr₁]; omega)
      (addSameLengthLimbs.go_toList_take_le C₀ (k + 2 * m) (2 * m) (2 * k - 2 * m) r₁.1 0 r₁.2.1
        h2A h2B (k + 2 * m) (by omega))
      (addSameLengthLimbs.go_toList_drop C₀ (k + 2 * m) (2 * m) (2 * k - 2 * m) r₁.1 0 r₁.2.1
        h2A h2B)
      (by
        have h := addSameLengthLimbs.go_correct C₀ (k + 2 * m) (2 * m) (2 * k - 2 * m) r₁.1 0
          r₁.2.1 h2A h2B
        rw [← hr₂_def] at h
        simp only [Nat.add_zero, Nat.sub_zero] at h
        linarith [h])
    rw [show k + 2 * m + (2 * k - 2 * m) = 3 * k from by omega] at h
    exact h
  -- Pass 1c.
  have h₃ : ∃ e₃, T₃ + e₃ * 2 ^ (64 * (2 * len)) = T₂ + c₂ * 2 ^ (64 * (k + 2 * m)) := by
    refine ⟨r₃.2.toNat, ?_⟩
    have h := toNat_update r₂.1 r₃.1 (k + 2 * m) (2 * len - (k + 2 * m)) c₂ r₃.2.toNat
      (by rw [hr₃, hr₂]) (by rw [hr₂]; omega)
      (addLimb_toList_take r₂.1 (k + 2 * m) (2 * len) b₃ h3lo h3hi)
      (by rw [drop_size_eq_nil r₃.1 _ (by rw [hr₃]; omega),
        drop_size_eq_nil r₂.1 _ (by rw [hr₂]; omega)])
      (by
        have h := addLimb_toNat r₂.1 (k + 2 * m) (2 * len) b₃ h3lo h3hi (by omega)
        simp only at h
        rw [← hr₃_def, hb₃] at h
        exact h)
    rw [show k + 2 * m + (2 * len - (k + 2 * m)) = 2 * len from by omega] at h
    exact h
  -- Pass 1d.
  have h₄ : ∃ e₄, T₄ + e₄ * 2 ^ (64 * (2 * len)) = T₃ + d * 2 ^ (64 * (3 * k)) := by
    refine ⟨r₄.2.toNat, ?_⟩
    have h := toNat_update r₃.1 r₄.1 (3 * k) (2 * len - 3 * k) d r₄.2.toNat
      (by rw [hr₄, hr₃]) (by rw [hr₃]; omega)
      (addLimb_toList_take r₃.1 (3 * k) (2 * len) b₄ h4lo h4hi)
      (by rw [drop_size_eq_nil r₄.1 _ (by rw [hr₄]; omega),
        drop_size_eq_nil r₃.1 _ (by rw [hr₃]; omega)])
      (by
        have h := addLimb.go_correct (2 * len) r₃.1 (3 * k) b₄ h4hi
          (Or.inl (by rw [hb₄, hd_def]; cases r₂.2 <;> decide))
        change toNatLimbsList ((r₄.1.toList.drop (3 * k)).take (2 * len - 3 * k))
          + r₄.2.toNat * 2 ^ (64 * (2 * len - 3 * k))
          = toNatLimbsList ((r₃.1.toList.drop (3 * k)).take (2 * len - 3 * k)) + b₄.toNat at h
        rw [hb₄] at h
        exact h)
    rw [show 3 * k + (2 * len - 3 * k) = 2 * len from by omega] at h
    exact h
  obtain ⟨e₃, h₃⟩ := h₃
  obtain ⟨e₄, h₄⟩ := h₄
  -- Through pass 1: `T₄ ≡ T₀ + (N₀ + N₁) β^k`.
  have h_pow_k2m : (2 : Nat) ^ (64 * (k + 2 * m)) = 2 ^ (64 * k) * 2 ^ (64 * (2 * m)) := by
    rw [show 64 * (k + 2 * m) = 64 * k + 64 * (2 * m) from by ring, Nat.pow_add]
  have h_pass1 : T₄ + (e₃ + e₄) * 2 ^ (64 * (2 * len)) = T₀ + (N₀ + N₁) * 2 ^ (64 * k) := by
    rw [hC₀_split, h_pow_k2m] at *
    zify at h₁ h₂ h₃ h₄ ⊢
    linear_combination h₁ + h₂ + h₃ + h₄
  have hT₄_lt : T₄ < 2 ^ (64 * (2 * len)) := by
    have := toNatLimbsList_lt_pow r₄.1.toList
    rw [Array.length_toList, hr₄] at this; exact this
  -- Pass 2 and the final value.
  cases sameSign with
  | true =>
    simp only [↓reduceIte] at h_total_bound ⊢
    have h_le := h_sub_ok rfl
    set r₅ := subGeqLimbs r₄.1 C₂ k (2 * len - k) 0 (2 * k) h5A h5B h5ge h5posA h5posB
      with hr₅_def
    have hr₅ : r₅.1.size = 2 * len := by rw [hr₅_def, subGeqLimbs_size, hr₄]
    have h₅ : T₄ + r₅.2.toNat * 2 ^ (64 * (2 * len))
        = toNatLimbsList r₅.1.toList + N₂ * 2 ^ (64 * k) := by
      have h := toNat_update r₅.1 r₄.1 k (2 * len - k) N₂ r₅.2.toNat (by rw [hr₅, hr₄])
        (by rw [hr₅]; omega)
        (by
          symm
          apply take_eq_of_getElem r₄.1 r₅.1 k (by rw [hr₅, hr₄]) (by rw [hr₄]; omega)
          intro j hj hjk
          exact subGeqLimbs_get_outside r₄.1 C₂ k (2 * len - k) 0 (2 * k) h5A h5B h5ge h5posA
            h5posB j (Or.inl hjk) hj)
        (by rw [drop_size_eq_nil r₅.1 _ (by rw [hr₅]; omega),
          drop_size_eq_nil r₄.1 _ (by rw [hr₄]; omega)])
        (by
          have h := subGeqLimbs_toNat r₄.1 C₂ k (2 * len - k) 0 (2 * k) h5A h5B h5ge h5posA h5posB
          simp only at h
          have h_C₂_take : C₂.toList.take (2 * k) = C₂.toList :=
            List.take_of_length_le (by rw [Array.length_toList, hC₂])
          rw [← hr₅_def, List.drop_zero, h_C₂_take] at h
          exact h)
      rw [show k + (2 * len - k) = 2 * len from by omega] at h
      exact h
    have hT₅_lt : toNatLimbsList r₅.1.toList < 2 ^ (64 * (2 * len)) := by
      have := toNatLimbsList_lt_pow r₅.1.toList
      rw [Array.length_toList, hr₅] at this; exact this
    apply eq_of_add_mul_eq_add_mul _ _ (e₃ + e₄) (r₅.2.toNat) _ hT₅_lt h_total_bound
    rw [hT₀] at h_pass1
    zify [h_le] at h_pass1 h₅ ⊢
    linear_combination h_pass1 - h₅
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h_total_bound ⊢
    set r₅ := addGeqLimbs r₄.1 C₂ k (2 * len - k) 0 (2 * k) h5A h5B h5ge h5posA h5posB
      with hr₅_def
    have hr₅ : r₅.1.size = 2 * len := by rw [hr₅_def, addGeqLimbs_size, hr₄]
    have h₅ : toNatLimbsList r₅.1.toList + r₅.2.toNat * 2 ^ (64 * (2 * len))
        = T₄ + N₂ * 2 ^ (64 * k) := by
      have h := toNat_update r₄.1 r₅.1 k (2 * len - k) N₂ r₅.2.toNat (by rw [hr₅, hr₄])
        (by rw [hr₄]; omega)
        (by
          apply take_eq_of_getElem r₄.1 r₅.1 k (by rw [hr₅, hr₄]) (by rw [hr₄]; omega)
          intro j hj hjk
          exact addGeqLimbs_get_outside r₄.1 C₂ k (2 * len - k) 0 (2 * k) h5A h5B h5ge h5posA
            h5posB j (Or.inl hjk) hj)
        (by rw [drop_size_eq_nil r₅.1 _ (by rw [hr₅]; omega),
          drop_size_eq_nil r₄.1 _ (by rw [hr₄]; omega)])
        (by
          have h := addGeqLimbs_toNat r₄.1 C₂ k (2 * len - k) 0 (2 * k) h5A h5B h5ge h5posA h5posB
          simp only at h
          have h_C₂_take : C₂.toList.take (2 * k) = C₂.toList :=
            List.take_of_length_le (by rw [Array.length_toList, hC₂])
          rw [← hr₅_def, List.drop_zero, h_C₂_take] at h
          exact h)
      rw [show k + (2 * len - k) = 2 * len from by omega] at h
      exact h
    have hT₅_lt : toNatLimbsList r₅.1.toList < 2 ^ (64 * (2 * len)) := by
      have := toNatLimbsList_lt_pow r₅.1.toList
      rw [Array.length_toList, hr₅] at this; exact this
    apply eq_of_add_mul_eq_add_mul _ _ (e₃ + e₄ + r₅.2.toNat) 0 _ hT₅_lt h_total_bound
    rw [hT₀] at h_pass1
    zify at h_pass1 h₅ ⊢
    linear_combination h_pass1 + h₅

/-! ### Correctness of `karatsubaMulLimbsRec` and `karatsubaMulLimbs` -/

/-- The middle term `A₀·B₁ + A₁·B₀` is bounded by `2 · β^(k+m)`, hence
    fits into `2*len - k` limbs (using `m ≥ 1`). -/
lemma mid_value_lt (A0 A1 B0 B1 : Nat) (k m : Nat)
    (hA0 : A0 < 2 ^ (64 * k)) (hA1 : A1 < 2 ^ (64 * m))
    (hB0 : B0 < 2 ^ (64 * k)) (hB1 : B1 < 2 ^ (64 * m))
    (h_mpos : 0 < m) :
    A0 * B1 + A1 * B0 < 2 ^ (64 * (k + m + m)) := by
  have h_pow_eq : 2 ^ (64 * (k + m + m)) = 2 ^ (64 * (k + m)) * 2 ^ (64 * m) := by
    rw [← Nat.pow_add]; congr 1; ring
  have h_β_ge_2 : 2 ≤ 2 ^ (64 * m) := by
    have : 2 ^ 1 ≤ 2 ^ (64 * m) := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  have h_km_eq : 2 ^ (64 * (k + m)) = 2 ^ (64 * k) * 2 ^ (64 * m) := by
    rw [← Nat.pow_add]; congr 1; ring
  have h_A0B1_lt : A0 * B1 < 2 ^ (64 * (k + m)) := by
    rw [h_km_eq]
    exact Nat.mul_lt_mul_of_lt_of_lt hA0 hB1
  have h_A1B0_lt : A1 * B0 < 2 ^ (64 * (k + m)) := by
    rw [h_km_eq, Nat.mul_comm (2 ^ (64 * k)) (2 ^ (64 * m))]
    exact Nat.mul_lt_mul_of_lt_of_lt hA1 hB0
  rw [h_pow_eq]
  have h_pos_km : 0 < 2 ^ (64 * (k + m)) := Nat.two_pow_pos _
  nlinarith

/-- The total `A·B = A₀·B₀ + (A₀·B₁+A₁·B₀)·β^k + A₁·B₁·β^(2k)` is bounded
    by `β^(2*len)`. -/
lemma total_lt (A0 A1 B0 B1 : Nat) (k m len : Nat)
    (hA0 : A0 < 2 ^ (64 * k)) (hA1 : A1 < 2 ^ (64 * m))
    (hB0 : B0 < 2 ^ (64 * k)) (hB1 : B1 < 2 ^ (64 * m))
    (hkm : k + m = len) :
    (A0 + A1 * 2 ^ (64 * k)) * (B0 + B1 * 2 ^ (64 * k)) < 2 ^ (64 * (2 * len)) := by
  have h_eq_len : 2 ^ (64 * len) = 2 ^ (64 * m) * 2 ^ (64 * k) := by
    rw [← Nat.pow_add]; congr 1; rw [show 64 * len = 64 * m + 64 * k from by omega]
  have bound_combined : ∀ X0 X1, X0 < 2 ^ (64 * k) → X1 < 2 ^ (64 * m) →
      X0 + X1 * 2 ^ (64 * k) < 2 ^ (64 * len) := by
    intro X0 X1 hX0 hX1
    rw [h_eq_len]
    have h_X1_succ : X1 + 1 ≤ 2 ^ (64 * m) := hX1
    have h_step : (X1 + 1) * 2 ^ (64 * k) ≤ 2 ^ (64 * m) * 2 ^ (64 * k) :=
      Nat.mul_le_mul_right _ h_X1_succ
    have h_expand : (X1 + 1) * 2 ^ (64 * k) = X1 * 2 ^ (64 * k) + 2 ^ (64 * k) := by ring
    omega
  have h_A_lt := bound_combined A0 A1 hA0 hA1
  have h_B_lt := bound_combined B0 B1 hB0 hB1
  have h_2len_eq : 2 ^ (64 * (2 * len)) = 2 ^ (64 * len) * 2 ^ (64 * len) := by
    rw [← Nat.pow_add]; congr 1; ring
  rw [h_2len_eq]
  exact Nat.mul_lt_mul_of_lt_of_lt h_A_lt h_B_lt

/-- The middle term computed by `middleBuf` (with sign-aware add/sub of `C₂`)
    equals `A₀·B₁ + A₁·B₀`.  This is the algebraic identity at the heart of
    Karatsuba: `(A₀ − A₁)(B₀ − B₁) = A₀·B₀ + A₁·B₁ − (A₀·B₁ + A₁·B₀)`,
    handled in ℕ by case analysis on the four sign combinations. -/
lemma middle_equals_cross_terms (A0 A1 B0 B1 : Nat) (sgnA sgnB : Bool)
    (hsgnA : sgnA = true ↔ A1 ≤ A0) (hsgnB : sgnB = true ↔ B1 ≤ B0)
    (absAv : Nat) (h_absA : absAv = if A1 ≤ A0 then A0 - A1 else A1 - A0)
    (absBv : Nat) (h_absB : absBv = if B1 ≤ B0 then B0 - B1 else B1 - B0) :
    (if sgnA == sgnB then A0 * B0 + A1 * B1 - absAv * absBv
                     else A0 * B0 + A1 * B1 + absAv * absBv)
      = A0 * B1 + A1 * B0 := by
  by_cases hA' : A1 ≤ A0
  · have h_sgnA : sgnA = true := hsgnA.mpr hA'
    by_cases hB' : B1 ≤ B0
    · -- A1 ≤ A0, B1 ≤ B0; sgnA = sgnB = true; subtract.
      have h_sgnB : sgnB = true := hsgnB.mpr hB'
      rw [h_sgnA, h_sgnB]
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [ite_eq_left hA'] at h_absA; rw [ite_eq_left hB'] at h_absB
      subst h_absA; subst h_absB
      have h_expand : (A0 - A1) * (B0 - B1) = A0*B0 + A1*B1 - A0*B1 - A1*B0 := by
        rw [Nat.sub_mul, Nat.mul_sub, Nat.mul_sub]
        have h1 : A0 * B1 ≤ A0 * B0 := Nat.mul_le_mul_left A0 hB'
        have h2 : A1 * B1 ≤ A1 * B0 := Nat.mul_le_mul_left A1 hB'
        have h3 : A1 * B0 ≤ A0 * B0 := Nat.mul_le_mul_right B0 hA'
        omega
      have h_le : A0 * B1 + A1 * B0 ≤ A0 * B0 + A1 * B1 := by nlinarith
      omega
    · -- A1 ≤ A0, B0 < B1; sgnA = true, sgnB = false; add.
      have h_sgnB : sgnB = false := by
        cases hb : sgnB
        · rfl
        · exact absurd (hsgnB.mp hb) hB'
      rw [h_sgnA, h_sgnB, ite_eq_right (by decide : ¬ ((true : Bool) == false) = true)]
      rw [ite_eq_left hA'] at h_absA; rw [ite_eq_right hB'] at h_absB
      subst h_absA; subst h_absB
      have hB_le : B0 ≤ B1 := by omega
      have h_expand : (A0 - A1) * (B1 - B0) = A0*B1 + A1*B0 - A0*B0 - A1*B1 := by
        rw [Nat.sub_mul, Nat.mul_sub, Nat.mul_sub]
        have h1 : A0 * B0 ≤ A0 * B1 := Nat.mul_le_mul_left A0 hB_le
        have h2 : A1 * B0 ≤ A1 * B1 := Nat.mul_le_mul_left A1 hB_le
        have h3 : A1 * B0 ≤ A0 * B0 := Nat.mul_le_mul_right B0 hA'
        omega
      have h_le : A0 * B0 + A1 * B1 ≤ A0 * B1 + A1 * B0 := by nlinarith
      omega
  · have h_sgnA : sgnA = false := by
      cases ha : sgnA
      · rfl
      · exact absurd (hsgnA.mp ha) hA'
    have hA_lt : A0 < A1 := by omega
    by_cases hB' : B1 ≤ B0
    · -- A0 < A1, B1 ≤ B0; sgnA = false, sgnB = true; add.
      have h_sgnB : sgnB = true := hsgnB.mpr hB'
      rw [h_sgnA, h_sgnB, ite_eq_right (by decide : ¬ ((false : Bool) == true) = true)]
      rw [ite_eq_right hA'] at h_absA; rw [ite_eq_left hB'] at h_absB
      subst h_absA; subst h_absB
      have hA_le : A0 ≤ A1 := by omega
      have h_expand : (A1 - A0) * (B0 - B1) = A1*B0 + A0*B1 - A0*B0 - A1*B1 := by
        rw [Nat.sub_mul, Nat.mul_sub, Nat.mul_sub]
        have h1 : A1 * B1 ≤ A1 * B0 := Nat.mul_le_mul_left A1 hB'
        have h2 : A0 * B1 ≤ A0 * B0 := Nat.mul_le_mul_left A0 hB'
        have h3 : A0 * B0 ≤ A1 * B0 := Nat.mul_le_mul_right B0 hA_le
        omega
      have h_le : A0 * B0 + A1 * B1 ≤ A0 * B1 + A1 * B0 := by nlinarith
      omega
    · -- A0 < A1, B0 < B1; sgnA = sgnB = false; subtract.
      have h_sgnB : sgnB = false := by
        cases hb : sgnB
        · rfl
        · exact absurd (hsgnB.mp hb) hB'
      rw [h_sgnA, h_sgnB]
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [ite_eq_right hA'] at h_absA; rw [ite_eq_right hB'] at h_absB
      subst h_absA; subst h_absB
      have hA_le : A0 ≤ A1 := by omega
      have hB_le : B0 ≤ B1 := by omega
      have h_expand : (A1 - A0) * (B1 - B0) = A1*B1 + A0*B0 - A0*B1 - A1*B0 := by
        rw [Nat.sub_mul, Nat.mul_sub, Nat.mul_sub]
        have h1 : A1 * B0 ≤ A1 * B1 := Nat.mul_le_mul_left A1 hB_le
        have h2 : A0 * B0 ≤ A0 * B1 := Nat.mul_le_mul_left A0 hB_le
        have h3 : A0 * B1 ≤ A1 * B1 := Nat.mul_le_mul_right B1 hA_le
        omega
      have h_le : A0 * B1 + A1 * B0 ≤ A0 * B0 + A1 * B1 := by nlinarith
      omega

/-- The bound `toNat C₂ ≤ toNat C₀ + toNat C₁` needed by `middleBuf_toNat`'s
    subtraction case (when `sameSign = true`). -/
lemma C2_le_C0_plus_C1 (A0 A1 B0 B1 : Nat) (sgnA sgnB : Bool)
    (hsgnA : sgnA = true ↔ A1 ≤ A0) (hsgnB : sgnB = true ↔ B1 ≤ B0)
    (absAv absBv : Nat)
    (h_absA : absAv = if A1 ≤ A0 then A0 - A1 else A1 - A0)
    (h_absB : absBv = if B1 ≤ B0 then B0 - B1 else B1 - B0)
    (h_same : (sgnA == sgnB) = true) :
    absAv * absBv ≤ A0 * B0 + A1 * B1 := by
  by_cases hA' : A1 ≤ A0
  · have h_sgnA : sgnA = true := hsgnA.mpr hA'
    by_cases hB' : B1 ≤ B0
    · have h_sgnB : sgnB = true := hsgnB.mpr hB'
      rw [ite_eq_left hA'] at h_absA; rw [ite_eq_left hB'] at h_absB
      subst h_absA; subst h_absB
      have h_expand : (A0 - A1) * (B0 - B1) = A0*B0 + A1*B1 - A0*B1 - A1*B0 := by
        rw [Nat.sub_mul, Nat.mul_sub, Nat.mul_sub]
        have h1 : A0 * B1 ≤ A0 * B0 := Nat.mul_le_mul_left A0 hB'
        have h2 : A1 * B1 ≤ A1 * B0 := Nat.mul_le_mul_left A1 hB'
        have h3 : A1 * B0 ≤ A0 * B0 := Nat.mul_le_mul_right B0 hA'
        omega
      omega
    · -- contradiction: sgnA = true, sgnB = false but h_same says equal.
      have h_sgnB : sgnB = false := by
        cases hb : sgnB
        · rfl
        · exact absurd (hsgnB.mp hb) hB'
      rw [h_sgnA, h_sgnB] at h_same; exact absurd h_same (by decide)
  · have h_sgnA : sgnA = false := by
      cases ha : sgnA
      · rfl
      · exact absurd (hsgnA.mp ha) hA'
    by_cases hB' : B1 ≤ B0
    · have h_sgnB : sgnB = true := hsgnB.mpr hB'
      rw [h_sgnA, h_sgnB] at h_same; exact absurd h_same (by decide)
    · rw [ite_eq_right hA'] at h_absA; rw [ite_eq_right hB'] at h_absB
      subst h_absA; subst h_absB
      have hA_le : A0 ≤ A1 := by omega
      have hB_le : B0 ≤ B1 := by omega
      have h_expand : (A1 - A0) * (B1 - B0) = A1*B1 + A0*B0 - A0*B1 - A1*B0 := by
        rw [Nat.sub_mul, Nat.mul_sub, Nat.mul_sub]
        have h1 : A1 * B0 ≤ A1 * B1 := Nat.mul_le_mul_left A1 hB_le
        have h2 : A0 * B0 ≤ A0 * B1 := Nat.mul_le_mul_left A0 hB_le
        have h3 : A0 * B1 ≤ A1 * B1 := Nat.mul_le_mul_right B1 hA_le
        omega
      omega

set_option maxHeartbeats 1600000 in
/-- Correctness of the size-tracked recursive version. -/
theorem karatsubaMulLimbsRec_toNat (threshold : Nat) :
    ∀ (len : Nat) (a b : Array UInt64) (loA loB : Nat)
      (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size),
    toNatLimbsList (karatsubaMulLimbsRec threshold a b loA loB len hA hB).val.toList
      = toNatLimbsList ((a.toList.drop loA).take len)
        * toNatLimbsList ((b.toList.drop loB).take len) := by
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
    intros a b loA loB hA hB
    unfold karatsubaMulLimbsRec
    by_cases h_base : len < 2 ∨ len < threshold
    · -- Base case: schoolbookMulLimbs.
      simp only [h_base, ↓reduceDIte]
      exact schoolbookMulLimbs_toNat a b loA len loB len hA hB
    · -- Recursive case.
      simp only [h_base, ↓reduceDIte]
      have hlen : 2 ≤ len := by omega
      set k := (len + 1) / 2 with hk_def
      set m := len - k with hm_def
      have hk_pos : 0 < k := by show 0 < (len + 1) / 2; omega
      have hk_le : k ≤ len := by show (len + 1) / 2 ≤ len; omega
      have hk_lt : k < len := by show (len + 1) / 2 < len; omega
      have hm_pos : 0 < m := by show 0 < len - (len + 1) / 2; omega
      have hm_le : m ≤ k := by show len - (len + 1) / 2 ≤ (len + 1) / 2; omega
      have hm_lt : m < len := by show len - (len + 1) / 2 < len; omega
      have hkm : k + m = len := by
        show (len + 1) / 2 + (len - (len + 1) / 2) = len; omega
      have hA0 : loA + k ≤ a.size := by omega
      have hB0 : loB + k ≤ b.size := by omega
      have hA1 : (loA + k) + m ≤ a.size := by omega
      have hB1 : (loB + k) + m ≤ b.size := by omega
      have hAabs : loA + k + m ≤ a.size := by omega
      have hBabs : loB + k + m ≤ b.size := by omega
      -- Bind the recursive results.
      set C0 := karatsubaMulLimbsRec threshold a b loA loB k hA0 hB0 with hC0_def
      set C1 := karatsubaMulLimbsRec threshold a b (loA + k) (loB + k) m hA1 hB1 with hC1_def
      set absA := absSubLimbsKM a loA k m hAabs hm_le hk_pos hm_pos with habsA_def
      set absB := absSubLimbsKM b loB k m hBabs hm_le hk_pos hm_pos with habsB_def
      have hAabs_lim : 0 + k ≤ absA.1.1.size := by rw [absA.1.2]; omega
      have hBabs_lim : 0 + k ≤ absB.1.1.size := by rw [absB.1.2]; omega
      set C2 := karatsubaMulLimbsRec threshold absA.1.1 absB.1.1 0 0 k
                  hAabs_lim hBabs_lim with hC2_def
      -- Slice values.
      set A0 := toNatLimbsList ((a.toList.drop loA).take k) with hA0_val
      set A1 := toNatLimbsList ((a.toList.drop (loA + k)).take m) with hA1_val
      set B0 := toNatLimbsList ((b.toList.drop loB).take k) with hB0_val
      set B1 := toNatLimbsList ((b.toList.drop (loB + k)).take m) with hB1_val
      -- Bounds.
      have hA0_lt : A0 < 2 ^ (64 * k) := slice_lt_pow a loA k
      have hB0_lt : B0 < 2 ^ (64 * k) := slice_lt_pow b loB k
      have hA1_lt : A1 < 2 ^ (64 * m) := slice_lt_pow a (loA + k) m
      have hB1_lt : B1 < 2 ^ (64 * m) := slice_lt_pow b (loB + k) m
      -- IH on k, m.
      have h_C0_toNat : toNatLimbsList C0.1.toList = A0 * B0 := by
        rw [hC0_def]; exact ih k hk_lt a b loA loB hA0 hB0
      have h_C1_toNat : toNatLimbsList C1.1.toList = A1 * B1 := by
        rw [hC1_def]; exact ih m hm_lt a b (loA + k) (loB + k) hA1 hB1
      -- absSubLimbsKM_toNat.
      have h_absA_props := absSubLimbsKM_toNat a loA k m hAabs hm_le hk_pos hm_pos
      rw [show absSubLimbsKM a loA k m hAabs hm_le hk_pos hm_pos = absA from rfl] at h_absA_props
      simp only at h_absA_props
      obtain ⟨hsignA, h_absA_val⟩ := h_absA_props
      have h_absB_props := absSubLimbsKM_toNat b loB k m hBabs hm_le hk_pos hm_pos
      rw [show absSubLimbsKM b loB k m hBabs hm_le hk_pos hm_pos = absB from rfl] at h_absB_props
      simp only at h_absB_props
      obtain ⟨hsignB, h_absB_val⟩ := h_absB_props
      -- IH on k for C2 (with absA, absB arrays).
      have h_absA_size : absA.1.1.size = k := absA.1.2
      have h_absB_size : absB.1.1.size = k := absB.1.2
      have h_C2_toNat : toNatLimbsList C2.1.toList
                       = toNatLimbsList absA.1.1.toList * toNatLimbsList absB.1.1.toList := by
        rw [hC2_def]
        have h_ih := ih k hk_lt absA.1.1 absB.1.1 0 0 hAabs_lim hBabs_lim
        rw [List.drop_zero, List.drop_zero] at h_ih
        rw [List.take_of_length_le (by rw [Array.length_toList, h_absA_size]),
            List.take_of_length_le (by rw [Array.length_toList, h_absB_size])] at h_ih
        exact h_ih
      have h_C2_value : toNatLimbsList C2.1.toList
                       = (if A1 ≤ A0 then A0 - A1 else A1 - A0) *
                         (if B1 ≤ B0 then B0 - B1 else B1 - B0) := by
        rw [h_C2_toNat, h_absA_val, h_absB_val]
      -- middleBuf_toNat.
      have h_sub_ok : (absA.2 == absB.2) = true →
          toNatLimbsList C2.1.toList ≤ toNatLimbsList C0.1.toList + toNatLimbsList C1.1.toList := by
        intro h_same
        rw [h_C2_value, h_C0_toNat, h_C1_toNat]
        exact C2_le_C0_plus_C1 A0 A1 B0 B1 absA.2 absB.2 hsignA hsignB
          _ _ rfl rfl h_same
      -- The middle term `C0 + C1 ∓ C2 = A0*B1 + A1*B0`.
      have h_middle_value :
          (if (absA.2 == absB.2) then
            toNatLimbsList C0.1.toList + toNatLimbsList C1.1.toList - toNatLimbsList C2.1.toList
          else
            toNatLimbsList C0.1.toList + toNatLimbsList C1.1.toList + toNatLimbsList C2.1.toList)
          = A0 * B1 + A1 * B0 := by
        rw [h_C0_toNat, h_C1_toNat, h_C2_value]
        exact middle_equals_cross_terms A0 A1 B0 B1 absA.2 absB.2 hsignA hsignB
          _ rfl _ rfl
      have h_2k_eq : 2 ^ (64 * (2 * k)) = 2 ^ (64 * k) * 2 ^ (64 * k) := pow_double_factor k
      have h_total_bound :
          toNatLimbsList C0.1.toList
          + (if (absA.2 == absB.2) then
              toNatLimbsList C0.1.toList + toNatLimbsList C1.1.toList
                - toNatLimbsList C2.1.toList
            else
              toNatLimbsList C0.1.toList + toNatLimbsList C1.1.toList
                + toNatLimbsList C2.1.toList) * 2 ^ (64 * k)
          + toNatLimbsList C1.1.toList * 2 ^ (64 * (2 * k))
          < 2 ^ (64 * (2 * len)) := by
        rw [h_middle_value, h_C0_toNat, h_C1_toNat]
        have h_factor : A0 * B0 + (A0 * B1 + A1 * B0) * 2 ^ (64 * k)
                          + A1 * B1 * 2 ^ (64 * (2 * k))
                       = (A0 + A1 * 2 ^ (64 * k)) * (B0 + B1 * 2 ^ (64 * k)) := by
          rw [h_2k_eq]; ring
        rw [h_factor]
        exact total_lt A0 A1 B0 B1 k m len hA0_lt hA1_lt hB0_lt hB1_lt hkm
      have hk2m : k ≤ 2 * m := by omega
      have h_assemble := karatsubaMulLimbsRec.assemble_toNat k m len C0.1 C1.1 C2.1
        (absA.2 == absB.2) C0.2 C1.2 C2.2 hkm hk_pos hm_pos hm_le hk2m h_sub_ok h_total_bound
      -- Combine.
      rw [h_assemble, h_middle_value, h_C0_toNat, h_C1_toNat]
      -- Final algebra: A * B = A0*B0 + (A0*B1 + A1*B0)*β^k + A1*B1*β^(2k).
      have h_slice_a : toNatLimbsList ((a.toList.drop loA).take len)
                         = A0 + A1 * 2 ^ (64 * k) := by
        rw [show len = k + m from hkm.symm]
        exact toNat_slice_split a loA k m (by omega)
      have h_slice_b : toNatLimbsList ((b.toList.drop loB).take len)
                         = B0 + B1 * 2 ^ (64 * k) := by
        rw [show len = k + m from hkm.symm]
        exact toNat_slice_split b loB k m (by omega)
      rw [h_slice_a, h_slice_b, h_2k_eq]
      ring

/-- Correctness of `karatsubaMulLimbs`: agrees with multiplication of the
    corresponding limb-slice integers. -/
theorem karatsubaMulLimbs_toNat (threshold : Nat) (a b : Array UInt64)
    (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    toNatLimbsList (karatsubaMulLimbs threshold a b loA loB len hA hB).toList
      = toNatLimbsList ((a.toList.drop loA).take len)
        * toNatLimbsList ((b.toList.drop loB).take len) :=
  karatsubaMulLimbsRec_toNat threshold len a b loA loB hA hB

/-! ### Correctness of the limb-level dispatcher and AzNat-level mul -/

/-- `toNat` of an array followed by zero-limb padding equals `toNat` of the
    original array. -/
lemma toNatLimbsList_append_zeros (l : List UInt64) (k : Nat) :
    toNatLimbsList (l ++ List.replicate k 0) = toNatLimbsList l := by
  rw [toNatLimbsList_append]
  have h_zero : toNatLimbsList (List.replicate k (0 : UInt64)) = 0 := by
    induction k with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, toNatLimbsList_cons, ih]; simp
  rw [h_zero]; ring

end Azurite.AzNat
