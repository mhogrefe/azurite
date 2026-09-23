/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.LimbDigitsPow2
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.GetBits
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.UInt64.Equiv.Digits
import Mathlib.Data.Nat.Digits.Lemmas

namespace Azurite.AzNat

/-! ### Helpers connecting `toNatLimbsList` and `Nat.ofDigits` -/

/-- `toNatLimbsList` is exactly `Nat.ofDigits` in base `2^64`. -/
private theorem toNatLimbsList_eq_ofDigits (l : List UInt64) :
    toNatLimbsList l = Nat.ofDigits (2 ^ 64) (l.map UInt64.toNat) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [toNatLimbsList_cons, ih, List.map_cons, Nat.ofDigits_cons]
    push_cast; ring

/-- `Nat.ofDigits` is unchanged by trailing zeros from `trimTrailingZeros`. -/
private theorem ofDigits_trimTrailingZeros (b : Nat) (a : Array UInt64) :
    Nat.ofDigits b ((trimTrailingZeros a).toList.map UInt64.toNat) =
    Nat.ofDigits b (a.toList.map UInt64.toNat) := by
  rw [trimTrailingZeros]
  by_cases h : a.size = 0
  · simp [h]
  · have h_idx : a.size - 1 < a.size :=
      Nat.sub_lt (Nat.pos_of_ne_zero h) Nat.zero_lt_one
    by_cases h_last : a[a.size - 1]'h_idx = 0
    · simp only [h, ↓reduceDIte, h_last, ite_true]
      rw [ofDigits_trimTrailingZeros b a.pop]
      have h_ne : a.toList ≠ [] := by
        intro he
        apply h
        have h_len : a.toList.length = 0 := by rw [he]; rfl
        rwa [Array.length_toList] at h_len
      have h_pop_eq : a.toList = a.pop.toList ++ [a.toList.getLast h_ne] := by
        rw [Array.toList_pop]
        exact (List.dropLast_append_getLast h_ne).symm
      have h_getLast : a.toList.getLast h_ne = a[a.size - 1]'h_idx := by
        rw [List.getLast_eq_getElem]
        simp
      rw [h_pop_eq, h_getLast, h_last, List.map_append, List.map_singleton]
      have : (0 : UInt64).toNat = 0 := rfl
      rw [this, Nat.ofDigits_append_zero]
    · simp [h, h_last]
  termination_by a.size
  decreasing_by simp [Array.size_pop]; omega

/-- Generic helper: if `b.back? ≠ some 0` and the mapped-toNat list is
    nonempty, its last element (in Nat) is nonzero. -/
private theorem getLast_map_toNat_ne_zero_of_back?_ne_some_zero
    {b : Array UInt64} (h_back : b.back? ≠ some 0)
    (h_ne : b.toList.map UInt64.toNat ≠ []) :
    (b.toList.map UInt64.toNat).getLast h_ne ≠ 0 := by
  have h_ne_b : b.toList ≠ [] := fun he => h_ne (by rw [he]; rfl)
  rw [List.getLast_map]
  intro h_eq
  apply h_back
  rw [← Array.getLast?_toList, List.getLast?_eq_some_getLast h_ne_b]
  congr 1
  apply UInt64.toNat.inj
  rw [h_eq]; rfl

/-! ### Per-limb padded contribution

For `1 ≤ k < 64` with `k | 64`, the per-limb digit list (zero-padded
to width `perLimb = 64 / k`) represents the limb's value in base
`2^k`, and each digit is `< 2^k`. -/

/-- Helper expanding the conditional padding to a single `++ replicate` form. -/
private def paddedDigitsPow2 (k : Nat) (l : UInt64) : Array UInt64 :=
  let d := UInt64.digitsPow2 k l
  if d.size < 64 / k then d ++ Array.replicate (64 / k - d.size) (0 : UInt64)
  else d

private theorem ofDigits_paddedDigitsPow2 (k : Nat) (hk : 1 ≤ k) (l : UInt64) :
    Nat.ofDigits (2 ^ k) ((paddedDigitsPow2 k l).toList.map UInt64.toNat) = l.toNat := by
  unfold paddedDigitsPow2
  have h_dig_lt : Nat.ofDigits (2 ^ k)
      ((UInt64.digitsPow2 k l).toList.map UInt64.toNat) = l.toNat := by
    rw [UInt64.digitsPow2_eq k hk, Nat.ofDigits_digits]
  by_cases h_lt : (UInt64.digitsPow2 k l).size < 64 / k
  · rw [ite_eq_left h_lt, Array.toList_append, Array.toList_replicate,
        List.map_append, List.map_replicate]
    have h0 : (0 : UInt64).toNat = 0 := rfl
    rw [h0, Nat.ofDigits_append_replicate_zero]
    exact h_dig_lt
  · rw [ite_eq_right h_lt]
    exact h_dig_lt

private theorem digit_lt_of_paddedDigitsPow2 (k : Nat) (hk : 1 ≤ k) (l : UInt64) :
    ∀ x ∈ (paddedDigitsPow2 k l).toList.map UInt64.toNat, x < 2 ^ k := by
  intro x hx
  unfold paddedDigitsPow2 at hx
  have h_dig_eq : (UInt64.digitsPow2 k l).toList.map UInt64.toNat =
      Nat.digits (2 ^ k) l.toNat := UInt64.digitsPow2_eq k hk l
  have h_2k : 1 < 2 ^ k := by
    calc (1 : Nat) = 2 ^ 0 := by simp
      _ < 2 ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
  by_cases h_lt : (UInt64.digitsPow2 k l).size < 64 / k
  · rw [ite_eq_left h_lt] at hx
    rw [Array.toList_append, Array.toList_replicate, List.map_append,
        List.map_replicate, List.mem_append] at hx
    cases hx with
    | inl hx =>
      rw [h_dig_eq] at hx
      exact Nat.digits_lt_base h_2k hx
    | inr hx =>
      rw [List.mem_replicate] at hx
      have : x = (0 : UInt64).toNat := hx.2
      rw [this]
      show 0 < 2 ^ k
      positivity
  · rw [ite_eq_right h_lt] at hx
    rw [h_dig_eq] at hx
    exact Nat.digits_lt_base h_2k hx

/-- Padded contribution has length exactly `64 / k` when `64 % k = 0`. -/
private theorem paddedDigitsPow2_size (k : Nat) (hk : 1 ≤ k) (hk_lt : k < 64)
    (hk_div : 64 % k = 0) (l : UInt64) :
    (paddedDigitsPow2 k l).size = 64 / k := by
  unfold paddedDigitsPow2
  have h_2k : 1 < 2 ^ k := by
    calc (1 : Nat) = 2 ^ 0 := by simp
      _ < 2 ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
  have h_size_dig : (UInt64.digitsPow2 k l).size = (Nat.digits (2 ^ k) l.toNat).length := by
    rw [Array.size_eq_length_toList, ← List.length_map (f := UInt64.toNat),
        UInt64.digitsPow2_eq k hk]
  have h_dig_size_le : (UInt64.digitsPow2 k l).size ≤ 64 / k := by
    rw [h_size_dig, Nat.digits_length_le_iff h_2k]
    have h_l : l.toNat < 2 ^ 64 := UInt64.toNat_lt l
    have h_k_times : k * (64 / k) = 64 := by
      have := Nat.div_add_mod 64 k
      omega
    have h_pow_eq : (2 ^ k) ^ (64 / k) = 2 ^ 64 := by
      rw [← Nat.pow_mul, h_k_times]
    omega
  by_cases h_lt : (UInt64.digitsPow2 k l).size < 64 / k
  · rw [ite_eq_left h_lt]
    rw [Array.size_append, Array.size_replicate]
    omega
  · rw [ite_eq_right h_lt]; omega

/-! ### Main correctness theorem -/

/-- Inductive accumulation lemma for the `k | 64 ∧ k < 64` branch's foldl. -/
private theorem ofDigits_foldl_padded (k : Nat) (hk : 1 ≤ k) (hk_lt : k < 64)
    (hk_div : 64 % k = 0) :
    ∀ (acc : Array UInt64) (ls : List UInt64),
    Nat.ofDigits (2 ^ k)
        ((ls.foldl (fun a l => a ++ paddedDigitsPow2 k l) acc).toList.map UInt64.toNat) =
      Nat.ofDigits (2 ^ k) (acc.toList.map UInt64.toNat)
      + (2 ^ k) ^ acc.size * toNatLimbsList ls := by
  intro acc ls
  induction ls generalizing acc with
  | nil =>
    show Nat.ofDigits (2 ^ k) (acc.toList.map UInt64.toNat) =
        Nat.ofDigits (2 ^ k) (acc.toList.map UInt64.toNat) + (2 ^ k) ^ acc.size * 0
    ring
  | cons l ls ih =>
    rw [List.foldl_cons, ih (acc ++ paddedDigitsPow2 k l)]
    rw [Array.toList_append, List.map_append, Nat.ofDigits_append]
    rw [Array.size_append, paddedDigitsPow2_size k hk hk_lt hk_div l]
    rw [List.length_map, Array.length_toList,
        ofDigits_paddedDigitsPow2 k hk l, toNatLimbsList_cons]
    have h_pow_64 : (2 ^ k) ^ (64 / k) = 2 ^ 64 := by
      rw [← Nat.pow_mul]
      congr 1
      have := Nat.div_add_mod 64 k
      omega
    have h_pow_split : (2 ^ k) ^ (acc.size + 64 / k) = (2 ^ k) ^ acc.size * 2 ^ 64 := by
      rw [Nat.pow_add, h_pow_64]
    rw [h_pow_split]
    ring

/-- `trimTrailingZeros` only removes elements; every survivor was already there. -/
private theorem mem_of_mem_trimTrailingZeros (a : Array UInt64) :
    ∀ y ∈ (trimTrailingZeros a).toList, y ∈ a.toList := by
  rw [trimTrailingZeros]
  by_cases h : a.size = 0
  · simp [h]
  · have h_idx : a.size - 1 < a.size :=
      Nat.sub_lt (Nat.pos_of_ne_zero h) Nat.zero_lt_one
    by_cases h_last : a[a.size - 1]'h_idx = 0
    · simp only [h, ↓reduceDIte, h_last, ite_true]
      intro y hy
      have := mem_of_mem_trimTrailingZeros a.pop y hy
      rw [Array.toList_pop] at this
      exact List.mem_of_mem_dropLast this
    · simp [h, h_last]
  termination_by a.size
  decreasing_by simp [Array.size_pop]; omega

/-- Inductive digit-bound for the foldl. -/
private theorem digit_lt_foldl_padded (k : Nat) (hk : 1 ≤ k) :
    ∀ (acc : Array UInt64) (ls : List UInt64),
    (∀ x ∈ acc.toList.map UInt64.toNat, x < 2 ^ k) →
    ∀ x ∈ (ls.foldl (fun a l => a ++ paddedDigitsPow2 k l) acc).toList.map UInt64.toNat,
      x < 2 ^ k := by
  intro acc ls h_acc
  induction ls generalizing acc with
  | nil => exact h_acc
  | cons l ls ih =>
    rw [List.foldl_cons]
    apply ih
    intro x hx
    rw [Array.toList_append, List.map_append, List.mem_append] at hx
    cases hx with
    | inl h => exact h_acc x h
    | inr h => exact digit_lt_of_paddedDigitsPow2 k hk l x h

/-- The `k | 64 ∧ k < 64` branch: per-limb digitsPow2, padded, concatenated, trimmed. -/
private theorem limbDigitsPow2_eq_of_div_64 (k : Nat) (hk : 1 ≤ k) (hk_lt : k < 64)
    (hk_div : 64 % k = 0) (n : AzNat) :
    (AzNat.trimTrailingZeros
        (n.limbs.foldl (init := (#[] : Array UInt64)) fun acc l => acc ++ paddedDigitsPow2 k l)
      ).toList.map UInt64.toNat = Nat.digits (2 ^ k) n.toNat := by
  have h_2k : 1 < 2 ^ k := by
    calc (1 : Nat) = 2 ^ 0 := by simp
      _ < 2 ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
  set raw := n.limbs.foldl (init := (#[] : Array UInt64))
              (fun acc l => acc ++ paddedDigitsPow2 k l) with hraw
  set L := (AzNat.trimTrailingZeros raw).toList.map UInt64.toNat with hL
  -- Value preservation
  have h_val : Nat.ofDigits (2 ^ k) L = n.toNat := by
    rw [hL, ofDigits_trimTrailingZeros]
    rw [hraw, ← Array.foldl_toList]
    have := ofDigits_foldl_padded k hk hk_lt hk_div #[] n.limbs.toList
    show Nat.ofDigits (2 ^ k) ((List.foldl _ #[] n.limbs.toList).toList.map UInt64.toNat) = n.toNat
    rw [this]
    show 0 + 1 * toNatLimbsList n.limbs.toList = n.toNat
    have : n.toNat = toNatLimbsList n.limbs.toList := rfl
    omega
  -- Bound: each digit < 2^k
  have h_raw_lt : ∀ x ∈ raw.toList.map UInt64.toNat, x < 2 ^ k := by
    rw [hraw, ← Array.foldl_toList]
    apply digit_lt_foldl_padded k hk #[] n.limbs.toList
    intro x hx; simp at hx
  have h_lt : ∀ x ∈ L, x < 2 ^ k := by
    intro x hx
    rw [hL, List.mem_map] at hx
    obtain ⟨u, hu_mem, hu_eq⟩ := hx
    apply h_raw_lt
    rw [List.mem_map]
    exact ⟨u, mem_of_mem_trimTrailingZeros raw u hu_mem, hu_eq⟩
  -- Last ≠ 0
  have h_last : ∀ hne : L ≠ [], L.getLast hne ≠ 0 := by
    rw [hL]
    exact getLast_map_toNat_ne_zero_of_back?_ne_some_zero
      (back?_trimTrailingZeros raw)
  rw [← h_val, Nat.digits_ofDigits (2 ^ k) h_2k L h_lt h_last]

/-! ### Reconstruction lemma for the `k ∤ 64` branch -/

/-- `Nat.ofDigits` applied to the truncated base-`b` expansion of `x` (the
    first `N` digits, computed as `x / b^i % b`) gives `x % b^N`. -/
private theorem ofDigits_ofFn_div_mod (b : Nat) (_hb : 1 < b) (x : Nat) :
    ∀ N : Nat,
    Nat.ofDigits b (List.ofFn (n := N) (fun i : Fin N => x / b ^ i.val % b)) = x % b ^ N := by
  intro N
  induction N with
  | zero => simp [List.ofFn_zero, Nat.mod_one]
  | succ N ih =>
    rw [List.ofFn_succ_last, Nat.ofDigits_append, List.length_ofFn]
    have h_castSucc :
        (List.ofFn (n := N) fun i : Fin N => x / b ^ (i.castSucc).val % b) =
        (List.ofFn (n := N) fun i : Fin N => x / b ^ i.val % b) := by
      simp
    rw [h_castSucc, ih, Nat.ofDigits_singleton]
    show x % b ^ N + b ^ N * (x / b ^ (Fin.last N).val % b) = x % b ^ (N + 1)
    rw [Fin.val_last, Nat.mod_pow_succ]

/-- The `k = 64` branch: the limb array is already the digit array. -/
private theorem limbDigitsPow2_eq_of_eq_64 (n : AzNat) :
    n.limbs.toList.map UInt64.toNat = Nat.digits (2 ^ 64) n.toNat := by
  have h_2k : 1 < 2 ^ 64 := by decide
  set L := n.limbs.toList.map UInt64.toNat with hL
  have h_val : Nat.ofDigits (2 ^ 64) L = n.toNat := by
    rw [hL, ← toNatLimbsList_eq_ofDigits]; rfl
  have h_lt : ∀ x ∈ L, x < 2 ^ 64 := by
    intro x hx
    rw [hL, List.mem_map] at hx
    obtain ⟨u, _, hu⟩ := hx
    rw [← hu]; exact UInt64.toNat_lt u
  have h_last : ∀ hne : L ≠ [], L.getLast hne ≠ 0 :=
    getLast_map_toNat_ne_zero_of_back?_ne_some_zero n.last_ne_zero
  rw [← h_val, Nat.digits_ofDigits (2 ^ 64) h_2k L h_lt h_last]

/-- **Correctness of `AzNat.limbDigitsPow2`.** For `k ∈ [1, 64]`, the
    function produces the base-`2^k` digit array of `n`, LSB-first,
    trimmed of trailing zeros. -/
theorem limbDigitsPow2_eq (k : Nat) (hk : 1 ≤ k) (hk64 : k ≤ 64) (n : AzNat) :
    (n.limbDigitsPow2 k).toList.map UInt64.toNat = Nat.digits (2 ^ k) n.toNat := by
  unfold AzNat.limbDigitsPow2
  by_cases h_64 : k = 64
  · rw [ite_eq_left h_64]
    subst h_64
    exact limbDigitsPow2_eq_of_eq_64 n
  · rw [ite_eq_right h_64]
    by_cases h_div : 1 ≤ k ∧ k < 64 ∧ 64 % k = 0
    · rw [dite_eq_left h_div]
      exact limbDigitsPow2_eq_of_div_64 k h_div.1 h_div.2.1 h_div.2.2 n
    · rw [dite_eq_right h_div]
      have h_lt_64 : 1 ≤ k ∧ k < 64 := ⟨hk, by omega⟩
      rw [dite_eq_left h_lt_64]
      -- k ∤ 64 case: getBits path
      have h_2k : 1 < 2 ^ k := by
        calc (1 : Nat) = 2 ^ 0 := by simp
          _ < 2 ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
      set totalBits := n.limbs.size * 64 with htotal
      set numDigits := (totalBits + k - 1) / k with hnum
      set raw := Array.ofFn (n := numDigits) fun i =>
        n.getBitsAsLimb (i.val * k) (i.val * k + k) (by have := h_lt_64.2; omega) with hraw
      set L := (AzNat.trimTrailingZeros raw).toList.map UInt64.toNat with hL
      -- Reconstruction: each digit is `n.toNat / 2^(i*k) % 2^k`.
      have h_raw_toNat : raw.toList.map UInt64.toNat =
          List.ofFn (n := numDigits)
            fun i : Fin numDigits => n.toNat / (2 ^ k) ^ i.val % 2 ^ k := by
        rw [hraw, Array.toList_ofFn, List.map_ofFn]
        congr; funext i
        show (n.getBitsAsLimb (i.val * k) (i.val * k + k) _).toNat = _
        rw [toNat_getBitsAsLimb]
        have h_pow : (2 ^ k) ^ i.val = 2 ^ (i.val * k) := by
          rw [← Nat.pow_mul, Nat.mul_comm]
        rw [h_pow, show i.val * k + k - i.val * k = k from by omega]
      -- Value: ofDigits (2^k) raw = n.toNat
      have h_n_lt : n.toNat < (2 ^ k) ^ numDigits := by
        have h_lt_total : n.toNat < 2 ^ totalBits := by
          show toNatLimbsList n.limbs.toList < 2 ^ (n.limbs.size * 64)
          have := toNatLimbsList_lt_pow n.limbs.toList
          rw [Array.length_toList] at this
          rw [show 64 * n.limbs.size = n.limbs.size * 64 from by ring] at this
          exact this
        have h_pow_eq : (2 ^ k) ^ numDigits = 2 ^ (k * numDigits) := by rw [← Nat.pow_mul]
        rw [h_pow_eq]
        have h_k_nd : totalBits ≤ k * numDigits := by
          rw [hnum]
          have := Nat.div_add_mod (totalBits + k - 1) k
          have h_mod_lt : (totalBits + k - 1) % k < k := Nat.mod_lt _ (by omega)
          omega
        have h_pow_le : 2 ^ totalBits ≤ 2 ^ (k * numDigits) :=
          Nat.pow_le_pow_right (by omega) h_k_nd
        omega
      have h_val : Nat.ofDigits (2 ^ k) L = n.toNat := by
        rw [hL, ofDigits_trimTrailingZeros, h_raw_toNat,
            ofDigits_ofFn_div_mod (2 ^ k) h_2k n.toNat numDigits]
        exact Nat.mod_eq_of_lt h_n_lt
      -- Bound: each digit < 2^k.
      have h_raw_lt : ∀ x ∈ raw.toList.map UInt64.toNat, x < 2 ^ k := by
        rw [h_raw_toNat]
        intro x hx
        rw [List.mem_ofFn] at hx
        obtain ⟨i, hi⟩ := hx
        rw [← hi]
        exact Nat.mod_lt _ (by positivity)
      have h_lt : ∀ x ∈ L, x < 2 ^ k := by
        intro x hx
        rw [hL, List.mem_map] at hx
        obtain ⟨u, hu_mem, hu_eq⟩ := hx
        apply h_raw_lt
        rw [List.mem_map]
        exact ⟨u, mem_of_mem_trimTrailingZeros raw u hu_mem, hu_eq⟩
      -- Last ≠ 0.
      have h_last : ∀ hne : L ≠ [], L.getLast hne ≠ 0 := by
        rw [hL]
        exact getLast_map_toNat_ne_zero_of_back?_ne_some_zero
          (back?_trimTrailingZeros raw)
      rw [← h_val, Nat.digits_ofDigits (2 ^ k) h_2k L h_lt h_last]

end Azurite.AzNat
