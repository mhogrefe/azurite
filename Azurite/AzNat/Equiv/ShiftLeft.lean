/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.Equiv.Basic

namespace Azurite.AzNat

/-- Computing a single limb of the left-shift: write the input `x` shifted
    left by `sh` bits OR-ed with the incoming carry, and the outgoing carry
    is the top `sh` bits of `x`. -/
lemma limb_shift_step (x carry : UInt64) (sh : Nat)
    (hsh_lb : 1 ≤ sh) (hsh_ub : sh ≤ 63) (hcarry : carry.toNat < 2 ^ sh) :
    ((x <<< UInt64.ofNat sh) ||| carry).toNat
        + (x >>> UInt64.ofNat (64 - sh)).toNat * 2 ^ 64
      = x.toNat * 2 ^ sh + carry.toNat
    ∧ (x >>> UInt64.ofNat (64 - sh)).toNat < 2 ^ sh := by
  have h_pow_gt_64 : (2 : Nat) ^ 64 > 64 := by decide
  have hsh_lt : sh < 64 := by omega
  have h_mod : sh % 64 = sh := Nat.mod_eq_of_lt hsh_lt
  have h_ofNat : (UInt64.ofNat sh).toNat = sh := by
    show sh % 2 ^ 64 = sh
    exact Nat.mod_eq_of_lt (by omega)
  have h_ofNat' : (UInt64.ofNat (64 - sh)).toNat = 64 - sh := by
    show (64 - sh) % 2 ^ 64 = 64 - sh
    exact Nat.mod_eq_of_lt (by omega)
  have h_sub_mod : (64 - sh) % 64 = 64 - sh := Nat.mod_eq_of_lt (by omega)
  have hxlt : x.toNat < 2 ^ 64 := UInt64.toNat_lt _
  have h_pow_eq : 2 ^ (64 - sh) * 2 ^ sh = 2 ^ 64 := by
    rw [← Nat.pow_add]; congr 1; omega
  -- Compute the right shift (new carry)
  have h_shr : (x >>> UInt64.ofNat (64 - sh)).toNat = x.toNat / 2 ^ (64 - sh) := by
    rw [UInt64.toNat_shiftRight, h_ofNat', h_sub_mod, Nat.shiftRight_eq_div_pow]
  have h_shr_lt : (x >>> UInt64.ofNat (64 - sh)).toNat < 2 ^ sh := by
    rw [h_shr]
    apply Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _) |>.mpr
    rw [Nat.mul_comm, h_pow_eq]
    exact hxlt
  -- Decomposition: x.toNat = 2^(64-sh) * (x.toNat / 2^(64-sh)) + (x.toNat % 2^(64-sh))
  have h_div_mod : x.toNat = 2 ^ (64 - sh) * (x.toNat / 2 ^ (64 - sh))
                           + x.toNat % 2 ^ (64 - sh) := (Nat.div_add_mod _ _).symm
  have h_mod_lt : x.toNat % 2 ^ (64 - sh) < 2 ^ (64 - sh) := Nat.mod_lt _ (Nat.two_pow_pos _)
  -- Compute the left shift
  have h_shl_nat : ((x <<< UInt64.ofNat sh).toNat)
                    = (x.toNat * 2 ^ sh) % 2 ^ 64 := by
    rw [UInt64.toNat_shiftLeft, h_ofNat, h_mod, Nat.shiftLeft_eq]
  have h_xtimes : x.toNat * 2 ^ sh
        = (x.toNat / 2 ^ (64 - sh)) * 2 ^ 64
          + (x.toNat % 2 ^ (64 - sh)) * 2 ^ sh := by
    conv_lhs => rw [h_div_mod]
    rw [Nat.add_mul]
    have : 2 ^ (64 - sh) * (x.toNat / 2 ^ (64 - sh)) * 2 ^ sh
         = (x.toNat / 2 ^ (64 - sh)) * (2 ^ (64 - sh) * 2 ^ sh) := by ring
    rw [this, h_pow_eq]
  have h_lowpart : (x.toNat % 2 ^ (64 - sh)) * 2 ^ sh < 2 ^ 64 := by
    rw [← h_pow_eq]
    exact Nat.mul_lt_mul_of_pos_right h_mod_lt (Nat.two_pow_pos _)
  have h_shl_nat' : (x <<< UInt64.ofNat sh).toNat
                    = (x.toNat % 2 ^ (64 - sh)) * 2 ^ sh := by
    rw [h_shl_nat, h_xtimes, Nat.add_comm, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt h_lowpart]
  -- OR with carry = addition (since carry < 2^sh and (x << sh) has low sh bits zero)
  have h_or_add : (x <<< UInt64.ofNat sh).toNat ||| carry.toNat
                  = (x <<< UInt64.ofNat sh).toNat + carry.toNat := by
    rw [h_shl_nat']
    -- Show: (k * 2^sh) ||| carry = (k * 2^sh) + carry where carry < 2^sh
    set k := x.toNat % 2 ^ (64 - sh)
    rw [show k * 2 ^ sh = 2 ^ sh * k from Nat.mul_comm _ _]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add k hcarry j]
    by_cases hj : j < sh
    · simp [hj]
      have h_mul_test : (2 ^ sh * k).testBit j = false := by
        have : (2 ^ sh * k + 0).testBit j = if j < sh then (0 : Nat).testBit j else k.testBit (j - sh) := by
          exact Nat.testBit_two_pow_mul_add k (Nat.two_pow_pos _) j
        rw [Nat.add_zero] at this
        rw [this]
        simp [hj]
      rw [h_mul_test]
      simp
    · simp [hj]
      have hj' : sh ≤ j := by omega
      have h_carry_test : carry.toNat.testBit j = false := by
        apply Nat.testBit_lt_two_pow
        exact lt_of_lt_of_le hcarry (Nat.pow_le_pow_right (by omega) hj')
      rw [h_carry_test]
      rw [show (2 : Nat) ^ sh * k = 2 ^ sh * k + 0 from (Nat.add_zero _).symm]
      rw [Nat.testBit_two_pow_mul_add k (Nat.two_pow_pos sh) j]
      simp [hj]
  have h_or : ((x <<< UInt64.ofNat sh) ||| carry).toNat
                = (x <<< UInt64.ofNat sh).toNat + carry.toNat := by
    rw [UInt64.toNat_or, h_or_add]
  refine ⟨?_, h_shr_lt⟩
  rw [h_or, h_shl_nat', h_shr, h_xtimes]
  ring

private lemma toNatLimbsList_take_succ (a : Array UInt64) (i hi : Nat)
    (h : i < a.size) (hi_lt : i + 1 ≤ hi) :
    toNatLimbsList ((a.toList.drop i).take (hi - i))
      = a[i].toNat + toNatLimbsList ((a.toList.drop (i + 1)).take (hi - (i + 1))) * 2 ^ 64 := by
  have h_len : a.toList.length = a.size := rfl
  have h_lt_list : i < a.toList.length := by rw [h_len]; exact h
  rw [List.drop_eq_getElem_cons h_lt_list]
  have h_sub : hi - i = (hi - (i + 1)) + 1 := by omega
  rw [h_sub, List.take_succ_cons, toNatLimbsList_cons]
  rw [show a.toList[i] = a[i] from (Array.getElem_toList h).symm]
  ring

private lemma shiftLimbsLeft.go_toList_take (hi sh : Nat) (a : Array UInt64) (i : Nat)
    (carry : UInt64) (h_size : hi ≤ a.size) :
    (shiftLimbsLeft.go hi sh a i carry h_size).1.toList.take i = a.toList.take i := by
  induction hi_sub_i : hi - i generalizing a i carry with
  | zero =>
    have h_ge : hi ≤ i := by omega
    have h_eq : shiftLimbsLeft.go hi sh a i carry h_size = (a, carry) := by
      conv_lhs => rw [shiftLimbsLeft.go]
      simp [Nat.not_lt.mpr h_ge]
    rw [h_eq]
  | succ n ih =>
    have h_lt : i < hi := by omega
    have h_i_size : i < a.size := Nat.lt_of_lt_of_le h_lt h_size
    have h_eq : shiftLimbsLeft.go hi sh a i carry h_size
                = shiftLimbsLeft.go hi sh
                    (a.set i ((a[i] <<< UInt64.ofNat sh) ||| carry)) (i + 1)
                    (a[i] >>> UInt64.ofNat (64 - sh))
                    (by rw [Array.size_set]; exact h_size) := by
      conv_lhs => rw [shiftLimbsLeft.go]
      simp [h_lt]
    rw [h_eq]
    have h_rec : hi - (i + 1) = n := by omega
    set a' := a.set i ((a[i] <<< UInt64.ofNat sh) ||| carry) with ha'_def
    set newCarry := a[i] >>> UInt64.ofNat (64 - sh) with hnc_def
    have h_size' : hi ≤ a'.size := by rw [ha'_def, Array.size_set]; exact h_size
    have h_ih := ih a' (i + 1) newCarry h_size' h_rec
    have h_take_succ_take_i : List.take i
          ((shiftLimbsLeft.go hi sh a' (i + 1) newCarry h_size').1.toList.take (i + 1))
                    = (shiftLimbsLeft.go hi sh a' (i + 1) newCarry h_size').1.toList.take i := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [← h_take_succ_take_i, h_ih]
    rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [ha'_def, Array.toList_set]
    rw [List.take_set]
    rw [List.set_eq_of_length_le]
    rw [List.length_take]
    have h_len : a.toList.length = a.size := rfl
    rw [h_len]
    omega

/-- Invariant of `shiftLimbsLeft.go`: starting from state `(a, i, carry)`, the final
    result's slice `[i, hi)` plus the final carry at position `hi` equals the original
    slice's shifted value plus the input carry at position `i`. -/
private lemma shiftLimbsLeft.go_correct (hi sh : Nat) (hsh_lb : 1 ≤ sh) (hsh_ub : sh ≤ 63)
    (a : Array UInt64) (i : Nat) (carry : UInt64) (h_size : hi ≤ a.size)
    (hcarry : carry.toNat < 2 ^ sh) :
    toNatLimbsList (((shiftLimbsLeft.go hi sh a i carry h_size).1.toList.drop i).take (hi - i))
      + (shiftLimbsLeft.go hi sh a i carry h_size).2.toNat * 2 ^ (64 * (hi - i))
      = toNatLimbsList ((a.toList.drop i).take (hi - i)) * 2 ^ sh + carry.toNat := by
  induction hi_sub_i : hi - i generalizing a i carry with
  | zero =>
    have h_ge : hi ≤ i := by omega
    have h_eq : shiftLimbsLeft.go hi sh a i carry h_size = (a, carry) := by
      conv_lhs => rw [shiftLimbsLeft.go]
      simp [Nat.not_lt.mpr h_ge]
    rw [h_eq]
    simp [toNatLimbsList]
  | succ n ih =>
    have h_lt : i < hi := by omega
    have h_i_size : i < a.size := Nat.lt_of_lt_of_le h_lt h_size
    set x := a[i] with hx_def
    set newCarry := x >>> UInt64.ofNat (64 - sh) with hnc_def
    set newVal := (x <<< UInt64.ofNat sh) ||| carry with hnv_def
    set a' := a.set i newVal with ha'_def
    have h_size' : hi ≤ a'.size := by rw [ha'_def, Array.size_set]; exact h_size
    have h_eq : shiftLimbsLeft.go hi sh a i carry h_size
                = shiftLimbsLeft.go hi sh a' (i + 1) newCarry h_size' := by
      conv_lhs => rw [shiftLimbsLeft.go]
      simp [h_lt, hx_def, hnc_def, hnv_def, ha'_def]
    -- Single-limb identity
    obtain ⟨h_limb_eq, h_newCarry_lt⟩ := limb_shift_step x carry sh hsh_lb hsh_ub hcarry
    -- Apply inductive hypothesis
    have h_rec : hi - (i + 1) = n := by omega
    have h_ih := ih a' (i + 1) newCarry h_size' h_newCarry_lt h_rec
    -- Relate result slice at i to slice at i+1: result.1[i] = newVal
    have h_prefix := shiftLimbsLeft.go_toList_take hi sh a' (i + 1) newCarry h_size'
    -- Both sides have i < i+1 so we can extract position i of the prefix
    have h_res_size :
        (shiftLimbsLeft.go hi sh a' (i + 1) newCarry h_size').1.size = a'.size :=
      shiftLimbsLeft.go_size hi sh a' (i + 1) newCarry h_size'
    have h_res_size_eq : (shiftLimbsLeft.go hi sh a' (i + 1) newCarry h_size').1.size = a.size := by
      rw [h_res_size, ha'_def, Array.size_set]
    have h_res_i_size : i < (shiftLimbsLeft.go hi sh a' (i + 1) newCarry h_size').1.size := by
      rw [h_res_size_eq]; exact h_i_size
    have h_res_i : (shiftLimbsLeft.go hi sh a' (i + 1) newCarry h_size').1[i]'h_res_i_size
                  = newVal := by
      have h_toList_len : ((shiftLimbsLeft.go hi sh a' (i + 1) newCarry h_size').1.toList).length
                        = a.size := by
        rw [Array.length_toList]; exact h_res_size_eq
      have h_i_lt_toList : i < ((shiftLimbsLeft.go hi sh a' (i + 1) newCarry h_size').1.toList).length := by
        rw [h_toList_len]; exact h_i_size
      have h_a'_i_lt : i < a'.toList.length := by
        rw [Array.length_toList, ha'_def, Array.size_set]; exact h_i_size
      have h_both_eq_take :
        (shiftLimbsLeft.go hi sh a' (i + 1) newCarry h_size').1.toList[i]'h_i_lt_toList
          = a'.toList[i]'h_a'_i_lt := by
        have hlen_L : (((shiftLimbsLeft.go hi sh a' (i + 1) newCarry h_size').1.toList).take (i + 1)).length
                    = i + 1 := by
          rw [List.length_take]; rw [h_toList_len]; omega
        have hlen_R : (a'.toList.take (i + 1)).length = i + 1 := by
          rw [List.length_take, Array.length_toList, ha'_def, Array.size_set]; omega
        have h_i_lt_L : i < (((shiftLimbsLeft.go hi sh a' (i + 1) newCarry h_size').1.toList).take (i + 1)).length := by
          rw [hlen_L]; omega
        have h_i_lt_R : i < (a'.toList.take (i + 1)).length := by rw [hlen_R]; omega
        have hA : (((shiftLimbsLeft.go hi sh a' (i + 1) newCarry h_size').1.toList).take (i + 1))[i]'h_i_lt_L
                = (a'.toList.take (i + 1))[i]'h_i_lt_R := by
          congr 1
        rw [List.getElem_take, List.getElem_take] at hA
        exact hA
      rw [← Array.getElem_toList h_res_i_size, h_both_eq_take]
      show (a.set i newVal).toList[i] = newVal
      simp
    rw [h_eq]
    -- Rewrite n + 1 back to hi - i to match toNatLimbsList_take_succ
    rw [show (n + 1) = hi - i from hi_sub_i.symm]
    -- Expand toNatLimbsList on both sides using toNatLimbsList_take_succ
    rw [toNatLimbsList_take_succ (shiftLimbsLeft.go hi sh a' (i + 1) newCarry h_size').1 i hi
          h_res_i_size h_lt]
    rw [h_res_i]
    rw [toNatLimbsList_take_succ a i hi h_i_size h_lt]
    -- Clean up: 2 ^ (64 * (hi - i)) = 2 ^ (64 * (hi - (i+1))) * 2 ^ 64
    have h_pow : (2 : Nat) ^ (64 * (hi - i))
                = 2 ^ (64 * (hi - (i + 1))) * 2 ^ 64 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [h_pow]
    -- We also need the IH statement to apply; note go at (i+1) uses a'
    -- and a'.toList.drop (i+1) = a.toList.drop (i+1) (set at i doesn't affect drop (i+1))
    have h_drop_eq : a'.toList.drop (i + 1) = a.toList.drop (i + 1) := by
      rw [ha'_def, Array.toList_set, List.drop_set]
      simp
    rw [← h_drop_eq]
    -- Now shape: newVal.toNat + P * 2^64 + res.2.toNat * (2^(64*...) * 2^64)
    --         = (a[i].toNat + Q * 2^64) * 2^sh + carry.toNat
    -- where P = toNatLimbsList(res.take at i+1), Q = toNatLimbsList(a'.take at i+1)
    -- The IH gives P + res.2.toNat * 2^(64*(hi - (i+1))) = Q * 2^sh + newCarry.toNat
    -- And the limb equation gives newVal.toNat + newCarry.toNat * 2^64 = a[i].toNat * 2^sh + carry.toNat
    -- Combining:
    have h_ih' := h_ih
    rw [← h_rec] at h_ih'
    -- Denote
    set P := toNatLimbsList (((shiftLimbsLeft.go hi sh a' (i + 1) newCarry h_size').1.toList.drop (i + 1)).take (hi - (i + 1))) with hP_def
    set Q := toNatLimbsList ((a'.toList.drop (i + 1)).take (hi - (i + 1))) with hQ_def
    set R := (shiftLimbsLeft.go hi sh a' (i + 1) newCarry h_size').2.toNat with hR_def
    -- IH: P + R * 2^(64 * (hi - (i+1))) = Q * 2^sh + newCarry.toNat
    change newVal.toNat + P * 2 ^ 64 + R * (2 ^ (64 * (hi - (i + 1))) * 2 ^ 64)
         = (x.toNat + Q * 2 ^ 64) * 2 ^ sh + carry.toNat
    -- Rearrange: newVal + P * 2^64 + R * 2^(64*(hi-(i+1))) * 2^64
    --         = newVal + (P + R * 2^(64*(hi-(i+1)))) * 2^64
    --         = newVal + (Q * 2^sh + newCarry.toNat) * 2^64      [by IH]
    --         = newVal + newCarry.toNat * 2^64 + Q * 2^sh * 2^64
    --         = (newVal + newCarry.toNat * 2^64) + Q * 2^sh * 2^64
    --         = (x.toNat * 2^sh + carry.toNat) + Q * 2^sh * 2^64  [by limb eq]
    --         = (x.toNat + Q * 2^64) * 2^sh + carry.toNat
    have h1 : newVal.toNat + P * 2 ^ 64 + R * (2 ^ (64 * (hi - (i + 1))) * 2 ^ 64)
            = newVal.toNat + (P + R * 2 ^ (64 * (hi - (i + 1)))) * 2 ^ 64 := by ring
    rw [h1, h_ih']
    -- Now: newVal + (Q * 2^sh + newCarry) * 2^64 = (x + Q * 2^64) * 2^sh + carry
    have h2 : newVal.toNat + (Q * 2 ^ sh + newCarry.toNat) * 2 ^ 64
            = (newVal.toNat + newCarry.toNat * 2 ^ 64) + Q * 2 ^ sh * 2 ^ 64 := by ring
    rw [h2, h_limb_eq]
    ring

/-- Correctness of `shiftLimbsLeft`: the modified limbs `[lo, hi)` plus the returned
    carry at the top represent the original slice shifted left by `sh` bits. -/
theorem shiftLimbsLeft_toNat (a : Array UInt64) (lo hi sh : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size)
    (hsh_lb : 1 ≤ sh) (hsh_ub : sh ≤ 63) :
    let (a', carry) := shiftLimbsLeft a lo hi sh hlo hhi hsh_lb hsh_ub
    toNatLimbsList ((a'.toList.drop lo).take (hi - lo))
        + carry.toNat * 2 ^ (64 * (hi - lo))
      = toNatLimbsList ((a.toList.drop lo).take (hi - lo)) * 2 ^ sh := by
  have hcarry : (0 : UInt64).toNat < 2 ^ sh := by
    show 0 < 2 ^ sh
    exact Nat.two_pow_pos _
  have h := shiftLimbsLeft.go_correct hi sh hsh_lb hsh_ub a lo 0 hhi hcarry
  simp at h
  exact h

/-- `shiftLimbsLeft` leaves the prefix `[0, lo)` unchanged. -/
theorem shiftLimbsLeft_toList_take (a : Array UInt64) (lo hi sh : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size)
    (hsh_lb : 1 ≤ sh) (hsh_ub : sh ≤ 63) :
    (shiftLimbsLeft a lo hi sh hlo hhi hsh_lb hsh_ub).1.toList.take lo
      = a.toList.take lo :=
  shiftLimbsLeft.go_toList_take hi sh a lo 0 hhi

/-- `toNatLimbsList` of a `List.replicate k 0` is zero. -/
private lemma toNatLimbsList_replicate_zero (k : Nat) :
    toNatLimbsList (List.replicate k (0 : UInt64)) = 0 := by
  induction k with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, toNatLimbsList_cons, ih]; simp

/-- The carry returned by `shiftLimbsLeft.go` is bounded by `2^sh`. -/
private lemma shiftLimbsLeft.go_carry_lt (hi sh : Nat) (hsh_lb : 1 ≤ sh) (hsh_ub : sh ≤ 63)
    (a : Array UInt64) (i : Nat) (carry : UInt64) (h_size : hi ≤ a.size)
    (hcarry : carry.toNat < 2 ^ sh) :
    (shiftLimbsLeft.go hi sh a i carry h_size).2.toNat < 2 ^ sh := by
  induction hi_sub_i : hi - i generalizing a i carry with
  | zero =>
    have h_ge : hi ≤ i := by omega
    rw [shiftLimbsLeft.go]
    simp [Nat.not_lt.mpr h_ge]
    exact hcarry
  | succ n ih =>
    have h_lt : i < hi := by omega
    have h_i_size : i < a.size := Nat.lt_of_lt_of_le h_lt h_size
    rw [shiftLimbsLeft.go]
    simp only [h_lt, dite_eq_left]
    have h_rec : hi - (i + 1) = n := by omega
    obtain ⟨_, h_newCarry_lt⟩ :=
      limb_shift_step a[i] carry sh hsh_lb hsh_ub hcarry
    exact ih _ _ _ (by rw [Array.size_set]; exact h_size) h_newCarry_lt h_rec

/-- The carry returned by `shiftLimbsLeft` is bounded by `2^sh`. -/
theorem shiftLimbsLeft_carry_lt (a : Array UInt64) (lo hi sh : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size)
    (hsh_lb : 1 ≤ sh) (hsh_ub : sh ≤ 63) :
    (shiftLimbsLeft a lo hi sh hlo hhi hsh_lb hsh_ub).2.toNat < 2 ^ sh :=
  shiftLimbsLeft.go_carry_lt hi sh hsh_lb hsh_ub a lo 0 hhi (by
    show 0 < 2 ^ sh
    exact Nat.two_pow_pos _)

/-- The carry-out of `shiftLimbsLeft.go hi sh a i carry` (when `i < hi`) equals
    `a[hi - 1] >>> (64 - sh)`. The original limb at position `hi - 1` is read
    because writes only touch positions `< hi - 1` before that step. -/
private lemma shiftLimbsLeft.go_carry_eq (hi sh : Nat)
    (a : Array UInt64) (i : Nat) (carry : UInt64) (h_size : hi ≤ a.size)
    (hi_lt : i < hi) :
    (shiftLimbsLeft.go hi sh a i carry h_size).2
      = a[hi - 1]'(by omega) >>> UInt64.ofNat (64 - sh) := by
  induction hi_sub_i : hi - i generalizing a i carry with
  | zero => omega
  | succ n ih =>
    have h_i_size : i < a.size := Nat.lt_of_lt_of_le hi_lt h_size
    rw [shiftLimbsLeft.go]
    simp only [hi_lt, dite_eq_left]
    by_cases hn : n = 0
    · -- Base: i + 1 = hi, recursive call returns its carry input.
      have hi1_eq : i + 1 = hi := by omega
      have h_ge : ¬ i + 1 < hi := by omega
      rw [shiftLimbsLeft.go]
      simp only [h_ge, dite_eq_right, not_false_eq_true]
      congr 1
      have hi_eq : hi - 1 = i := by omega
      subst hi_eq; rfl
    · -- Inductive: i + 1 < hi, apply IH to the recursive call.
      have hi1_lt : i + 1 < hi := by omega
      have h_rec : hi - (i + 1) = n := by omega
      have h_new_size : hi ≤ (a.set i ((a[i] <<< UInt64.ofNat sh) ||| carry)).size := by
        rw [Array.size_set]; exact h_size
      rw [ih _ _ _ h_new_size hi1_lt h_rec]
      have h_ne : i ≠ hi - 1 := by omega
      rw [Array.getElem_set_ne _ _ h_ne]

/-- The carry-out of `shiftLimbsLeft a lo hi sh` (when `lo < hi`) equals
    `a[hi - 1] >>> (64 - sh)`. -/
theorem shiftLimbsLeft_carry_eq (a : Array UInt64) (lo hi sh : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size)
    (hsh_lb : 1 ≤ sh) (hsh_ub : sh ≤ 63) (hlo_lt : lo < hi) :
    (shiftLimbsLeft a lo hi sh hlo hhi hsh_lb hsh_ub).2
      = a[hi - 1]'(by omega) >>> UInt64.ofNat (64 - sh) :=
  shiftLimbsLeft.go_carry_eq hi sh a lo 0 hhi hlo_lt

/-- `shiftLeftMul64 a k` represents `a * 2^(64*k)`. -/
theorem toNat_shiftLeftMul64 (a : AzNat) (k : Nat) :
    (shiftLeftMul64 a k).toNat = a.toNat * 2 ^ (64 * k) := by
  by_cases hz : a.limbs.size = 0
  · have h_toNat_zero : a.toNat = 0 := by
      show toNatLimbsList a.limbs.toList = 0
      have h_len : a.limbs.toList.length = 0 := hz
      have h_nil : a.limbs.toList = [] := by simp_all
      rw [h_nil]; rfl
    have h_eq : shiftLeftMul64 a k = a := by unfold shiftLeftMul64; rw [dite_eq_left hz]
    rw [h_eq, h_toNat_zero]; simp
  · have h_limbs : (shiftLeftMul64 a k).limbs = Array.replicate k 0 ++ a.limbs := by
      unfold shiftLeftMul64; rw [dite_eq_right hz]
    show toNatLimbsList (shiftLeftMul64 a k).limbs.toList = _
    rw [h_limbs, Array.toList_append, Array.toList_replicate]
    rw [toNatLimbsList_append, toNatLimbsList_replicate_zero, List.length_replicate]
    show toNatLimbsList a.limbs.toList * 2^(64*k) + 0 = toNatLimbsList a.limbs.toList * 2^(64*k)
    ring

/-- Correctness of `shiftLeftGeneralLimbs`. -/
theorem toNat_shiftLeftGeneralLimbs (a : AzNat) (sh : Nat)
    (hz : ¬ a.limbs.size = 0) (hsm : ¬ sh % 64 = 0) :
    toNatLimbsList (shiftLeftGeneralLimbs a sh hz hsm).toList = a.toNat * 2 ^ sh := by
  have hn_pos : 0 < a.limbs.size := Nat.pos_of_ne_zero hz
  have h_last_idx_lt : a.limbs.size - 1 < a.limbs.size := Nat.sub_lt hn_pos Nat.zero_lt_one
  have hsh_lb : 1 ≤ sh % 64 := by omega
  have hsh_ub : sh % 64 ≤ 63 := by
    have : sh % 64 < 64 := Nat.mod_lt _ (by omega)
    omega
  show toNatLimbsList _ = _
  unfold shiftLeftGeneralLimbs
  extract_lets bigShift smallShift _ _ combined _ prefixResult prefixShifted prevCarry
    h_psize h_last_idx last_orig new_last top_carry withLast
  have h_combined_size : combined.size = bigShift + a.limbs.size := by
    show (Array.replicate _ _ ++ _).size = _; simp [Array.size_append, Array.size_replicate]
  have h_combined_toList : combined.toList = List.replicate bigShift 0 ++ a.limbs.toList := by
    show (Array.replicate _ _ ++ _).toList = _
    rw [Array.toList_append, Array.toList_replicate]
  have h_prefix_size : prefixShifted.toList.length = bigShift + a.limbs.size := h_psize
  have h_a_limbs_len : a.limbs.toList.length = a.limbs.size := rfl
  have h_shift : toNatLimbsList ((prefixShifted.toList.drop bigShift).take (a.limbs.size - 1))
      + prevCarry.toNat * 2 ^ (64 * (a.limbs.size - 1))
    = toNatLimbsList ((combined.toList.drop bigShift).take (a.limbs.size - 1)) * 2 ^ smallShift := by
    have hhi : bigShift + a.limbs.size - 1 ≤ combined.size := by rw [h_combined_size]; omega
    have h := shiftLimbsLeft_toNat combined bigShift (bigShift + a.limbs.size - 1) smallShift
      (by omega) hhi hsh_lb hsh_ub
    simp only at h
    have heq : bigShift + a.limbs.size - 1 - bigShift = a.limbs.size - 1 := by omega
    rw [heq] at h
    exact h
  have h_prevCarry_lt : prevCarry.toNat < 2 ^ smallShift := by
    show (shiftLimbsLeft _ _ _ _ _ _ _ _).2.toNat < _
    exact shiftLimbsLeft_carry_lt _ _ _ _ _ _ _ _
  obtain ⟨h_limb, _⟩ := limb_shift_step last_orig prevCarry smallShift hsh_lb hsh_ub h_prevCarry_lt
  change new_last.toNat + top_carry.toNat * 2 ^ 64 =
      last_orig.toNat * 2 ^ smallShift + prevCarry.toNat at h_limb
  -- Decompose a.limbs.toList
  have h_a_limbs_split : a.limbs.toList = a.limbs.toList.take (a.limbs.size - 1) ++ [last_orig] := by
    show _ = _ ++ [a.limbs[a.limbs.size - 1]]
    have h_len_lt : a.limbs.size - 1 < a.limbs.toList.length := by rw [h_a_limbs_len]; exact h_last_idx_lt
    rw [show a.limbs[a.limbs.size - 1] = a.limbs.toList[a.limbs.size - 1]'h_len_lt from
      (Array.getElem_toList _).symm]
    conv_lhs => rw [← List.take_append_drop (a.limbs.size - 1) a.limbs.toList]
    congr 1
    rw [List.drop_eq_getElem_cons h_len_lt]
    have h : a.limbs.size - 1 + 1 = a.limbs.toList.length := by rw [h_a_limbs_len]; omega
    simp [h]
  have h_prefix_a_len : (a.limbs.toList.take (a.limbs.size - 1)).length = a.limbs.size - 1 := by
    rw [List.length_take, h_a_limbs_len]; omega
  have h_a_decompose :
      a.toNat = last_orig.toNat * 2 ^ (64 * (a.limbs.size - 1))
              + toNatLimbsList (a.limbs.toList.take (a.limbs.size - 1)) := by
    show toNatLimbsList a.limbs.toList = _
    conv_lhs => rw [h_a_limbs_split]
    rw [toNatLimbsList_append, h_prefix_a_len]
    show toNatLimbsList [last_orig] * _ + _ = _
    have : toNatLimbsList [last_orig] = last_orig.toNat := by
      unfold toNatLimbsList; simp
    rw [this]
  -- prefixShifted.toList.take bigShift = List.replicate bigShift 0
  have h_take_zero : prefixShifted.toList.take bigShift = List.replicate bigShift 0 := by
    show (shiftLimbsLeft _ _ _ _ _ _ _ _).1.toList.take _ = _
    rw [shiftLimbsLeft_toList_take, h_combined_toList]
    simp [List.length_replicate]
  -- combined.toList.drop bigShift = a.limbs.toList
  have h_drop_combined : combined.toList.drop bigShift = a.limbs.toList := by
    rw [h_combined_toList]; simp [List.length_replicate]
  -- prefixShifted.toList.take (bigShift + a.limbs.size - 1) decomposition
  have h_prefix_take : prefixShifted.toList.take (bigShift + a.limbs.size - 1)
      = List.replicate bigShift 0
        ++ (prefixShifted.toList.drop bigShift).take (a.limbs.size - 1) := by
    have heq : bigShift + a.limbs.size - 1 = bigShift + (a.limbs.size - 1) := by omega
    rw [heq, List.take_add, h_take_zero]
  -- withLast.toList
  have h_withLast_toList : withLast.toList
      = prefixShifted.toList.take (bigShift + a.limbs.size - 1) ++ [new_last] := by
    show (prefixShifted.set _ _ _).toList = _
    rw [Array.toList_set]
    have h_idx_lt : bigShift + a.limbs.size - 1 < prefixShifted.toList.length := by
      rw [h_prefix_size]; omega
    rw [List.set_eq_take_cons_drop new_last h_idx_lt]
    have : prefixShifted.toList.drop (bigShift + a.limbs.size - 1 + 1) = [] := by
      apply List.drop_eq_nil_of_le; rw [h_prefix_size]; omega
    rw [this]
  -- Simplified shift correctness
  have h_shift' :
      toNatLimbsList ((prefixShifted.toList.drop bigShift).take (a.limbs.size - 1))
        + prevCarry.toNat * 2 ^ (64 * (a.limbs.size - 1))
      = toNatLimbsList (a.limbs.toList.take (a.limbs.size - 1)) * 2 ^ smallShift := by
    rw [h_shift, h_drop_combined]
  -- sh split
  have h_sh_eq : sh = 64 * bigShift + smallShift := by
    show sh = 64 * (sh/64) + sh%64; rw [Nat.div_add_mod]
  have h_pow_sh : (2 : Nat) ^ sh = 2 ^ (64 * bigShift) * 2 ^ smallShift := by
    rw [h_sh_eq, Nat.pow_add]
  -- Size split
  have h_size_split : 64 * (bigShift + (a.limbs.size - 1))
      = 64 * bigShift + 64 * (a.limbs.size - 1) := by ring
  have h_prefix_slice_len :
      ((prefixShifted.toList.drop bigShift).take (a.limbs.size - 1)).length = a.limbs.size - 1 := by
    rw [List.length_take, List.length_drop, h_prefix_size]; omega
  have h_list_len :
      (List.replicate bigShift (0 : UInt64)
        ++ (prefixShifted.toList.drop bigShift).take (a.limbs.size - 1)).length
      = bigShift + (a.limbs.size - 1) := by
    rw [List.length_append, List.length_replicate, h_prefix_slice_len]
  -- Abbreviate
  set S := (2 : Nat) ^ smallShift with hS_def
  set B := (2 : Nat) ^ (64 * bigShift) with hB_def
  set E := (2 : Nat) ^ (64 * (a.limbs.size - 1)) with hE_def
  set x1 := toNatLimbsList ((prefixShifted.toList.drop bigShift).take (a.limbs.size - 1)) with hx1
  set x2 := prevCarry.toNat with hx2
  set x3 := new_last.toNat with hx3
  set x4 := top_carry.toNat with hx4
  set xL := last_orig.toNat with hxL
  set xP := toNatLimbsList (a.limbs.toList.take (a.limbs.size - 1)) with hxP
  -- h_shift' : x1 + x2 * E = xP * S
  -- h_limb : x3 + x4 * 2^64 = xL * S + x2
  -- h_a_decompose : a.toNat = xL * E + xP
  -- h_pow_sh : 2^sh = B * S
  -- Target splits:
  split_ifs with htc
  · -- withLast case, top_carry = 0 → x4 = 0
    rw [h_withLast_toList, h_prefix_take, toNatLimbsList_append, h_list_len]
    show toNatLimbsList [new_last] * _ + _ = _
    have h_nl_list : toNatLimbsList [new_last] = x3 := by unfold toNatLimbsList; simp [hx3]
    rw [h_nl_list, toNatLimbsList_append, toNatLimbsList_replicate_zero,
        Nat.add_zero, List.length_replicate]
    -- Goal: x3 * 2^(64*(bigShift + (a.limbs.size - 1))) + x1 * B = a.toNat * 2^sh
    rw [h_size_split, Nat.pow_add]
    rw [h_a_decompose, h_pow_sh]
    -- Goal: x3 * (B * E) + x1 * B = (xL * E + xP) * (B * S)
    have h_x4_zero : x4 = 0 := by rw [hx4, htc]; rfl
    have h_limb' : x3 = xL * S + x2 := by
      have h := h_limb
      rw [h_x4_zero] at h
      simpa using h
    rw [h_limb']
    -- Goal: (xL * S + x2) * (B * E) + x1 * B = (xL * E + xP) * (B * S)
    -- Use h_shift': xP * S = x1 + x2 * E
    have h_shift'' : xP * S = x1 + x2 * E := by
      rw [← h_shift']
    rw [show (xL * E + xP) * (B * S) = xL * E * (B * S) + xP * S * B by ring,
        h_shift'']
    ring
  · -- push case
    rw [Array.toList_push, h_withLast_toList]
    rw [show ((prefixShifted.toList.take (bigShift + a.limbs.size - 1) ++ [new_last]) ++ [top_carry])
        = prefixShifted.toList.take (bigShift + a.limbs.size - 1) ++ [new_last, top_carry] from
      by simp]
    rw [h_prefix_take, toNatLimbsList_append, h_list_len,
        toNatLimbsList_append, toNatLimbsList_replicate_zero, Nat.add_zero,
        List.length_replicate]
    have h_nt_list : toNatLimbsList [new_last, top_carry] = x4 * 2 ^ 64 + x3 := by
      unfold toNatLimbsList; simp [hx3, hx4, Nat.mul_comm]
    rw [h_nt_list]
    rw [h_size_split, Nat.pow_add]
    rw [h_a_decompose, h_pow_sh]
    have h_shift'' : xP * S = x1 + x2 * E := h_shift'.symm
    rw [show (x4 * 2 ^ 64 + x3) * (B * E) + x1 * B = (x3 + x4 * 2 ^ 64) * (B * E) + x1 * B by ring]
    rw [h_limb]
    rw [show (xL * E + xP) * (B * S) = xL * E * (B * S) + xP * S * B by ring, h_shift'']
    ring

/-- Correctness of `shiftLeft`: `toNat (a <<< sh) = a.toNat * 2 ^ sh`. -/
theorem toNat_shiftLeft (a : AzNat) (sh : Nat) :
    (shiftLeft a sh).toNat = a.toNat * 2 ^ sh := by
  unfold shiftLeft
  by_cases hz : a.limbs.size = 0
  · rw [dite_eq_left hz]
    have h_nil : a.limbs.toList = [] := by
      have : a.limbs.toList.length = 0 := hz
      simp_all
    have h_toNat_zero : a.toNat = 0 := by
      show toNatLimbsList a.limbs.toList = 0
      rw [h_nil]; rfl
    rw [h_toNat_zero]; simp
  · rw [dite_eq_right hz]
    by_cases hsm : sh % 64 = 0
    · rw [dite_eq_left hsm, toNat_shiftLeftMul64]
      congr 1
      conv_rhs => rw [show sh = 64 * (sh / 64) + sh % 64 from (Nat.div_add_mod sh 64).symm]
      rw [hsm, Nat.add_zero]
    · rw [dite_eq_right hsm]
      show toNatLimbsList _ = _
      exact toNat_shiftLeftGeneralLimbs a sh hz hsm

/-- Compatibility of `HShiftLeft` notation with `shiftLeft`. -/
@[simp] lemma hShiftLeft_eq (a : AzNat) (sh : Nat) : a <<< sh = shiftLeft a sh := rfl

/-- `toNat` respects left shift. -/
theorem toNat_hShiftLeft (a : AzNat) (sh : Nat) :
    (a <<< sh).toNat = a.toNat <<< sh := by
  rw [hShiftLeft_eq, toNat_shiftLeft, Nat.shiftLeft_eq]

/-- `ofNat` respects left shift. -/
theorem ofNat_shiftLeft (n sh : Nat) : ofNat (n <<< sh) = ofNat n <<< sh := by
  apply toNat_injective
  rw [toNat_hShiftLeft, toNat_ofNat, toNat_ofNat]

end Azurite.AzNat
