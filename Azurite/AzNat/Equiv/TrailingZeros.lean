/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.TrailingZeros
import Azurite.AzNat.Equiv.Basic
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Azurite.AzNat

theorem trailingZeros_zero : (0 : AzNat).trailingZeros = none := by
  unfold trailingZeros
  decide

private lemma dvd_of_testBit_false (n k : Nat) (h : ∀ i < k, n.testBit i = false) :
    2 ^ k ∣ n := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih (fun i hi => h i (by omega))
    have hk := h k (by omega)
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hm,
          Nat.mul_div_cancel_left _ (Nat.two_pow_pos k)] at hk
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero (by omega)
    rw [hm, hq]; exact ⟨q, by rw [Nat.pow_succ, Nat.mul_assoc]⟩

private lemma not_dvd_of_testBit_true (n k : Nat) (h : n.testBit k = true) :
    ¬ 2 ^ (k + 1) ∣ n := by
  intro ⟨m, hm⟩
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hm, Nat.pow_succ, Nat.mul_assoc,
        Nat.mul_div_cancel_left _ (Nat.two_pow_pos k)] at h

private lemma toNatLimbsList_all_zero (l : List UInt64) (h : ∀ x ∈ l, x = 0) :
    toNatLimbsList l = 0 := by
  induction l with
  | nil => simp [toNatLimbsList]
  | cons x xs ih =>
    rw [toNatLimbsList_cons]
    have hx : x = 0 := h x (List.mem_cons.mpr (Or.inl rfl))
    have hxs : ∀ y ∈ xs, y = 0 := fun y hy => h y (List.mem_cons.mpr (Or.inr hy))
    rw [ih hxs, hx]; simp

-- Bridge: ctz of nonzero UInt64 = padicValNat 2
private lemma ctz_eq_padicValNat (x : UInt64) (hx : x ≠ 0) :
    x.toBitVec.ctz.toNat = padicValNat 2 x.toNat := by
  have hbv : x.toBitVec ≠ 0#64 := by
    intro h; apply hx; exact UInt64.eq_of_toBitVec_eq h
  have hnat : x.toNat ≠ 0 := by
    intro h; apply hx; ext; exact h
  apply le_antisymm
  · rw [← Nat.pow_dvd_iff_le_padicValNat (by omega) hnat]
    exact dvd_of_testBit_false _ _ (fun i hi => BitVec.getLsbD_false_of_lt_ctz hi)
  · by_contra hc
    push Not at hc
    have h_dvd : 2 ^ (x.toBitVec.ctz.toNat + 1) ∣ x.toNat := by
      rw [Nat.pow_dvd_iff_le_padicValNat (by omega) hnat]; omega
    exact not_dvd_of_testBit_true _ _ (BitVec.getLsbD_true_ctz_of_ne_zero hbv) h_dvd

-- Non-divisibility for cons: if ¬ 2^(k+1) | x.toNat and k < 64,
-- then ¬ 2^(k+1) | toNatLimbsList (x :: rest)
private lemma not_dvd_toNatLimbsList_cons (x : UInt64) (rest : List UInt64) (k : Nat)
    (hk : k < 64)
    (hx : ¬ 2 ^ (k + 1) ∣ x.toNat) :
    ¬ 2 ^ (k + 1) ∣ toNatLimbsList (x :: rest) := by
  rw [toNatLimbsList_cons]
  intro h_dvd
  apply hx
  have h64 : 2 ^ (k + 1) ∣ toNatLimbsList rest * 2 ^ 64 :=
    Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by omega)) _
  exact (Nat.dvd_add_right h64).mp h_dvd

-- The ctz of a nonzero UInt64 is < 64
private lemma ctz_lt_64 (x : UInt64) (hx : x ≠ 0) : x.toBitVec.ctz.toNat < 64 := by
  have hbv : x.toBitVec ≠ 0#64 := by
    intro h; apply hx; exact UInt64.eq_of_toBitVec_eq h
  have h := BitVec.ctz_lt_iff_ne_zero.mpr hbv
  simp [BitVec.lt_def] at h
  exact h

-- padicValNat 2 of toNatLimbsList (x :: rest) = padicValNat 2 x.toNat when x ≠ 0
private lemma padicValNat_toNatLimbsList_cons (x : UInt64) (rest : List UInt64) (hx : x ≠ 0) :
    padicValNat 2 (toNatLimbsList (x :: rest)) = padicValNat 2 x.toNat := by
  have hxnat : x.toNat ≠ 0 := by intro h; apply hx; ext; exact h
  have hcons_ne : toNatLimbsList (x :: rest) ≠ 0 := by
    rw [toNatLimbsList_cons]; omega
  apply le_antisymm
  · rw [← not_lt]
    intro hlt
    have h_dvd : 2 ^ (padicValNat 2 x.toNat + 1) ∣ toNatLimbsList (x :: rest) :=
      (Nat.pow_dvd_iff_le_padicValNat (by omega) hcons_ne).mpr (by omega)
    have h_ctz_lt : padicValNat 2 x.toNat < 64 := by
      rw [← ctz_eq_padicValNat x hx]; exact ctz_lt_64 x hx
    have h_not : ¬ 2 ^ (padicValNat 2 x.toNat + 1) ∣ x.toNat := by
      rw [Nat.pow_dvd_iff_le_padicValNat (by omega) hxnat]; omega
    exact not_dvd_toNatLimbsList_cons x rest _ h_ctz_lt h_not h_dvd
  · rw [← Nat.pow_dvd_iff_le_padicValNat (by omega) hcons_ne]
    have h_dvd_x : 2 ^ padicValNat 2 x.toNat ∣ x.toNat := pow_padicValNat_dvd
    have h_le_64 : padicValNat 2 x.toNat ≤ 64 := by
      rw [← ctz_eq_padicValNat x hx]; exact Nat.le_of_lt (ctz_lt_64 x hx)
    rw [toNatLimbsList_cons]
    exact Nat.dvd_add (Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 h_le_64) _) h_dvd_x

-- Core inductive lemma
private lemma trailingZerosLimbsAux_eq (a : AzNat) (start : Nat) (hstart : start < a.limbs.size)
    (h_zeros : ∀ k (hk : k < start),
      a.limbs.toList[k]'(by rw [Array.length_toList]; omega) = 0) :
    trailingZerosLimbsAux a.limbs start hstart = padicValNat 2 a.toNat := by
  have h_len : a.limbs.toList.length = a.limbs.size := Array.length_toList
  unfold trailingZerosLimbsAux
  split
  case isTrue h =>
    have hi2 : start + 1 < a.limbs.size := by
      if hc : start + 1 < a.limbs.size then exact hc
      else
        have heq : a.limbs.size - 1 = start := by omega
        subst heq
        have hback : a.limbs.back? = some 0 := by
          show a.limbs[a.limbs.size - 1]? = some 0
          rw [Array.getElem?_eq_getElem hstart]
          exact congrArg some h
        exact absurd hback a.last_ne_zero
    have h_zeros' : ∀ k (hk : k < start + 1),
        a.limbs.toList[k]'(by rw [h_len]; omega) = 0 := by
      intro k hk
      if hke : k < start then exact h_zeros k hke
      else
        have : k = start := by omega
        subst this
        rw [show a.limbs.toList[k] = a.limbs[k] from Array.getElem_toList (by omega)]
        exact h
    rw [dite_eq_left hi2]
    exact trailingZerosLimbsAux_eq a (start + 1) hi2 h_zeros'
  case isFalse h =>
    -- limbs[start] ≠ 0, first nonzero limb
    have h_len : a.limbs.toList.length = a.limbs.size := Array.length_toList
    have h_split : a.limbs.toList = a.limbs.toList.take start ++ a.limbs.toList.drop start :=
      (List.take_append_drop start a.limbs.toList).symm
    have h_take_zero : toNatLimbsList (a.limbs.toList.take start) = 0 := by
      apply toNatLimbsList_all_zero
      intro x hx
      obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp hx
      rw [List.length_take_of_le (by omega)] at hk
      rw [← hkx, List.getElem_take]
      exact h_zeros k hk
    have h_drop_ne : a.limbs.toList.drop start ≠ [] := by
      intro hc; have := congr_arg List.length hc
      simp [List.length_drop, h_len] at this; omega
    have h_drop_head : (a.limbs.toList.drop start).head h_drop_ne = a.limbs[start] := by
      rw [List.head_drop]; exact Array.getElem_toList (by omega)
    have h_limb_ne : a.limbs[start] ≠ 0 := h
    have h_head_ne : (a.limbs.toList.drop start).head h_drop_ne ≠ 0 := h_drop_head ▸ h_limb_ne
    -- toNat decomposition
    have h_toNat : a.toNat = toNatLimbsList (a.limbs.toList.drop start) * 2 ^ (64 * start) := by
      unfold toNat
      conv_lhs => rw [h_split, toNatLimbsList_append]
      rw [h_take_zero, Nat.add_zero, List.length_take_of_le (by omega)]
    -- inner ≠ 0
    have h_drop_cons : a.limbs.toList.drop start =
        (a.limbs.toList.drop start).head h_drop_ne :: (a.limbs.toList.drop start).tail :=
      (List.cons_head_tail h_drop_ne).symm
    have h_inner_ne : toNatLimbsList (a.limbs.toList.drop start) ≠ 0 := by
      rw [h_drop_cons, toNatLimbsList_cons]; intro hc
      have : ((a.limbs.toList.drop start).head h_drop_ne).toNat = 0 := by omega
      exact h_head_ne (by ext; exact this)
    -- padicValNat decomposition via mul
    have h_pv : padicValNat 2 a.toNat =
        padicValNat 2 (toNatLimbsList (a.limbs.toList.drop start)) + 64 * start := by
      rw [h_toNat, padicValNat.mul h_inner_ne (by positivity), padicValNat.prime_pow]
    -- padicValNat of inner = padicValNat of head limb
    have h_inner_pv : padicValNat 2 (toNatLimbsList (a.limbs.toList.drop start)) =
        padicValNat 2 ((a.limbs.toList.drop start).head h_drop_ne).toNat := by
      have : toNatLimbsList (a.limbs.toList.drop start) =
          toNatLimbsList ((a.limbs.toList.drop start).head h_drop_ne ::
            (a.limbs.toList.drop start).tail) := by
        rw [List.cons_head_tail h_drop_ne]
      rw [this]; exact padicValNat_toNatLimbsList_cons _ _ h_head_ne
    -- ctz = padicValNat 2 of head limb
    have h_ctz : a.limbs[start].toBitVec.ctz.toNat =
        padicValNat 2 ((a.limbs.toList.drop start).head h_drop_ne).toNat := by
      rw [← h_drop_head]; exact ctz_eq_padicValNat _ h_head_ne
    rw [h_pv, h_inner_pv, ← h_ctz]; ring

-- Main theorem
theorem trailingZeros_eq_padicValNat (n : AzNat) (hn : n ≠ 0) :
    n.trailingZeros = some (padicValNat 2 n.toNat) := by
  unfold trailingZeros
  have h_ne : n.limbs.size ≠ 0 := by
    intro h
    apply hn
    have h_empty : n.limbs = #[] := Array.eq_empty_of_size_eq_zero h
    rcases n with ⟨limbs, last_ne⟩
    simp only at h_empty
    subst h_empty
    rfl
  rw [ite_eq_right h_ne]
  congr 1
  show trailingZerosLimbs n.limbs = _
  unfold trailingZerosLimbs
  rw [dite_eq_left (by omega : 0 < n.limbs.size)]
  exact trailingZerosLimbsAux_eq n 0 (by omega) (fun _ hk => absurd hk (Nat.not_lt_zero _))

theorem trailingZeros_ofNat (n : Nat) (hn : n ≠ 0) :
    (ofNat n).trailingZeros = some (padicValNat 2 n) := by
  have h : ofNat n ≠ 0 := by
    intro h
    apply hn
    have := congrArg toNat h
    rw [toNat_ofNat, toNat_zero] at this
    exact this
  rw [trailingZeros_eq_padicValNat _ h, toNat_ofNat]

end Azurite.AzNat
