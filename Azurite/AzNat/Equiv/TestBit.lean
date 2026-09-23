/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.TestBit
import Azurite.AzNat.Equiv.Basic
import Azurite.UInt64.Equiv.TestBit
import Mathlib.Data.Nat.Bitwise

namespace Azurite.AzNat

/-- Auxiliary: bit `r + 64 * q` of `toNatLimbsList l` is bit `r` of limb `q`, when the
limb exists (and `r < 64`). This version indexes by `(q, r)` directly, avoiding
dependently-typed rewrites of `i / 64`. -/
lemma testBit_toNatLimbsList_aux (q r : Nat) (hr : r < 64) :
    ∀ l : List UInt64,
      Nat.testBit (toNatLimbsList l) (r + 64 * q) =
        if h : q < l.length then Nat.testBit (l[q]'h).toNat r else false := by
  induction q with
  | zero =>
    intro l
    cases l with
    | nil => simp [toNatLimbsList]
    | cons x xs =>
      rw [toNatLimbsList_cons, Nat.mul_comm]
      rw [Nat.testBit_two_pow_mul_add _ (UInt64.toNat_lt x)]
      simp only [Nat.mul_zero, Nat.add_zero, hr, ite_true,
        List.length_cons, Nat.zero_lt_succ, dite_eq_left, List.getElem_cons_zero]
  | succ k ih =>
    intro l
    cases l with
    | nil => simp [toNatLimbsList]
    | cons x xs =>
      have h_expand : r + 64 * (k + 1) = (r + 64 * k) + 64 := by ring
      rw [h_expand, toNatLimbsList_cons, Nat.mul_comm]
      rw [Nat.testBit_two_pow_mul_add _ (UInt64.toNat_lt x)]
      have h_not_lt : ¬ (r + 64 * k + 64 < 64) := by omega
      simp only [h_not_lt, ite_false]
      have h_sub : r + 64 * k + 64 - 64 = r + 64 * k := by omega
      rw [h_sub, ih xs]
      by_cases hk : k < xs.length
      · have h_cons_lt : k + 1 < (x :: xs).length := by simp; omega
        simp only [hk, dite_eq_left, h_cons_lt, dite_eq_left, List.getElem_cons_succ]
      · have h_cons_not_lt : ¬ k + 1 < (x :: xs).length := by
          simp only [List.length_cons, not_lt]; omega
        simp only [hk, dite_eq_right, not_false_eq_true, h_cons_not_lt]

theorem testBit_eq_toNat_testBit (n : AzNat) (i : Nat) :
    n.testBit i = n.toNat.testBit i := by
  unfold testBit toNat
  have h_decomp : i = (i % 64) + 64 * (i / 64) := by omega
  conv_rhs => rw [h_decomp]
  rw [testBit_toNatLimbsList_aux (i / 64) (i % 64) (Nat.mod_lt _ (by omega))]
  have h_size_eq : n.limbs.size = n.limbs.toList.length := rfl
  by_cases h : i / 64 < n.limbs.size
  · have h' : i / 64 < n.limbs.toList.length := h_size_eq ▸ h
    simp only [h, dite_eq_left, h', dite_eq_left]
    rw [← Array.getElem_toList (xs := n.limbs) (h := h')]
    exact UInt64.testBit_eq_toNat_testBit _ _
  · have h' : ¬ i / 64 < n.limbs.toList.length := fun hc => h (h_size_eq ▸ hc)
    simp only [h, dite_eq_right, not_false_eq_true, h', dite_eq_right]

theorem testBit_ofNat (n i : Nat) : (ofNat n).testBit i = n.testBit i := by
  rw [testBit_eq_toNat_testBit, toNat_ofNat]

end Azurite.AzNat
