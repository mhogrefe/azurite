/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.ExactDivOdd
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.UInt64.Equiv.WideMul
import Azurite.UInt64.Equiv.SubWithBorrow

/-!
# Correctness of exact division by an odd limb

`exactDivOdd_toNat`: for `d · dinv = 1` (as `UInt64`s) and `d ∣ n`, `exactDivOdd d dinv n`
is `n / d`.  The proof is the loop invariant described in `AzNat/ExactDivOdd.lean`: with
`β = 2^64`, `Q = n / d` and `T_i` the value of the limbs from position `i` on,

  `T_i = hi + borrow + d · (Q / β^i)`   and   `acc` holds `Q mod β^i`

before step `i`.  The step produces the `i`-th limb of `Q` because `r := n_i − hi − borrow` is
congruent to `d · (Q / β^i)` modulo `β` and `dinv` inverts `d` modulo `β`.
-/

namespace Azurite.AzNat

lemma sliceVal_succ (a : Array UInt64) (lo len : Nat) (h : lo < a.size) :
    sliceVal a lo (len + 1) = (a[lo]'h).toNat + 2 ^ 64 * sliceVal a (lo + 1) len := by
  unfold sliceVal
  have hlo : lo < a.toList.length := by simpa using h
  rw [List.drop_eq_getElem_cons hlo, List.take_succ_cons, toNatLimbsList_cons]
  simp only [Array.getElem_toList]
  ring

lemma sliceVal_lt (a : Array UInt64) (lo len : Nat) (hA : lo + len ≤ a.size) :
    sliceVal a lo len < 2 ^ (64 * len) := by
  unfold sliceVal
  have hlen : ((a.toList.drop lo).take len).length = len := by
    rw [List.length_take, List.length_drop, Array.length_toList]
    omega
  have := toNatLimbsList_lt_pow ((a.toList.drop lo).take len)
  rwa [hlen] at this

lemma toNatLimbsList_nil : toNatLimbsList [] = 0 := rfl

/-- `d.toNat · dinv.toNat ≡ 1 (mod 2^64)` from the `UInt64` equation `d * dinv = 1`. -/
lemma toNat_mul_inv {d dinv : UInt64} (hinv : d * dinv = 1) :
    d.toNat * dinv.toNat % 2 ^ 64 = 1 := by
  have := congrArg UInt64.toNat hinv
  rwa [UInt64.toNat_mul] at this

/-- The loop invariant, by induction on the number of remaining limbs. -/
theorem exactDivOddLimbs.go_toNat (d dinv : UInt64) (hinv : d * dinv = 1) (a : Array UInt64)
    (lo len : Nat) (hA : lo + len ≤ a.size) (Q : Nat) :
    ∀ (n : Nat) (acc : Array UInt64) (i : Nat) (hi : UInt64) (borrow : Bool), len - i = n →
      i ≤ len → acc.size = i → toNatLimbsList acc.toList = Q % 2 ^ (64 * i) →
      sliceVal a (lo + i) (len - i)
        = hi.toNat + (if borrow then 1 else 0) + d.toNat * (Q / 2 ^ (64 * i)) →
      toNatLimbsList (exactDivOddLimbs.go d dinv a lo len hA acc i hi borrow).toList
        = Q % 2 ^ (64 * len) := by
  intro n
  induction n with
  | zero =>
    intro acc i hi borrow hn hi_le _ hacc _
    have hi_eq : i = len := by omega
    rw [exactDivOddLimbs.go, dite_eq_right (by omega), hacc, hi_eq]
  | succ n ih =>
    intro acc i hi borrow hn hi_le hsize hacc hT
    have h : i < len := by omega
    have h_idx : lo + i < a.size := by omega
    rw [exactDivOddLimbs.go, dite_eq_left h]
    simp only []
    -- names for the step's quantities
    set r := (UInt64.subWithBorrow (a[lo + i]'h_idx) hi borrow).1 with hr
    set b' := (UInt64.subWithBorrow (a[lo + i]'h_idx) hi borrow).2 with hb'
    set X := Q / 2 ^ (64 * i) with hX
    set bv : Nat := if borrow then 1 else 0 with hbv
    set bv' : Nat := if b' then 1 else 0 with hbv'
    have hbv_le : bv ≤ 1 := by rw [hbv]; split_ifs <;> omega
    have hbv'_le : bv' ≤ 1 := by rw [hbv']; split_ifs <;> omega
    -- (B) the borrow subtraction
    have hB : r.toNat + hi.toNat + bv = (a[lo + i]'h_idx).toNat + bv' * 2 ^ 64 :=
      UInt64.subWithBorrow_eq _ _ _
    -- (A) peel the bottom limb off the slice
    have hlen : len - i = (len - (i + 1)) + 1 := by omega
    rw [hlen, sliceVal_succ a (lo + i) _ h_idx] at hT
    set S' := sliceVal a (lo + i + 1) (len - (i + 1)) with hS'
    -- (C) `r ≡ d · X (mod β)`
    have hrX : r.toNat + 2 ^ 64 * S' = d.toNat * X + 2 ^ 64 * bv' := by omega
    have hr_mod : r.toNat % 2 ^ 64 = (d.toNat * X) % 2 ^ 64 := by omega
    -- the quotient limb is `X mod β`
    have hq : (r * dinv).toNat = X % 2 ^ 64 := by
      rw [UInt64.toNat_mul, Nat.mul_mod, hr_mod, ← Nat.mul_mod, Nat.mul_right_comm,
        Nat.mul_mod, toNat_mul_inv hinv, Nat.one_mul, Nat.mod_mod]
    -- (D) the wide product `q · d = hi' · β + lo'`, with `lo' = r`
    have hW := UInt64.toNat_wideMul (r * dinv) d
    set hi' := (UInt64.wideMul (r * dinv) d).1 with hhi'
    set lo' := (UInt64.wideMul (r * dinv) d).2 with hlo'
    rw [hq] at hW
    have hXd : X = X % 2 ^ 64 + 2 ^ 64 * (X / 2 ^ 64) := (Nat.mod_add_div X (2 ^ 64)).symm
    have hlo'_lt := UInt64.toNat_lt lo'
    have hr_lt := UInt64.toNat_lt r
    -- from `hW`, `hrX` and `hXd`: `lo' = r` and `S' = bv' + hi' + d · (X / β)`
    have hsplit : d.toNat * X = d.toNat * (X % 2 ^ 64) + 2 ^ 64 * (d.toNat * (X / 2 ^ 64)) := by
      conv_lhs => rw [hXd]
      ring
    rw [Nat.mul_comm (X % 2 ^ 64) d.toNat] at hW
    have hkey : lo'.toNat + 2 ^ 64 * hi'.toNat + 2 ^ 64 * (d.toNat * (X / 2 ^ 64))
        = d.toNat * X := by omega
    have hlo'_eq : lo'.toNat = r.toNat := by omega
    have hS'_eq : S' = hi'.toNat + bv' + d.toNat * (X / 2 ^ 64) := by omega
    -- apply the induction hypothesis at `i + 1`
    have hQ_succ : Q / 2 ^ (64 * (i + 1)) = X / 2 ^ 64 := by
      rw [hX, Nat.div_div_eq_div_mul, ← Nat.pow_add, show 64 * i + 64 = 64 * (i + 1) by ring]
    have hmodsplit : Q % 2 ^ (64 * (i + 1)) = Q % 2 ^ (64 * i) + 2 ^ (64 * i) * (X % 2 ^ 64) := by
      rw [hX, show 2 ^ (64 * (i + 1)) = (2 ^ 64) ^ (i + 1) by rw [← pow_mul],
        show 2 ^ (64 * i) = (2 ^ 64) ^ i by rw [← pow_mul], Nat.mod_pow_succ]
    have hacc' : toNatLimbsList (acc.push (r * dinv)).toList = Q % 2 ^ (64 * (i + 1)) := by
      rw [Array.toList_push, toNatLimbsList_append, hacc, toNatLimbsList_cons,
        toNatLimbsList_nil, Array.length_toList, hsize, hq, Nat.zero_mul, Nat.zero_add,
        hmodsplit]
      ring
    exact ih (acc.push (r * dinv)) (i + 1) hi' b' (by omega) (by omega)
      (by rw [Array.size_push, hsize]) hacc' (by rw [hQ_succ, ← hS'_eq]; rfl)

/-- The slice version: if `d ∣ slice` then the result is the quotient. -/
theorem exactDivOddLimbs_toNat (d dinv : UInt64) (hinv : d * dinv = 1) (a : Array UInt64)
    (lo len : Nat) (hA : lo + len ≤ a.size) (Q : Nat) (hQ : sliceVal a lo len = d.toNat * Q) :
    toNatLimbsList (exactDivOddLimbs d dinv a lo len hA).toList = Q := by
  have hd : 1 ≤ d.toNat := by
    rcases Nat.eq_zero_or_pos d.toNat with h0 | hpos
    · exfalso
      have := toNat_mul_inv hinv
      rw [h0, Nat.zero_mul, Nat.zero_mod] at this
      exact absurd this (by decide)
    · exact hpos
  have hQ_lt : Q < 2 ^ (64 * len) := by
    have := sliceVal_lt a lo len hA
    rw [hQ] at this
    calc Q = 1 * Q := (Nat.one_mul Q).symm
      _ ≤ d.toNat * Q := Nat.mul_le_mul_right Q hd
      _ < 2 ^ (64 * len) := this
  unfold exactDivOddLimbs
  rw [exactDivOddLimbs.go_toNat d dinv hinv a lo len hA Q (len - 0) #[] 0 0 false rfl
    (Nat.zero_le _) rfl (by simp [toNatLimbsList_nil, Nat.mod_one])
    (by simpa [sliceVal, Nat.mul_zero, Nat.pow_zero, Nat.div_one] using hQ)]
  exact Nat.mod_eq_of_lt hQ_lt

/-- **Correctness of `exactDivOdd`**: with `d · dinv = 1` and `d ∣ n`, the result is `n / d`. -/
theorem exactDivOdd_toNat (d dinv : UInt64) (hinv : d * dinv = 1) (n : AzNat)
    (hd : d.toNat ∣ n.toNat) : (exactDivOdd d dinv n).toNat = n.toNat / d.toNat := by
  unfold exactDivOdd
  rw [toNat_ofLimbs]
  apply exactDivOddLimbs_toNat d dinv hinv _ 0 _ _ (n.toNat / d.toNat)
  have hwhole : sliceVal n.limbs 0 n.limbs.size = n.toNat := by
    unfold sliceVal
    rw [List.drop_zero, List.take_of_length_le (by simp)]
    rfl
  rw [hwhole]
  exact (Nat.mul_div_cancel' hd).symm

end Azurite.AzNat
