/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.UInt64.TrailingZeros

namespace UInt64

theorem toNat_log2 (a : UInt64) : a.log2.toNat = a.toNat.log2 := rfl

/-- The count of trailing zeros of a nonzero bit vector is below the width. -/
theorem toNat_ctz_lt (d : UInt64) (hd : d ≠ 0) : d.toBitVec.ctz.toNat < 64 := by
  have hbv : d.toBitVec ≠ 0#64 := fun h => hd (UInt64.eq_of_toBitVec_eq h)
  have h := BitVec.ctz_lt_iff_ne_zero.mpr hbv
  simpa [BitVec.lt_def] using h

/-- `d &&& -d` is the lowest set bit of `d`. -/
theorem toBitVec_and_neg (d : UInt64) (hd : d ≠ 0) :
    (d &&& -d).toBitVec = BitVec.twoPow 64 d.toBitVec.ctz.toNat := by
  have hbv : d.toBitVec ≠ 0#64 := fun h => hd (UInt64.eq_of_toBitVec_eq h)
  have hk := toNat_ctz_lt d hd
  have hbit := BitVec.getLsbD_true_ctz_of_ne_zero hbv
  rw [UInt64.toBitVec_and, UInt64.toBitVec_neg]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_neg, BitVec.getLsbD_twoPow, decide_eq_true hi,
    decide_eq_true hk, Bool.true_and, Bool.true_and]
  rcases Nat.lt_trichotomy i d.toBitVec.ctz.toNat with h | h | h
  · have h2 : ¬ ∃ j < i, d.toBitVec.getLsbD j = true := fun ⟨j, hj, hjt⟩ => by
      rw [BitVec.getLsbD_false_of_lt_ctz (by omega)] at hjt
      exact Bool.false_ne_true hjt
    rw [BitVec.getLsbD_false_of_lt_ctz h, decide_eq_false h2, decide_eq_false (by omega)]
    rfl
  · subst h
    have h2 : ¬ ∃ j < d.toBitVec.ctz.toNat, d.toBitVec.getLsbD j = true := fun ⟨j, hj, hjt⟩ => by
      rw [BitVec.getLsbD_false_of_lt_ctz hj] at hjt
      exact Bool.false_ne_true hjt
    rw [hbit, decide_eq_false h2, decide_eq_true rfl]
    rfl
  · rw [decide_eq_true ⟨_, h, hbit⟩, decide_eq_false (by omega)]
    cases d.toBitVec.getLsbD i <;> rfl

/-- `trailingZeros` agrees with `BitVec.ctz` on nonzero inputs. -/
theorem trailingZeros_eq_ctz (d : UInt64) (hd : d ≠ 0) :
    d.trailingZeros = d.toBitVec.ctz.toNat := by
  have hk := toNat_ctz_lt d hd
  unfold trailingZeros
  rw [toNat_log2]
  show ((d &&& -d).toBitVec.toNat).log2 = _
  rw [toBitVec_and_neg d hd, BitVec.toNat_twoPow,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right Nat.one_lt_two hk), Nat.log2_two_pow]

end UInt64
