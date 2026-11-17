/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Bernoulli
import Azurite.AzRat.Equiv.Construct
import Azurite.AzNat.Equiv.TangentNumbers
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.Sub

/-!
# Equivalence: Bernoulli numbers

`toRat_bernoulli : (bernoulli n).toRat = _root_.bernoulli n` (Mathlib's Bernoulli numbers,
`B_1 = −1/2`) and `toRat_bernoulliEvens` for the table, from `toRat_bernoulliOfTangent`: the
formula (4.62) of Brent–Zimmermann (`BZ.bernoulli_two_mul_eq_tangentNumber`) applied to the
tangent numbers of `AzNat.toNat_tangentNumbers`.
-/

namespace Azurite.AzRat

open BZ

/-- `bernoulliOfTangent j T` is `B_{2j}` when `T` is the tangent number `T_j`. -/
theorem toRat_bernoulliOfTangent {j : ℕ} (hj : 1 ≤ j) {T : AzNat}
    (hT : ((T.toNat : ℕ) : ℤ) = tangentNumber j) :
    (bernoulliOfTangent j T).toRat = _root_.bernoulli (2 * j) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hTq : (T.toNat : ℚ) = (tangentNumber (k + 1) : ℚ) := by exact_mod_cast hT
  have hden : (((1 : AzNat) <<< (4 * (k + 1))) - ((1 : AzNat) <<< (2 * (k + 1)))).toNat
      = 4 ^ (2 * (k + 1)) - 2 ^ (2 * (k + 1)) := by
    rw [AzNat.toNat_sub, AzNat.toNat_hShiftLeft, AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq,
      Nat.shiftLeft_eq, AzNat.toNat_one, one_mul, one_mul,
      show 4 * (k + 1) = 2 * (2 * (k + 1)) by ring, pow_mul]
    norm_num
  have hle : 2 ^ (2 * (k + 1)) ≤ 4 ^ (2 * (k + 1)) :=
    Nat.pow_le_pow_left (by norm_num) _
  rw [bernoulliOfTangent, toRat_ofSignAzNats, AzNat.toNat_mulNat, hden,
    bernoulli_two_mul_eq_tangentNumber k]
  push_cast [Nat.cast_sub hle]
  rw [hTq]
  rcases Nat.even_or_odd k with hk | hk
  · have : (k + 1) % 2 = 1 := by obtain ⟨c, rfl⟩ := hk; omega
    rw [hk.neg_one_pow]
    simp only [this, decide_true, ↓reduceIte]
    ring
  · have : ¬ (k + 1) % 2 = 1 := by obtain ⟨c, rfl⟩ := hk; omega
    rw [hk.neg_one_pow]
    simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte]
    ring

/-- **`bernoulli n` is the Bernoulli number `B_n`.** -/
theorem toRat_bernoulli (n : ℕ) : (bernoulli n).toRat = _root_.bernoulli n := by
  unfold bernoulli
  split_ifs with h0 h1 hodd
  · rw [h0, toRat_one, bernoulli_zero]
  · rw [h1, toRat_ofSignAzNats, AzNat.toNat_ofNat, AzNat.toNat_ofNat, bernoulli_one]
    norm_num
  · rw [toRat_zero, bernoulli_eq_zero_of_odd (Nat.odd_iff.mpr hodd) (by omega)]
  · have hn : n = 2 * (n / 2) := by omega
    rw [toRat_bernoulliOfTangent (by omega)
      (AzNat.toNat_tangentNumbers (by omega) le_rfl), ← hn]

theorem size_bernoulliEvens (m : ℕ) : (bernoulliEvens m).size = m := Array.size_ofFn

/-- **The table holds `B_2, …, B_{2m}`**: `B_{2(i+1)}` at index `i`. -/
theorem toRat_bernoulliEvens {m i : ℕ} (hi : i < m) :
    ((bernoulliEvens m).getD i 0).toRat = _root_.bernoulli (2 * (i + 1)) := by
  unfold bernoulliEvens
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hi, ↓reduceDIte, Option.getD_some]
  exact toRat_bernoulliOfTangent (by omega)
    (AzNat.toNat_tangentNumbers (j := i + 1) (by omega) (by omega))

end Azurite.AzRat
