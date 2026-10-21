/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.LogBase2
import Azurite.AzNat.Equiv.Pow2
import Azurite.AzNat.Equiv.Size
import Mathlib.Data.Nat.Log

/-!
# Equivalence: base-2 logarithms of naturals

`floorLogBase2_eq : n.floorLogBase2 = some (Nat.log 2 n.toNat)` and
`ceilingLogBase2_eq : n.ceilingLogBase2 = some (Nat.clog 2 n.toNat)` for `n ≠ 0` (`none` for
`0`), `checkedLogBase2_eq_some_iff : n.checkedLogBase2 = some k ↔ n.toNat = 2 ^ k` and
`checkedLogBase2_eq_none_iff`; for a base `2^k` with `0 < k`, `floorLogBasePowerOf2_eq`
(`= some (Nat.log (2 ^ k) n.toNat)`), `ceilingLogBasePowerOf2_eq` (`= some (Nat.clog (2 ^ k)
n.toNat)`) and `checkedLogBasePowerOf2_eq_some_iff` (`= some e ↔ n.toNat = (2 ^ k) ^ e`).
-/

namespace Azurite.AzNat

theorem toNat_ne_zero_of_ne_zero' {n : AzNat} (h : n ≠ 0) : n.toNat ≠ 0 :=
  fun h0 => h (toNat_injective (by rw [h0, toNat_zero]))

/-- For `n ≠ 0`, `2^(size − 1) ≤ n < 2^size`. -/
theorem size_bounds (n : AzNat) (h : n ≠ 0) :
    2 ^ (n.size - 1) ≤ n.toNat ∧ n.toNat < 2 ^ n.size := by
  have hpos : 0 < n.toNat := Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero' h)
  have hs : 0 < n.size := by rw [← size_toNat]; exact Nat.size_pos.mpr hpos
  constructor
  · rw [← size_toNat]
    rw [← size_toNat] at hs
    exact Nat.lt_size.mp (by omega)
  · rw [← size_toNat]; exact Nat.lt_size_self _

@[simp] theorem floorLogBase2_zero : (0 : AzNat).floorLogBase2 = none := rfl

theorem floorLogBase2_eq (n : AzNat) (h : n ≠ 0) :
    n.floorLogBase2 = some (Nat.log 2 n.toNat) := by
  unfold floorLogBase2
  rw [ite_eq_right h]
  obtain ⟨hlo, hhi⟩ := size_bounds n h
  have hs : 0 < n.size := by
    rw [← size_toNat]; exact Nat.size_pos.mpr (Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero' h))
  congr 1
  symm
  apply Nat.log_eq_of_pow_le_of_lt_pow hlo
  rwa [Nat.sub_add_cancel hs]

@[simp] theorem ceilingLogBase2_zero : (0 : AzNat).ceilingLogBase2 = none := rfl

theorem ceilingLogBase2_eq (n : AzNat) (h : n ≠ 0) :
    n.ceilingLogBase2 = some (Nat.clog 2 n.toNat) := by
  unfold ceilingLogBase2
  rw [ite_eq_right h]
  obtain ⟨hlo, hhi⟩ := size_bounds n h
  have hs : 0 < n.size := by
    rw [← size_toNat]; exact Nat.size_pos.mpr (Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero' h))
  split_ifs with hp
  · obtain ⟨k, hk⟩ := (isPowerOfTwo_iff n).mp hp
    rw [hk, Nat.clog_pow _ _ (by norm_num), ← size_toNat, hk, Nat.size_pow, Nat.add_sub_cancel]
  · congr 1
    symm
    apply le_antisymm
    · exact Nat.clog_le_of_le_pow hhi.le
    · by_contra hlt
      push Not at hlt
      have hle : n.toNat ≤ 2 ^ (n.size - 1) :=
        (Nat.clog_le_iff_le_pow (by norm_num)).mp (by omega)
      have heq : n.toNat = 2 ^ (n.size - 1) := le_antisymm hle hlo
      exact hp ((isPowerOfTwo_iff n).mpr ⟨_, heq⟩)

theorem checkedLogBase2_eq_some_iff (n : AzNat) (k : ℕ) :
    n.checkedLogBase2 = some k ↔ n.toNat = 2 ^ k := by
  unfold checkedLogBase2
  constructor
  · intro h
    split_ifs at h with hp
    · obtain ⟨m, hm⟩ := (isPowerOfTwo_iff n).mp hp
      have hs : n.size = m + 1 := by rw [← size_toNat, hm, Nat.size_pow]
      simp only [Option.some.injEq] at h
      rw [hm]
      congr 1
      omega
  · intro h
    have hp : n.isPowerOfTwo = true := (isPowerOfTwo_iff n).mpr ⟨k, h⟩
    rw [ite_eq_left hp]
    congr 1
    rw [← size_toNat, h, Nat.size_pow]
    omega

theorem checkedLogBase2_eq_none_iff (n : AzNat) :
    n.checkedLogBase2 = none ↔ ∀ k : ℕ, n.toNat ≠ 2 ^ k := by
  constructor
  · intro h k hk
    have := (checkedLogBase2_eq_some_iff n k).mpr hk
    rw [h] at this
    cases this
  · intro h
    unfold checkedLogBase2
    rw [ite_eq_right]
    intro hp
    obtain ⟨k, hk⟩ := (isPowerOfTwo_iff n).mp hp
    exact h k hk

/-! ### Power-of-two bases -/

theorem floorLogBasePowerOf2_eq (n : AzNat) (k : ℕ) (hn : n ≠ 0) (hk : 0 < k) :
    n.floorLogBasePowerOf2 k = some (Nat.log (2 ^ k) n.toNat) := by
  unfold floorLogBasePowerOf2
  rw [ite_eq_right hk.ne', floorLogBase2_eq n hn, Option.map_some, Nat.log_pow_left]

theorem ceilingLogBasePowerOf2_eq (n : AzNat) (k : ℕ) (hn : n ≠ 0) (hk : 0 < k) :
    n.ceilingLogBasePowerOf2 k = some (Nat.clog (2 ^ k) n.toNat) := by
  unfold ceilingLogBasePowerOf2
  rw [ite_eq_right hk.ne', ceilingLogBase2_eq n hn, Option.map_some, Nat.clog_pow_left]
  congr 2
  omega

theorem checkedLogBasePowerOf2_eq_some_iff (n : AzNat) (k : ℕ) (hk : 0 < k) (e : ℕ) :
    n.checkedLogBasePowerOf2 k = some e ↔ n.toNat = (2 ^ k) ^ e := by
  unfold checkedLogBasePowerOf2
  rw [ite_eq_right hk.ne', ← pow_mul]
  constructor
  · intro h
    rcases hc : n.checkedLogBase2 with _ | m
    · rw [hc] at h; cases h
    · rw [hc, Option.bind_some] at h
      split_ifs at h with hm
      · simp only [Option.some.injEq] at h
        rw [(checkedLogBase2_eq_some_iff n m).mp hc, ← h,
          Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm)]
  · intro h
    rw [(checkedLogBase2_eq_some_iff n (k * e)).mpr h, Option.bind_some,
      ite_eq_left (Nat.mul_mod_right k e), Nat.mul_div_cancel_left e hk]

theorem checkedLogBasePowerOf2_eq_none_iff (n : AzNat) (k : ℕ) (hk : 0 < k) :
    n.checkedLogBasePowerOf2 k = none ↔ ∀ e : ℕ, n.toNat ≠ (2 ^ k) ^ e := by
  constructor
  · intro h e he
    have := (checkedLogBasePowerOf2_eq_some_iff n k hk e).mpr he
    rw [h] at this
    cases this
  · intro h
    rcases hc : n.checkedLogBasePowerOf2 k with _ | e
    · rfl
    · exact absurd ((checkedLogBasePowerOf2_eq_some_iff n k hk e).mp hc) (h e)

end Azurite.AzNat
