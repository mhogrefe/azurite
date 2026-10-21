/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.LogBase
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.LogBase2
import Azurite.AzNat.Equiv.Pow
import Mathlib.Data.Nat.Log

/-!
# Equivalence: logarithms of naturals in a general base

`floorLogBase_eq : floorLogBase b n = some (Nat.log b.toNat n.toNat)` for `2 ≤ b` and `n ≠ 0`
(the `Float` estimate plays no part: `floorLogSearch_eq` holds for any valid bracket, and the
bracket is checked), `ceilingLogBase_eq` (`Nat.clog`) and `checkedLogBase_eq_some_iff`
(`= some e ↔ n.toNat = b.toNat ^ e`).
-/

namespace Azurite.AzNat

/-- The search returns `⌊log_b n⌋` from any valid bracket. -/
theorem floorLogSearch_eq (b n : AzNat) : ∀ (lo hi : ℕ), lo < hi → b.toNat ^ lo ≤ n.toNat →
    n.toNat < b.toNat ^ hi → floorLogSearch b n lo hi = Nat.log b.toNat n.toNat
  | lo, hi, hlt, hlo, hhi => by
    unfold floorLogSearch
    simp only []
    split_ifs with h1 h2
    · exact floorLogSearch_eq b n _ hi (by omega)
        (by rwa [le_iff_toNat_le, toNat_pow] at h2) hhi
    · exact floorLogSearch_eq b n lo _ (by omega) hlo
        (by rw [le_iff_toNat_le, toNat_pow] at h2; push Not at h2; exact h2)
    · have : hi = lo + 1 := by omega
      subst this
      exact (Nat.log_eq_of_pow_le_of_lt_pow hlo hhi).symm
  termination_by lo hi => hi - lo

theorem two_le_toNat_of_size (b : AzNat) (h : ¬ b.size ≤ 1) : 2 ≤ b.toNat := by
  rw [← size_toNat] at h
  by_contra hlt
  exact h (Nat.size_le.mpr (by omega))

theorem floorLogBase_eq (b n : AzNat) (hb : 2 ≤ b.toNat) (hn : n ≠ 0) :
    floorLogBase b n = some (Nat.log b.toNat n.toNat) := by
  unfold floorLogBase
  have hb' : ¬ b.size ≤ 1 := by
    rw [← size_toNat]
    intro h
    have := Nat.size_le.mp h
    omega
  rw [ite_eq_right (not_or.mpr ⟨hb', hn⟩)]
  simp only []
  split_ifs with hbr
  · obtain ⟨hlo, hhi⟩ := hbr
    rw [le_iff_toNat_le, toNat_pow] at hlo
    rw [lt_iff_toNat_lt, toNat_pow] at hhi
    rw [floorLogSearch_eq b n _ _ (by omega) hlo hhi]
  · have hpos : 0 < n.toNat := Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero' hn)
    have hs : 0 < n.size := by rw [← size_toNat]; exact Nat.size_pos.mpr hpos
    rw [floorLogSearch_eq b n 0 n.size hs (by rw [pow_zero]; exact hpos)]
    calc n.toNat < 2 ^ n.toNat.size := Nat.lt_size_self _
      _ = 2 ^ n.size := by rw [size_toNat]
      _ ≤ b.toNat ^ n.size := Nat.pow_le_pow_left hb _

@[simp] theorem floorLogBase_zero_right (b : AzNat) : floorLogBase b 0 = none := by
  unfold floorLogBase
  rw [ite_eq_left (Or.inr rfl)]

theorem floorLogBase_of_le_one (b n : AzNat) (hb : b.toNat ≤ 1) : floorLogBase b n = none := by
  unfold floorLogBase
  rw [ite_eq_left (Or.inl (by rw [← size_toNat]; exact Nat.size_le.mpr (by omega)))]

theorem ceilingLogBase_eq (b n : AzNat) (hb : 2 ≤ b.toNat) (hn : n ≠ 0) :
    ceilingLogBase b n = some (Nat.clog b.toNat n.toNat) := by
  unfold ceilingLogBase
  rw [floorLogBase_eq b n hb hn, Option.map_some]
  congr 1
  set e := Nat.log b.toNat n.toNat with he
  have hpos : 0 < n.toNat := Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero' hn)
  have hlo : b.toNat ^ e ≤ n.toNat := Nat.pow_log_le_self _ hpos.ne'
  have hhi : n.toNat < b.toNat ^ (e + 1) := Nat.lt_pow_succ_log_self (by omega) _
  split_ifs with hex
  · have := congrArg toNat hex
    rw [toNat_pow] at this
    rw [← this, Nat.clog_pow _ _ (by omega)]
  · have hne : b.toNat ^ e ≠ n.toNat := fun h => hex (toNat_injective (by rw [toNat_pow, h]))
    symm
    apply Nat.le_antisymm
    · exact Nat.clog_le_of_le_pow hhi.le
    · by_contra hlt
      push Not at hlt
      have hle : n.toNat ≤ b.toNat ^ e := (Nat.clog_le_iff_le_pow (by omega)).mp (by omega)
      exact hne (Nat.le_antisymm hlo hle)

theorem checkedLogBase_eq_some_iff (b n : AzNat) (hb : 2 ≤ b.toNat) (hn : n ≠ 0) (e : ℕ) :
    checkedLogBase b n = some e ↔ n.toNat = b.toNat ^ e := by
  unfold checkedLogBase
  rw [floorLogBase_eq b n hb hn, Option.bind_some]
  constructor
  · intro h
    split_ifs at h with hex
    · simp only [Option.some.injEq] at h
      have := congrArg toNat hex
      rw [toNat_pow, h] at this
      exact this.symm
  · intro h
    have hlog : Nat.log b.toNat n.toNat = e := by rw [h, Nat.log_pow (by omega)]
    rw [hlog, ite_eq_left (toNat_injective (by rw [toNat_pow, h]))]

theorem checkedLogBase_eq_none_iff (b n : AzNat) (hb : 2 ≤ b.toNat) (hn : n ≠ 0) :
    checkedLogBase b n = none ↔ ∀ e : ℕ, n.toNat ≠ b.toNat ^ e := by
  constructor
  · intro h e he
    have := (checkedLogBase_eq_some_iff b n hb hn e).mpr he
    rw [h] at this
    cases this
  · intro h
    rcases hc : checkedLogBase b n with _ | e
    · rfl
    · exact absurd ((checkedLogBase_eq_some_iff b n hb hn e).mp hc) (h e)

end Azurite.AzNat
