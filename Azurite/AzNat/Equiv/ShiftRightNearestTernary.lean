/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.ShiftRightNearestTernary
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.ModPow2
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Parity
import Azurite.AzNat.Equiv.Add
import Azurite.AzInt.Equiv.Basic
import Azurite.AzInt.Equiv.Add
import Azurite.Rounding.IntNearest

/-!
# Equivalence: the ternary nearest shifts

`toNat_shiftRightNearestTernary`: the `AzNat` shift is `NearestTernary` for `n / 2^sh` with its
ternary; `toInt_shiftRightNearestTernary`: the signed version, with the ternary comparing the
signed values.
-/

namespace Azurite

open RoundingTarget

theorem AzNat.toNat_shiftRightNearestTernary (n : AzNat) (o : Ordering) (sh : ℕ) :
    NearestTernary ((n.toNat : ℝ) / (2 : ℝ) ^ sh)
      ((n.shiftRightNearestTernary o sh).toNat : ℤ) o := by
  unfold AzNat.shiftRightNearestTernary NearestTernary
  by_cases hsh : sh = 0
  · subst hsh
    simp only [↓reduceIte, pow_zero, div_one]
    refine ⟨by simp, fun h => ?_⟩
    simp at h
  rw [ite_eq_right hsh]
  simp only []
  set N := n.toNat with hN
  set q := N / 2 ^ sh with hq
  set rem := N % 2 ^ sh with hrem
  have h1u : (1 : UInt64).toNat = 1 := rfl
  have hhalf : ((AzNat.ofNat 1).shiftLeft (sh - 1)).toNat = 2 ^ (sh - 1) := by
    rw [AzNat.toNat_shiftLeft, AzNat.toNat_ofNat, one_mul]
  have hremT : (n.modPow2 sh).toNat = rem := AzNat.toNat_modPow2 n sh
  have hqT : (n.shiftRight sh).toNat = q := AzNat.toNat_shiftRight n sh
  have hsh2 : (2 : ℕ) ^ sh = 2 * 2 ^ (sh - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hdecomp : N = 2 ^ sh * q + rem := (Nat.div_add_mod N (2 ^ sh)).symm
  have hremlt : rem < 2 ^ sh := Nat.mod_lt _ (by positivity)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ sh := by positivity
  have hy : (N : ℝ) / (2 : ℝ) ^ sh = q + (rem : ℝ) / (2 : ℝ) ^ sh := by
    rw [hdecomp]; push_cast; field_simp
  have hsh2R : (2 : ℝ) ^ sh = 2 * (2 : ℝ) ^ (sh - 1) := by exact_mod_cast hsh2
  have hcmp : AzNat.compare (n.modPow2 sh) ((AzNat.ofNat 1).shiftLeft (sh - 1))
      = Ord.compare rem (2 ^ (sh - 1)) := by
    rw [AzNat.compare_eq_compare_toNat, hremT, hhalf]
  rw [hcmp]
  have hremR : (rem : ℝ) / (2 : ℝ) ^ sh = (rem : ℝ) / (2 * (2 : ℝ) ^ (sh - 1)) := by
    rw [hsh2R]
  have hhalfpos : (0 : ℝ) < (2 : ℝ) ^ (sh - 1) := by positivity
  rcases lt_trichotomy rem (2 ^ (sh - 1)) with hlt | heq | hgt
  · rw [compare_lt_iff_lt.mpr hlt, hqT, hy]
    have h1 : (rem : ℝ) / (2 : ℝ) ^ sh < 1 / 2 := by
      rw [hremR, div_lt_iff₀ (by positivity)]
      have : (rem : ℝ) < (2 : ℝ) ^ (sh - 1) := by exact_mod_cast hlt
      linarith
    have h0 : (0 : ℝ) ≤ (rem : ℝ) / (2 : ℝ) ^ sh := by positivity
    refine ⟨by rw [abs_le]; push_cast; constructor <;> linarith, fun h => ?_⟩
    exfalso
    rw [abs_of_nonneg (by push_cast; linarith)] at h
    push_cast at h
    linarith
  · rw [compare_eq_iff_eq.mpr heq, hy]
    have hremhalf : (rem : ℝ) / (2 : ℝ) ^ sh = 1 / 2 := by
      rw [hremR]
      have : (rem : ℝ) = (2 : ℝ) ^ (sh - 1) := by exact_mod_cast heq
      rw [this]; field_simp
    rw [hremhalf]
    cases o with
    | lt =>
      rw [AzNat.toNat_addUInt64, hqT, h1u]
      refine ⟨?_, fun _ => ⟨fun _ => ?_, ⟨fun h => absurd h (by decide),
        fun h => absurd h (by decide)⟩⟩⟩
      · rw [abs_le]; push_cast; constructor <;> norm_num
      · push_cast; norm_num
    | gt =>
      rw [hqT]
      refine ⟨?_, fun _ => ⟨fun h => absurd h (by decide), ⟨fun _ => ?_,
        fun h => absurd h (by decide)⟩⟩⟩
      · rw [abs_le]; constructor <;> norm_num
      · norm_num
    | eq =>
      by_cases hodd : (n.shiftRight sh).isOdd = true
      · rw [ite_eq_left hodd, AzNat.toNat_addUInt64, hqT, h1u]
        have hOdd : Odd q := by rw [← hqT]; exact (AzNat.isOdd_iff _).mp hodd
        refine ⟨?_, fun _ => ⟨fun h => absurd h (by decide), ⟨fun h => absurd h (by decide),
          fun _ => ?_⟩⟩⟩
        · rw [abs_le]; push_cast; constructor <;> norm_num
        · have : Even (q + 1) := Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hOdd)
          exact_mod_cast this
      · rw [ite_eq_right hodd, hqT]
        have hEven : Even q := by
          rw [← hqT]
          have := (not_iff_not.mpr (AzNat.isOdd_iff (n.shiftRight sh))).mp hodd
          exact Nat.not_odd_iff_even.mp this
        refine ⟨?_, fun _ => ⟨fun h => absurd h (by decide), ⟨fun h => absurd h (by decide),
          fun _ => ?_⟩⟩⟩
        · rw [abs_le]; constructor <;> norm_num
        · exact_mod_cast hEven
  · rw [compare_gt_iff_gt.mpr hgt, AzNat.toNat_addUInt64, hqT, hy, h1u]
    have h1 : 1 / 2 < (rem : ℝ) / (2 : ℝ) ^ sh := by
      rw [hremR, lt_div_iff₀ (by positivity)]
      have : (2 : ℝ) ^ (sh - 1) < (rem : ℝ) := by exact_mod_cast hgt
      linarith
    have h2 : (rem : ℝ) / (2 : ℝ) ^ sh < 1 := by
      rw [div_lt_one hpow]; exact_mod_cast hremlt
    refine ⟨by rw [abs_le]; push_cast; constructor <;> linarith, fun h => ?_⟩
    exfalso
    rw [abs_of_nonpos (by push_cast; linarith)] at h
    push_cast at h
    linarith

/-- The signed shift: `NearestTernary` for `z / 2^sh` with the ternary of the signed values. -/
theorem AzInt.toInt_shiftRightNearestTernary (z : AzInt) (o : Ordering) (sh : ℕ) :
    NearestTernary ((z.toInt : ℝ) / (2 : ℝ) ^ sh)
      (z.shiftRightNearestTernary o sh).toInt o := by
  unfold AzInt.shiftRightNearestTernary
  have hz : z.toInt = if z.sign then (z.abs.toNat : ℤ) else -(z.abs.toNat : ℤ) := rfl
  by_cases hs : z.sign = true
  · simp only [hs, ↓reduceIte] at hz ⊢
    have h := AzNat.toNat_shiftRightNearestTernary z.abs o sh
    rw [AzInt.toInt_mkNorm_true, hz]
    push_cast
    exact h
  · have hs' : z.sign = false := Bool.eq_false_iff.mpr hs
    simp only [hs', Bool.false_eq_true, ↓reduceIte] at hz ⊢
    have h := AzNat.toNat_shiftRightNearestTernary z.abs o.swap sh
    set R := z.abs.shiftRightNearestTernary o.swap sh with hRdef
    have hR : (AzInt.mkNorm false R).toInt = -(R.toNat : ℤ) := by
      by_cases hR0 : R = 0
      · rw [hR0]
        simp [AzInt.mkNorm, AzInt.toInt, AzNat.toNat_zero]
      · exact AzInt.toInt_mkNorm_false R hR0
    rw [hR, hz]
    push_cast
    rw [neg_div]
    exact nearestTernary_neg h

end Azurite
