/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Data.Nat.Size
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# BPR §8.1 Definition 8.4: Bitsize of an integer

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1.

The **size** (or **bitsize**) of a non-zero integer `N` is the number
`bit(N)` of bits in its binary representation, characterized by

  `2^{bit(N) − 1} ≤ |N| < 2^{bit(N)}`.

For `N = 0` we follow Mathlib's `Nat.size 0 = 0` convention.

Mathlib provides `Nat.size : ℕ → ℕ` (in `Mathlib.Data.Nat.Size`),
characterized by `Nat.lt_size : m < n.size ↔ 2 ^ m ≤ n` and
`Nat.lt_size_self : n < 2 ^ n.size`. There is no `Int.size` in Mathlib,
so we define one as `N.natAbs.size`.

The unnumbered companion definition `Rat.size` for the bitsize of a
rational `a / b` in lowest terms also lives here.
-/

namespace Azurite.BPR

/-- BPR Definition 8.4. The bitsize of an integer `N`, defined as the
    number of bits in the binary representation of `|N|`.
    Returns `0` for `N = 0`. -/
def Int.size (N : ℤ) : ℕ := N.natAbs.size

/-- For `N ≠ 0`, `2^{bit(N)−1} ≤ |N|`. -/
theorem Int.two_pow_pred_le_natAbs (N : ℤ) (hN : N ≠ 0) :
    2 ^ (Int.size N - 1) ≤ N.natAbs := by
  have hpos : 0 < N.natAbs := Int.natAbs_pos.mpr hN
  have hsize : 0 < N.natAbs.size := Nat.size_pos.mpr hpos
  show 2 ^ (N.natAbs.size - 1) ≤ N.natAbs
  exact Nat.lt_size.mp (Nat.sub_one_lt_of_le hsize le_rfl)

/-- `|N| < 2^{bit(N)}` (holds for all integers, including `0`). -/
theorem Int.natAbs_lt_two_pow_bitsize (N : ℤ) :
    N.natAbs < 2 ^ (Int.size N) :=
  Nat.lt_size_self N.natAbs

/-- The bitsize of a nonzero integer is positive. -/
theorem Int.size_pos (N : ℤ) (hN : N ≠ 0) : 0 < Int.size N :=
  Nat.size_pos.mpr (Int.natAbs_pos.mpr hN)

/-- Corollary of Definition 8.4: `bit(N) − 1 ≤ log₂(|N|)`. -/
theorem Int.size_sub_one_le_logb (N : ℤ) (hN : N ≠ 0) :
    (Int.size N : ℝ) - 1 ≤ Real.logb 2 (N.natAbs : ℝ) := by
  have hposR : (0 : ℝ) < ↑N.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hN
  have hbs := size_pos N hN
  rw [show (Int.size N : ℝ) - 1 = ((Int.size N - 1 : ℕ) : ℝ) from by
        rw [Nat.cast_sub hbs]; norm_cast,
      Real.le_logb_iff_rpow_le (by norm_num) hposR, Real.rpow_natCast]
  exact_mod_cast two_pow_pred_le_natAbs N hN

/-- Corollary of Definition 8.4: `log₂(|N|) < bit(N)`. -/
theorem Int.logb_lt_size (N : ℤ) (hN : N ≠ 0) :
    Real.logb 2 (N.natAbs : ℝ) < (Int.size N : ℝ) := by
  have hposR : (0 : ℝ) < ↑N.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hN
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) hposR, Real.rpow_natCast]
  exact_mod_cast natAbs_lt_two_pow_bitsize N

/-!
### Bitsize of a rational number

BPR's §8.1 also (unnumbered) sets the size of a rational `a / b` in
lowest terms to `bit(a/b) = bit(a) + bit(b)`.
-/

/-- The size of a rational number `a/b` (in lowest terms):
    `bit(a/b) = bit(a) + bit(b)`. BPR §8.1, unnumbered definition. -/
def Rat.size (q : Rat) : ℕ := Int.size q.num + Nat.size q.den

end Azurite.BPR
