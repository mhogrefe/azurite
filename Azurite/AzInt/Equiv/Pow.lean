/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Pow
import Azurite.AzInt.Equiv.Add
import Azurite.AzNat.Equiv.Pow

/-!
# Equivalence: `AzInt.pow` ↔ `ℤ` power

`AzInt.pow` (sign-magnitude, delegating the magnitude to `AzNat`'s sliding-window power) agrees
with `ℤ` exponentiation under `toInt`. The magnitude side reuses `AzNat.toNat_pow`; the sign side
is a case split on `z.sign` and the parity of `n` (an even exponent makes the result nonnegative).

## Main theorems

- `toInt_pow`: `(z.pow n).toInt = z.toInt ^ n`.
- `ofInt_pow`: `(ofInt i).pow n = ofInt (i ^ n)`.
-/

namespace Azurite.AzInt

private lemma toInt_mkNorm_zero (s : Bool) : (mkNorm s 0).toInt = 0 := by
  unfold mkNorm
  split_ifs
  · rfl
  · contradiction

/-- Forward direction: `toInt` preserves `pow`. -/
@[simp] theorem toInt_pow (z : AzInt) (n : ℕ) : (z.pow n).toInt = z.toInt ^ n := by
  show (mkNorm (z.sign || (n % 2 == 0)) (z.abs.pow n)).toInt = z.toInt ^ n
  have htn : (z.abs.pow n).toNat = z.abs.toNat ^ n := AzNat.toNat_pow z.abs n
  have htz : z.toInt = if z.sign then (z.abs.toNat : Int) else -(z.abs.toNat : Int) := rfl
  by_cases h0 : z.abs.pow n = 0
  · -- magnitude is `0`: both sides are `0`
    rw [h0, toInt_mkNorm_zero]
    have hm0 : z.abs.toNat ^ n = 0 := by rw [← htn, h0]; rfl
    obtain ⟨hm, hne⟩ := Nat.pow_eq_zero.mp hm0
    have hz0 : z.toInt = 0 := by rw [htz, hm]; simp
    rw [hz0, zero_pow hne]
  · cases hs : z.sign
    · -- negative base: sign of the power depends on the parity of `n`
      have hztz : z.toInt = -(z.abs.toNat : Int) := by simp [htz, hs]
      rcases Nat.even_or_odd n with he | ho
      · rw [show (false || (n % 2 == 0)) = true by simp [Nat.even_iff.mp he],
          toInt_mkNorm_true, htn, hztz, Even.neg_pow he]
        push_cast; ring
      · rw [show (false || (n % 2 == 0)) = false by simp [Nat.odd_iff.mp ho],
          toInt_mkNorm_false _ h0, htn, hztz, Odd.neg_pow ho]
        push_cast; ring
    · -- nonnegative base: the power is nonnegative
      have hztz : z.toInt = (z.abs.toNat : Int) := by simp [htz, hs]
      rw [show (true || (n % 2 == 0)) = true by simp, toInt_mkNorm_true, htn, hztz]
      push_cast; ring

/-- Backward direction: `ofInt` preserves `pow`. -/
theorem ofInt_pow (i : Int) (n : ℕ) : (ofInt i).pow n = ofInt (i ^ n) := by
  have h : ((ofInt i).pow n).toInt = (ofInt (i ^ n)).toInt := by
    rw [toInt_pow, toInt_ofInt, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

end Azurite.AzInt
