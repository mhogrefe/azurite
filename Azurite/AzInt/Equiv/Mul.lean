/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Mul
import Azurite.AzInt.Equiv.MulSmall
import Azurite.AzNat.Equiv.Mul.Dispatch

namespace Azurite.AzInt

/-- Correctness of `AzInt.mul`. -/
theorem toInt_mul (a b : AzInt) : (a * b).toInt = a.toInt * b.toInt := by
  show (mul a b).toInt = a.toInt * b.toInt
  unfold mul
  have h_ta : a.toInt = if a.sign then (a.abs.toNat : Int) else -(a.abs.toNat : Int) := rfl
  have h_tb : b.toInt = if b.sign then (b.abs.toNat : Int) else -(b.abs.toNat : Int) := rfl
  by_cases h0 : a.abs * b.abs = 0
  · have h0' : (a.abs * b.abs).toNat = 0 := by rw [h0]; rfl
    rw [AzNat.toNat_mul] at h0'
    rw [h0, toInt_mkNorm_zero, h_ta, h_tb]
    rcases Nat.mul_eq_zero.mp h0' with ha | hb
    · have h_abs_a : a.abs = 0 :=
        AzNat.toNat_injective (by rw [ha, AzNat.toNat_zero])
      rw [h_abs_a]; simp
    · have h_abs_b : b.abs = 0 :=
        AzNat.toNat_injective (by rw [hb, AzNat.toNat_zero])
      rw [h_abs_b]; simp
  · cases hsa : a.sign <;> cases hsb : b.sign
    · show (mkNorm true _).toInt = _
      rw [toInt_mkNorm_true, AzNat.toNat_mul, h_ta, h_tb, hsa, hsb]
      push_cast; simp
    · show (mkNorm false _).toInt = _
      rw [toInt_mkNorm_false _ h0, AzNat.toNat_mul, h_ta, h_tb, hsa, hsb]
      push_cast; simp
    · show (mkNorm false _).toInt = _
      rw [toInt_mkNorm_false _ h0, AzNat.toNat_mul, h_ta, h_tb, hsa, hsb]
      push_cast; simp
    · show (mkNorm true _).toInt = _
      rw [toInt_mkNorm_true, AzNat.toNat_mul, h_ta, h_tb, hsa, hsb]
      push_cast; simp

/-- `ofInt`-version of `toInt_mul`. -/
theorem ofInt_mul (i j : Int) : ofInt (i * j) = ofInt i * ofInt j := by
  have h : (ofInt (i * j)).toInt = (ofInt i * ofInt j).toInt := by
    rw [toInt_ofInt, toInt_mul, toInt_ofInt, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

end Azurite.AzInt
