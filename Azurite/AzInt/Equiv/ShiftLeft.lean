/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.ShiftLeft
import Azurite.AzInt.Equiv.Basic
import Azurite.AzNat.Equiv.ShiftLeft

namespace Azurite.AzInt

/-- Correctness of `AzInt.shiftLeft`. -/
theorem toInt_shiftLeft (z : AzInt) (sh : Nat) :
    (shiftLeft z sh).toInt = z.toInt * 2 ^ sh := by
  have h_abs : (z.abs <<< sh).toNat = z.abs.toNat * 2 ^ sh := by
    rw [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq]
  show (if z.sign then ((z.abs <<< sh).toNat : Int) else -((z.abs <<< sh).toNat : Int))
       = z.toInt * 2 ^ sh
  rw [h_abs]
  show (if z.sign then ((z.abs.toNat * 2 ^ sh : Nat) : Int)
         else -((z.abs.toNat * 2 ^ sh : Nat) : Int))
       = z.toInt * 2 ^ sh
  cases hs : z.sign
  · have hz : z.toInt = -(z.abs.toNat : Int) := by
      change (if z.sign then _ else _) = _
      rw [hs]; simp
    rw [hz]
    simp only [Bool.false_eq_true, ↓reduceIte]
    push_cast; ring
  · have hz : z.toInt = (z.abs.toNat : Int) := by
      change (if z.sign then _ else _) = _
      rw [hs]; simp
    rw [hz]
    simp only [↓reduceIte]
    push_cast; ring

/-- Compatibility of `HShiftLeft` notation with `shiftLeft`. -/
@[simp] lemma hShiftLeft_eq (z : AzInt) (sh : Nat) : z <<< sh = shiftLeft z sh := rfl

/-- `toInt` respects left shift. -/
theorem toInt_hShiftLeft (z : AzInt) (sh : Nat) :
    (z <<< sh).toInt = z.toInt * 2 ^ sh := by
  rw [hShiftLeft_eq, toInt_shiftLeft]

/-- `ofInt`-version of `toInt_shiftLeft`. -/
theorem ofInt_shiftLeft (i : Int) (sh : Nat) :
    ofInt (i * 2 ^ sh) = (ofInt i) <<< sh := by
  have h : (ofInt (i * 2 ^ sh)).toInt = ((ofInt i) <<< sh).toInt := by
    rw [toInt_ofInt, toInt_hShiftLeft, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

end Azurite.AzInt
