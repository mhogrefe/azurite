/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Square
import Azurite.AzNat.Equiv.Square.ToomCook4

/-! # Correctness of the squaring dispatcher -/

namespace Azurite.AzNat

/-- Correctness of `squareLimbs`: agrees with squaring on the slice, regardless of which branch
(schoolbook / Karatsuba / Toom-3 / Toom-4) fires. -/
theorem squareLimbs_toNat (a : Array UInt64) (lo len : Nat) (hA : lo + len ≤ a.size) :
    toNatLimbsList (squareLimbs a lo len hA).toList
      = (toNatLimbsList ((a.toList.drop lo).take len)) ^ 2 := by
  unfold squareLimbs squareLimbsParam
  by_cases h4 : squareDispatchToomCook4Cutoff ≤ len
  · rw [ite_eq_left h4]
    exact toomCook4SquareLimbs_toNat squareDispatchToomCook4Cutoff squareDispatchToomCook3Cutoff
      squareDispatchThreshold a lo len hA
  · rw [ite_eq_right h4]
    by_cases h_toom : squareDispatchToomCook3Cutoff ≤ len
    · rw [ite_eq_left h_toom]
      exact toomCook3SquareLimbs_toNat squareDispatchToomCook3Cutoff squareDispatchThreshold
        a lo len hA
    · rw [ite_eq_right h_toom]
      by_cases h_kara : squareDispatchThreshold ≤ len
      · rw [ite_eq_left h_kara]
        exact karatsubaSquareLimbs_toNat squareDispatchThreshold a lo len hA
      · rw [ite_eq_right h_kara]
        exact schoolbookSquareLimbs_toNat a lo len hA

/-- Correctness of `square` (the dispatched AzNat squaring). -/
theorem toNat_square (a : AzNat) : (square a).toNat = a.toNat ^ 2 := by
  show (ofLimbs (squareLimbs a.limbs 0 a.limbs.size _)).toNat = _
  rw [toNat_ofLimbs, squareLimbs_toNat]
  show (toNatLimbsList ((a.limbs.toList.drop 0).take a.limbs.size)) ^ 2 = a.toNat ^ 2
  rw [List.drop_zero, List.take_of_length_le (by rw [Array.length_toList])]
  rfl

end Azurite.AzNat
