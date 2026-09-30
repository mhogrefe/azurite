/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Square
import Azurite.AzNat.Equiv.Square.ToomCook4
import Azurite.AzNat.Equiv.Mul.SchonhageStrassen

/-! # Correctness of the squaring dispatcher -/

namespace Azurite.AzNat

/-- The Toom squaring ladder squares the slice, whichever branch fires. -/
theorem toomSquareLadderLimbs_toNat (t k4 k3 : Nat) (a : Array UInt64) (lo len : Nat)
    (hA : lo + len ≤ a.size) :
    toNatLimbsList (toomSquareLadderLimbs t k3 k4 a lo len hA).toList
      = (toNatLimbsList ((a.toList.drop lo).take len)) ^ 2 := by
  unfold toomSquareLadderLimbs
  split_ifs
  · exact toomCook4SquareLimbs_toNat _ _ _ a lo len hA
  · exact toomCook3SquareLimbs_toNat _ _ a lo len hA
  · exact karatsubaSquareLimbs_toNat _ a lo len hA
  · exact schoolbookSquareLimbs_toNat a lo len hA

/-- The Toom squaring ladder on an `AzNat` squares. -/
theorem toomSquareLadder_toNat (t k3 k4 : Nat) (x : AzNat) :
    (toomSquareLadder t k3 k4 x).toNat = x.toNat * x.toNat := by
  unfold toomSquareLadder
  rw [toNat_ofLimbs, toomSquareLadderLimbs_toNat]
  show (toNatLimbsList ((x.limbs.toList.drop 0).take x.limbs.size)) ^ 2 = x.toNat * x.toNat
  rw [List.drop_zero, List.take_of_length_le (by rw [Array.length_toList]), sq]
  rfl

/-- Correctness of `squareLimbs`: agrees with squaring on the slice, regardless of which branch
(schoolbook / Karatsuba / Toom-3 / Toom-4 / FFT) fires. -/
theorem squareLimbs_toNat (a : Array UInt64) (lo len : Nat) (hA : lo + len ≤ a.size) :
    toNatLimbsList (squareLimbs a lo len hA).toList
      = (toNatLimbsList ((a.toList.drop lo).take len)) ^ 2 := by
  unfold squareLimbs squareLimbsParam
  split_ifs
  · rw [fftSquareLimbs_toNat _ (toomSquareLadder_toNat _ _ _) a lo len hA, sq]
  · exact toomSquareLadderLimbs_toNat _ _ _ a lo len hA

/-- Correctness of `square` (the dispatched AzNat squaring). -/
theorem toNat_square (a : AzNat) : (square a).toNat = a.toNat ^ 2 := by
  show (ofLimbs (squareLimbs a.limbs 0 a.limbs.size _)).toNat = _
  rw [toNat_ofLimbs, squareLimbs_toNat]
  show (toNatLimbsList ((a.limbs.toList.drop 0).take a.limbs.size)) ^ 2 = a.toNat ^ 2
  rw [List.drop_zero, List.take_of_length_le (by rw [Array.length_toList])]
  rfl

end Azurite.AzNat
