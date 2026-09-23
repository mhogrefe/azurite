/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.ShiftRight
import Azurite.AzInt.Equiv.ShiftRightRound
import Mathlib.Algebra.Order.Floor.Ring

namespace Azurite
open RoundingTarget

/-- **Correctness of `AzInt.shiftRight`.**

`AzInt.shiftRight z sh` realises floor-rounding of `z.toInt / 2^sh` against the
`intSet` rounding target. -/
theorem AzInt.toInt_shiftRight (z : AzInt) (sh : Nat) :
    (((z.shiftRight sh).toInt : ℝ) : EReal) =
      (round intSet .Floor ((z.toInt : ℝ) / ((2 : ℝ) ^ sh))).val := by
  unfold AzInt.shiftRight
  exact AzInt.toInt_shiftRightRound z .Floor sh

/-- Compatibility of `HShiftRight` notation with `shiftRight`. -/
@[simp] lemma AzInt.hShiftRight_eq (z : AzInt) (sh : Nat) :
    z >>> sh = AzInt.shiftRight z sh := rfl

/-- The `toInt` of `z >>> sh` matches the right-shift on `Int` (floor division by `2^sh`). -/
theorem AzInt.toInt_hShiftRight (z : AzInt) (sh : Nat) :
    (z >>> sh).toInt = z.toInt >>> sh := by
  have h := AzInt.toInt_shiftRight z sh
  have hround : (round intSet .Floor ((z.toInt : ℝ) / ((2 : ℝ) ^ sh))).val =
      (((z.toInt >>> sh : Int) : ℝ) : EReal) := by
    show (roundFloor intSet ((z.toInt : ℝ) / ((2 : ℝ) ^ sh))).val = _
    rw [val_roundFloor_intSet]
    have h2 : ⌊((z.toInt : ℝ)) / ((2 : ℝ) ^ sh)⌋ = z.toInt >>> sh := by
      rw [Int.shiftRight_eq_div_pow]
      rw [show ((2 : ℝ) ^ sh) = (((2 ^ sh : ℕ) : ℝ)) by push_cast; rfl]
      rw [Int.floor_div_natCast, Int.floor_intCast]
    rw [h2]
  rw [hround] at h
  rw [AzInt.hShiftRight_eq]
  exact_mod_cast h

/-- `ofInt`-version of `AzInt.toInt_shiftRight`. -/
theorem AzInt.ofInt_shiftRight (i : Int) (sh : Nat) :
    AzInt.ofInt (i >>> sh) = (AzInt.ofInt i) >>> sh := by
  have h : (AzInt.ofInt (i >>> sh)).toInt = ((AzInt.ofInt i) >>> sh).toInt := by
    rw [AzInt.toInt_ofInt, AzInt.toInt_hShiftRight, AzInt.toInt_ofInt]
  have := congrArg AzInt.ofInt h
  rwa [AzInt.ofInt_toInt, AzInt.ofInt_toInt] at this

end Azurite
