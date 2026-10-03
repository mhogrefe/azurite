/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Literals
import Azurite.AzFloat.Equiv.Conversion
import Azurite.AzFloat.Equiv.Rounding
import Azurite.AzRat.Equiv.FromSci

/-!
# Values of literals
-/

namespace Azurite.AzFloat

open RoundingTarget

instance : NeZero literalPrecision := ⟨by decide⟩
instance : Fact (1 < 2) := ⟨by norm_num⟩

theorem toVal_ofNat (n : ℕ) :
    toVal (OfNat.ofNat (n + 2) : AzFloat) = some (((n + 2 : ℕ) : ℝ) : EReal) := by
  show toVal (ofAzNat (AzNat.ofNat (n + 2))) = _
  rw [toVal_ofAzNat, AzNat.toNat_ofNat]

theorem toRat_scientificValue (m : ℕ) (negExp : Bool) (e : ℕ) :
    AzRat.toRat (scientificValue m negExp e) = (m : ℚ) * 10 ^ (if negExp then -(e : ℤ) else e) := by
  unfold scientificValue
  rw [AzRat.toRat_ofSciParts 10 (by decide), AzNat.toNat_ofNat]
  simp

/-- A scientific literal is the exact decimal rounded to nearest at `literalPrecision` bits. -/
theorem toVal_ofScientific (m : ℕ) (negExp : Bool) (e : ℕ) :
    toVal (OfScientific.ofScientific m negExp e : AzFloat)
      = some (RoundingTarget.round (precisionSet 2 literalPrecision) .Nearest
          (((m : ℚ) * 10 ^ (if negExp then -(e : ℤ) else e) : ℚ) : ℝ)).val := by
  show toVal (ofAzRatRound (scientificValue m negExp e) literalPrecision .Nearest).1 = _
  rw [toVal_ofAzRatRound, toRat_scientificValue]

end Azurite.AzFloat
