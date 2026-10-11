/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.CompareProducts
import Azurite.AzInt.Equiv.CompareProduct
import Azurite.AzNat.Equiv.CompareProducts

/-!
## Correctness of `AzInt.compareProducts`

`compareProducts_eq : compareProducts a b c d = compare (a.toInt * b.toInt) (c.toInt * d.toInt)`:
both products are signed products of magnitudes, and `compare_signed` settles the sign cases,
deferring to `AzNat.compareProducts_eq` for equal signs.
-/

namespace Azurite.AzInt

/-- The value of a product of two integers as a signed product of magnitudes. -/
theorem toInt_mul_signed (as bs : Bool) (aa ba : AzNat) :
    (if as then (aa.toNat : ℤ) else -(aa.toNat : ℤ))
        * (if bs then (ba.toNat : ℤ) else -(ba.toNat : ℤ))
      = if (as == bs) then ((aa.toNat * ba.toNat : ℕ) : ℤ)
        else -((aa.toNat * ba.toNat : ℕ) : ℤ) := by
  cases as <;> cases bs <;> simp [Nat.cast_mul]

/-- **Correctness of `compareProducts`.** -/
theorem compareProducts_eq (a b c d : AzInt) :
    compareProducts a b c d = Ord.compare (a.toInt * b.toInt) (c.toInt * d.toInt) := by
  rcases a with ⟨as, aa, _⟩
  rcases b with ⟨bs, ba, _⟩
  rcases c with ⟨cs, ca, _⟩
  rcases d with ⟨ds, da, _⟩
  unfold compareProducts toInt
  dsimp only
  rw [toInt_mul_signed, toInt_mul_signed, compare_signed]
  simp only [AzNat.eq_zero_iff_toNat, AzNat.compareProducts_eq, Nat.mul_eq_zero]

end Azurite.AzInt
