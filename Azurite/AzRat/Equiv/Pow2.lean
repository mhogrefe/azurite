/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Pow2
import Azurite.AzNat.Equiv.Pow2

/-!
# Equivalence: powers of two among rationals

`isPowerOfTwo_iff`: `q.isPowerOfTwo` holds iff `q` is positive and numerator and denominator are
powers of two.  The value `q = 2^(powerOfTwoExponent q)` is proven where `toRat` is available as a
real quotient (`Azurite/AzFloat/Equiv/Log2Bracket.lean`, `toRat_of_isPowerOfTwo`).
-/

namespace Azurite.AzRat

theorem isPowerOfTwo_iff (q : AzRat) :
    q.isPowerOfTwo = true ↔
      q.sign = true ∧ q.num.toNat.isPowerOfTwo ∧ q.den.toNat.isPowerOfTwo := by
  unfold isPowerOfTwo
  rw [Bool.and_eq_true, Bool.and_eq_true, AzNat.isPowerOfTwo_iff, AzNat.isPowerOfTwo_iff, and_assoc]

end Azurite.AzRat
