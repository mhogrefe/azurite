/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Basic
import Azurite.AzNat.Size
import Azurite.AzNat.NormalizedCompare

/-!
# Base-2 logarithm of `|AzRat|`

`floorLogBase2Abs q` and `ceilingLogBase2Abs q` compute `⌊log₂ |q|⌋` and `⌈log₂ |q|⌉` as
integers, staying limb-level: the bit lengths come from `AzNat.size` (not the GMP-backed
`Nat.log2`) and the boundary fractional comparison from the allocation-free
`AzNat.normalizedCompare`.

For positive `n`, `AzNat.size n = Nat.log2 n + 1`, so the exponent `size num - size den` equals
`Nat.log2 num - Nat.log2 den`.
-/

namespace Azurite.AzRat

/-- Floor of the base-2 logarithm of the absolute value of `q`. -/
def floorLogBase2Abs (q : AzRat) : ℤ :=
  let exponent : ℤ := (q.num.size : ℤ) - (q.den.size : ℤ)
  if AzNat.normalizedCompare q.num q.den == Ordering.lt then
    exponent - 1
  else
    exponent

/-- Ceiling of the base-2 logarithm of the absolute value of `q`. -/
def ceilingLogBase2Abs (q : AzRat) : ℤ :=
  let exponent : ℤ := (q.num.size : ℤ) - (q.den.size : ℤ)
  if AzNat.normalizedCompare q.num q.den == Ordering.gt then
    exponent + 1
  else
    exponent

end Azurite.AzRat
