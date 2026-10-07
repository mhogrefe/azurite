/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Equiv.ExtendedGcd.Binary
import Azurite.AzInt.Equiv.ExtendedGcd.HalfBinary
import Azurite.AzInt.ExtendedGcd

/-!
## Correctness of `AzInt.egcd`

Both dispatch targets satisfy the Bézout identity and compute `Nat.gcd` (`egcdBinary_bezout`,
`egcdBinary_gcd`, `egcdHalfBinary_bezout`, `egcdHalfBinary_gcd`), hence so does `egcd`.
-/

namespace Azurite.AzInt

/-- **Bézout identity for `egcd`.**  With `(g, s, t) = egcd a b`, `s · a + t · b = g` over `ℤ`. -/
theorem egcd_bezout (a b : AzNat) :
    (egcd a b).2.1.toInt * (a.toNat : ℤ) + (egcd a b).2.2.toInt * (b.toNat : ℤ)
      = ((egcd a b).1.toNat : ℤ) := by
  unfold egcd
  split_ifs
  · exact egcdBinary_bezout a b
  · exact egcdHalfBinary_bezout a b

/-- **gcd-value equality for `egcd`.**  With `(g, s, t) = egcd a b`, `g = gcd a b`. -/
theorem egcd_gcd (a b : AzNat) : (egcd a b).1.toNat = Nat.gcd a.toNat b.toNat := by
  unfold egcd
  split_ifs
  · exact egcdBinary_gcd a b
  · exact egcdHalfBinary_gcd a b

end Azurite.AzInt
