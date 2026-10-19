/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Basic
import Azurite.AzNat.Pow2
import Azurite.AzNat.Size

/-!
# Powers of two among rationals

`isPowerOfTwo q` decides whether `q = 2^k` for an integer `k`: `q` is positive and its numerator
and denominator are powers of two (the fraction is reduced, so one of them is `1`).  For such a
`q`, `powerOfTwoExponent q` is `k`, the difference of the bit lengths of numerator and
denominator.
-/

namespace Azurite.AzRat

/-- Whether `q` is an integer power of two `2^k` (`k ∈ ℤ`). -/
def isPowerOfTwo (q : AzRat) : Bool := q.sign && q.num.isPowerOfTwo && q.den.isPowerOfTwo

/-- The exponent `k` of a power of two `q = 2^k`: `size num − size den` (meaningful only when
`isPowerOfTwo q`). -/
def powerOfTwoExponent (q : AzRat) : AzInt :=
  (AzNat.ofNat q.num.size).toAzInt - (AzNat.ofNat q.den.size).toAzInt

end Azurite.AzRat
