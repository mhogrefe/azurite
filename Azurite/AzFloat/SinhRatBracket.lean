/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinhBracket
import Azurite.AzFloat.TanRatBracket

/-!
## The bracket of `sinh q` for a rational `q`

`sinhRatBracket q w` is `sinhOfExpM1` (`(u + u/(1 + u))/2`, `AzFloat/SinhBracket.lean`) on
`expM1RatBracket |q| w`, the enclosure of `u = exp |q| − 1` for a rational argument (relative
accuracy for a small `q`); `sinhRatApprox` is the pair of `Roundable`s, negated and swapped for
`q < 0`.  Tiny arguments use `tanTinyRat?`, as the float `sinh` uses `tanTiny?`.

The proofs are in `Equiv/SinhRatBracket.lean`.
-/

namespace Azurite.AzFloat

/-- The bracket of `sinh |q|` at Ziv level `w` for a rational `q ≠ 0`. -/
def sinhRatBracket (q : AzRat) (w : Nat) : Encl :=
  sinhOfExpM1 (expM1RatBracket q.abs w) (w + 16)

/-- The bracket of `sinh q` as a pair of `Roundable`s. -/
def sinhRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  enclApprox (!q.sign) (sinhRatBracket q w)

end Azurite.AzFloat
