/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosWithPeriodBracket
import Azurite.AzFloat.CosRatBracket
import Azurite.AzFloat.SecBracket

/-!
## The brackets of `sec (2π x / u)` and of `sec q`

`secPeriodBracket r w` encloses `sec (2πr)` for a rational `r ∈ [0, 1)` (the exact reduction
`periodFrac` of `|x|/u`) at Ziv level `w`, and `secRatBracket q w` encloses `sec q` for a
rational `q`: the quotient step `tanOfSinCos` (`AzFloat/TanBracket.lean`) applied to the exact
numerator `1` and the bracket of the cosine (`cosPeriodBracket`, `cosRatBracket`) — or the dummy
bracket `[−1, 1]` while that bracket contains `0`.
-/

namespace Azurite.AzFloat

/-- The bracket of `sec (2πr)` at Ziv level `w` for a rational `r ∈ [0, 1)`, or the dummy
bracket `[−1, 1]` when the bracket of `cos (2πr)` contains `0`. -/
def secPeriodBracket (r : AzRat) (w : Nat) : AzFloat × AzFloat :=
  tanOfSinCos (Encl.exact one, cosPeriodBracket r w) (w + 12)

/-- `secPeriodBracket` as a pair of `Roundable`s for the Ziv loop. -/
def secPeriodApprox (r : AzRat) (w : Nat) : Roundable × Roundable :=
  negSwapApprox false (secPeriodBracket r w)

/-- The bracket of `sec q` at Ziv level `w` for a rational `q`, or the dummy bracket `[−1, 1]`
when the bracket of `cos q` contains `0`. -/
def secRatBracket (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  tanOfSinCos (Encl.exact one, cosRatBracket q w) (w + 12)

/-- `secRatBracket` as a pair of `Roundable`s for the Ziv loop. -/
def secRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  negSwapApprox false (secRatBracket q w)

end Azurite.AzFloat
