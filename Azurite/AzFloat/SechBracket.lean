/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CoshBracket

/-!
## The brackets of `sech x` and `sech q`

`sech x = 1 / cosh x`, in `(0, 1]`.  `sechOfCosh c W` is the reciprocal of an enclosure `c` of
`cosh x ≥ 1` with outward rounding at `W` bits (the lower end of `c` is first raised to `1`),
and `sechBracket x e w` applies it to `coshBracket x e w` (`AzFloat/CoshBracket.lean`), whose
relative accuracy it keeps: for a large `x` the value is `≈ 2 e^(−|x|)`.  `sechApprox` is the
pair of `Roundable`s for the Ziv loop of `AzFloat/Sech.lean`.  `sechRatBracket q w` and
`sechRatApprox` are the same on `coshRatBracket q w` for a rational `q`
(`AzFloat/SechRat.lean`).

**Tiny arguments**: `exp (−x²/2) ≤ sech x < 1`, so for `|x| < 2^e` the value is `exp v` with
`−2^(2e−1) < v < 0`, and the tiny-exponent test of the exponential, `expNearOne? false` (exact
end `1` at the open side), applies at the exponent `coshTinyExp e = 2e − 1`
(`coshRatTinyExp q` for a rational).

The proofs are in `Equiv/SechBracket.lean`.
-/

namespace Azurite.AzFloat

/-- `1/C` on an enclosure of `C ≥ 1`, rounded outwards at precision `W`. -/
def sechOfCosh (c : Encl) (W : Nat) : Encl :=
  ((divPrecRound one c.2 W .Floor).1, (divPrecRound one (maxOf c.1 one) W .Ceiling).1)

/-- The bracket of `sech x` at Ziv level `w` for a finite float `x` with `|x| < 2^e`. -/
def sechBracket (x : AzFloat) (e : AzInt) (w : Nat) : Encl :=
  sechOfCosh (coshBracket x e w) (w + 16)

/-- The bracket of `sech x` as a pair of `Roundable`s. -/
def sechApprox (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  enclApprox false (sechBracket x e w)

/-- The bracket of `sech q` at Ziv level `w` for a rational `q`. -/
def sechRatBracket (q : AzRat) (w : Nat) : Encl :=
  sechOfCosh (coshRatBracket q w) (w + 16)

/-- The bracket of `sech q` as a pair of `Roundable`s. -/
def sechRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  enclApprox false (sechRatBracket q w)

end Azurite.AzFloat
