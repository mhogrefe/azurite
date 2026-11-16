/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsecWithPeriod
import Azurite.AzFloat.AsecRat

/-!
## `arcsec (x) / π`

`asecPiPrecRound x p mode` is `arcsec (x) / π` for a float `x` (the arcsecant in half-turns, in
`[0, 1]`), correctly rounded to precision `p` in `mode`, with the comparison against the exact
value; `asecPi x` rounds to nearest at the precision of `x`.  `asecPiRatPrecRound q p mode` and
`asecPiRat q p` are the same for an `AzRat` `q`.  These are the period-`2` cases of
`asecWithPeriodPrecRound` and `asecRatWithPeriodPrecRound`.

Rational values: `asecPi 1 = 0`, `asecPi (−1) = 1`, `asecPi (±∞) = 1/2`, and the correctly
rounded `asecPi 2 = 1/3`, `asecPi (−2) = 2/3`; every other value is irrational.  `NaN` for `NaN`
and for `|x| < 1`.
-/

namespace Azurite.AzFloat

/-- `arcsec (x) / π` rounded to precision `p` with `mode`, and the comparison with the exact
value. -/
def asecPiPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  asecWithPeriodPrecRound x 2 p mode

/-- `arcsec (x) / π` rounded to nearest at the precision of `x` (at precision `1` for
`x = ±∞`). -/
def asecPi (x : AzFloat) : AzFloat := (asecPiPrecRound x (x.precision?.getD 1) .Nearest).1

/-- `arcsec (q) / π` for an `AzRat` `q`, rounded to precision `p` with `mode`, and the
comparison with the exact value. -/
def asecPiRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  asecRatWithPeriodPrecRound q 2 p mode

/-- `arcsec (q) / π` rounded to nearest at precision `p`. -/
def asecPiRat (q : AzRat) (p : Nat) : AzFloat := (asecPiRatPrecRound q p .Nearest).1

end Azurite.AzFloat
