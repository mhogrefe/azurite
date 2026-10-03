/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzRat.ToSci

/-!
# Decimal (and other base) output with explicit options

`toString` prints the shortest round-tripping decimal.  `toSci x o` instead renders the exact
value of `x` with `AzRat.toSci`'s options: the base, the rounding mode of the digits, a fixed
number of significant digits or of digits after the point, and the layout (`SciOptions`).  The
special values are their names; the `.0` convention of `toString` is not applied here.
-/

namespace Azurite.AzFloat

/-- The `SciNumber` of a finite float under `o` (`none` for `NaN`, `±∞` and invalid options). -/
def toSciNumber (x : AzFloat) (o : SciOptions := {}) : Option SciNumber :=
  x.toAzRat?.bind (·.toSciNumber o)

/-- Render `x` with explicit options; `NaN`, `Infinity`, `-Infinity` for the special values,
`none` for invalid options. -/
def toSci (x : AzFloat) (o : SciOptions := {}) : Option String :=
  match x with
  | nan => some "NaN"
  | infinity true => some "Infinity"
  | infinity false => some "-Infinity"
  | _ => x.toAzRat?.bind (·.toSci o)

end Azurite.AzFloat
