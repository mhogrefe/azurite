/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PiBracket
import Azurite.AzFloat.LogBasePow2Bracket

/-!
## The bracket of `π/3`

`piDiv3Approx w` divides the bracket of `π` (`piBracket w`) by `3` with directed rounding
(`divBracketByInt`), as a pair of `Roundable`s for the Ziv loop.  The other multiples of `π`
by powers of two are exact shifts (`AzFloat/PiMultiples`).
-/

namespace Azurite.AzFloat

/-- The two ends of the `π/3` bracket, rounded at any requested precision. -/
def piDiv3Approx (w : Nat) : Roundable × Roundable :=
  divBracketByInt (piBracket w) (AzInt.ofInt 3) w

end Azurite.AzFloat
