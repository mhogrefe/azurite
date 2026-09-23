/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Basic
import Azurite.AzNat.TrailingZeros

namespace Azurite

/-- Count the number of trailing zeros in the binary representation of an integer.
Returns `none` for zero (which has infinitely many trailing zeros). -/
def AzInt.trailingZeros (z : AzInt) : Option Nat := z.abs.trailingZeros

end Azurite
