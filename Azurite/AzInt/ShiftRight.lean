/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.ShiftRightRound

namespace Azurite.AzInt

/-- Right shift: `z >>> sh`. Rounds toward `−∞` (`Floor`), matching the abstract
`round intSet .Floor (z.toInt / 2^sh)`. For nonnegative `z` this is the plain
magnitude shift; for negative `z` the magnitude is rounded *away* from zero
(equivalent to `−⌈|z|/2^sh⌉`). -/
def shiftRight (z : AzInt) (sh : Nat) : AzInt :=
  (z.shiftRightRound .Floor sh).1

instance : HShiftRight AzInt Nat AzInt := ⟨shiftRight⟩

end Azurite.AzInt
