/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Recip
import Azurite.AzFloat.Equiv.Div
import Azurite.AzFloat.Equiv.Sum

/-!
# Equivalence: the reciprocal

`recipPrecRound_eq_liftVal : recipPrecRound y p mode = liftVal (fun a => Spec.div 1 a) y p mode`,
from the division specification with `one` as the dividend.
-/

namespace Azurite.AzFloat

/-- **The reciprocal is correctly rounded.** -/
theorem recipPrecRound_eq_liftVal (y : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    recipPrecRound y p mode = liftVal (fun a => Spec.div 1 a) y p mode := by
  unfold recipPrecRound liftVal
  rw [divPrecRound_eq_liftVal₂, liftVal₂, toVal_one', Option.bind_some, EReal.coe_one]

end Azurite.AzFloat
