/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Gen.Search
import Azurite.ECPP.Equiv.Check

/-!
# Soundness of primality proving by elliptic curves

The generator is not verified; its output is checked.  **`provePrime_sound`**:
`provePrime n P = true → Nat.Prime n.toNat`, for every choice of parameters.
-/

namespace Azurite.ECPP

/-- **`provePrime` proves primality.** -/
theorem provePrime_sound {n : AzNat} {P : GenParams} (h : provePrime n P = true) :
    Nat.Prime n.toNat := by
  unfold provePrime at h
  split at h
  · exact check_prime h
  · exact absurd h (by simp)

end Azurite.ECPP
