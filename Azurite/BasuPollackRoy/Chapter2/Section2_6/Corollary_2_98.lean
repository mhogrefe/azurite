/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_6.AlgebraicPuiseux
import Azurite.BasuPollackRoy.Chapter2.Section2_6.Theorem_2_91
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_10

/-! # BPR §2.6 Corollary 2.98 — `R⟨ε⟩` is real closed

When `R` is real closed, the field `R⟨ε⟩` of algebraic Puiseux series is real closed. It is the
real closure of `R(ε)` (with the order `0₊`): it consists of the elements of the real closed field
`R⟨⟨ε⟩⟩` (Theorem 2.91) algebraic over `R(ε)`, which is exactly the relative algebraic closure
characterized in Exercise 2.10. -/

namespace Azurite.BPR

/-- **Corollary 2.98.** When `R` is real closed, the field `R⟨ε⟩` of algebraic Puiseux series is
real closed. -/
theorem isRealClosed_algebraicPuiseux (R : Type*) [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [IsRealClosed R] : IsRealClosed (algebraicPuiseux R) := by
  have : IsRealClosed (PuiseuxSeries R) := isRealClosed_puiseuxSeries
  exact isRealClosed_algebraicClosure (RatFunc R) (PuiseuxSeries R)

end Azurite.BPR
