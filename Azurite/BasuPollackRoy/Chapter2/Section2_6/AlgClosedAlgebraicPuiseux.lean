/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_6.AlgebraicPuiseux
import Azurite.BasuPollackRoy.Chapter2.Section2_6.Theorem_2_92

/-! # BPR §2.6 — `C⟨ε⟩` is an algebraic closure of `C(ε)`

This is the algebraically closed analogue of Corollary 2.98. When `C` is algebraically closed of
characteristic zero, Theorem 2.92 says the Puiseux series `C⟨⟨ε⟩⟩ = PuiseuxSeries C` are
algebraically closed. Hence the field `C⟨ε⟩ = algebraicPuiseux C` of *algebraic* Puiseux series — the
relative algebraic closure of `C(ε) = RatFunc C` inside `C⟨⟨ε⟩⟩` — is an algebraic closure of `C(ε)`:
it is algebraically closed (this file) and, by construction, algebraic over `C(ε)`.

In the case `C = R[i]` for `R` real closed, this matches the field `R⟨ε⟩[i]` obtained from
Corollary 2.98 (`R⟨ε⟩` is real closed) together with Theorem 2.11 (`R⟨ε⟩[i]` is algebraically
closed): `C⟨ε⟩ = R⟨ε⟩[i]`. -/

namespace Azurite.BPR

open Polynomial

/-- The algebraic Puiseux series `C⟨ε⟩` over an algebraically closed field `C` of characteristic
zero form **an algebraic closure of `C(ε)`** (`IsAlgClosure`): they are algebraically closed and
algebraic over `C(ε) = RatFunc C`. This is the relative algebraic closure of `C(ε)` inside the
algebraically closed field `C⟨⟨ε⟩⟩` (Theorem 2.92). -/
theorem isAlgClosure_algebraicPuiseux (C : Type*) [Field C] [IsAlgClosed C] [CharZero C] :
    IsAlgClosure (RatFunc C) (algebraicClosure (RatFunc C) (PuiseuxSeries C)) := by
  have : IsAlgClosed (PuiseuxSeries C) := isAlgClosed_puiseuxSeries C
  infer_instance

/-- **`C⟨ε⟩` is algebraically closed.** When `C` is algebraically closed of characteristic zero, the
field `C⟨ε⟩` of algebraic Puiseux series is algebraically closed (the field analogue of
Corollary 2.98). Together with the fact that `C⟨ε⟩` is algebraic over `C(ε)` by construction, this
exhibits `C⟨ε⟩` as an algebraic closure of `C(ε)`. -/
theorem isAlgClosed_algebraicPuiseux (C : Type*) [Field C] [IsAlgClosed C] [CharZero C] :
    IsAlgClosed (algebraicPuiseux C) := by
  have : IsAlgClosed (PuiseuxSeries C) := isAlgClosed_puiseuxSeries C
  exact (algebraicClosure.isAlgClosure (RatFunc C) (PuiseuxSeries C)).isAlgClosed

end Azurite.BPR
