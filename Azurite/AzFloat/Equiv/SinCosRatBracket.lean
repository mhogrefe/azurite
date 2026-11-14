/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinCosRatBracket
import Azurite.AzFloat.Equiv.CosRatBracket
import Azurite.AzFloat.Equiv.SinRatBracket
import Azurite.AzFloat.Equiv.ZivPair

/-!
# Equivalence: the joint bracket of `sin q` and `cos q` for a rational `q`

`sinCosRatApprox_isSome_exists`: the joint Ziv certificate, from the specifications of the two
components (`sinRatApprox_spec`, `cosRatApprox_spec`) and the irrationality of `sin q` and
`cos q` for a rational `q ≠ 0`.
-/

namespace Azurite.AzFloat

/-- The joint Ziv certificate for `sin q` and `cos q`, `q` a nonzero rational. -/
theorem sinCosRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible₂ (sinCosRatApprox q (w₀ * 2 ^ f)) p mode).isSome = true :=
  exists_isSome₂_of_irrational_threshold p mode (sinCosRatApprox q) (irrational_sin_toRat q h0)
    (irrational_cos_toRat q h0) (sinRatEps q) (cosRatEps q) (tendsto_sinRatEps q)
    (tendsto_cosRatEps q) 64
    (fun w hw => by rw [sinCosRatApprox_fst]; exact sinRatApprox_spec q h0 hw)
    (fun w hw => by rw [sinCosRatApprox_snd]; exact cosRatApprox_spec q hw) w₀ hw₀

end Azurite.AzFloat
