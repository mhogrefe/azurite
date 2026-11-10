/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Dottie

/-!
# Equivalence: the Dottie number

`dottiePrecRound_eq_liftVal₀ : dottiePrecRound p mode = liftVal₀ (some dottieNumber) p mode` for
`p ≠ 0`, with `Azurite.dottieNumber` the solution of `cos x = x` (`Transcendental/Dottie.lean`).
-/

namespace Azurite.AzFloat

/-- **The Dottie number is correctly rounded.** -/
theorem dottiePrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    dottiePrecRound p mode = liftVal₀ (some ((Azurite.dottieNumber : ℝ) : EReal)) p mode := by
  unfold dottiePrecRound liftVal₀
  split_ifs with hp
  · exact absurd hp (NeZero.ne p)
  exact zivLoopCertified_eq_threshold' p mode dottieApprox Azurite.dottieNumber
    (not_mem_floatSet_of_irrational p irrational_dottie) (p + zivGuardBits)
    (by unfold zivGuardBits; omega)
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
        dottieApprox_spec (w := w) (by unfold zivGuardBits at hw; omega)
      exact ⟨lv, hv, hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
