/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Pi

/-!
# Equivalence: `π`

`piPrecRound p mode = liftVal₀ π p mode` (`piPrecRound_eq_liftVal₀`): `π` is correctly rounded
in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- **`π` is correctly rounded.** -/
theorem piPrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    piPrecRound p mode = liftVal₀ (some ((Real.pi : ℝ) : EReal)) p mode := by
  unfold piPrecRound liftVal₀
  split_ifs with hp
  · exact absurd hp (NeZero.ne p)
  apply zivLoopCertified_eq_threshold p mode piApprox Real.pi (p + zivGuardBits)
    (by unfold zivGuardBits; omega)
  intro w hw
  obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
    piApprox_spec (w := w) (by unfold zivGuardBits at hw; omega)
  exact ⟨lv, hv, hl, hh, hlo.le, hhi, fun h => absurd h hlo.ne⟩

end Azurite.AzFloat
