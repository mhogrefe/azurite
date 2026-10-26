/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Phi

/-!
# Equivalence: the golden ratio is correctly rounded

`phiPrecRound_eq_liftVal₀ : phiPrecRound p mode = liftVal₀ (some φ) p mode` for every `p ≠ 0`
and every mode, without fuel.
-/

namespace Azurite.AzFloat

/-- **The golden ratio is correctly rounded.** -/
theorem phiPrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    phiPrecRound p mode = liftVal₀ (some (((1 + Real.sqrt 5) / 2 : ℝ) : EReal)) p mode := by
  unfold phiPrecRound liftVal₀
  split_ifs with hp
  · exact absurd hp (NeZero.ne p)
  apply zivLoopCertified_eq_threshold p mode phiApprox ((1 + Real.sqrt 5) / 2)
    (p + zivGuardBits) (by unfold zivGuardBits; omega)
  intro w hw
  have : NeZero w := ⟨by omega⟩
  obtain ⟨lv, hv, hl, hh, hlo, hhi, heq, -⟩ := phiApprox_encloses w
  exact ⟨lv, hv, hl, hh, hlo, hhi, heq⟩

end Azurite.AzFloat
