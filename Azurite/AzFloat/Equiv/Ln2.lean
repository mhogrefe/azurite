/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ln2

/-!
# Equivalence: `ln2PrecRound` is the correctly rounded `ln 2`

`ln2PrecRound p mode = liftVal₀ (ln 2) p mode` for every `p ≠ 0` and every mode.
-/

namespace Azurite.AzFloat

/-- **`ln 2` is correctly rounded.** -/
theorem ln2PrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    ln2PrecRound p mode = liftVal₀ (some ((Real.log 2 : ℝ) : EReal)) p mode := by
  unfold ln2PrecRound liftVal₀
  split_ifs with hp
  · exact absurd hp (NeZero.ne p)
  apply zivLoopCertified_eq p mode ln2Approx (Real.log 2) ?_ (p + zivGuardBits)
    (by unfold zivGuardBits; omega)
  intro w _
  obtain ⟨hl, hh⟩ := ln2Approx_spec w
  obtain ⟨hlo, hhi⟩ := ln2Bracket_mem w
  exact ⟨_, _, hl, hh, hlo, hhi, fun h => absurd h (lo_lt_log_two w).ne⟩

end Azurite.AzFloat
