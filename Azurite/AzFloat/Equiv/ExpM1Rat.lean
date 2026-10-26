/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpM1Rat
import Azurite.AzFloat.Equiv.ExpM1

/-!
# Equivalence: `exp q − 1` for a rational

`expM1RatPrecRound_eq : expM1RatPrecRound q p mode = roundVal p mode (Spec.expM1 q)` for
`p ≠ 0`: `exp q − 1` is correctly rounded in every mode, with the exact comparison, and without
fuel.
-/

namespace Azurite.AzFloat

/-- **`exp q − 1` of a rational is correctly rounded.** -/
theorem expM1RatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    expM1RatPrecRound q p mode
      = roundVal p mode (Spec.expM1 ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold expM1RatPrecRound
  rw [Spec.expM1_coe]
  split_ifs with hp h0
  · exact absurd hp (NeZero.ne p)
  · rw [(AzRat.toRat_eq_zero_iff q).mpr h0, Real.exp_zero, sub_self, EReal.coe_zero, roundVal_zero]
  · exact zivLoopCertified_eq_threshold p mode _ (Real.exp (AzRat.toRat q : ℝ) - 1) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
          expM1RatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q h0
        exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

end Azurite.AzFloat
