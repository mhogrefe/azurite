/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpRat
import Azurite.AzFloat.Equiv.Exp

/-!
# Equivalence: the exponential of a rational

`expRatPrecRound_eq : expRatPrecRound q p mode = roundVal p mode (Spec.exp q)` for `p ≠ 0`:
`exp q` is correctly rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- **`exp` of a rational is correctly rounded.** -/
theorem expRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    expRatPrecRound q p mode = roundVal p mode (Spec.exp ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold expRatPrecRound
  rw [Spec.exp_coe]
  split_ifs with hp h0
  · exact absurd hp (NeZero.ne p)
  · rw [(AzRat.toRat_eq_zero_iff q).mpr h0, Real.exp_zero, setPrecRound_eq_roundVal toVal_one']
  · exact zivLoopCertified_eq_threshold p mode _ (Real.exp (AzRat.toRat q : ℝ)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
          expRatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q h0
        exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

end Azurite.AzFloat
