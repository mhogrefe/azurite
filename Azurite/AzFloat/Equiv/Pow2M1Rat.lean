/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Pow2M1
import Azurite.AzFloat.Equiv.Pow2Rat
import Azurite.AzFloat.Pow2M1Rat

/-!
# Equivalence: `2^q − 1` for a rational

`pow2M1RatPrecRound_eq : pow2M1RatPrecRound q p mode = roundVal p mode (Spec.pow2M1 q)` for
`p ≠ 0`: `2^q − 1` is correctly rounded in every mode, with the exact comparison, and without
fuel.
-/

namespace Azurite.AzFloat

/-- **`2^q − 1` of a rational is correctly rounded.** -/
theorem pow2M1RatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    pow2M1RatPrecRound q p mode
      = roundVal p mode (Spec.pow2M1 ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold pow2M1RatPrecRound
  rw [Spec.pow2M1_coe]
  split_ifs with hp h0 hd
  · exact absurd hp (NeZero.ne p)
  · rw [(AzRat.toRat_eq_zero_iff q).mpr h0, Real.rpow_zero, sub_self, EReal.coe_zero,
      roundVal_zero]
  · rw [subPrecRound_eq_liftVal₂, liftVal₂, toVal_powerOf2, toVal_one', Option.bind_some,
      Option.bind_some, Spec.sub, ← EReal.coe_neg, Spec.add_coe_coe, toInt_mkNorm]
    have hval : (AzRat.toRat q : ℝ)
        = (((if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ)) : ℤ) : ℝ) := by
      rw [AzRat.toRat_cast_eq, hd, Nat.cast_one, div_one]
    rw [hval, Real.rpow_intCast, sub_eq_add_neg]
  · exact zivLoopCertified_eq_threshold p mode _ ((2 : ℝ) ^ (AzRat.toRat q : ℝ) - 1) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
          pow2M1RatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q h0 hd
        exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

end Azurite.AzFloat
