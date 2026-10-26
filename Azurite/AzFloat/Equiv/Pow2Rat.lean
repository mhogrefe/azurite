/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Pow2
import Azurite.AzFloat.Pow2Rat

/-!
# Equivalence: `2^q` for a rational

`pow2RatPrecRound_eq : pow2RatPrecRound q p mode = roundVal p mode (Spec.pow2 q)` for `p ≠ 0`:
`2^q` is correctly rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- The value of `AzInt.mkNorm s a`. -/
theorem toInt_mkNorm (s : Bool) (a : AzNat) :
    (AzInt.mkNorm s a).toInt = if s then (a.toNat : ℤ) else -(a.toNat : ℤ) := by
  unfold AzInt.mkNorm AzInt.toInt
  split_ifs with h0 hs hs <;> simp_all [AzNat.toNat_zero]

/-- **`2^q` of a rational is correctly rounded.** -/
theorem pow2RatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    pow2RatPrecRound q p mode = roundVal p mode (Spec.pow2 ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold pow2RatPrecRound
  rw [Spec.pow2_coe]
  split_ifs with hp hd
  · exact absurd hp (NeZero.ne p)
  · rw [setPrecRound_eq_roundVal (toVal_powerOf2 _), toInt_mkNorm]
    have hval : (AzRat.toRat q : ℝ)
        = (((if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ)) : ℤ) : ℝ) := by
      rw [AzRat.toRat_cast_eq, hd, Nat.cast_one, div_one]
    rw [hval, Real.rpow_intCast]
  · exact zivLoopCertified_eq_threshold p mode _ ((2 : ℝ) ^ (AzRat.toRat q : ℝ)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
          pow2RatApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) q hd
        exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

end Azurite.AzFloat
