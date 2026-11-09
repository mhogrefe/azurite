/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnRat
import Azurite.AzFloat.Equiv.Ln

/-!
# Equivalence: the natural logarithm of a rational

`lnRatPrecRound_eq : lnRatPrecRound q p mode = roundVal p mode (Spec.log q)` for `p ≠ 0`: `ln q`
is correctly rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- `lnRatPrecRoundCore A hA` is correctly rounded for every bracket function `A` with the
conclusion of `lnRatApprox_spec`. -/
theorem lnRatPrecRoundCore_eq (A : AzRat → ℕ → Roundable × Roundable) (hA)
    (hspec : ∀ {w : ℕ}, 64 ≤ w → ∀ (q : AzRat), (0 : ℚ) < AzRat.toRat q → AzRat.toRat q ≠ 1 →
      ∃ lv hv : ℝ, Rounds (A q w).1 lv ∧ Rounds (A q w).2 hv ∧
        lv < Real.log (AzRat.toRat q : ℝ) ∧ Real.log (AzRat.toRat q : ℝ) < hv ∧
        hv - lv ≤ lnRatEps (⌊2 * |Real.log (AzRat.toRat q : ℝ)|⌋₊ + 2)
          |Real.log (AzRat.toRat q : ℝ)| w)
    (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnRatPrecRoundCore A hA q p mode
      = roundVal p mode (Spec.log ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold lnRatPrecRoundCore
  split_ifs with h0 hs h1 hp
  · rw [(AzRat.toRat_eq_zero_iff q).mpr h0]
    simp only [EReal.coe_zero, Spec.log_zero, roundVal_bot]
  · rw [toRat_eq_one_of_num_eq_den q hs h1]
    simp only [Rat.cast_one]
    rw [Spec.log_coe _ one_pos, Real.log_one, EReal.coe_zero, roundVal_zero]
  · exact absurd hp (NeZero.ne p)
  · have hq := toRat_pos_of_sign q hs h0
    have hq1 := toRat_ne_one_of_num_ne_den q hs h1
    rw [Spec.log_coe _ (by exact_mod_cast hq)]
    exact zivLoopCertified_eq_threshold p mode _ (Real.log (AzRat.toRat q : ℝ)) _
      (by unfold zivGuardBits; omega)
      (fun w hw => by
        obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
          hspec (w := w) (by unfold zivGuardBits at hw; omega) q hq hq1
        exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _
  · have hneg := toRat_neg_of_sign q (by simpa using hs) h0
    rw [Spec.log_coe_neg _ hneg, roundVal_none]

/-- **`ln` of a rational is correctly rounded.** -/
theorem lnRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnRatPrecRound q p mode = roundVal p mode (Spec.log ((AzRat.toRat q : ℝ) : EReal)) :=
  lnRatPrecRoundCore_eq _ _ @lnRatApprox_spec q p mode

/-- **`ln` of a rational with precomputed constants is correctly rounded.** -/
theorem lnRatPrecRoundWith_eq (c : LnConsts) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnRatPrecRoundWith c q p mode = roundVal p mode (Spec.log ((AzRat.toRat q : ℝ) : EReal)) :=
  lnRatPrecRoundCore_eq _ _ (@lnRatApproxWith_spec c) q p mode

theorem lnRatPrecRoundWith_eq_lnRatPrecRound (c : LnConsts) (q : AzRat) (p : ℕ)
    (mode : RoundingMode) : lnRatPrecRoundWith c q p mode = lnRatPrecRound q p mode := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simp [lnRatPrecRoundWith, lnRatPrecRound, lnRatPrecRoundCore]
  · have : NeZero p := ⟨hp.ne'⟩
    rw [lnRatPrecRoundWith_eq, lnRatPrecRound_eq]

theorem lnRatWith_eq_lnRat (c : LnConsts) (q : AzRat) (p : ℕ) : lnRatWith c q p = lnRat q p := by
  unfold lnRatWith lnRat
  rw [lnRatPrecRoundWith_eq_lnRatPrecRound]

end Azurite.AzFloat
