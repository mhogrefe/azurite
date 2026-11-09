/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Log2Rat
import Azurite.AzFloat.Equiv.Log2

/-!
# Equivalence: the base-2 logarithm of a rational

`log2RatPrecRound_eq : log2RatPrecRound q p mode = roundVal p mode (Spec.log2 q)` for `p ≠ 0`:
`log₂ q` is correctly rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- `log2RatPrecRoundCore A hA` is correctly rounded for every bracket function `A` with the
conclusion of `log2RatApprox_spec`. -/
theorem log2RatPrecRoundCore_eq (A : AzRat → ℕ → Roundable × Roundable) (hA)
    (hspec : ∀ {w : ℕ}, 64 ≤ w → ∀ (q : AzRat), (0 : ℚ) < AzRat.toRat q →
      q.isPowerOfTwo = false →
      ∃ lv hv : ℝ, Rounds (A q w).1 lv ∧ Rounds (A q w).2 hv ∧
        lv < Real.logb 2 (AzRat.toRat q : ℝ) ∧ Real.logb 2 (AzRat.toRat q : ℝ) < hv ∧
        hv - lv ≤ log2RatEps (⌊2 * |Real.log (AzRat.toRat q : ℝ)|⌋₊ + 2)
          |Real.log (AzRat.toRat q : ℝ)| w)
    (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log2RatPrecRoundCore A hA q p mode
      = roundVal p mode (Spec.log2 ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold log2RatPrecRoundCore
  split_ifs with h0 hs hp
  · rw [(AzRat.toRat_eq_zero_iff q).mpr h0]
    simp only [EReal.coe_zero, Spec.log2_zero, roundVal_bot]
  · exact absurd hp (NeZero.ne p)
  · have hq := toRat_pos_of_sign q hs h0
    have hqr : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
    split
    · rename_i k hk
      obtain ⟨h2, rfl⟩ := AzRat.checkedLogBase2_eq_some q k hk
      rw [setPrecRound_eq_roundVal (toVal_ofAzInt _), Spec.log2_coe _ hqr,
        AzRat.toRat_of_isPowerOfTwo q h2, logb_two_zpow]
    · rename_i hk
      have h2 := AzRat.isPowerOfTwo_eq_false_of_checkedLogBase2_eq_none q hk
      rw [Spec.log2_coe _ hqr]
      exact zivLoopCertified_eq_threshold p mode _ (Real.logb 2 (AzRat.toRat q : ℝ)) _
        (by unfold zivGuardBits; omega)
        (fun w hw => by
          obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
            hspec (w := w) (by unfold zivGuardBits at hw; omega) q hq h2
          exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _
  · have hneg := toRat_neg_of_sign q (by simpa using hs) h0
    rw [Spec.log2_coe_neg _ hneg, roundVal_none]

/-- **`log₂` of a rational is correctly rounded.** -/
theorem log2RatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log2RatPrecRound q p mode = roundVal p mode (Spec.log2 ((AzRat.toRat q : ℝ) : EReal)) :=
  log2RatPrecRoundCore_eq _ _ @log2RatApprox_spec q p mode

/-- **`log₂` of a rational with precomputed constants is correctly rounded.** -/
theorem log2RatPrecRoundWith_eq (c : LnConsts) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    log2RatPrecRoundWith c q p mode = roundVal p mode (Spec.log2 ((AzRat.toRat q : ℝ) : EReal)) :=
  log2RatPrecRoundCore_eq _ _ (@log2RatApproxWith_spec c) q p mode

theorem log2RatPrecRoundWith_eq_log2RatPrecRound (c : LnConsts) (q : AzRat) (p : ℕ)
    (mode : RoundingMode) : log2RatPrecRoundWith c q p mode = log2RatPrecRound q p mode := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    simp [log2RatPrecRoundWith, log2RatPrecRound, log2RatPrecRoundCore]
  · have : NeZero p := ⟨hp.ne'⟩
    rw [log2RatPrecRoundWith_eq, log2RatPrecRound_eq]

theorem log2RatWith_eq_log2Rat (c : LnConsts) (q : AzRat) (p : ℕ) :
    log2RatWith c q p = log2Rat q p := by
  unfold log2RatWith log2Rat
  rw [log2RatPrecRoundWith_eq_log2RatPrecRound]

end Azurite.AzFloat
