/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LogBase
import Azurite.AzFloat.Equiv.LogBasePow2Rat
import Azurite.AzFloat.LogBaseRat

/-!
# Equivalence: the logarithm of a rational in a natural base

* `logBaseRatPrecRound_eq : logBaseRatPrecRound q b p mode = roundVal p mode (Spec.logBase
  b.toNat (toRat q))` for `2 ≤ b`: `log_b` of a rational is correctly rounded in every mode, with
  the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- `logBaseRatPrecRoundCore b P2 A hA` is correctly rounded for every correctly rounded
power-of-two driver `P2` and every bracket function `A` with the conclusion of
`logBaseRatApprox_spec`. -/
theorem logBaseRatPrecRoundCore_eq (b : UInt64)
    (P2 : AzRat → AzInt → ℕ → RoundingMode → AzFloat × Ordering)
    (A : AzRat → ℕ → Roundable × Roundable) (hA)
    (hP2 : ∀ (q : AzRat) (k : AzInt), k ≠ 0 → ∀ (p : ℕ) [NeZero p] (mode : RoundingMode),
      P2 q k p mode = roundVal p mode (Spec.logBasePow2 k.toInt ((AzRat.toRat q : ℝ) : EReal)))
    (hspec : ∀ {w : ℕ}, 64 ≤ w → ∀ (q : AzRat), (0 : ℚ) < AzRat.toRat q → 2 ≤ b.toNat →
      Irrational (Real.log (AzRat.toRat q : ℝ) / Real.log b.toNat) →
      ∃ lv hv' : ℝ, Rounds (A q w).1 lv ∧ Rounds (A q w).2 hv' ∧
        lv < Real.log (AzRat.toRat q : ℝ) / Real.log b.toNat ∧
        Real.log (AzRat.toRat q : ℝ) / Real.log b.toNat < hv' ∧
        hv' - lv ≤ logBaseRatEps (⌊2 * |Real.log (AzRat.toRat q : ℝ)|⌋₊ + 2)
          ((baseFloat b).exponent?.getD 0).toInt |Real.log (AzRat.toRat q : ℝ)| w)
    (q : AzRat) (hb : 2 ≤ b.toNat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    logBaseRatPrecRoundCore b P2 A hA q p mode
      = roundVal p mode (Spec.logBase b.toNat ((AzRat.toRat q : ℝ) : EReal)) := by
  unfold logBaseRatPrecRoundCore
  rw [dite_eq_right (not_lt.mpr hb)]
  split
  · -- a power-of-two base delegates
    next k hk =>
      have hbk : b.toNat = 2 ^ k := by
        have := (AzNat.checkedLogBase2_eq_some_iff _ k).mp hk
        rwa [AzNat.toNat_ofNat] at this
      have hk0 : (AzNat.ofNat k).toAzInt ≠ 0 := by
        intro h0
        have h1 := congrArg AzInt.toInt h0
        rw [toInt_toAzInt, AzNat.toNat_ofNat, show (0 : AzInt).toInt = 0 from rfl] at h1
        have : k = 0 := by exact_mod_cast h1
        subst this
        omega
      rw [hP2 q _ hk0 p mode, toInt_toAzInt, AzNat.toNat_ofNat, hbk, Spec.logBase_two_pow]
  · next =>
    split_ifs with h0 hs hp
    · rw [(AzRat.toRat_eq_zero_iff q).mpr h0, EReal.coe_zero, Spec.logBase_zero _ hb]
      exact (roundVal_inf p mode false).symm
    · exact absurd hp (NeZero.ne p)
    · have hq := toRat_pos_of_sign q hs h0
      have hqr : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
      rw [Spec.logBase_coe _ hb _ hqr]
      split
      · rename_i r hx
        have hval := logBaseExactRat?_some q hq _ (by rw [AzNat.toNat_ofNat]; exact hb)
          (by rw [AzNat.toNat_ofNat]; exact b.toBitVec.isLt) r hx
        rw [AzNat.toNat_ofNat] at hval
        rw [ofAzRatRound_eq_roundVal, ← hval]
      · rename_i hx
        exact zivLoopCertified_eq_threshold p mode _
          (Real.log (AzRat.toRat q : ℝ) / Real.log b.toNat) _ (by unfold zivGuardBits; omega)
          (fun w hw => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
              hspec (w := w) (by unfold zivGuardBits at hw; omega) q hq hb
                (AzNat.toNat_ofNat b.toNat ▸
                  irrational_of_logBaseExactRat?_none q hq (AzNat.ofNat b.toNat)
                    (by rw [AzNat.toNat_ofNat]; exact hb)
                    (by rw [AzNat.toNat_ofNat]; exact b.toBitVec.isLt) hx)
            exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _
    · have hneg := toRat_neg_of_sign q (by simpa using hs) h0
      rw [Spec.logBase_coe_neg _ _ hneg, roundVal_none]

/-- **`log_b` of a rational is correctly rounded.** -/
theorem logBaseRatPrecRound_eq (q : AzRat) (b : UInt64) (hb : 2 ≤ b.toNat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    logBaseRatPrecRound q b p mode
      = roundVal p mode (Spec.logBase b.toNat ((AzRat.toRat q : ℝ) : EReal)) :=
  logBaseRatPrecRoundCore_eq b _ _ _
    (fun q k hk p _ mode => logBasePow2RatPrecRound_eq q k hk p mode)
    (fun hw q hq hb hirr => logBaseRatApprox_spec hw q hq b hb hirr) q hb p mode

/-- **`log_b` of a rational with precomputed constants is correctly rounded.** -/
theorem logBaseRatPrecRoundWith_eq (cb : LogBaseConsts) (q : AzRat) (hb : 2 ≤ cb.base.toNat)
    (p : ℕ) [NeZero p] (mode : RoundingMode) :
    logBaseRatPrecRoundWith cb q p mode
      = roundVal p mode (Spec.logBase cb.base.toNat ((AzRat.toRat q : ℝ) : EReal)) :=
  logBaseRatPrecRoundCore_eq cb.base _ _ _
    (fun q k hk p _ mode => logBasePow2RatPrecRoundWith_eq cb.ln q k hk p mode)
    (fun hw q hq hb hirr => logBaseRatApproxWith_spec cb hw q hq hb hirr) q hb p mode

theorem logBaseRatPrecRoundWith_eq_logBaseRatPrecRound (cb : LogBaseConsts) (q : AzRat) (p : ℕ)
    (mode : RoundingMode) :
    logBaseRatPrecRoundWith cb q p mode = logBaseRatPrecRound q cb.base p mode := by
  by_cases hb : cb.base.toNat < 2
  · simp [logBaseRatPrecRoundWith, logBaseRatPrecRound, logBaseRatPrecRoundCore, hb]
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    unfold logBaseRatPrecRoundWith logBaseRatPrecRound logBaseRatPrecRoundCore
    rw [dite_eq_right hb, dite_eq_right hb]
    split
    · rw [logBasePow2RatPrecRoundWith_eq_logBasePow2RatPrecRound]
    · simp
  · have : NeZero p := ⟨hp.ne'⟩
    rw [logBaseRatPrecRoundWith_eq cb q (not_lt.mp hb),
      logBaseRatPrecRound_eq q cb.base (not_lt.mp hb)]

theorem logBaseRatWith_eq_logBaseRat (cb : LogBaseConsts) (q : AzRat) (p : ℕ) :
    logBaseRatWith cb q p = logBaseRat q cb.base p := by
  unfold logBaseRatWith logBaseRat
  rw [logBaseRatPrecRoundWith_eq_logBaseRatPrecRound]

end Azurite.AzFloat
