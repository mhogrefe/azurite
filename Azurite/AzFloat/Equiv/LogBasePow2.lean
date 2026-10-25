/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBasePow2
import Azurite.AzFloat.Equiv.Log2
import Azurite.AzRat.Equiv.Construct

/-!
# Equivalence: the logarithm in a power-of-two base

* `Spec.logBasePow2 k a = (Spec.log2 a).map (· * ↑(k⁻¹))`: `log₂` scaled by `1/k` in the
  extended reals, so `log_{2^k} ∞ = ±∞` and `log_{2^k} 0 = ∓∞` by the sign of `k`.
* `logBasePow2PrecRound_eq_liftVal : logBasePow2PrecRound x k p mode =
  liftVal (Spec.logBasePow2 k.toInt) x p mode` for `k ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

/-- Extended-real `log_{2^k}`: `log₂` scaled by `1/k`. -/
noncomputable def logBasePow2 (k : ℤ) (a : EReal) : Option EReal :=
  (log2 a).map fun L => L * (((k : ℝ)⁻¹ : ℝ) : EReal)

theorem logBasePow2_coe (k : ℤ) (r : ℝ) (hr : 0 < r) :
    logBasePow2 k (r : EReal) = some ((Real.logb 2 r / k : ℝ) : EReal) := by
  unfold logBasePow2
  rw [log2_coe r hr, Option.map_some, ← EReal.coe_mul, div_eq_mul_inv]

theorem logBasePow2_coe_neg (k : ℤ) (r : ℝ) (hr : r < 0) : logBasePow2 k (r : EReal) = none := by
  unfold logBasePow2
  rw [log2_coe_neg r hr, Option.map_none]

theorem logBasePow2_top (k : ℤ) (hk : k ≠ 0) :
    logBasePow2 k ⊤ = some (if 0 < k then ⊤ else ⊥) := by
  unfold logBasePow2
  rw [log2_top, Option.map_some]
  rcases lt_or_gt_of_ne hk with h | h
  · rw [ite_eq_right (not_lt.mpr h.le), EReal.top_mul_coe_of_neg (by simpa using h)]
  · rw [ite_eq_left h, EReal.top_mul_coe_of_pos (by simpa using h)]

theorem logBasePow2_zero (k : ℤ) (hk : k ≠ 0) :
    logBasePow2 k 0 = some (if 0 < k then ⊥ else ⊤) := by
  unfold logBasePow2
  rw [log2_zero, Option.map_some]
  rcases lt_or_gt_of_ne hk with h | h
  · rw [ite_eq_right (not_lt.mpr h.le), EReal.bot_mul_coe_of_neg (by simpa using h)]
  · rw [ite_eq_left h, EReal.bot_mul_coe_of_pos (by simpa using h)]

@[simp] theorem logBasePow2_bot (k : ℤ) : logBasePow2 k ⊥ = none := by
  unfold logBasePow2
  rw [log2_bot, Option.map_none]

end Spec

theorem sign_eq_decide_pos_toInt (k : AzInt) (hk : k ≠ 0) : k.sign = decide (0 < k.toInt) := by
  have hne := toInt_ne_zero_of_ne_zero hk
  rw [Bool.eq_iff_iff, AzInt.sign_eq_true_iff, decide_eq_true_iff]
  constructor
  · intro h; exact lt_of_le_of_ne h (Ne.symm hne)
  · intro h; exact h.le

/-- **`log_{2^k}` is correctly rounded.** -/
theorem logBasePow2PrecRound_eq_liftVal (x : AzFloat) (k : AzInt) (hk : k ≠ 0) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    logBasePow2PrecRound x k p mode = liftVal (Spec.logBasePow2 k.toInt) x p mode := by
  have hkI := toInt_ne_zero_of_ne_zero hk
  unfold logBasePow2PrecRound liftVal
  rw [dite_eq_right hk]
  cases x with
  | nan => rfl
  | infinity s =>
    cases s
    · simp
    · simp only [↓reduceIte, toVal_infinity, Option.bind_some, Spec.logBasePow2_top _ hkI]
      rw [sign_eq_decide_pos_toInt k hk]
      rcases lt_or_gt_of_ne hkI with h | h
      · rw [ite_eq_right (not_lt.mpr h.le), decide_eq_false (not_lt.mpr h.le)]
        exact (roundVal_inf p mode false).symm
      · rw [ite_eq_left h, decide_eq_true h]
        exact (roundVal_inf p mode true).symm
  | zero =>
    simp only [toVal_zero, Option.bind_some, Spec.logBasePow2_zero _ hkI]
    rw [sign_eq_decide_pos_toInt k hk]
    rcases lt_or_gt_of_ne hkI with h | h
    · rw [ite_eq_right (not_lt.mpr h.le), decide_eq_false (not_lt.mpr h.le)]
      exact (roundVal_inf p mode true).symm
    · rw [ite_eq_left h, decide_eq_true h]
      exact (roundVal_inf p mode false).symm
  | finite s e q m hv =>
    cases s with
    | true =>
      have hv0 := finiteVal_true_pos e hv
      simp only [toVal_finite, Option.bind_some, Spec.logBasePow2_coe _ _ hv0]
      split_ifs with hp h2
      · exact absurd hp (NeZero.ne p)
      · rw [ofAzRatRound_eq_roundVal, AzRat.toRat_ofAzInts, finiteVal_true_of_isPowerOfTwo e m h2,
          logb_two_zpow, AzInt.toInt_sub]
        push_cast
        rw [show (1 : AzInt).toInt = 1 from rfl, Int.cast_one]
      · rw [← Real.log_div_log]
        exact zivLoopCertified_eq_threshold p mode _
          (Real.log (finiteVal true e m) / Real.log 2 / k.toInt) _ (by unfold zivGuardBits; omega)
          (fun w hw => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
              logBasePow2Approx_spec (w := w) (by unfold zivGuardBits at hw; omega) e hv
                (Bool.eq_false_iff.mpr h2) k hk
            exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _
    | false =>
      simp only [toVal_finite]
      rw [finiteVal_false, Option.bind_some,
        Spec.logBasePow2_coe_neg _ _ (neg_neg_iff_pos.mpr (finiteVal_true_pos e hv)), roundVal_none]

end Azurite.AzFloat
