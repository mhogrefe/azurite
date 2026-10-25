/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBase
import Azurite.AzFloat.Equiv.LogBasePow2
import Azurite.AzNat.Equiv.LogBase2

/-!
# Equivalence: the logarithm in a natural base

* `Spec.logBase b a = (Spec.log2 a).map (· * ↑((logb 2 b)⁻¹))`: `log₂` scaled by `1 / log₂ b`
  in the extended reals (`log_b (+∞) = +∞`, `log_b 0 = −∞`, `NaN` on negatives).
* `logBasePrecRound_eq_liftVal : logBasePrecRound x b p mode = liftVal (Spec.logBase b.toNat) x
  p mode` for `2 ≤ b`: `log_b` is correctly rounded in every mode, with the exact comparison,
  and without fuel.
-/

namespace Azurite.AzFloat

/-! ### The specification -/

namespace Spec

/-- Extended-real `log_b`: `log₂` scaled by `1 / log₂ b`. -/
noncomputable def logBase (b : ℕ) (a : EReal) : Option EReal :=
  (log2 a).map fun L => L * (((Real.logb 2 b)⁻¹ : ℝ) : EReal)

theorem logBase_coe (b : ℕ) (hb : 2 ≤ b) (r : ℝ) (hr : 0 < r) :
    logBase b (r : EReal) = some ((Real.log r / Real.log b : ℝ) : EReal) := by
  unfold logBase
  rw [log2_coe r hr, Option.map_some, ← EReal.coe_mul]
  congr 2
  have h2 : Real.log 2 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one two_pos (by norm_num)
  have hb' : Real.log b ≠ 0 := (log_pos_of_two_le hb).ne'
  unfold Real.logb
  field_simp

theorem logBase_coe_neg (b : ℕ) (r : ℝ) (hr : r < 0) : logBase b (r : EReal) = none := by
  unfold logBase
  rw [log2_coe_neg r hr, Option.map_none]

theorem logBase_top (b : ℕ) (hb : 2 ≤ b) : logBase b ⊤ = some ⊤ := by
  unfold logBase
  rw [log2_top, Option.map_some, EReal.top_mul_coe_of_pos]
  exact inv_pos.mpr (Real.logb_pos one_lt_two (by exact_mod_cast hb))

theorem logBase_zero (b : ℕ) (hb : 2 ≤ b) : logBase b 0 = some ⊥ := by
  unfold logBase
  rw [log2_zero, Option.map_some, EReal.bot_mul_coe_of_pos]
  exact inv_pos.mpr (Real.logb_pos one_lt_two (by exact_mod_cast hb))

@[simp] theorem logBase_bot (b : ℕ) : logBase b ⊥ = none := by
  unfold logBase
  rw [log2_bot, Option.map_none]

/-- A power-of-two base is the scaled `log₂`. -/
theorem logBase_two_pow (k : ℕ) : logBase (2 ^ k) = logBasePow2 (k : ℤ) := by
  funext a
  unfold logBase logBasePow2
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one,
    Int.cast_natCast]

end Spec

/-! ### The equivalence -/

/-- **`log_b` is correctly rounded.** -/
theorem logBasePrecRound_eq_liftVal (x : AzFloat) (b : UInt64) (hb : 2 ≤ b.toNat) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    logBasePrecRound x b p mode = liftVal (Spec.logBase b.toNat) x p mode := by
  unfold logBasePrecRound
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
      rw [logBasePow2PrecRound_eq_liftVal x _ hk0 p mode, toInt_toAzInt, AzNat.toNat_ofNat, hbk,
        Spec.logBase_two_pow]
  · next hnone =>
    unfold liftVal
    cases x with
    | nan => rfl
    | infinity s =>
      cases s
      · simp
      · simp only [↓reduceIte, toVal_infinity, Option.bind_some, Spec.logBase_top _ hb]
        exact (roundVal_inf p mode true).symm
    | zero =>
      simp only [toVal_zero, Option.bind_some, Spec.logBase_zero _ hb]
      exact (roundVal_inf p mode false).symm
    | finite s e q m hv =>
      cases s with
      | true =>
        have hv0 := finiteVal_true_pos e hv
        simp only [toVal_finite, Option.bind_some, Spec.logBase_coe _ hb _ hv0]
        rw [dite_eq_right (NeZero.ne p)]
        split
        · next r hx =>
          obtain ⟨v, hvv, -, hval⟩ :=
            logBaseExact?_some _ _ (by rw [AzNat.toNat_ofNat]; exact hb) r hx
          rw [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hvv
          rw [ofAzRatRound_eq_roundVal, ← hval, hvv, AzNat.toNat_ofNat]
        · next hx =>
          exact zivLoopCertified_eq_threshold p mode _
            (Real.log (finiteVal true e m) / Real.log b.toNat) _ (by unfold zivGuardBits; omega)
            (fun w hw => by
              obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
                logBaseApprox_spec (w := w) (by unfold zivGuardBits at hw; omega) e hv b hb
                  (AzNat.toNat_ofNat b.toNat ▸
                    irrational_of_logBaseExact?_none e hv (AzNat.ofNat b.toNat)
                    (by rw [AzNat.toNat_ofNat]; exact hb)
                    (by rw [AzNat.toNat_ofNat]; exact b.toBitVec.isLt)
                    ((AzNat.checkedLogBase2_eq_none_iff _).mp hnone) hx)
              exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _
      | false =>
        simp only [toVal_finite]
        rw [finiteVal_false, Option.bind_some,
          Spec.logBase_coe_neg _ _ (neg_neg_iff_pos.mpr (finiteVal_true_pos e hv)), roundVal_none]

end Azurite.AzFloat
