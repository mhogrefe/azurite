/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Log2P1
import Azurite.AzFloat.Equiv.LogBasePow2
import Azurite.AzFloat.LogBasePow2P1

/-!
# Equivalence: `log_{2^k} (1 + x)`

`logBasePow2P1PrecRound_eq_liftVal : logBasePow2P1PrecRound x k p mode = liftVal (fun a =>
Spec.logBasePow2 k.toInt (a + 1)) x p mode` for `k ≠ 0`: `log_{2^k} (1 + x)` is correctly rounded
in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- The specification of a bracket function for `log_{2^k} (1 + x)`: the conclusion of
`logBasePow2P1Approx_spec`. -/
def LogBasePow2P1ApproxFn (A : AzFloat → AzInt → ℕ → Roundable × Roundable) : Prop :=
  ∀ {w : ℕ}, 64 ≤ w → ∀ {x : AzFloat} {xv : ℝ}, x.toVal = some (xv : EReal) → -1 < xv →
    ∀ (k : AzInt), k ≠ 0 → Irrational (Real.logb 2 (1 + xv) / k.toInt) →
    ∃ lv hv' : ℝ, Rounds (A x k w).1 lv ∧ Rounds (A x k w).2 hv' ∧
      lv < Real.logb 2 (1 + xv) / k.toInt ∧ Real.logb 2 (1 + xv) / k.toInt < hv' ∧
      hv' - lv ≤ logBasePow2RatEps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2) |Real.log (1 + xv)| w

/-- The finite case: the exact branch and the Ziv loop round `log₂ (1 + x) / k`. -/
theorem logBasePow2P1Finite_eq (A : AzFloat → AzInt → ℕ → Roundable × Roundable)
    (hA : ∀ (p : ℕ) [NeZero p] (mode : RoundingMode) {x : AzFloat} {xv : ℝ},
      x.toVal = some (xv : EReal) → -1 < xv → ∀ k : AzInt, k ≠ 0 →
      Irrational (Real.logb 2 (1 + xv) / k.toInt) → ∀ w₀ : ℕ, 0 < w₀ →
      ∃ f : ℕ, (roundingPossible (A x k (w₀ * 2 ^ f)).1 (A x k (w₀ * 2 ^ f)).2 p mode).isSome
        = true)
    (hspec : LogBasePow2P1ApproxFn A)
    (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hgt : -1 < finiteVal s e m) (k : AzInt) (hk : k ≠ 0) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    logBasePow2P1Finite A hA s e hv hgt k hk p mode
      = roundVal p mode
          (some ((Real.logb 2 (1 + finiteVal s e m) / k.toInt : ℝ) : EReal)) := by
  have hpos : 0 < 1 + finiteVal s e m := by linarith
  have hw : NeZero (lnP1Start e p) := ⟨by have := lnP1Start_ge e p; omega⟩
  unfold logBasePow2P1Finite
  split
  · rename_i j hj
    rw [ofAzRatRound_eq_roundVal, AzRat.toRat_ofAzInts,
      onePlusPow2Exponent?_some (toVal_finite s e q m hv) _ hj, logb_two_zpow]
    push_cast
    rfl
  · rename_i hj
    have hirr := Irrational.div_intCast
      (irrational_logb_two_one_add_of_none (toVal_finite s e q m hv)
        (w := lnP1Start e p) (by have := lnP1Start_ge e p; omega) hpos hj)
      (toInt_ne_zero_of_ne_zero hk)
    split
    · next r hT =>
      exact log2P1Pow2Fast?_eq (toVal_finite s e q m hv) (toInt_ne_zero_of_ne_zero hk) hT
    exact zivLoopCertified_eq_threshold p mode _
      (Real.logb 2 (1 + finiteVal s e m) / k.toInt) _ (by have := lnP1Start_ge e p; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          hspec (w := w) (by have := lnP1Start_ge e p; omega)
            (toVal_finite s e q m hv) hgt k hk hirr
        exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

/-- `logBasePow2P1PrecRoundCore A hA` is correctly rounded for every bracket function `A` with
the conclusion of `logBasePow2P1Approx_spec`. -/
theorem logBasePow2P1PrecRoundCore_eq_liftVal (A : AzFloat → AzInt → ℕ → Roundable × Roundable)
    (hA) (hspec : LogBasePow2P1ApproxFn A) (x : AzFloat) (k : AzInt) (hk : k ≠ 0) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    logBasePow2P1PrecRoundCore A hA x k p mode
      = liftVal (fun a => Spec.logBasePow2 k.toInt (a + 1)) x p mode := by
  have hkI := toInt_ne_zero_of_ne_zero hk
  unfold logBasePow2P1PrecRoundCore liftVal
  rw [dite_eq_right hk]
  cases x with
  | nan => rfl
  | infinity s =>
    cases s
    · simp only [toVal_infinity, Bool.false_eq_true, ↓reduceIte, Option.bind_some, EReal.bot_add,
        Spec.logBasePow2_bot, roundVal_none]
    · simp only [toVal_infinity, ↓reduceIte, Option.bind_some]
      rw [← EReal.coe_one, EReal.top_add_coe, Spec.logBasePow2_top _ hkI,
        sign_eq_decide_pos_toInt k hk]
      rcases lt_or_gt_of_ne hkI with h | h
      · rw [ite_eq_right (not_lt.mpr h.le), decide_eq_false (not_lt.mpr h.le)]
        exact (roundVal_inf p mode false).symm
      · rw [ite_eq_left h, decide_eq_true h]
        exact (roundVal_inf p mode true).symm
  | zero =>
    simp only [toVal_zero, Option.bind_some]
    rw [zero_add, ← EReal.coe_one, Spec.logBasePow2_coe _ _ one_pos, Real.logb_one, zero_div,
      EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    cases s with
    | true =>
      have hpos := finiteVal_true_pos e hv
      simp only [toVal_finite, Option.bind_some]
      split_ifs with hp
      · exact absurd hp (NeZero.ne p)
      rw [← EReal.coe_one, ← EReal.coe_add, Spec.logBasePow2_coe _ _ (by linarith),
        add_comm (finiteVal true e m) 1]
      exact logBasePow2P1Finite_eq A hA hspec true e hv _ k hk p mode
    | false =>
      simp only [toVal_finite, Option.bind_some]
      split_ifs with hneg heq hp
      · obtain ⟨v, hx, h1⟩ := (eqIEEE_iff _ _).mp heq
        rw [toVal_finite] at hx
        rw [toVal_neg_one, ← hx, Option.some.injEq, EReal.coe_eq_coe_iff] at h1
        rw [← h1, ← EReal.coe_one, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero,
          Spec.logBasePow2_zero _ hkI, sign_eq_decide_pos_toInt k hk]
        rcases lt_or_gt_of_ne hkI with h | h
        · rw [ite_eq_right (not_lt.mpr h.le), decide_eq_false (not_lt.mpr h.le)]
          exact (roundVal_inf p mode true).symm
        · rw [ite_eq_left h, decide_eq_true h]
          exact (roundVal_inf p mode false).symm
      · have hle := finiteVal_false_le_neg_one e hv hneg
        have hne : finiteVal false e m ≠ -1 := fun h => heq ((eqIEEE_iff _ _).mpr
          ⟨((-1 : ℝ) : EReal), by rw [toVal_finite, h], toVal_neg_one⟩)
        have hlt : finiteVal false e m + 1 < 0 := by
          rcases lt_or_eq_of_le hle with h | h
          · linarith
          · exact absurd h hne
        rw [← EReal.coe_one, ← EReal.coe_add, Spec.logBasePow2_coe_neg _ _ hlt, roundVal_none]
      · exact absurd hp (NeZero.ne p)
      · have hgt := finiteVal_false_gt_neg_one e hv hneg
        rw [← EReal.coe_one, ← EReal.coe_add, Spec.logBasePow2_coe _ _ (by linarith),
          add_comm (finiteVal false e m) 1]
        exact logBasePow2P1Finite_eq A hA hspec false e hv hgt k hk p mode

/-- **`log_{2^k} (1 + x)` is correctly rounded.** -/
theorem logBasePow2P1PrecRound_eq_liftVal (x : AzFloat) (k : AzInt) (hk : k ≠ 0) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    logBasePow2P1PrecRound x k p mode
      = liftVal (fun a => Spec.logBasePow2 k.toInt (a + 1)) x p mode :=
  logBasePow2P1PrecRoundCore_eq_liftVal _ _ @logBasePow2P1Approx_spec x k hk p mode

/-- **`log_{2^k} (1 + x)` with precomputed constants is correctly rounded.** -/
theorem logBasePow2P1PrecRoundWith_eq_liftVal (c : LnConsts) (x : AzFloat) (k : AzInt)
    (hk : k ≠ 0) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    logBasePow2P1PrecRoundWith c x k p mode
      = liftVal (fun a => Spec.logBasePow2 k.toInt (a + 1)) x p mode :=
  logBasePow2P1PrecRoundCore_eq_liftVal _ _ (@logBasePow2P1ApproxWith_spec c) x k hk p mode

theorem logBasePow2P1PrecRoundWith_eq_logBasePow2P1PrecRound (c : LnConsts) (x : AzFloat)
    (k : AzInt) (p : ℕ) (mode : RoundingMode) :
    logBasePow2P1PrecRoundWith c x k p mode = logBasePow2P1PrecRound x k p mode := by
  by_cases hk : k = 0
  · subst hk
    simp [logBasePow2P1PrecRoundWith, logBasePow2P1PrecRound, logBasePow2P1PrecRoundCore]
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    cases x with
    | finite s e q m hv =>
      cases s <;>
        simp [logBasePow2P1PrecRoundWith, logBasePow2P1PrecRound, logBasePow2P1PrecRoundCore]
    | _ => rfl
  · have : NeZero p := ⟨hp.ne'⟩
    rw [logBasePow2P1PrecRoundWith_eq_liftVal c x k hk, logBasePow2P1PrecRound_eq_liftVal x k hk]

theorem logBasePow2P1With_eq_logBasePow2P1 (c : LnConsts) (x : AzFloat) (k : AzInt) :
    logBasePow2P1With c x k = logBasePow2P1 x k := by
  unfold logBasePow2P1With logBasePow2P1
  rw [logBasePow2P1PrecRoundWith_eq_logBasePow2P1PrecRound]

end Azurite.AzFloat
