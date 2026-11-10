/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Log2P1
import Azurite.AzFloat.Equiv.Log2

/-!
# Equivalence: `log₂ (1 + x)`

`log2P1PrecRound_eq_liftVal : log2P1PrecRound x p mode = liftVal (fun a => Spec.log2 (a + 1)) x p
mode`: `log₂ (1 + x)` is correctly rounded in every mode, with the exact comparison, and
without fuel.
-/

namespace Azurite.AzFloat

/-- The specification of a bracket function for `log₂ (1 + x)`: the conclusion of
`log2P1Approx_spec`. -/
def Log2P1ApproxFn (A : AzFloat → ℕ → Roundable × Roundable) : Prop :=
  ∀ {w : ℕ}, 64 ≤ w → ∀ {x : AzFloat} {xv : ℝ}, x.toVal = some (xv : EReal) → -1 < xv →
    Irrational (Real.logb 2 (1 + xv)) →
    ∃ lv hv : ℝ, Rounds (A x w).1 lv ∧ Rounds (A x w).2 hv ∧
      lv < Real.logb 2 (1 + xv) ∧ Real.logb 2 (1 + xv) < hv ∧
      hv - lv ≤ log2RatEps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2) |Real.log (1 + xv)| w

/-- The finite case of `log2P1PrecRoundCore`: the exact branch or the Ziv loop. -/
theorem log2P1_finite_eq (A : AzFloat → ℕ → Roundable × Roundable)
    (hA : ∀ (p : ℕ) [NeZero p] (mode : RoundingMode) {x : AzFloat} {xv : ℝ},
      x.toVal = some (xv : EReal) → -1 < xv → Irrational (Real.logb 2 (1 + xv)) →
      ∀ w₀ : ℕ, 0 < w₀ →
      ∃ f : ℕ, (roundingPossible (A x (w₀ * 2 ^ f)).1 (A x (w₀ * 2 ^ f)).2 p mode).isSome = true)
    (hspec : Log2P1ApproxFn A)
    (p : ℕ) [NeZero p] (mode : RoundingMode) (s : Bool) (e : AzInt) {q : ℕ}
    {m : AzNat} (hv : FiniteValid q m) (hgt : -1 < finiteVal s e m) :
    (match h : onePlusPow2Exponent? (finite s e q m hv) (lnP1Start e p)
        with
      | some k => setPrecRound (ofAzInt k) p mode
      | none =>
        match log2P1Pow2Fast? (finite s e q m hv) (AzInt.ofInt 1) p mode with
        | some r => r
        | none =>
        zivLoopCertified (A (finite s e q m hv)) p mode
          (lnP1Start e p)
          (hA p mode (toVal_finite s e q m hv) hgt
            (irrational_logb_two_one_add_of_none (toVal_finite s e q m hv)
              (by have := lnP1Start_ge e p; omega) (by linarith) h)
            _ (by have := lnP1Start_ge e p; omega)))
      = roundVal p mode (some ((Real.logb 2 (1 + finiteVal s e m) : ℝ) : EReal)) := by
  have hpos : 0 < 1 + finiteVal s e m := by linarith
  have hw : NeZero (lnP1Start e p) := ⟨by have := lnP1Start_ge e p; omega⟩
  split
  · rename_i k h
    rw [setPrecRound_eq_roundVal (toVal_ofAzInt k),
      onePlusPow2Exponent?_some (toVal_finite s e q m hv) _ h, logb_two_zpow]
  · rename_i h
    have hirr := irrational_logb_two_one_add_of_none (toVal_finite s e q m hv)
      (w := lnP1Start e p) (by have := lnP1Start_ge e p; omega) hpos h
    split
    · next r hT =>
      have := log2P1Pow2Fast?_eq (toVal_finite s e q m hv) (k := AzInt.ofInt 1)
        (by rw [AzInt.toInt_ofInt]; norm_num) hT
      rwa [AzInt.toInt_ofInt, Int.cast_one, div_one] at this
    exact zivLoopCertified_eq_threshold p mode _ (Real.logb 2 (1 + finiteVal s e m)) _
      (by have := lnP1Start_ge e p; omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
          hspec (w := w) (by have := lnP1Start_ge e p; omega)
            (toVal_finite s e q m hv) hgt hirr
        exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

/-- `log2P1PrecRoundCore A hA` is correctly rounded for every bracket function `A` with the
conclusion of `log2P1Approx_spec`. -/
theorem log2P1PrecRoundCore_eq_liftVal (A : AzFloat → ℕ → Roundable × Roundable) (hA)
    (hspec : Log2P1ApproxFn A) (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log2P1PrecRoundCore A hA x p mode = liftVal (fun a => Spec.log2 (a + 1)) x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    cases s
    · simp only [log2P1PrecRoundCore, toVal_infinity, Bool.false_eq_true, ↓reduceIte,
        Option.bind_some, EReal.bot_add, Spec.log2_bot, roundVal_none]
    · simp only [log2P1PrecRoundCore, toVal_infinity, ↓reduceIte, Option.bind_some]
      rw [← EReal.coe_one, EReal.top_add_coe, Spec.log2_top, roundVal_top]
  | zero =>
    simp only [log2P1PrecRoundCore, toVal_zero, Option.bind_some]
    rw [zero_add, ← EReal.coe_one, Spec.log2_coe _ one_pos, Real.logb_one, EReal.coe_zero,
      roundVal_zero]
  | finite s e q m hv =>
    cases s with
    | true =>
      have hpos := finiteVal_true_pos e hv
      simp only [log2P1PrecRoundCore, toVal_finite, Option.bind_some]
      split_ifs with hp
      · exact absurd hp (NeZero.ne p)
      rw [← EReal.coe_one, ← EReal.coe_add, Spec.log2_coe _ (by linarith),
        add_comm (finiteVal true e m) 1]
      exact log2P1_finite_eq A hA hspec p mode true e hv (by linarith)
    | false =>
      simp only [log2P1PrecRoundCore, toVal_finite, Option.bind_some]
      split_ifs with hneg heq hp
      · obtain ⟨v, hx, h1⟩ := (eqIEEE_iff _ _).mp heq
        rw [toVal_finite] at hx
        rw [toVal_neg_one, ← hx, Option.some.injEq, EReal.coe_eq_coe_iff] at h1
        rw [← h1, ← EReal.coe_one, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero,
          Spec.log2_zero, roundVal_bot]
      · have hle := finiteVal_false_le_neg_one e hv hneg
        have hne : finiteVal false e m ≠ -1 := fun h => heq ((eqIEEE_iff _ _).mpr
          ⟨((-1 : ℝ) : EReal), by rw [toVal_finite, h], toVal_neg_one⟩)
        have hlt : finiteVal false e m + 1 < 0 := by
          rcases lt_or_eq_of_le hle with h | h
          · linarith
          · exact absurd h hne
        rw [← EReal.coe_one, ← EReal.coe_add, Spec.log2_coe_neg _ hlt, roundVal_none]
      · exact absurd hp (NeZero.ne p)
      · have hgt := finiteVal_false_gt_neg_one e hv hneg
        rw [← EReal.coe_one, ← EReal.coe_add, Spec.log2_coe _ (by linarith),
          add_comm (finiteVal false e m) 1]
        exact log2P1_finite_eq A hA hspec p mode false e hv hgt

/-- **`log₂ (1 + x)` is correctly rounded.** -/
theorem log2P1PrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    log2P1PrecRound x p mode = liftVal (fun a => Spec.log2 (a + 1)) x p mode :=
  log2P1PrecRoundCore_eq_liftVal _ _ @log2P1Approx_spec x p mode

/-- **`log₂ (1 + x)` with precomputed constants is correctly rounded.** -/
theorem log2P1PrecRoundWith_eq_liftVal (c : LnConsts) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    log2P1PrecRoundWith c x p mode = liftVal (fun a => Spec.log2 (a + 1)) x p mode :=
  log2P1PrecRoundCore_eq_liftVal _ _ (@log2P1ApproxWith_spec c) x p mode

theorem log2P1PrecRoundWith_eq_log2P1PrecRound (c : LnConsts) (x : AzFloat) (p : ℕ)
    (mode : RoundingMode) : log2P1PrecRoundWith c x p mode = log2P1PrecRound x p mode := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    cases x with
    | finite s e q m hv =>
      cases s <;> simp [log2P1PrecRoundWith, log2P1PrecRound, log2P1PrecRoundCore]
    | _ => rfl
  · have : NeZero p := ⟨hp.ne'⟩
    rw [log2P1PrecRoundWith_eq_liftVal, log2P1PrecRound_eq_liftVal]

theorem log2P1With_eq_log2P1 (c : LnConsts) (x : AzFloat) : log2P1With c x = log2P1 x := by
  unfold log2P1With log2P1
  rw [log2P1PrecRoundWith_eq_log2P1PrecRound]

end Azurite.AzFloat
